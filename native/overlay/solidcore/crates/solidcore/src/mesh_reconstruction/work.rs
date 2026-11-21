//! Workflow-owned opaque counters and borrowed native cancellation views.
use super::types::{MeshError, Result};
use crate::Kernel;
use std::cell::{Cell, RefCell};
const LIMIT: usize = 200_000_000;
const CELL_LIMIT: usize = 2_000_000;
const OUTPUT_LIMIT: usize = 200_000;
const OP: &str = "mesh_reconstruction::workflow_budget";
/// One complete mesh command's counters; nonClone, local, and independent of Kernel lifetime.
#[derive(Debug)]
pub struct MeshWork {
    remaining: Cell<usize>,
    cells: Cell<usize>,
    outputs: Cell<usize>,
    exhausted: Cell<u8>,
    failure: RefCell<Option<crate::SolidError>>,
}
impl Default for MeshWork {
    fn default() -> Self {
        Self::new()
    }
}
impl MeshWork {
    /// Start exactly one complete command, passing this same object through all stages.
    #[must_use]
    pub fn new() -> Self {
        Self {
            remaining: Cell::new(LIMIT),
            cells: Cell::new(CELL_LIMIT),
            outputs: Cell::new(OUTPUT_LIMIT),
            exhausted: Cell::new(0),
            failure: RefCell::new(None),
        }
    }
    fn take(&self, counter: &Cell<usize>, count: usize, kind: u8) -> bool {
        let Some(left) = counter.get().checked_sub(count) else {
            self.exhausted.set(self.exhausted.get() | kind);
            return false;
        };
        counter.set(left);
        true
    }
    pub(crate) fn try_spend(&self, count: usize) -> bool {
        self.take(&self.remaining, count, 1)
    }
    pub(crate) fn try_reserve_cells(&self, count: usize) -> bool {
        self.take(&self.cells, count, 2)
    }
    pub(crate) fn try_reserve_output(&self, count: usize) -> bool {
        self.take(&self.outputs, count, 4)
    }
    /// Check before classifying any stage refusal or adopting an output. Cancellation and
    /// actual Core errors remain their original types; latched budget failures stay typed.
    pub fn check(&self, k: &Kernel) -> Result<()> {
        k.check_cancelled(OP)?;
        if let Some(error) = self.failure.borrow().as_ref() {
            return Err(MeshError::Kernel(error.clone()));
        }
        let flags = self.exhausted.get();
        if flags & 1 != 0 {
            return Err(MeshError::BudgetExceeded {
                stage: "complete mesh workflow work",
                limit: LIMIT,
            });
        }
        if flags & 2 != 0 {
            return Err(MeshError::BudgetExceeded {
                stage: "complete mesh workflow certificate cells",
                limit: CELL_LIMIT,
            });
        }
        if flags & 4 != 0 {
            return Err(MeshError::BudgetExceeded {
                stage: "complete mesh workflow output references",
                limit: OUTPUT_LIMIT,
            });
        }
        Ok(())
    }
    pub(crate) fn spend(&self, k: &Kernel, n: usize) -> Result<()> {
        let _ = self.try_spend(n);
        self.check(k)
    }
    pub(crate) fn reserve_cells(&self, k: &Kernel, n: usize) -> Result<()> {
        let _ = self.try_reserve_cells(n);
        self.check(k)
    }
    pub(crate) fn reserve_output(&self, k: &Kernel, n: usize) -> Result<()> {
        let _ = self.try_reserve_output(n);
        self.check(k)
    }
    fn core_result(&self, k: &Kernel) -> crate::Result<()> {
        match self.check(k) {
            Ok(()) => Ok(()),
            Err(MeshError::Kernel(error)) => Err(error),
            Err(_) => Err(crate::SolidError::Unsupported {
                operation: OP,
                reason: "complete mesh workflow budget exhausted",
            }),
        }
    }
    pub(crate) fn spend_core(&self, k: &Kernel, n: usize) -> crate::Result<()> {
        let _ = self.try_spend(n);
        self.core_result(k)
    }
    pub(crate) fn reserve_cells_core(&self, k: &Kernel, n: usize) -> crate::Result<()> {
        let _ = self.try_reserve_cells(n);
        self.core_result(k)
    }
    pub(crate) fn reserve_output_core(&self, k: &Kernel, n: usize) -> crate::Result<()> {
        let _ = self.try_reserve_output(n);
        self.core_result(k)
    }
    fn capture<T>(&self, value: crate::Result<T>) -> Option<T> {
        match value {
            Ok(v) => Some(v),
            Err(error) => {
                let vacant = self.failure.borrow().is_none();
                if vacant {
                    *self.failure.borrow_mut() = Some(error);
                }
                None
            }
        }
    }
}
enum Storage<'a> {
    Owned(MeshWork),
    Borrowed(&'a MeshWork),
}
pub(crate) struct Work<'a> {
    kernel: &'a Kernel,
    storage: Storage<'a>,
}
impl<'a> Work<'a> {
    pub fn new(kernel: &'a Kernel) -> Result<Self> {
        kernel.check_cancelled(OP)?;
        Ok(Self {
            kernel,
            storage: Storage::Owned(MeshWork::new()),
        })
    }
    pub fn with_budget(kernel: &'a Kernel, budget: &'a MeshWork) -> Result<Self> {
        budget.check(kernel)?;
        Ok(Self {
            kernel,
            storage: Storage::Borrowed(budget),
        })
    }
    pub(crate) fn budget(&self) -> &MeshWork {
        match &self.storage {
            Storage::Owned(b) => b,
            Storage::Borrowed(b) => b,
        }
    }
    pub(crate) fn kernel(&self) -> &Kernel {
        self.kernel
    }

    pub fn try_spend(&self, n: usize) -> bool {
        !self.kernel.is_cancelled() && self.budget().try_spend(n)
    }
    pub fn check(&self) -> Result<()> {
        self.budget().check(self.kernel)
    }
    pub fn spend(&self, n: usize) -> Result<()> {
        self.budget().spend(self.kernel, n)
    }
    pub fn core<T>(&self, value: crate::Result<T>) -> Option<T> {
        self.budget().capture(value)
    }
    pub fn invariant(&self, reason: &'static str) {
        let _ = self.core::<()>(Err(crate::SolidError::port_invariant(
            "mesh_reconstruction::numeric",
            reason,
        )));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn multiple_stages_share_one_cumulative_work_counter() {
        let k = Kernel::default();
        let budget = MeshWork::new();
        budget.spend(&k, LIMIT - 2).unwrap();
        Work::with_budget(&k, &budget).unwrap().spend(1).unwrap();
        Work::with_budget(&k, &budget).unwrap().spend(1).unwrap();
        assert!(matches!(
            Work::with_budget(&k, &budget).unwrap().spend(1),
            Err(MeshError::BudgetExceeded { limit: LIMIT, .. })
        ));
    }
    #[test]
    fn cell_and_output_reservations_are_shared_and_latched() {
        let k = Kernel::default();
        let budget = MeshWork::new();
        budget.reserve_cells(&k, CELL_LIMIT - 1).unwrap();
        budget.reserve_cells(&k, 1).unwrap();
        assert!(budget.reserve_cells_core(&k, 1).is_err());
        assert!(matches!(
            budget.check(&k),
            Err(MeshError::BudgetExceeded {
                limit: CELL_LIMIT,
                ..
            })
        ));
        let budget = MeshWork::new();
        budget.reserve_output(&k, OUTPUT_LIMIT).unwrap();
        assert!(budget.reserve_output_core(&k, 1).is_err());
        assert!(matches!(
            budget.check(&k),
            Err(MeshError::BudgetExceeded {
                limit: OUTPUT_LIMIT,
                ..
            })
        ));
    }
    #[test]
    fn kernel_cancellation_remains_typed_and_is_not_a_budget_refusal() {
        let token = crate::kernel::CancelToken::new();
        let mut k = Kernel::default();
        k.set_cancel_token(token.clone());
        let budget = MeshWork::new();
        token.cancel();
        assert!(matches!(budget.check(&k),Err(MeshError::Kernel(error)) if error.is_cancelled()));
    }
}
