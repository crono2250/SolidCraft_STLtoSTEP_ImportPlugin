//! Deliberate expected-refusal policy for optional certificate steering.
//! Internal defects, ids, missing ports/preparation and unknown failures propagate.
use crate::SolidError;
pub(super) fn expected(error: &SolidError) -> bool {
    if error.is_port_failure() || error.is_defect() || error.is_cancelled() {
        return false;
    }
    matches!(
        error,
        SolidError::Unsupported { .. }
            | SolidError::NotConverged { .. }
            | SolidError::Degenerate { .. }
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn internal_identity_failure_is_not_geometric_indecision() {
        assert!(!expected(&SolidError::PortInvariant {
            operation: "test",
            reason: "owner identity missing"
        }));
        assert!(!expected(&SolidError::Cancelled { operation: "test" }));
        assert!(expected(&SolidError::Unsupported {
            operation: "test",
            reason: "uncertified parameter box"
        }));
    }
}
