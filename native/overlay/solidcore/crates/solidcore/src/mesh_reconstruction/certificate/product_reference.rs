//! Borrowed geometric data of one independently proved finite product.
//!
//! Original products retain their SAME source proof/view; rectangle recipes have
//! a distinct opaque constructor proving their entire requested finite domain.
//! Neither case can manufacture the other's source/material/identity premise.
use super::super::work::MeshWork;
use super::exact_geometry as x;
use super::fitted_recipe::RectangularRecipe;
use super::source_prism::SourcePrism;
use super::source_topology::SourceManifold;
use super::source_view::copy_point_with_work;
use crate::{Kernel, Result, SolidError};
use std::borrow::Cow;
use std::collections::BTreeMap;

#[derive(Clone, Copy)]
enum Origin<'a, 's, 'raw> {
    Original(&'a SourcePrism<'s, 'raw>),
    Recipe(&'a RectangularRecipe<'a>),
}
/// All fields borrow an already-proved product owner. This is not an input DTO.
#[derive(Clone, Copy)]
pub(crate) struct ProductReference<'a, 's, 'raw> {
    cap_levels: &'a [x::E; 2],
    translation: &'a x::P,
    cap_normal: &'a x::P,
    upper_to_lower: &'a BTreeMap<u32, u32>,
    profile_rims: &'a Vec<Vec<u32>>,
    origin: Origin<'a, 's, 'raw>,
}
impl<'a, 's, 'raw> ProductReference<'a, 's, 'raw> {
    pub(crate) fn original(source: &'a SourcePrism<'s, 'raw>) -> Self {
        Self {
            cap_levels: &source.cap_levels,
            translation: &source.translation,
            cap_normal: &source.cap_normal,
            upper_to_lower: &source.upper_to_lower,
            profile_rims: &source.profile_rims,
            origin: Origin::Original(source),
        }
    }
    pub(crate) fn recipe(recipe: &'a RectangularRecipe<'a>) -> Self {
        Self {
            cap_levels: recipe.cap_levels(),
            translation: recipe.translation(),
            cap_normal: recipe.cap_normal(),
            upper_to_lower: recipe.partners(),
            profile_rims: recipe.rims(),
            origin: Origin::Recipe(recipe),
        }
    }
    pub(crate) fn cap_levels(&self) -> &'a [x::E; 2] {
        self.cap_levels
    }
    pub(crate) fn translation(&self) -> &'a x::P {
        self.translation
    }
    pub(crate) fn cap_normal(&self) -> &'a x::P {
        self.cap_normal
    }
    pub(crate) fn upper_to_lower(&self) -> &'a BTreeMap<u32, u32> {
        self.upper_to_lower
    }
    pub(crate) fn profile_rims(&self) -> &'a Vec<Vec<u32>> {
        self.profile_rims
    }
    pub(crate) fn same_owner(&self, other: &Self) -> bool {
        match (self.origin, other.origin) {
            (Origin::Original(a), Origin::Original(b)) => core::ptr::eq(a, b),
            (Origin::Recipe(a), Origin::Recipe(b)) => core::ptr::eq(a, b),
            _ => false,
        }
    }
    pub(crate) fn original_source(&self) -> Option<&'s SourceManifold<'raw>> {
        match self.origin {
            Origin::Original(source) => Some(source.view.source()),
            Origin::Recipe(_) => None,
        }
    }
    pub(crate) fn recipe_owner(&self) -> Option<&'a RectangularRecipe<'a>> {
        match self.origin {
            Origin::Original(_) => None,
            Origin::Recipe(recipe) => Some(recipe),
        }
    }
    pub(crate) fn prior_motion_upper(&self) -> Option<f64> {
        match self.origin {
            Origin::Original(source) => Some(source.view.prior_motion_upper()),
            Origin::Recipe(_) => None,
        }
    }
    pub(crate) fn has_vertex(&self, id: u32) -> bool {
        match self.origin {
            Origin::Original(source) => source.view.source().position(id).is_some(),
            Origin::Recipe(recipe) => usize::try_from(id)
                .ok()
                .and_then(|i| recipe.points().get(i))
                .is_some(),
        }
    }
    pub(crate) fn position_with_work(
        &self,
        k: &Kernel,
        work: &MeshWork,
        id: u32,
    ) -> Result<Option<Cow<'_, x::P>>> {
        match self.origin {
            Origin::Original(source) => source.view.position_with_work(k, work, id),
            Origin::Recipe(recipe) => {
                work.spend_core(k, 1)?;
                Ok(usize::try_from(id)
                    .ok()
                    .and_then(|i| recipe.points().get(i))
                    .map(Cow::Borrowed))
            }
        }
    }
    pub(crate) fn points_with_work(
        &self,
        k: &Kernel,
        work: &MeshWork,
        ids: &[u32],
    ) -> Result<Vec<x::P>> {
        work.reserve_output_core(k, ids.len())?;
        let mut out = Vec::new();
        for &id in ids {
            let p = self
                .position_with_work(k, work, id)?
                .ok_or(SolidError::PortInvariant {
                    operation: "mesh_reconstruction::product_reference",
                    reason: "proved reference vertex missing",
                })?;
            out.push(copy_point_with_work(k, work, &p)?);
        }
        Ok(out)
    }
}
