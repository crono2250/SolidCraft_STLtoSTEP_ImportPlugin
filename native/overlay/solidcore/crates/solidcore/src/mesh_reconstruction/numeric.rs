//! Fitting aliases over the existing native vector and extent operations.
pub(crate) use crate::eval::vec::VecExt as Vec3Numeric;
pub(crate) use crate::geom::extent3d::Extent3d as Bounds3;
use crate::math::Vec2;

/// Short names retained by the planar fit; the existing kernel operations do the work.
pub(crate) trait Vec2Numeric {
    fn len(self) -> f64;
    fn len2(self) -> f64;
    fn dist(self, point: Vec2) -> f64;
    fn cross(self, point: Vec2) -> f64;
}
impl Vec2Numeric for Vec2 {
    fn len(self) -> f64 {
        self.length()
    }
    fn len2(self) -> f64 {
        self.length_squared()
    }
    fn dist(self, point: Vec2) -> f64 {
        self.distance(point)
    }
    fn cross(self, point: Vec2) -> f64 {
        crate::prism::profile::cross2(self, point)
    }
}
