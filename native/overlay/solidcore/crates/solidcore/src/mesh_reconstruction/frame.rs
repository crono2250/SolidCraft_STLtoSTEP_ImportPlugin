//! Orthonormal reconstruction frames, using the kernel's plain frame data.
use super::numeric::Vec3Numeric;
use crate::eval::Frame;
use crate::math::{Vec2, Vec3};
use crate::prism::profile;
pub(crate) trait FrameGeometry: Sized {
    fn new(origin: Vec3, x: Vec3, y: Vec3) -> Option<Self>;
    fn from_normal(origin: Vec3, normal: Vec3) -> Option<Frame>;
    fn normal(&self) -> Vec3;
    fn to_local(&self, p: Vec3) -> Vec2;
}
impl FrameGeometry for Frame {
    fn new(origin: Vec3, x: Vec3, y: Vec3) -> Option<Frame> {
        let x = x.normalized()?;
        let n = x.cross(y).normalized()?;
        let y = n.cross(x).normalized()?;
        origin.is_finite().then_some(Frame {
            origin: origin.to_array(),
            x_axis: x.to_array(),
            y_axis: y.to_array(),
        })
    }
    fn from_normal(origin: Vec3, n: Vec3) -> Option<Frame> {
        let n = n.normalized()?;
        let candidate = if n.dot(Vec3::Z).abs() > 0.9 {
            Vec3::X
        } else {
            Vec3::Z.cross(n)
        };
        let x = (candidate - n * candidate.dot(n)).normalized()?;
        Self::new(origin, x, n.cross(x))
    }
    fn normal(&self) -> Vec3 {
        Vec3::from_array(self.x_axis).cross(Vec3::from_array(self.y_axis))
    }
    fn to_local(&self, p: Vec3) -> Vec2 {
        profile::to_local(self, p)
    }
}
