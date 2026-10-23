import FractalGeometry.SelfAffine.Rectangular.Defs

namespace FractalGeometry.RectangularIFS

/-- Positive diagonal/anti-diagonal coefficients, as in Fraser–Jordan–Jurga (2020). -/
class PositiveRatios {ι : Type*} (S : RectangularIFS ι) : Prop where
  a_pos : ∀ i, 0 < S.a i
  b_pos : ∀ i, 0 < S.b i

end FractalGeometry.RectangularIFS
