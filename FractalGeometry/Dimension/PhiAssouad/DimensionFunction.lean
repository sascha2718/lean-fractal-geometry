import Mathlib

namespace FractalGeometry.Dimension.PhiAssouad

open Filter Topology Set

structure DimFun where

  toFun : ℝ → ℝ

  pos : ∀ R ∈ Set.Ioo (0 : ℝ) 1, 0 < toFun R

  mono : ∀ R ∈ Set.Ioo (0 : ℝ) 1, ∀ S ∈ Set.Ioo (0 : ℝ) 1,
    R ≤ S → toFun R ≤ toFun S

  gap_mono : ∀ R ∈ Set.Ioo (0 : ℝ) 1, ∀ S ∈ Set.Ioo (0 : ℝ) 1,
    R ≤ S → toFun S * Real.log (1 / S) ≤ toFun R * Real.log (1 / R)

  gap_tendsto :
    Tendsto (fun R => toFun R * Real.log (1 / R)) (𝓝[>] (0 : ℝ)) atTop

end FractalGeometry.Dimension.PhiAssouad
