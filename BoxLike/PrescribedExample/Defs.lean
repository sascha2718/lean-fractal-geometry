module

/-
The definitions of `ex:projection_double_dimensional` shared by the modules of
`BoxLike/PrescribedExample/`: the functions `H`, `J`, the parameters `a`, `b` and the system
of four maps with translation vector `t ∈ ℝ^8`. The article indexes the maps by `1, …, 4` and
the translations by `1, …, 8`; here the index of a map is `i : Fin 4`, the first coordinate of
its translation is `t i` and the second is `t (i + 4)`. The maps `0`, `1` are diagonal and the
maps `2`, `3` are anti-diagonal.

* `PrescribedExample.H`, `PrescribedExample.J`, `PrescribedExample.ratio`: the functions
  `H(p)`, `J(p)` and `(log 2 + H(p)) / (log 2 + J(p))`.
* `PrescribedExample.aOf`, `PrescribedExample.bOf`: `a = (p/2)^{1/s_1}`, `b = ((1-p)/2)^{1/s_1}`.
* `PrescribedExample.Params`, `PrescribedExample.paramsOf`: two reals with `0 < b < a < 1/2`,
  and the parameters `a`, `b` of the example for `0 < s_1 ≤ 1` and `1/2 < p < 1`.
* `PrescribedExample.orient`, `PrescribedExample.sys`: the orientations and the system.
* `PrescribedExample.sys_phi_of_lt`, `PrescribedExample.sys_phi_of_le`: the maps
  `φ_i(x, y) = (a x + t_i, b y + t_{i+4})` and `φ_i(x, y) = (a y + t_i, b x + t_{i+4})`.
-/
public import BoxLike.System
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace BoxLike

namespace PrescribedExample

/-- `H(p) = -p log p - (1 - p) log(1 - p)` of `ex:projection_double_dimensional`. -/
noncomputable def H (p : ℝ) : ℝ := -p * Real.log p - (1 - p) * Real.log (1 - p)

/-- `J(p) = -p log(1 - p) - (1 - p) log p` of `ex:projection_double_dimensional`. -/
noncomputable def J (p : ℝ) : ℝ := -p * Real.log (1 - p) - (1 - p) * Real.log p

/-- The ratio `(log 2 + H(p)) / (log 2 + J(p))` of `ex:projection_double_dimensional`, which
the parameter `p` makes equal to `s_2 / s_1`. -/
noncomputable def ratio (p : ℝ) : ℝ := (Real.log 2 + H p) / (Real.log 2 + J p)

/-- The contraction `a = (p/2)^{1/s_1}` of `ex:projection_double_dimensional`. -/
noncomputable def aOf (s₁ p : ℝ) : ℝ := (p / 2) ^ (1 / s₁)

/-- The contraction `b = ((1-p)/2)^{1/s_1}` of `ex:projection_double_dimensional`. -/
noncomputable def bOf (s₁ p : ℝ) : ℝ := ((1 - p) / 2) ^ (1 / s₁)

/-- Two contractions `0 < b < a < 1/2`, as `ex:projection_double_dimensional` obtains them. -/
structure Params where
  /-- The contraction `a`. -/
  a : ℝ
  /-- The contraction `b`. -/
  b : ℝ
  b_pos : 0 < b
  b_lt_a : b < a
  a_lt_half : a < 1 / 2

namespace Params

variable (P : Params)

/-- `0 < a`. -/
theorem a_pos : 0 < P.a := P.b_pos.trans P.b_lt_a

/-- `a < 1`. -/
theorem a_lt_one : P.a < 1 := by linarith [P.a_lt_half]

/-- `b < 1`. -/
theorem b_lt_one : P.b < 1 := by linarith [P.b_lt_a, P.a_lt_half]

end Params

/-- The parameters `a = (p/2)^{1/s_1}` and `b = ((1-p)/2)^{1/s_1}` of
`ex:projection_double_dimensional` for `0 < s_1 ≤ 1` and `1/2 < p < 1`, which satisfy
`0 < b < a < 1/2`. -/
noncomputable def paramsOf (s₁ p : ℝ) (hs₀ : 0 < s₁) (hs₁ : s₁ ≤ 1) (hp₀ : 1 / 2 < p)
    (hp₁ : p < 1) : Params where
  a := aOf s₁ p
  b := bOf s₁ p
  b_pos := Real.rpow_pos_of_pos (by linarith) _
  b_lt_a := Real.rpow_lt_rpow (by linarith) (by linarith) (by positivity)
  a_lt_half := by
    have h : aOf s₁ p ≤ (p / 2) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (by linarith) (by linarith) (one_le_one_div hs₀ hs₁)
    rw [Real.rpow_one] at h
    linarith

/-- The contraction `a` of `paramsOf` is `(p/2)^{1/s_1}`. -/
@[simp] theorem paramsOf_a (s₁ p : ℝ) (hs₀ : 0 < s₁) (hs₁ : s₁ ≤ 1) (hp₀ : 1 / 2 < p)
    (hp₁ : p < 1) : (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁).a = aOf s₁ p := rfl

/-- The contraction `b` of `paramsOf` is `((1-p)/2)^{1/s_1}`. -/
@[simp] theorem paramsOf_b (s₁ p : ℝ) (hs₀ : 0 < s₁) (hs₁ : s₁ ≤ 1) (hp₀ : 1 / 2 < p)
    (hp₁ : p < 1) : (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁).b = bOf s₁ p := rfl

/-- The orientations of `ex:projection_double_dimensional`: the maps `0`, `1` are diagonal and
the maps `2`, `3` are anti-diagonal. -/
def orient (i : Fin 4) : ZMod 2 := if (i : ℕ) < 2 then 0 else 1

/-- The system of `ex:projection_double_dimensional` with translation vector `t ∈ ℝ^8`:
`φ_i(x, y) = (a x + t_i, b y + t_{i+4})` for the diagonal maps and
`φ_i(x, y) = (a y + t_i, b x + t_{i+4})` for the anti-diagonal ones. -/
noncomputable def sys (P : Params) (t : Fin 8 → ℝ) : System (Fin 4) where
  o := orient
  a _ := P.a
  b _ := P.b
  v i := (t (Fin.castAdd 4 i), t (Fin.natAdd 4 i))
  a_ne_zero _ := P.a_pos.ne'
  b_ne_zero _ := P.b_pos.ne'
  abs_a_lt_one _ := by rw [abs_of_pos P.a_pos]; exact P.a_lt_one
  abs_b_lt_one _ := by rw [abs_of_pos P.b_pos]; exact P.b_lt_one

/-- The diagonal maps of `ex:projection_double_dimensional`:
`φ_i(x, y) = (a x + t_i, b y + t_{i+4})` for `i < 2`. -/
theorem sys_phi_of_lt (P : Params) (t : Fin 8 → ℝ) {i : Fin 4} (hi : (i : ℕ) < 2)
    (z : ℝ × ℝ) :
    (sys P t).phi i z = (P.a * z.1 + t (Fin.castAdd 4 i), P.b * z.2 + t (Fin.natAdd 4 i)) := by
  simp [System.phi, sys, orient, hi]

/-- The anti-diagonal maps of `ex:projection_double_dimensional`:
`φ_i(x, y) = (a y + t_i, b x + t_{i+4})` for `2 ≤ i`. -/
theorem sys_phi_of_le (P : Params) (t : Fin 8 → ℝ) {i : Fin 4} (hi : 2 ≤ (i : ℕ))
    (z : ℝ × ℝ) :
    (sys P t).phi i z = (P.a * z.2 + t (Fin.castAdd 4 i), P.b * z.1 + t (Fin.natAdd 4 i)) := by
  simp [System.phi, sys, orient, not_lt.2 hi, show (1 : ZMod 2) + 1 = 0 from by decide]

end PrescribedExample

end BoxLike
