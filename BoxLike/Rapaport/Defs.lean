module

/-
Shared definitions for the proof of Rapaport's theorem (arXiv:2309.03985, Theorem 1.3 in the
plane), `thm:rapaport` of the paper, stated in the library as `BoxLike.RapaportDiagonalDimension`.

* `ent θ f`, `cent θ f g`: Shannon entropy (nats) of a labelling `f : X → L` under a measure `θ`,
  and the conditional entropy of `f` given `g`, Rapaport's `H(θ, 𝒟)` and `H(θ, 𝒟 ∣ ℰ)` for the
  partitions into fibres of `f` and `g`.
* `comp θ f b`: the component `θ_{f = b}`, the normalised restriction of `θ` to a fibre.
* `cavg θ f F`: the component average `𝔼(F(θ_{x}))` over the components of `θ` for `f`.
* `rect i j`, `hLabel i`, `vLabel j`: the dyadic rectangle partition of the plane with horizontal
  level `i` and vertical level `j`, and its two coordinate partitions.
* `lvl χ n`: the dyadic level `⌊χ n / log 2⌋`, of mesh `e^{-χ n}` up to a factor `2`.
* `Exps`, `Exps.E`, `Exps.E₁`, `Exps.E₂`, `Exps.Dsq`: two exponents `0 < χ₁ < χ₂` and Rapaport's
  non-conformal partitions `ℰ_n`, `π₁⁻¹ ℰ_n`, `π₂⁻¹ ℰ_n` and `𝒟²_{χ₂ n}` (Section 2.5 of the
  source).
* `InBall θ c R`, `BddSupp θ`: compact support hypotheses for planar measures, in the supremum
  norm of `ℝ × ℝ`.
* `diagMap s t`: the diagonal linear map `(x, y) ↦ (s x, t y)`; `Exps.resc χ i` is Rapaport's
  `A_χ^i = diag(e^{χ₁ i}, e^{χ₂ i})`.
* `var₁ θ`, `var₂ θ`: the variances of the two coordinates.
* `convk k θ`, `convPow θ k`: the convolution `θ_0 ∗ ⋯ ∗ θ_{k-1}` of `k` planar measures and the
  `k`-fold self-convolution `θ^{∗k}`.
* `HomogeneousCore`: the core theorem as a `Prop`, proved by `Rapaport.homogeneousCore`
  (`Rapaport/Core`), and the hypothesis of the glue modules `Rapaport/Glue`,
  `Rapaport/Diagonal/Weighted` and `Rapaport/Diagonal/Reduction`.
* `HomSystem ι`: a homogeneous diagonal planar system `φ_i(z) = diag(r₁, r₂) z + v_i` with
  positive weights `p`, `|r₂| < |r₁| < 1`, and its derived data: `χ₁ = -log |r₁|`,
  `χ₂ = -log |r₂|`, the entropy `H p`, the points `φ_u(0)`, the discrete laws `ν_n`, the
  invariance relation `IsInvariant μ` (Hutchinson's fixed point equation) and exponential
  separation of the first coordinate system `XSep`.

Logarithms are natural throughout; dyadic levels carry the factor `1 / log 2`.
-/
public import ExactOverlaps.Entropy.Dyadic
public import ExactOverlaps.Entropy.Finite
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Probability.Moments.Variance
public import BoxLike.MeasureDim

@[expose] public section

namespace BoxLike.Rapaport

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ### Entropy of a labelling -/

section Entropy

variable {X : Type*} [MeasurableSpace X]

/-- The Shannon entropy, in nats, of the law of the labels `f` under `θ`: Rapaport's
`H(θ, 𝒟)` for the partition `𝒟` into the fibres of `f`. -/
noncomputable def ent (θ : Measure X) {L : Type*} (f : X → L) : ℝ :=
  ∑' b : L, Real.negMulLog (θ.real (f ⁻¹' {b}))

/-- The conditional entropy `H(θ, 𝒟 ∣ ℰ) = H(θ, 𝒟 ∨ ℰ) - H(θ, ℰ)` of the labelling `f` given the
labelling `g`. -/
noncomputable def cent (θ : Measure X) {L L' : Type*} (f : X → L) (g : X → L') : ℝ :=
  ent θ (fun x => (f x, g x)) - ent θ g

/-- Only finitely many labels carry positive mass. -/
def FiniteLabels (θ : Measure X) {L : Type*} (f : X → L) : Prop :=
  (Function.support fun b : L => θ (f ⁻¹' {b})).Finite

/-- The component `θ_{f = b}`: the normalised restriction of `θ` to the fibre of the label `b`. -/
noncomputable def comp (θ : Measure X) {L : Type*} (f : X → L) (b : L) : Measure X :=
  θ[|f ⁻¹' {b}]

/-- The component average `𝔼_{x}(F(θ_{x}))` of Section 2.6 of the source: the mean of `F` over
the components of `θ` for the labelling `f`, weighted by their masses. -/
noncomputable def cavg (θ : Measure X) {L : Type*} (f : X → L) (F : Measure X → ℝ) : ℝ :=
  ∑' b : L, θ.real (f ⁻¹' {b}) * F (comp θ f b)

end Entropy

/-! ### Dyadic rectangles in the plane -/

section Dyadic

open ExactOverlaps.Entropy

/-- The dyadic rectangle label of `z` at horizontal level `i` and vertical level `j`: the cell
`[k 2^{-i}, (k+1) 2^{-i}) × [l 2^{-j}, (l+1) 2^{-j})` containing `z` has label `(k, l)`. -/
noncomputable def rect (i j : ℤ) (z : ℝ × ℝ) : ℤ × ℤ :=
  (dyadicQuantize i z.1, dyadicQuantize j z.2)

/-- The horizontal label `⌊2^i x⌋`, the partition `π₁⁻¹ 𝒟_i` of the plane. -/
noncomputable def hLabel (i : ℤ) (z : ℝ × ℝ) : ℤ := dyadicQuantize i z.1

/-- The vertical label `⌊2^j y⌋`, the partition `π₂⁻¹ 𝒟_j` of the plane. -/
noncomputable def vLabel (j : ℤ) (z : ℝ × ℝ) : ℤ := dyadicQuantize j z.2

/-- The dyadic level `⌊χ n / log 2⌋` of the exponent `χ > 0` at the planar level `n`, so that the
mesh `2^{-lvl χ n}` lies in `(e^{-χ n}, 2 e^{-χ n}]`. -/
noncomputable def lvl (χ : ℝ) (n : ℤ) : ℤ := ⌊χ * n / Real.log 2⌋

/-- The diagonal linear map `(x, y) ↦ (s x, t y)`. -/
def diagMap (s t : ℝ) (z : ℝ × ℝ) : ℝ × ℝ := (s * z.1, t * z.2)

/-- Two exponents `0 < χ₁ < χ₂`; Rapaport's `χ_1 < χ_2` for `d = 2`. -/
structure Exps where
  /-- The exponent of the first coordinate, the weaker contraction. -/
  χ₁ : ℝ
  /-- The exponent of the second coordinate, the stronger contraction. -/
  χ₂ : ℝ
  pos : 0 < χ₁
  lt : χ₁ < χ₂

namespace Exps

variable (χ : Exps)

theorem pos₂ : 0 < χ.χ₂ := χ.pos.trans χ.lt

/-- The level-`n` non-conformal partition `ℰ_n = 𝒟_{χ₁ n} × 𝒟_{χ₂ n}`. -/
noncomputable def E (n : ℤ) : ℝ × ℝ → ℤ × ℤ := rect (lvl χ.χ₁ n) (lvl χ.χ₂ n)

/-- The partition `π₁⁻¹ ℰ_n`. -/
noncomputable def E₁ (n : ℤ) : ℝ × ℝ → ℤ := hLabel (lvl χ.χ₁ n)

/-- The partition `π₂⁻¹ ℰ_n`. -/
noncomputable def E₂ (n : ℤ) : ℝ × ℝ → ℤ := vLabel (lvl χ.χ₂ n)

/-- The conformal partition `𝒟²_{χ₂ n}` into squares of side `2^{-lvl χ₂ n}`. -/
noncomputable def Dsq (n : ℤ) : ℝ × ℝ → ℤ × ℤ := rect (lvl χ.χ₂ n) (lvl χ.χ₂ n)

/-- Rapaport's `A_χ^i = diag(e^{χ₁ i}, e^{χ₂ i})`, which carries a cell of `ℰ_i` to a cell of size
between `1` and `2` in each coordinate. -/
noncomputable def resc (i : ℤ) : ℝ × ℝ → ℝ × ℝ :=
  diagMap (Real.exp (χ.χ₁ * i)) (Real.exp (χ.χ₂ * i))

end Exps

end Dyadic

/-! ### Planar measures -/

section Planar

/-- `θ` is carried by the closed ball of radius `R` about `c`, in the supremum norm. -/
def InBall (θ : Measure (ℝ × ℝ)) (c : ℝ × ℝ) (R : ℝ) : Prop := ∀ᵐ z ∂θ, ‖z - c‖ ≤ R

/-- `θ` has bounded support. -/
def BddSupp (θ : Measure (ℝ × ℝ)) : Prop := ∃ c R, InBall θ c R

/-- The variance `Var(π₁ θ)` of the first coordinate. -/
noncomputable def var₁ (θ : Measure (ℝ × ℝ)) : ℝ := ProbabilityTheory.variance (fun z => z.1) θ

/-- The variance `Var(π₂ θ)` of the second coordinate. -/
noncomputable def var₂ (θ : Measure (ℝ × ℝ)) : ℝ := ProbabilityTheory.variance (fun z => z.2) θ

open scoped MeasureTheory in
/-- The convolution `θ_0 ∗ θ_1 ∗ ⋯ ∗ θ_{k-1}` of `k` planar measures; the empty convolution is
`δ_0`. -/
noncomputable def convk : (k : ℕ) → (Fin k → Measure (ℝ × ℝ)) → Measure (ℝ × ℝ)
  | 0, _ => Measure.dirac 0
  | k + 1, θ => θ 0 ∗ convk k (Fin.tail θ)

/-- The `k`-fold self-convolution `θ^{∗k}`. -/
noncomputable def convPow (θ : Measure (ℝ × ℝ)) (k : ℕ) : Measure (ℝ × ℝ) :=
  convk k fun _ => θ

end Planar

/-! ### Homogeneous diagonal systems -/

/-- A homogeneous diagonal planar system: the maps `φ_i(z) = (r₁ z.1 + (v i).1, r₂ z.2 + (v i).2)`
with the common linear part `diag(r₁, r₂)`, `|r₂| < |r₁| < 1`, and a strictly positive
probability vector `p`. The setting of Rapaport's Theorem 1.2 in the plane whose linear parts
lie in a one-dimensional subgroup; for `d = 2` the first coordinate is the weaker contraction. -/
structure HomSystem (ι : Type*) [Fintype ι] where
  /-- The horizontal contraction. -/
  r₁ : ℝ
  /-- The vertical contraction. -/
  r₂ : ℝ
  /-- The translations. -/
  v : ι → ℝ × ℝ
  /-- The weights. -/
  p : ι → ℝ
  r₂_ne_zero : r₂ ≠ 0
  abs_r₂_lt : |r₂| < |r₁|
  abs_r₁_lt_one : |r₁| < 1
  p_pos : ∀ i, 0 < p i
  p_sum : ∑ i, p i = 1

namespace HomSystem

variable {ι : Type*} [Fintype ι] (S : HomSystem ι)

theorem r₁_ne_zero : S.r₁ ≠ 0 := by
  intro h
  have := S.abs_r₂_lt
  rw [h, abs_zero] at this
  exact absurd this (not_lt.2 (abs_nonneg _))

theorem abs_r₂_pos : 0 < |S.r₂| := abs_pos.2 S.r₂_ne_zero

theorem abs_r₁_pos : 0 < |S.r₁| := abs_pos.2 S.r₁_ne_zero

theorem abs_r₂_lt_one : |S.r₂| < 1 := S.abs_r₂_lt.trans S.abs_r₁_lt_one

/-- The exponent `χ₁ = -log |r₁|` of the first coordinate. -/
noncomputable def χ₁ : ℝ := -Real.log |S.r₁|

/-- The exponent `χ₂ = -log |r₂|` of the second coordinate. -/
noncomputable def χ₂ : ℝ := -Real.log |S.r₂|

theorem χ₁_pos : 0 < S.χ₁ := by
  rw [χ₁, neg_pos]
  exact Real.log_neg S.abs_r₁_pos S.abs_r₁_lt_one

theorem χ₁_lt_χ₂ : S.χ₁ < S.χ₂ := by
  rw [χ₁, χ₂, neg_lt_neg_iff]
  exact Real.log_lt_log S.abs_r₂_pos S.abs_r₂_lt

/-- The exponents as an `Exps`. -/
noncomputable def exps : Exps := ⟨S.χ₁, S.χ₂, S.χ₁_pos, S.χ₁_lt_χ₂⟩

/-- The entropy `H(p) = -∑ p_i log p_i` of the weights. -/
noncomputable def H : ℝ := ∑ i, Real.negMulLog (S.p i)

/-- The common linear part `A = diag(r₁, r₂)`. -/
def A : ℝ × ℝ → ℝ × ℝ := diagMap S.r₁ S.r₂

/-- The `n`-th power `A^n = diag(r₁^n, r₂^n)`. -/
def Apow (n : ℕ) : ℝ × ℝ → ℝ × ℝ := diagMap (S.r₁ ^ n) (S.r₂ ^ n)

/-- The map `φ_i(z) = A z + v_i`. -/
def φ (i : ι) (z : ℝ × ℝ) : ℝ × ℝ := S.A z + S.v i

/-- The composition `φ_u = φ_{u 0} ∘ ⋯ ∘ φ_{u (n-1)}` over a word of length `n`. -/
def φWord : (n : ℕ) → (Fin n → ι) → ℝ × ℝ → ℝ × ℝ
  | 0, _ => id
  | n + 1, u => S.φ (u 0) ∘ φWord n (fun k => u k.succ)

/-- The point `φ_u(0) = ∑_{k < n} A^k v_{u_k}`. -/
def point {n : ℕ} (u : Fin n → ι) : ℝ × ℝ := S.φWord n u 0

/-- The weight `p_u = ∏_k p_{u_k}` of a word. -/
def weight {n : ℕ} (u : Fin n → ι) : ℝ := ∏ k, S.p (u k)

/-- The discrete law `ν_n = ∑_{u ∈ ι^n} p_u δ_{φ_u(0)}`, Rapaport's `ev_0 ν^{(n)}`. -/
noncomputable def ν (n : ℕ) : Measure (ℝ × ℝ) :=
  ∑ u : Fin n → ι, ENNReal.ofReal (S.weight u) • Measure.dirac (S.point u)

/-- Hutchinson's invariance `μ = ∑ p_i (φ_i)_* μ`: `μ` is the self-affine measure of `(Φ, p)`. -/
def IsInvariant (μ : Measure (ℝ × ℝ)) : Prop :=
  μ = ∑ i, ENNReal.ofReal (S.p i) • μ.map (S.φ i)

/-- Exponential separation of the first coordinate system `Φ₁ = {t ↦ r₁ t + (v_i).1}`: for some
`c > 0` and infinitely many `n`, the first coordinates of the points `φ_u(0)`, `u ∈ ι^n`, are
`c^n`-separated. Since the linear parts coincide, this is Definition 1.1 of the source. -/
def XSep : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ᶠ n : ℕ in Filter.atTop,
    ∀ u u' : Fin n → ι, u ≠ u' → c ^ n ≤ |(S.point u).1 - (S.point u').1|

end HomSystem

universe u

/-- The core theorem, proved by `Rapaport.homogeneousCore`: Rapaport's Theorem 1.2 in the plane for
a homogeneous system, in the case of Section 6.3 of the source (lines 1900 to 1928) where both
coordinate projections have dimension one. If the self-affine measure `μ` of `S` is
exact-dimensional of dimension `α < 2`, both coordinate projections are exact-dimensional of
dimension `1`, and the first coordinate system is exponentially separated, then
`α = 1 + (H(p) - χ₁) / χ₂`. -/
def HomogeneousCore : Prop :=
  ∀ {ι : Type u} [Fintype ι] (S : HomSystem ι) (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ],
    S.IsInvariant μ → BddSupp μ → ∀ α : ℝ, IsExactDim μ α → α < 2 →
    IsExactDim (μ.map Prod.fst) 1 → IsExactDim (μ.map Prod.snd) 1 → S.XSep →
    α = 1 + (S.H - S.χ₁) / S.χ₂

end BoxLike.Rapaport
