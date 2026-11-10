module

/-
The sets `Σ^τ`, `Σ^ω`, `Σ'` and the Oseledets filtration of `sec:lyapunov_exponents`, in the
box-like form of tex lines 1521 to 1553: `Σ'` is the set of sequences for which the two backward
coordinate growth rates exist and equal `λ_1(𝖠, μ)` and `λ_2(𝖠, μ)` in either order, and the
slow subspace `V_𝐢^1` is a coordinate axis. The measure enters through the two exponents only.

* `SamePast`, `pastWord_congr`, `pastWord_eq_futureWord`: the relation `𝐢^- = 𝐣^-` of
  `sec:two_sided_shift_space` and the word `i_{-n} ⋯ i_{-1}`.
* `System.HasBackRate`, `System.hasBackRate_tau_iff`, `System.hasBackRate_omega_iff`: the
  backward growth rate of `|g'|` of `eq:lyapunov_exponent_gsystem` and its matrix form, from
  `thm:matrix_products_g_derivatives`.
* `System.SigmaTau`, `System.SigmaOmega`, `System.SigmaPrime`: the sets `Σ^τ`, `Σ^ω` of
  `eq:sigma_tau_omega` and `Σ' = Σ^τ ∪ Σ^ω`.
* `System.slowAxis`, `System.oseledets`, `System.mem_oseledets_iff`: the slow subspace `V_𝐢^1`
  as a coordinate axis and the filtration `V_𝐢^0 ⊋ V_𝐢^1 ⊋ V_𝐢^2`.
* `System.fastPart`, `System.slowPart`: the sets `τ(Σ^τ) ∪ ω(Σ^ω)` and `ω(Σ^τ) ∪ τ(Σ^ω)` of
  `thm:gibbs_tau_omega_positive`.
* `System.lyapunov_exponents_via_g_system`: `thm:lyapunov_exponents_via_g_system`.
* `System.disjoint_SigmaTau_SigmaOmega`: `eq:tau_omega_partition2`, the disjointness half.
* `System.mem_SigmaTau_of_samePast`, `System.mem_SigmaOmega_of_samePast`,
  `System.slowAxis_eq_of_samePast`: `Σ^τ`, `Σ^ω` and the slow axis depend only on the past.
* `System.measurableSet_SigmaTau`, `System.measurableSet_SigmaOmega`,
  `System.measurableSet_SigmaPrime`: the three sets are Borel.
-/
public import BoxLike.Lyapunov
public import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set Matrix

/-! ### The past of a sequence -/

/-- `𝐢^- = 𝐣^-`: the two sequences agree at all negative coordinates
(`sec:two_sided_shift_space`, tex line 728). -/
def SamePast {α : Type*} (x y : ℤ → α) : Prop := ∀ n : ℤ, n < 0 → x n = y n

/-- The relation `𝐢^- = 𝐣^-` of `sec:two_sided_shift_space` is reflexive. -/
theorem SamePast.refl {α : Type*} (x : ℤ → α) : SamePast x x := fun _ _ => rfl

/-- The relation `𝐢^- = 𝐣^-` of `sec:two_sided_shift_space` is symmetric. -/
theorem SamePast.symm {α : Type*} {x y : ℤ → α} (h : SamePast x y) : SamePast y x :=
  fun n hn => (h n hn).symm

/-- The relation `𝐢^- = 𝐣^-` of `sec:two_sided_shift_space` is transitive. -/
theorem SamePast.trans {α : Type*} {x y z : ℤ → α} (h : SamePast x y) (h' : SamePast y z) :
    SamePast x z := fun n hn => (h n hn).trans (h' n hn)

/-- The word `i_{-n} ⋯ i_{-1}` depends only on the past. -/
theorem pastWord_congr {α : Type*} {x y : ℤ → α} (h : SamePast x y) (n : ℕ) :
    pastWord x n = pastWord y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pastWord_succ, pastWord_succ, ih, h _ (by omega)]

/-- The word `i_{-n} ⋯ i_{-1}` of `𝐢` is the prefix of length `n` of `σ^{-n}(𝐢)`. -/
theorem pastWord_eq_futureWord {α : Type*} (x : ℤ → α) (n : ℕ) :
    pastWord x n = futureWord (shift (-(n : ℤ)) x) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by push_cast; ring
    rw [pastWord_succ, futureWord_succ', ih, shift_shift, e]
    simp

namespace System

/-! ### Backward growth rates -/

section BackRate

variable {ι : Type*} (S : System ι)

/-- The backward growth rate of `|g'|` along `𝐣 ∈ Σ_Z` exists and equals `l`:
`lim_n n⁻¹ log |g'_{j_{-n} ⋯ j_{-1}}(0)| = l`, as in `eq:lyapunov_exponent_gsystem`. By
`thm:matrix_products_g_derivatives`, for `𝐣 = τ(𝐢)` this is the growth rate of
`|A_{i_{-n}} ⋯ A_{i_{-1}} e_1|` and for `𝐣 = ω(𝐢)` that of `|A_{i_{-n}} ⋯ A_{i_{-1}} e_2|`. -/
def HasBackRate (y : ℤ → ι × ZMod 2) (l : ℝ) : Prop :=
  Tendsto (fun n : ℕ => Real.log |S.gDeriv (pastWord y n)| / n) atTop (𝓝 l)

/-- The backward growth rate of `e_1` along `𝐢`, in matrix form
(`thm:matrix_products_g_derivatives`, first identity). -/
theorem hasBackRate_tau_iff (x : ℤ → ι) (l : ℝ) :
    S.HasBackRate (tau S.o x) l ↔
      Tendsto (fun n : ℕ => Real.log (|(S.matWord (pastWord x n) *ᵥ ![1, 0]) 0| +
        |(S.matWord (pastWord x n) *ᵥ ![1, 0]) 1|) / n) atTop (𝓝 l) := by
  simp only [HasBackRate, abs_matWord_pastWord_e1]

/-- The backward growth rate of `e_2` along `𝐢`, in matrix form
(`thm:matrix_products_g_derivatives`, second identity). -/
theorem hasBackRate_omega_iff (x : ℤ → ι) (l : ℝ) :
    S.HasBackRate (omega S.o x) l ↔
      Tendsto (fun n : ℕ => Real.log (|(S.matWord (pastWord x n) *ᵥ ![0, 1]) 0| +
        |(S.matWord (pastWord x n) *ᵥ ![0, 1]) 1|) / n) atTop (𝓝 l) := by
  simp only [HasBackRate, abs_matWord_pastWord_e2]

end BackRate

/-! ### `Σ^τ`, `Σ^ω`, `Σ'` and the slow axis -/

section Sigma

variable {ι : Type*} [MeasurableSpace ι] (S : System ι)

/-- `Σ^τ` of `eq:sigma_tau_omega`, in the box-like form of `sec:lyapunov_exponents` (tex lines
1614 to 1625): the slow subspace `V_𝐢^1` is the `y`-axis, that is, `e_1` grows backwards at the
rate `λ_1(𝖠, μ)` and `e_2` at the rate `λ_2(𝖠, μ)`. -/
noncomputable def SigmaTau (μ : Measure (ℤ → ι)) : Set (ℤ → ι) :=
  {x | S.HasBackRate (tau S.o x) (S.lyapunov₁ μ) ∧ S.HasBackRate (omega S.o x) (S.lyapunov₂ μ)}

/-- `Σ^ω` of `eq:sigma_tau_omega`: the slow subspace `V_𝐢^1` is the `x`-axis, that is, `e_1`
grows backwards at the rate `λ_2(𝖠, μ)` and `e_2` at the rate `λ_1(𝖠, μ)`. -/
noncomputable def SigmaOmega (μ : Measure (ℤ → ι)) : Set (ℤ → ι) :=
  {x | S.HasBackRate (tau S.o x) (S.lyapunov₂ μ) ∧ S.HasBackRate (omega S.o x) (S.lyapunov₁ μ)}

/-- The set `Σ'` of `sec:lyapunov_exponents` in the box-like case (tex lines 1521 to 1523): "all
sequences for which the two backward coordinate growth rates exist and equal `λ_1(𝖠, μ)` and
`λ_2(𝖠, μ)` in either order". It depends on `μ` through the two exponents only. -/
noncomputable def SigmaPrime (μ : Measure (ℤ → ι)) : Set (ℤ → ι) :=
  S.SigmaTau μ ∪ S.SigmaOmega μ

open Classical in
/-- The slow subspace `V_𝐢^1` as a coordinate axis: `1` for the `y`-axis, on `Σ^τ`, and `0` for
the `x`-axis, on `Σ^ω`. Outside `Σ'` the value `0` is junk; when `λ_1 = λ_2` the sets `Σ^τ` and
`Σ^ω` coincide and the value is `1` on `Σ'`. -/
noncomputable def slowAxis (μ : Measure (ℤ → ι)) (x : ℤ → ι) : ZMod 2 :=
  if x ∈ S.SigmaTau μ then 1 else 0

/-- The Oseledets filtration `ℝ² = V_𝐢^0 ⊋ V_𝐢^1 ⊋ V_𝐢^2 = {0}` of `sec:lyapunov_exponents` in
the box-like case: `V_𝐢^1` is the coordinate axis `slowAxis`, the set of vectors whose other
coordinate vanishes. Indices above `2` repeat `{0}`. -/
noncomputable def oseledets (μ : Measure (ℤ → ι)) (x : ℤ → ι) : ℕ → Set (ℝ × ℝ)
  | 0 => univ
  | 1 => {v | coord (S.slowAxis μ x + 1) v = 0}
  | _ => {0}

/-- `τ(Σ^τ) ∪ ω(Σ^ω)`: the part of `Σ_Z` on which the backward rate is `λ_1(𝖠, μ)`
(`thm:gibbs_tau_omega_positive`); it carries `μ_1`. -/
noncomputable def fastPart (μ : Measure (ℤ → ι)) : Set (ℤ → ι × ZMod 2) :=
  tau S.o '' S.SigmaTau μ ∪ omega S.o '' S.SigmaOmega μ

/-- `ω(Σ^τ) ∪ τ(Σ^ω)`: the part of `Σ_Z` on which the backward rate is `λ_2(𝖠, μ)`
(`thm:gibbs_tau_omega_positive`); it carries `μ_2`. -/
noncomputable def slowPart (μ : Measure (ℤ → ι)) : Set (ℤ → ι × ZMod 2) :=
  omega S.o '' S.SigmaTau μ ∪ tau S.o '' S.SigmaOmega μ

/-- `thm:lyapunov_exponents_via_g_system`, proved. With the box-like definition of `Σ'` the four
limits hold by definition of `Σ^τ` and `Σ^ω`, for every `𝐢 ∈ Σ'` and without any hypothesis. The
content of the article's lemma moves to `measure_SigmaPrime_compl` (the set has full measure)
and `disjoint_SigmaTau_SigmaOmega` (the case distinction is well defined).
Depends on: `thm:matrix_products_g_derivatives`, through `hasBackRate_tau_iff` and
`hasBackRate_omega_iff`. -/
theorem lyapunov_exponents_via_g_system (μ : Measure (ℤ → ι)) {x : ℤ → ι} :
    (x ∈ S.SigmaTau μ → S.HasBackRate (tau S.o x) (S.lyapunov₁ μ) ∧
      S.HasBackRate (omega S.o x) (S.lyapunov₂ μ)) ∧
    (x ∈ S.SigmaOmega μ → S.HasBackRate (omega S.o x) (S.lyapunov₁ μ) ∧
      S.HasBackRate (tau S.o x) (S.lyapunov₂ μ)) :=
  ⟨fun h => h, fun h => ⟨h.2, h.1⟩⟩

/-- `eq:tau_omega_partition2`, the disjointness half, proved: `Σ^τ ∩ Σ^ω = ∅` when
`λ_2(𝖠, μ) < λ_1(𝖠, μ)`, by uniqueness of limits. The covering half `Σ' = Σ^τ ∪ Σ^ω` is the
definition of `SigmaPrime`. -/
theorem disjoint_SigmaTau_SigmaOmega (μ : Measure (ℤ → ι))
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) : Disjoint (S.SigmaTau μ) (S.SigmaOmega μ) := by
  rw [Set.disjoint_left]
  rintro x ⟨h1, -⟩ ⟨h2, -⟩
  exact hlt.ne (tendsto_nhds_unique h2 h1)

/-- `sec:lyapunov_exponents`, tex lines 1540 to 1541, proved: `Σ^τ` is saturated with respect to
the past. -/
theorem mem_SigmaTau_of_samePast (μ : Measure (ℤ → ι)) {x y : ℤ → ι} (h : SamePast x y)
    (hx : x ∈ S.SigmaTau μ) : y ∈ S.SigmaTau μ := by
  have e1 : ∀ n, pastWord (tau S.o y) n = pastWord (tau S.o x) n := fun n => by
    rw [← S.codeWord_pastWord_tau, ← S.codeWord_pastWord_tau, ← S.oWord_pastWord,
      ← S.oWord_pastWord, pastWord_congr h n]
  have e2 : ∀ n, pastWord (omega S.o y) n = pastWord (omega S.o x) n := fun n => by
    rw [← S.codeWord_pastWord_omega, ← S.codeWord_pastWord_omega, ← S.oWord_pastWord,
      ← S.oWord_pastWord, pastWord_congr h n]
  simpa only [SigmaTau, HasBackRate, mem_ofPred_eq, e1, e2] using hx

/-- `sec:lyapunov_exponents`, tex lines 1540 to 1541, proved: `Σ^ω` is saturated with respect to
the past. -/
theorem mem_SigmaOmega_of_samePast (μ : Measure (ℤ → ι)) {x y : ℤ → ι} (h : SamePast x y)
    (hx : x ∈ S.SigmaOmega μ) : y ∈ S.SigmaOmega μ := by
  have e1 : ∀ n, pastWord (tau S.o y) n = pastWord (tau S.o x) n := fun n => by
    rw [← S.codeWord_pastWord_tau, ← S.codeWord_pastWord_tau, ← S.oWord_pastWord,
      ← S.oWord_pastWord, pastWord_congr h n]
  have e2 : ∀ n, pastWord (omega S.o y) n = pastWord (omega S.o x) n := fun n => by
    rw [← S.codeWord_pastWord_omega, ← S.codeWord_pastWord_omega, ← S.oWord_pastWord,
      ← S.oWord_pastWord, pastWord_congr h n]
  simpa only [SigmaOmega, HasBackRate, mem_ofPred_eq, e1, e2] using hx

/-- The slow axis depends only on the past. -/
theorem slowAxis_eq_of_samePast (μ : Measure (ℤ → ι)) {x y : ℤ → ι} (h : SamePast x y) :
    S.slowAxis μ y = S.slowAxis μ x := by
  by_cases hx : x ∈ S.SigmaTau μ
  · simp [slowAxis, hx, S.mem_SigmaTau_of_samePast μ h hx]
  · have hy : y ∉ S.SigmaTau μ := fun hy => hx (S.mem_SigmaTau_of_samePast μ h.symm hy)
    simp [slowAxis, hx, hy]

/-- The coordinate maps are additive; used for the differences `π(𝐣) - π(𝐢)` of
`sec:entropies`. -/
theorem coord_sub (c : ZMod 2) (a b : ℝ × ℝ) : coord c (a - b) = coord c a - coord c b := by
  unfold coord
  split_ifs <;> rfl

/-- Membership of a difference in `V_𝐢^i`, unfolded: no condition for `i = 0`, equality of the
coordinates transverse to the slow axis for `i = 1`, equality for `i ≥ 2`. -/
theorem mem_oseledets_iff (μ : Measure (ℤ → ι)) (x : ℤ → ι) (i : ℕ) (a b : ℝ × ℝ) :
    a - b ∈ S.oseledets μ x i ↔
      (i = 0 ∨ (i = 1 ∧ coord (S.slowAxis μ x + 1) a = coord (S.slowAxis μ x + 1) b) ∨
        (2 ≤ i ∧ a = b)) := by
  rcases i with _ | _ | i
  · simp [oseledets]
  · simp [oseledets, coord_sub, sub_eq_zero]
  · simp [oseledets, sub_eq_zero]

end Sigma

/-! ### Measurability -/

section Measurability

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι)

/-- The set of points along whose image under a measurable coding the backward rate exists and
equals `l` is Borel: the defining limit is a limit of functions of finitely many coordinates. -/
theorem measurableSet_hasBackRate {T : (ℤ → ι) → ℤ → ι × ZMod 2} (hT : Measurable T) (l : ℝ) :
    MeasurableSet {x | S.HasBackRate (T x) l} := by
  refine measurableSet_tendsto (𝓝 l) fun n => ?_
  simp only [pastWord_eq_futureWord]
  exact ((measurable_comp_futureWord (fun w => Real.log |S.gDeriv w| / n) n).comp
    (measurable_shift _)).comp hT

/-- `sec:lyapunov_exponents`, tex line 1545, proved: `Σ^τ` is Borel. -/
theorem measurableSet_SigmaTau (μ : Measure (ℤ → ι)) : MeasurableSet (S.SigmaTau μ) :=
  (S.measurableSet_hasBackRate (measurable_tau S.o) _).inter
    (S.measurableSet_hasBackRate (measurable_omega S.o) _)

/-- `sec:lyapunov_exponents`, tex line 1546, proved: `Σ^ω` is Borel. -/
theorem measurableSet_SigmaOmega (μ : Measure (ℤ → ι)) : MeasurableSet (S.SigmaOmega μ) :=
  (S.measurableSet_hasBackRate (measurable_tau S.o) _).inter
    (S.measurableSet_hasBackRate (measurable_omega S.o) _)

/-- `sec:lyapunov_exponents`, tex line 1521, proved: `Σ'` is Borel. -/
theorem measurableSet_SigmaPrime (μ : Measure (ℤ → ι)) : MeasurableSet (S.SigmaPrime μ) :=
  (S.measurableSet_SigmaTau μ).union (S.measurableSet_SigmaOmega μ)

end Measurability

end System

end BoxLike
