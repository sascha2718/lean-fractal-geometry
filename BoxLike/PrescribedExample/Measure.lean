module

/-
The Gibbs measures and the equilibrium state of `ex:projection_double_dimensional` (tex lines
3028 to 3048): the matrix `M(u)`, the vector `v = (p, 1 - p)`, the transition matrix
`Q_{ij} = M(s)_{ij} v_j / v_i` on the two orientation states, the Markov measure on the
projective shift `Σ_Z` that it defines, the identification of the `s`-Gibbs measures `μ_1`, `μ_2`
of `thm:eq_state_is_sum` with this measure and its mirror image, and the entropy and the two
Lyapunov exponents of the `s`-equilibrium state through `thm:entropy_eq_gibbs` and
`thm:eq_state_is_sum`.

Throughout, `P : Params` gives the contractions `0 < b < a < 1/2`, and `s` is an exponent with
`0 < s ≤ 1` and `2 a^s + 2 b^s = 1`, so that `p = 2 a^s` and `1 - p = 2 b^s`. For the parameters of
the example, `a = (p/2)^{1/s_1}` and `b = ((1-p)/2)^{1/s_1}`, this holds with `s = s_1`. No
statement depends on the translation vector `t`.

The Markov measure is built from a Bernoulli measure on `(ZMod 2 × ZMod 2)^ℤ`, whose symbol
`(c_k, u_k)` is an orientation state with distribution `v` and an independent uniform bit; the
lifted symbol at time `k` is the map `label (c_{k+1} - c_k) u_k` on the axis `c_k`. Since `Q` has
identical rows, the orientation states are independent, which is what makes this construction
possible.

General lemmas:

* `Gibbs.negMulLog_sum_le`, `Gibbs.blockEntropy_map_le`: the entropy of a coarser partition is
  smaller.
* `Gibbs.eq_of_measureReal_cylinder_le`: an invariant probability measure whose cylinder
  masses are bounded by a multiple of those of an ergodic one equals it.

The orientation states:

* `Gibbs.stateRatio`, `Gibbs.ratio_sys`: the contraction `a` or `b` of the selected coordinate.
* `Gibbs.M`, `Gibbs.M_apply`: the matrix `M(u) = 2 (a^u, a^u; b^u, b^u)`.
* `Gibbs.v`, `Gibbs.prob`, `Gibbs.mulVec_M_v`: `v = (p, 1 - p)` with `p = 2 a^s`, and
  `M(s) v = v`.
* `Gibbs.Q`, `Gibbs.Q_apply`, `Gibbs.vecMul_v_Q`: `Q_{ij} = M(s)_{ij} v_j / v_i = v_j`, so that
  both rows are `(p, 1 - p)`, and `(p, 1 - p)` is stationary.
* `Gibbs.card_labels`, `Gibbs.labelledProb`, `Gibbs.sum_labelledProb`,
  `Gibbs.sum_negMulLog_labelledProb`: each transition has two equiprobable labelled map
  choices, and from either state the four labelled transitions have the probabilities
  `p/2, p/2, (1-p)/2, (1-p)/2`, of entropy `-p log(p/2) - (1-p) log((1-p)/2)`.

The Markov measure:

* `Gibbs.label`, `Gibbs.bit`, `Gibbs.lift`, `Gibbs.unlift`, `Gibbs.rho`, `Gibbs.markov`.
* `Gibbs.isProbabilityMeasure_markov`, `Gibbs.measurePreserving_shift_markov`,
  `Gibbs.markov_subshift_compl`: an invariant probability measure carried by `Σ_Z`.
* `Gibbs.markov_cylinder`, `Gibbs.markov_cylinder_eq_Q`: its cylinder masses
  `v_{c_0} ∏_k Q_{c_k c_{k+1}} / 2`, the Markov measure with initial distribution `v`, transition
  matrix `Q` and two equiprobable map choices per transition.
* `Gibbs.entropy_markov`: its entropy is `log 2 + H(p)`.
* `Gibbs.eq_markov_of_isGibbs`: every ergodic Gibbs measure for the potential
  `log(v_{c_0} / 2)` carried by `Σ_Z` is this measure.

The example:

* `Gibbs.withRotations`, `Gibbs.hasProximalDiagonal`, `Gibbs.proximal`, `Gibbs.irreducible`.
* `Gibbs.potential₁_sys`, `Gibbs.potential₂_sys`: `f_{1,s}` and `f_{2,s}` are the potentials of
  the Markov measures with the vectors `(p, 1 - p)` and `(1 - p, p)`.
* `Gibbs.GibbsDecomposition.eq_markov`: `μ_1 = markov p` and `μ_2 = markov (1 - p)`.
* `Gibbs.integral_markov_state`, `Gibbs.integral_potential₁_markov`,
  `Gibbs.integral_potential₂_markov`, `Gibbs.lyapBar_markov`: averages over the Markov measure
  with the weights `(q, 1 - q)`, `∫ f_{1,1} = q log a + (1 - q) log b` and
  `∫ f_{2,1} = q log b + (1 - q) log a`.
* `Gibbs.isEquilibriumState_spec`: for every invariant `s`-equilibrium state `μ`,
  `μ = q_*(markov p)`, `h_0(μ) = log 2 + H(p)`, `λ_1(𝖠, μ) = p log a + (1 - p) log b` and
  `λ_2(𝖠, μ) = p log b + (1 - p) log a`.
* `Gibbs.existsUnique_isEquilibriumState`: the `s`-equilibrium state exists and is unique.
-/
public import BoxLike.EntropyEqualityEndpoint
public import BoxLike.EquilibriumExistence
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.GibbsProperties
public import BoxLike.Main
public import BoxLike.PressureZ
public import BoxLike.PrescribedExample.Defs

@[expose] public section

namespace BoxLike

namespace PrescribedExample

namespace Gibbs

open MeasureTheory Filter Topology
open scoped ENNReal symmDiff

/-! ### General lemmas -/

/-- `negMulLog` is sub-additive on finite sums of non-negative reals. Used for the entropy of
the Markov measure in `ex:projection_double_dimensional`. -/
theorem negMulLog_sum_le {κ : Type*} (s : Finset κ) {x : κ → ℝ} (hx : ∀ i ∈ s, 0 ≤ x i) :
    Real.negMulLog (∑ i ∈ s, x i) ≤ ∑ i ∈ s, Real.negMulLog (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have h1 := hx i (Finset.mem_insert_self i s)
    have h2 : ∀ j ∈ s, 0 ≤ x j := fun j hj => hx j (Finset.mem_insert_of_mem hj)
    exact (negMulLog_add_le h1 (Finset.sum_nonneg h2)).trans (by linarith [ih h2])

/-- If the block of length `n` of `F(z)` is a function of the block of length `N` of `z`, then
`H_{F_*μ}(𝒫_0^{n-1}) ≤ H_μ(𝒫_0^{N-1})`: the pulled back partition is coarser. Used for the
entropy of the Markov measure in `ex:projection_double_dimensional`. -/
theorem blockEntropy_map_le {α β : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ] {F : (ℤ → α) → ℤ → β} (hF : Measurable F)
    {n N : ℕ} (f : (Fin N → α) → (Fin n → β)) (hf : ∀ z, block n (F z) = f (block N z)) :
    blockEntropy (μ.map F) n ≤ blockEntropy μ N := by
  classical
  have hv : ∀ v : Fin n → β, (μ.map F).real (cylinder v) =
      ∑ u ∈ Finset.univ.filter (fun u => f u = v), μ.real (cylinder u) := by
    intro v
    rw [map_measureReal_apply hF (measurableSet_cylinder v)]
    have e : F ⁻¹' cylinder v = block N ⁻¹' ↑(Finset.univ.filter fun u => f u = v) := by
      ext z
      simp [cylinder_eq_preimage, hf]
    rw [e, ← sum_measureReal_preimage_singleton _
      (fun u _ => measurable_block N (measurableSet_singleton u))]
    simp [cylinder_eq_preimage]
  calc blockEntropy (μ.map F) n
      = ∑ v : Fin n → β, Real.negMulLog
          (∑ u ∈ Finset.univ.filter (fun u => f u = v), μ.real (cylinder u)) := by
        simp only [blockEntropy, hv]
    _ ≤ ∑ v : Fin n → β, ∑ u ∈ Finset.univ.filter (fun u => f u = v),
          Real.negMulLog (μ.real (cylinder u)) :=
        Finset.sum_le_sum fun v _ => negMulLog_sum_le _ fun _ _ => measureReal_nonneg
    _ = blockEntropy μ N := Finset.sum_fiberwise Finset.univ f _

section Unique

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

omit [Fintype α] [MeasurableSingletonClass α] in
/-- A measurable cylinder of `ℤ → α`, a set depending on finitely many coordinates, is the
translate `σ^{-K}` of a set depending on the coordinates `0, …, N - 1`. -/
theorem exists_shift_block_eq_of_mem_measurableCylinders {B : Set (ℤ → α)}
    (hB : B ∈ measurableCylinders fun _ : ℤ => α) :
    ∃ (K N : ℕ) (T : Set (Fin N → α)), B = shift (-(K : ℤ)) ⁻¹' (block N ⁻¹' T) := by
  obtain ⟨I, S, -, rfl⟩ := (mem_measurableCylinders B).1 hB
  have hlt : ∀ i ∈ I, (i + (I.sup Int.natAbs : ℕ)).toNat < 2 * I.sup Int.natAbs + 1 := by
    intro i hi
    have := Finset.le_sup (f := Int.natAbs) hi
    omega
  let R : (Fin (2 * I.sup Int.natAbs + 1) → α) → (I → α) := fun w i =>
    w ⟨(i.1 + (I.sup Int.natAbs : ℕ)).toNat, hlt i.1 i.2⟩
  refine ⟨I.sup Int.natAbs, 2 * I.sup Int.natAbs + 1, R ⁻¹' S, ?_⟩
  ext x
  simp only [MeasureTheory.cylinder, Set.mem_preimage]
  have : I.restrict x = R (block _ (shift (-((I.sup Int.natAbs : ℕ) : ℤ)) x)) := by
    funext i
    have := Finset.le_sup (f := Int.natAbs) i.2
    simp only [Finset.restrict, R, block, shift_apply]
    congr 1
    omega
  rw [this]

open Classical in
/-- For an invariant measure, the translate `σ^{-K}` of the set of points whose block of length
`N` lies in `T` has the measure `∑_{w ∈ T} μ[w]`. -/
theorem measure_shift_block_preimage {μ : Measure (ℤ → α)} (hμ : MeasurePreserving (shift 1) μ μ)
    (K N : ℕ) (T : Set (Fin N → α)) :
    μ (shift (-(K : ℤ)) ⁻¹' (block N ⁻¹' T)) =
      ∑ w ∈ Finset.univ.filter (· ∈ T), μ (cylinder w) := by
  have hT : MeasurableSet (block N ⁻¹' T) := measurable_block N (Set.toFinite T).measurableSet
  rw [(measurePreserving_shift_neg_natCast hμ K).measure_preimage hT.nullMeasurableSet]
  have h := sum_measure_preimage_singleton (μ := μ) (Finset.univ.filter (· ∈ T)) (f := block N)
    fun w _ => measurable_block N (measurableSet_singleton w)
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.ofPred_mem_eq] at h
  rw [← h]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [cylinder_eq_preimage]

/-- The uniqueness argument for the Gibbs measures of `ex:projection_double_dimensional`: an
invariant probability measure `μ` on `ℤ → α` with `μ[w] ≤ C ν[w]` for every cylinder is equal to
the ergodic probability measure `ν`. The bound extends from the cylinders to every Borel set by
approximation, so `μ ≪ ν`, and an invariant measure absolutely continuous with respect to an
ergodic one equals it. -/
theorem eq_of_measureReal_cylinder_le {μ ν : Measure (ℤ → α)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : MeasurePreserving (shift 1) μ μ) (hν : Ergodic (shift 1) ν)
    {C : ℝ} (h : ∀ (n : ℕ) (w : Fin n → α), μ.real (cylinder w) ≤ C * ν.real (cylinder w)) :
    μ = ν := by
  have hC : 0 ≤ C := by
    have h0 := h 0 Fin.elim0
    have e : (cylinder (Fin.elim0 : Fin 0 → α) : Set (ℤ → α)) = Set.univ := by
      ext x; simp [cylinder]
    simp only [e, probReal_univ, mul_one] at h0
    linarith
  have hcyl : ∀ B ∈ measurableCylinders (fun _ : ℤ => α), μ.real B ≤ C * ν.real B := by
    intro B hB
    obtain ⟨K, N, T, rfl⟩ := exists_shift_block_eq_of_mem_measurableCylinders hB
    simp only [measureReal_def, measure_shift_block_preimage hμ,
      measure_shift_block_preimage hν.toMeasurePreserving]
    rw [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _),
      ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _), Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ => h N w
  refine hν.eq_of_absolutelyContinuous hμ (Measure.AbsolutelyContinuous.mk fun A hA hνA => ?_)
  have hνA' : ν.real A = 0 := by rw [measureReal_def, hνA, ENNReal.toReal_zero]
  have key : ∀ ε : ℝ, 0 < ε → μ.real A ≤ (C + 1) * ε := by
    intro ε hε
    obtain ⟨B, hB, hBA⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
      (μ := μ + ν) isSetRing_measurableCylinders
      ⟨{Set.univ}, Set.countable_singleton _,
        by simpa using univ_mem_measurableCylinders fun _ : ℤ => α, by simp⟩
      generateFrom_measurableCylinders.symm hA (ENNReal.ofReal_pos.2 hε)
    rw [Measure.add_apply] at hBA
    have h1 : μ.real (B ∆ A) < ε :=
      ENNReal.toReal_lt_of_lt_ofReal (lt_of_le_of_lt le_self_add hBA)
    have h2 : ν.real (B ∆ A) < ε :=
      ENNReal.toReal_lt_of_lt_ofReal (lt_of_le_of_lt le_add_self hBA)
    have hA1 : μ.real A ≤ μ.real B + μ.real (B ∆ A) := by
      refine (measureReal_mono (fun x hx => ?_)).trans (measureReal_union_le B (B ∆ A))
      by_cases hxB : x ∈ B
      · exact Or.inl hxB
      · exact Or.inr (Or.inr ⟨hx, hxB⟩)
    have hB1 : ν.real B ≤ ν.real A + ν.real (B ∆ A) := by
      refine (measureReal_mono (fun x hx => ?_)).trans (measureReal_union_le A (B ∆ A))
      by_cases hxA : x ∈ A
      · exact Or.inl hxA
      · exact Or.inr (Or.inl ⟨hx, hxA⟩)
    have := hcyl B hB
    rw [hνA'] at hB1
    nlinarith
  have h0 : μ.real A = 0 := le_antisymm (le_of_forall_pos_le_add fun ε hε => by
      have := key (ε / (C + 1)) (by positivity)
      rw [mul_div_cancel₀ _ (by positivity)] at this
      linarith) measureReal_nonneg
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 h0

end Unique

/-! ### The orientation states -/

/-- The contraction of the selected coordinate in the orientation state `c` of
`ex:projection_double_dimensional`: `a` on the first axis, `c = 0`, and `b` on the second,
`c = 1`. -/
noncomputable def stateRatio (P : Params) (c : ZMod 2) : ℝ := if c = 0 then P.a else P.b

/-- The ratio `g_j'` of the projective system of `ex:projection_double_dimensional` depends on
the axis of `j` only. -/
theorem ratio_sys (P : Params) (t : Fin 8 → ℝ) (q : Fin 4 × ZMod 2) :
    (sys P t).ratio q = stateRatio P q.2 := by
  simp [System.ratio, sys, stateRatio]

/-- The contractions `a`, `b` of the orientation states are positive. -/
theorem stateRatio_pos (P : Params) (c : ZMod 2) : 0 < stateRatio P c := by
  unfold stateRatio
  split_ifs
  · exact P.a_pos
  · exact P.b_pos

/-- The matrix `M(u)` of `ex:projection_double_dimensional` (tex lines 2844 to 2848): its
`(i, j)` entry sums the `u`th powers of the contractions from the coordinate `j` to the
coordinate `i`. By `System.coord_phi`, the map `k` sends the coordinate `i + o(k)` to the
coordinate `i` with the contraction of the axis `i`. -/
noncomputable def M (P : Params) (u : ℝ) : Matrix (ZMod 2) (ZMod 2) ℝ :=
  Matrix.of fun i j => ∑ k : Fin 4, if i + orient k = j then stateRatio P i ^ u else 0

/-- For every pair of axes `i`, `j` exactly two of the four maps lead from `j` to `i`:
the two diagonal maps when `i = j` and the two anti-diagonal maps otherwise. These are the two
labelled map choices of a transition in `ex:projection_double_dimensional`. -/
theorem card_labels (i j : ZMod 2) :
    (Finset.univ.filter fun k : Fin 4 => i + orient k = j).card = 2 := by
  revert i j
  decide

/-- `M(u) = 2 (a^u, a^u; b^u, b^u)`, the display of tex lines 2846 to 2848. -/
theorem M_apply (P : Params) (u : ℝ) (i j : ZMod 2) : M P u i j = 2 * stateRatio P i ^ u := by
  rw [M, Matrix.of_apply, ← Finset.sum_filter, Finset.sum_const, card_labels, nsmul_eq_mul]
  norm_num

/-- The vector `v = (p, 1 - p)` of `ex:projection_double_dimensional`, indexed by the
orientation states. -/
def v (p : ℝ) (c : ZMod 2) : ℝ := if c = 0 then p else 1 - p

/-- The parameter `p = 2 a^s`; for the example `a = (p/2)^{1/s_1}` and `s = s_1`. -/
noncomputable def prob (P : Params) (s : ℝ) : ℝ := 2 * P.a ^ s

section States

variable {p : ℝ}

/-- `v = (p, 1 - p)` is non-negative for `0 ≤ p ≤ 1`. -/
theorem v_nonneg (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (c : ZMod 2) : 0 ≤ v p c := by
  unfold v; split_ifs <;> linarith

/-- `v = (p, 1 - p)` is positive for `0 < p < 1`. -/
theorem v_pos (hp0 : 0 < p) (hp1 : p < 1) (c : ZMod 2) : 0 < v p c := by
  unfold v; split_ifs <;> linarith

/-- `v ≤ 1` for `0 ≤ p ≤ 1`. -/
theorem v_le_one (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (c : ZMod 2) : v p c ≤ 1 := by
  unfold v; split_ifs <;> linarith

/-- `v_0 = p`. -/
@[simp] theorem v_zero : v p 0 = p := rfl

/-- `v_1 = 1 - p`. -/
@[simp] theorem v_one : v p 1 = 1 - p := rfl

/-- The two entries of `v` sum to one. -/
theorem v_add_v_add_one (c : ZMod 2) : v p c + v p (c + 1) = 1 := by
  rcases zmod_two_cases c with rfl | rfl <;>
    simp [v, show (1 : ZMod 2) + 1 = 0 from by decide]

/-- The vector of the second Gibbs measure: `v_{c + 1} = (1 - p, p)_c`. -/
theorem v_add_one (c : ZMod 2) : v p (c + 1) = v (1 - p) c := by
  rcases zmod_two_cases c with rfl | rfl <;>
    simp [v, show (1 : ZMod 2) + 1 = 0 from by decide]

end States

section Eigen

variable (P : Params) {s : ℝ}

/-- With `p = 2 a^s` and `2 a^s + 2 b^s = 1`, the entries of `v` are `2 a^s` and `2 b^s`:
`v_c = 2 r_c^s`. -/
theorem v_prob (hP : 2 * P.a ^ s + 2 * P.b ^ s = 1) (c : ZMod 2) :
    v (prob P s) c = 2 * stateRatio P c ^ s := by
  rcases zmod_two_cases c with rfl | rfl
  · simp [v, prob, stateRatio]
  · simp only [v_one, prob, stateRatio]
    simp only [one_ne_zero, ite_false]
    linarith

/-- `0 < p = 2 a^s < 1`. -/
theorem prob_pos_lt_one (hP : 2 * P.a ^ s + 2 * P.b ^ s = 1) : 0 < prob P s ∧ prob P s < 1 := by
  have ha := Real.rpow_pos_of_pos P.a_pos s
  have hb := Real.rpow_pos_of_pos P.b_pos s
  unfold prob
  constructor <;> linarith

/-- `M(s) v = v`, tex line 2861: `v = (p, 1 - p)` is an eigenvector of `M(s)` with eigenvalue
`2 a^s + 2 b^s = 1`. -/
theorem mulVec_M_v (hP : 2 * P.a ^ s + 2 * P.b ^ s = 1) :
    (M P s).mulVec (v (prob P s)) = v (prob P s) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, M_apply, ← Finset.mul_sum, sum_zmod_two]
  rw [show (1 : ZMod 2) = 0 + 1 from (zero_add 1).symm, v_add_v_add_one, mul_one,
    v_prob P hP]

/-- The transition probabilities `Q_{ij} = M(s)_{ij} v_j / v_i` on the two orientation states of
the `s`-Gibbs measure `μ_1`, tex lines 2861 to 2866. -/
noncomputable def Q (s : ℝ) : Matrix (ZMod 2) (ZMod 2) ℝ :=
  Matrix.of fun i j => M P s i j * v (prob P s) j / v (prob P s) i

/-- `Q_{ij} = v_j`: both rows of `Q` are `(p, 1 - p)`, tex lines 2863 to 2865. -/
theorem Q_apply (hP : 2 * P.a ^ s + 2 * P.b ^ s = 1) (i j : ZMod 2) :
    Q P s i j = v (prob P s) j := by
  obtain ⟨h0, h1⟩ := prob_pos_lt_one P hP
  rw [Q, Matrix.of_apply, M_apply, ← v_prob P hP, mul_div_right_comm,
    div_self (v_pos h0 h1 i).ne', one_mul]

/-- The stationary distribution of `Q` is `(p, 1 - p)`, tex line 2866: `v Q = v`. -/
theorem vecMul_v_Q (hP : 2 * P.a ^ s + 2 * P.b ^ s = 1) :
    Matrix.vecMul (v (prob P s)) (Q P s) = v (prob P s) := by
  funext j
  simp only [Matrix.vecMul, dotProduct, Q_apply P hP, ← Finset.sum_mul, sum_zmod_two]
  rw [show (1 : ZMod 2) = 0 + 1 from (zero_add 1).symm, v_add_v_add_one, one_mul]

/-- The probability `Q_{i, i + o(k)} / 2` of the labelled transition by the map `k` from the
state `i`: the transition `i → i + o(k)` followed by one of its two equiprobable map choices,
tex lines 2866 to 2868. -/
noncomputable def labelledProb (s : ℝ) (i : ZMod 2) (k : Fin 4) : ℝ :=
  Q P s i (i + orient k) / 2

/-- The four labelled transitions from either state are a probability vector. -/
theorem sum_labelledProb (hP : 2 * P.a ^ s + 2 * P.b ^ s = 1) (i : ZMod 2) :
    ∑ k, labelledProb P s i k = 1 := by
  simp only [labelledProb, Q_apply P hP, Fin.sum_univ_four]
  rcases zmod_two_cases i with rfl | rfl <;>
    simp [orient, v, show (1 : ZMod 2) + 1 = 0 from by decide] <;> ring

/-- From either state the four labelled transitions have the probabilities
`p/2, p/2, (1-p)/2, (1-p)/2`, so their entropy is `-p log(p/2) - (1-p) log((1-p)/2)`,
tex lines 2866 to 2871. -/
theorem sum_negMulLog_labelledProb (hP : 2 * P.a ^ s + 2 * P.b ^ s = 1) (i : ZMod 2) :
    ∑ k, Real.negMulLog (labelledProb P s i k) =
      -(prob P s * Real.log (prob P s / 2)) -
        (1 - prob P s) * Real.log ((1 - prob P s) / 2) := by
  simp only [labelledProb, Q_apply P hP, Fin.sum_univ_four]
  rcases zmod_two_cases i with rfl | rfl <;>
    simp [orient, v, Real.negMulLog, show (1 : ZMod 2) + 1 = 0 from by decide] <;> ring

end Eigen

/-! ### The Markov measure -/

/-- The map with orientation `d` and choice bit `u`: the diagonal maps `0`, `1` for `d = 0` and
the anti-diagonal maps `2`, `3` for `d = 1`. -/
def label (d u : ZMod 2) : Fin 4 :=
  if d = 0 then (if u = 0 then 0 else 1) else (if u = 0 then 2 else 3)

/-- The choice bit of a map: `0` for the maps `0`, `2` and `1` for the maps `1`, `3`. -/
def bit (i : Fin 4) : ZMod 2 := if (i : ℕ) % 2 = 0 then 0 else 1

/-- The map `label d u` has the orientation `d`. -/
theorem orient_label (d u : ZMod 2) : orient (label d u) = d := by
  revert d u; decide

/-- The map `label d u` has the choice bit `u`. -/
theorem bit_label (d u : ZMod 2) : bit (label d u) = u := by
  revert d u; decide

/-- A map is determined by its orientation and its choice bit. -/
theorem label_orient_bit (i : Fin 4) : label (orient i) (bit i) = i := by
  revert i; decide

/-- The lift of a sequence `z_k = (c_k, u_k)` of orientation states and choice bits to `Σ_Z`:
at time `k` the map `label (c_{k+1} - c_k) u_k` on the axis `c_k`. -/
def lift (z : ℤ → ZMod 2 × ZMod 2) : ℤ → Fin 4 × ZMod 2 :=
  fun k => (label ((z (k + 1)).1 - (z k).1) (z k).2, (z k).1)

/-- The inverse of `lift`: the axis and the choice bit of each symbol. -/
def unlift (y : ℤ → Fin 4 × ZMod 2) : ℤ → ZMod 2 × ZMod 2 := fun k => ((y k).2, bit (y k).1)

/-- `unlift ∘ lift` is the identity. -/
theorem unlift_lift (z : ℤ → ZMod 2 × ZMod 2) : unlift (lift z) = z := by
  funext k
  simp [unlift, lift, bit_label]

/-- `lift` takes values in `Σ_Z`: the axis changes exactly at the anti-diagonal maps. -/
theorem lift_mem_subshift (z : ℤ → ZMod 2 × ZMod 2) : lift z ∈ subshift orient := by
  intro k
  simp only [Trans, lift, orient_label]
  ring

/-- `lift` commutes with the shift. -/
theorem lift_shift (m : ℤ) (z : ℤ → ZMod 2 × ZMod 2) : lift (shift m z) = shift m (lift z) := by
  funext k
  simp only [lift, shift_apply, add_assoc]

/-- `lift` is measurable. -/
theorem measurable_lift : Measurable lift := by
  refine Measurable.of_eval fun k => ?_
  have h : Measurable fun z : ℤ → ZMod 2 × ZMod 2 => (z k, z (k + 1)) :=
    (measurable_pi_apply k).prodMk (measurable_pi_apply (k + 1))
  exact (Measurable.of_discrete (f := fun q : (ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2) =>
    ((label (q.2.1 - q.1.1) q.1.2, q.1.1) : Fin 4 × ZMod 2))).comp h

/-- `unlift` is measurable. -/
theorem measurable_unlift : Measurable unlift :=
  Measurable.of_eval fun k =>
    (Measurable.of_discrete
      (f := fun q : Fin 4 × ZMod 2 => ((q.2, bit q.1) : ZMod 2 × ZMod 2))).comp
      (measurable_pi_apply k)

/-- The weight `v_c / 2` of the pair `(c, u)`: the orientation state `c` with distribution `v` and
an independent uniform choice bit `u`. -/
noncomputable def zWeight (p : ℝ) (x : ZMod 2 × ZMod 2) : ℝ := v p x.1 / 2

/-- The distribution `∑_{(c, u)} (v_c / 2) δ_{(c, u)}` of a pair. -/
noncomputable def rho (p : ℝ) : Measure (ZMod 2 × ZMod 2) := weightMeasure (zWeight p)

/-- The Markov measure on `Σ_Z` of `ex:projection_double_dimensional` with state vector
`v = (p, 1 - p)`: the image under `lift` of the Bernoulli measure with the distribution `rho p`.
`markov_cylinder_eq_Q` identifies its cylinder masses. -/
noncomputable def markov (p : ℝ) : Measure (ℤ → Fin 4 × ZMod 2) := (bernoulli (rho p)).map lift

section Markov

variable {p : ℝ}

/-- `rho p` is a probability measure for `0 ≤ p ≤ 1`. -/
theorem isProbabilityMeasure_rho (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : IsProbabilityMeasure (rho p) :=
  isProbabilityMeasure_weightMeasure (fun x => div_nonneg (v_nonneg hp0 hp1 _) two_pos.le) (by
    simp [zWeight, Fintype.sum_prod_type, sum_zmod_two, v])

/-- The pair `(c, u)` has the probability `v_c / 2`. -/
theorem rho_real_singleton (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ZMod 2 × ZMod 2) :
    (rho p).real {x} = v p x.1 / 2 :=
  measureReal_weightMeasure_singleton (p := zWeight p) (div_nonneg (v_nonneg hp0 hp1 _) two_pos.le)

/-- The Markov measure is a probability measure. -/
theorem isProbabilityMeasure_markov (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (markov p) := by
  have := isProbabilityMeasure_rho hp0 hp1
  unfold markov
  infer_instance

/-- The Markov measure is invariant, as the image of an invariant measure under a map that
commutes with the shift. -/
theorem measurePreserving_shift_markov (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    MeasurePreserving (shift 1) (markov p) (markov p) := by
  have := isProbabilityMeasure_rho hp0 hp1
  refine ⟨measurable_shift 1, ?_⟩
  rw [markov, Measure.map_map (measurable_shift 1) measurable_lift]
  have h : (shift 1 : (ℤ → Fin 4 × ZMod 2) → _) ∘ lift = lift ∘ shift 1 :=
    funext fun z => (lift_shift 1 z).symm
  rw [h, ← Measure.map_map measurable_lift (measurable_shift 1),
    (measurePreserving_shift_bernoulli (rho p) 1).map_eq]

/-- The Markov measure is carried by `Σ_Z`. -/
theorem markov_subshift_compl : markov p (subshift orient)ᶜ = 0 := by
  rw [markov, Measure.map_apply measurable_lift (measurableSet_subshift orient).compl]
  exact measure_mono_null (fun z hz => (hz (lift_mem_subshift z)).elim) measure_empty

/-- The orientation state of a pair has the distribution `v`. -/
theorem rho_fst (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (c : ZMod 2) :
    rho p {x | x.1 = c} = ENNReal.ofReal (v p c) := by
  have e : {x : ZMod 2 × ZMod 2 | x.1 = c} = {(c, 0)} ∪ {(c, 1)} := by
    ext ⟨a, b⟩
    rcases zmod_two_cases b with rfl | rfl <;> simp [eq_comm]
  have hv := v_nonneg hp0 hp1 c
  rw [e, measure_union (by simp) (measurableSet_singleton _), rho, weightMeasure_singleton,
    weightMeasure_singleton]
  simp only [zWeight]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- The preimage under `lift` of the cylinder of a point `y ∈ Σ_Z`: the pairs at the times
`k < n` are the axes and choice bits of `y`, and the axis at the time `n` is that of `y`. -/
theorem preimage_lift_cylinder {y : ℤ → Fin 4 × ZMod 2} (hy : y ∈ subshift orient) {n : ℕ}
    (hn : 0 < n) :
    lift ⁻¹' (cylinder fun k : Fin n => y k) =
      Set.pi (((Finset.range (n + 1)).map Nat.castEmbedding : Finset ℤ) : Set ℤ) fun j : ℤ =>
        if j < n then {((y j).2, bit (y j).1)} else {x | x.1 = (y j).2} := by
  ext z
  simp only [Set.mem_preimage, mem_cylinder, Finset.coe_map, Nat.castEmbedding_apply,
    Finset.coe_range, Set.mem_pi, Set.mem_image, Set.mem_Iio, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  constructor
  · intro h a ha
    by_cases han : a < n
    · have hk := Prod.ext_iff.1 (h ⟨a, han⟩)
      simp only [lift] at hk
      rw [ite_eq_left (by exact_mod_cast han), Set.mem_singleton_iff]
      have h2 := congrArg bit hk.1
      rw [bit_label] at h2
      exact Prod.ext hk.2 h2
    · have han' : a = n := by omega
      subst han'
      rw [ite_eq_right (lt_irrefl _), Set.mem_ofPred_eq]
      obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
      have hk := Prod.ext_iff.1 (h ⟨m, by omega⟩)
      simp only [lift] at hk
      have h1 := congrArg orient hk.1
      rw [orient_label] at h1
      have hs := hy (m : ℤ)
      simp only [Trans] at hs
      push_cast at h1 hs ⊢
      rw [hs, ← h1, ← hk.2]
      ring
  · intro h k
    have hz : ∀ a : ℕ, a ≤ n → (z a).1 = (y a).2 := by
      intro a ha
      have := h a (by omega)
      by_cases han : a < n
      · rw [ite_eq_left (by exact_mod_cast han), Set.mem_singleton_iff] at this
        rw [this]
      · have han' : a = n := by omega
        subst han'
        rw [ite_eq_right (lt_irrefl _), Set.mem_ofPred_eq] at this
        exact this
    have hk := h k (by omega)
    rw [ite_eq_left (by exact_mod_cast k.2), Set.mem_singleton_iff] at hk
    have hk1 := hz (k + 1) (by omega)
    have hs := hy (k : ℤ)
    simp only [Trans] at hs
    push_cast at hk1
    simp only [lift, hk, hk1, hs, add_sub_cancel_left, label_orient_bit]

/-- The cylinder masses of the Markov measure: for `y ∈ Σ_Z` with axes `c_k` and `n ≥ 1`,
`markov p [y|_n] = (∏_{k < n} v_{c_k} / 2) v_{c_n}`. -/
theorem markov_cylinder (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {y : ℤ → Fin 4 × ZMod 2}
    (hy : y ∈ subshift orient) {n : ℕ} (hn : 0 < n) :
    (markov p).real (cylinder fun k : Fin n => y k) =
      (∏ k : Fin n, v p (y k).2 / 2) * v p (y n).2 := by
  have hm : MeasurableSet (cylinder fun k : Fin n => y k) := measurableSet_cylinder _
  have := isProbabilityMeasure_rho hp0 hp1
  rw [markov, map_measureReal_apply measurable_lift hm, preimage_lift_cylinder hy hn,
    measureReal_def, bernoulli, Measure.infinitePi_pi]
  · simp only [Finset.prod_map, Nat.castEmbedding_apply, Nat.cast_lt]
    rw [Finset.prod_range_succ, ite_eq_right (lt_irrefl n), rho_fst hp0 hp1,
      ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_ofReal (v_nonneg hp0 hp1 _),
      ← Fin.prod_univ_eq_prod_range]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [ite_eq_left k.2, rho, weightMeasure_singleton, zWeight]
    exact ENNReal.toReal_ofReal (div_nonneg (v_nonneg hp0 hp1 _) two_pos.le)
  · intro j _
    split_ifs
    · exact measurableSet_singleton _
    · exact (Set.toFinite _).measurableSet

/-- The entropy of the Markov measure, tex lines 2868 to 2871:
`h(markov p) = -p log(p/2) - (1-p) log((1-p)/2) = log 2 + H(p)`. The `n`-cylinders of the
Markov measure are unions of `(n+1)`-cylinders of the Bernoulli measure and the reverse holds
with `n` in place of `n + 1`, so the block entropies differ by a bounded amount from those of
the Bernoulli measure with the distribution `p/2, p/2, (1-p)/2, (1-p)/2`. -/
theorem entropy_markov (hp0 : 0 < p) (hp1 : p < 1) :
    entropy (markov p) = Real.log 2 + H p := by
  have := isProbabilityMeasure_rho hp0.le hp1.le
  have := isProbabilityMeasure_markov hp0.le hp1.le
  set β := bernoulli (rho p)
  have h1 : ∀ n, blockEntropy (markov p) n ≤ blockEntropy β (n + 1) := fun n =>
    blockEntropy_map_le β measurable_lift
      (fun u (k : Fin n) => (label ((u k.succ).1 - (u k.castSucc).1) (u k.castSucc).2,
        (u k.castSucc).1)) fun z => by
      funext k
      simp only [block, lift, Fin.val_succ, Fin.val_castSucc]
      push_cast
      rfl
  have hβ : (markov p).map unlift = β := by
    rw [markov, Measure.map_map measurable_unlift measurable_lift]
    have : unlift ∘ lift = id := funext unlift_lift
    rw [this, Measure.map_id]
  have h2 : ∀ n, blockEntropy β n ≤ blockEntropy (markov p) n := fun n => by
    rw [← hβ]
    exact blockEntropy_map_le (markov p) measurable_unlift
      (fun w (k : Fin n) => ((w k).2, bit (w k).1)) fun _ => rfl
  have h3 : ∀ n, blockEntropy β (n + 1) =
      blockEntropy β n + ∑ x, Real.negMulLog ((rho p).real {x}) := fun n => by
    rw [blockEntropy_bernoulli, blockEntropy_bernoulli]
    push_cast
    ring
  have hX : 0 ≤ ∑ x, Real.negMulLog ((rho p).real {x}) :=
    Finset.sum_nonneg fun _ _ => Real.negMulLog_nonneg measureReal_nonneg measureReal_le_one
  have heq := entropy_eq_of_blockEntropy_close (ν := markov p)
    (tendsto_entropy (measurePreserving_shift_bernoulli (rho p) 1))
    (C := ∑ x, Real.negMulLog ((rho p).real {x})) fun n => by
      rw [abs_le]
      constructor <;> linarith [h1 n, h2 n, h3 n]
  rw [heq, entropy_bernoulli]
  simp only [rho_real_singleton hp0.le hp1.le, Fintype.sum_prod_type, sum_zmod_two, v_zero,
    v_one, H, Real.negMulLog]
  rw [Real.log_div hp0.ne' two_ne_zero, Real.log_div (by linarith) two_ne_zero]
  ring

/-- A Gibbs measure for the potential `log(v_{c_0} / 2)` and the Markov measure have comparable
cylinder masses: `ν[w] ≤ K exp(-nP) markov p [w]` and `markov p [w] ≤ C exp(nP) ν[w]`. -/
theorem measureReal_cylinder_le_of_isGibbsWith (hp0 : 0 < p) (hp1 : p < 1)
    {φ : Fin 4 × ZMod 2 → ℝ} (hφ : ∀ q, φ q = Real.log (v p q.2 / 2))
    {ν : Measure (ℤ → Fin 4 × ZMod 2)} [IsFiniteMeasure ν] (hsupp : ν (subshift orient)ᶜ = 0)
    {P C : ℝ} (hb : IsGibbsWith orient φ ν P C) {n : ℕ} (hn : 0 < n)
    (w : Fin n → Fin 4 × ZMod 2) :
    ν.real (cylinder w) ≤
        C / min p (1 - p) * Real.exp (-(n * P)) * (markov p).real (cylinder w) ∧
      (markov p).real (cylinder w) ≤ C * Real.exp (n * P) * ν.real (cylinder w) := by
  obtain ⟨hC, hb⟩ := hb
  have hδ : 0 < min p (1 - p) := lt_min hp0 (by linarith)
  by_cases hex : ∃ y ∈ subshift orient, y ∈ cylinder w
  · obtain ⟨y, hy, hyw⟩ := hex
    obtain rfl : w = fun k : Fin n => y k := funext fun k => (hyw k).symm
    have hm := markov_cylinder hp0.le hp1.le hy hn
    obtain ⟨hlo, hhi⟩ := hb y hy n hn
    have hexp : Real.exp (∑ k ∈ Finset.range n, φ (y k)) = ∏ k : Fin n, v p (y k).2 / 2 := by
      rw [Real.exp_sum, ← Fin.prod_univ_eq_prod_range (fun k => Real.exp (φ (y k))) n]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [hφ, Real.exp_log (div_pos (v_pos hp0 hp1 _) two_pos)]
    rw [Real.exp_add, hexp] at hlo hhi
    set E := ∏ k : Fin n, v p (y k).2 / 2
    have hE : 0 < E := Finset.prod_pos fun k _ => div_pos (v_pos hp0 hp1 _) two_pos
    have hvn := v_pos hp0 hp1 (y n).2
    have hvδ : min p (1 - p) ≤ v p (y n).2 := by
      unfold v
      split_ifs
      · exact min_le_left _ _
      · exact min_le_right _ _
    have hv1 := v_le_one hp0.le hp1.le (y n).2
    have hx := Real.exp_pos (-(n * P))
    have hx' := Real.exp_pos (n * P)
    have hxx : Real.exp (n * P) * Real.exp (-(n * P)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    constructor
    · rw [hm]
      refine hhi.trans ?_
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hδ]
      have : E * min p (1 - p) ≤ E * v p (y n).2 := mul_le_mul_of_nonneg_left hvδ hE.le
      have hCx : 0 ≤ C * Real.exp (-(n * P)) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this hCx]
    · rw [hm]
      have hEν : E ≤ C * Real.exp (n * P) * ν.real (cylinder fun k : Fin n => y k) := by
        rw [inv_mul_le_iff₀ hC] at hlo
        calc E = Real.exp (n * P) * (Real.exp (-(n * P)) * E) := by
              rw [← mul_assoc, hxx, one_mul]
          _ ≤ Real.exp (n * P) * (C * ν.real (cylinder fun k : Fin n => y k)) :=
              mul_le_mul_of_nonneg_left hlo hx'.le
          _ = C * Real.exp (n * P) * ν.real (cylinder fun k : Fin n => y k) := by ring
      calc E * v p (y n).2 ≤ E * 1 := mul_le_mul_of_nonneg_left hv1 hE.le
        _ = E := mul_one E
        _ ≤ _ := hEν
  · push Not at hex
    have hsub : cylinder w ⊆ (subshift orient)ᶜ := fun y hyw hy => hex y hy hyw
    have h1 : ν.real (cylinder w) = 0 := by
      rw [measureReal_def, measure_mono_null hsub hsupp, ENNReal.toReal_zero]
    have h2 : (markov p).real (cylinder w) = 0 := by
      rw [measureReal_def, measure_mono_null hsub markov_subshift_compl, ENNReal.toReal_zero]
    rw [h1, h2]
    simp

/-- Identification of the Gibbs measure, tex lines 2861 to 2866: an ergodic probability measure
carried by `Σ_Z` with the Gibbs property of `sec:gibbs_measures` for the potential
`φ(j_0) = log(v_{c_0} / 2)` is the Markov measure `markov p`. Summing the comparison of
`measureReal_cylinder_le_of_isGibbsWith` over the `n`-cylinders forces `P ≤ 0`, so
`markov p [w] ≤ C ν[w]` for every cylinder, and `eq_of_measureReal_cylinder_le` applies. -/
theorem eq_markov_of_isGibbs (hp0 : 0 < p) (hp1 : p < 1) {φ : Fin 4 × ZMod 2 → ℝ}
    (hφ : ∀ q, φ q = Real.log (v p q.2 / 2)) {ν : Measure (ℤ → Fin 4 × ZMod 2)}
    [IsProbabilityMeasure ν] (herg : Ergodic (shift 1) ν) (hsupp : ν (subshift orient)ᶜ = 0)
    (hG : IsGibbs orient φ ν) : ν = markov p := by
  obtain ⟨P, C, hb⟩ := isGibbs_iff.1 hG
  have hC := hb.1
  have := isProbabilityMeasure_markov hp0.le hp1.le
  have hδ : 0 < min p (1 - p) := lt_min hp0 (by linarith)
  have hK : 0 < C / min p (1 - p) := div_pos hC hδ
  have hall := fun n hn w => measureReal_cylinder_le_of_isGibbsWith hp0 hp1 hφ hsupp hb
    (n := n) hn w
  have hP : P ≤ 0 := by
    by_contra hpos
    push Not at hpos
    obtain ⟨n, hn⟩ := exists_nat_gt (Real.log (C / min p (1 - p)) / P)
    have hsum : (1 : ℝ) ≤ C / min p (1 - p) * Real.exp (-(((n + 1 : ℕ) : ℝ) * P)) := by
      calc (1 : ℝ) = ∑ w : Fin (n + 1) → Fin 4 × ZMod 2, ν.real (cylinder w) :=
            (sum_measureReal_cylinder ν (n + 1)).symm
        _ ≤ ∑ w : Fin (n + 1) → Fin 4 × ZMod 2, C / min p (1 - p) *
              Real.exp (-(((n + 1 : ℕ) : ℝ) * P)) * (markov p).real (cylinder w) :=
            Finset.sum_le_sum fun w _ => (hall (n + 1) n.succ_pos w).1
        _ = C / min p (1 - p) * Real.exp (-(((n + 1 : ℕ) : ℝ) * P)) := by
            rw [← Finset.mul_sum, sum_measureReal_cylinder, mul_one]
    have hl := Real.log_le_log one_pos hsum
    rw [Real.log_one, Real.log_mul hK.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
    rw [div_lt_iff₀ hpos] at hn
    push_cast at hl
    nlinarith
  refine (eq_of_measureReal_cylinder_le (μ := markov p) (ν := ν)
    (measurePreserving_shift_markov hp0.le hp1.le) herg (C := max C 1) fun n w => ?_).symm
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have e : (cylinder w : Set (ℤ → Fin 4 × ZMod 2)) = Set.univ := by
      ext x; simp [cylinder]
    rw [e, probReal_univ, probReal_univ, mul_one]
    exact le_max_right _ _
  · refine (hall n hn w).2.trans ?_
    have h1 : Real.exp (n * P) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) hP
    have h2 : C * Real.exp (n * P) ≤ max C 1 :=
      (mul_le_of_le_one_right hC.le h1).trans (le_max_left _ _)
    exact mul_le_mul_of_nonneg_right h2 measureReal_nonneg

end Markov

/-- The Markov form of the cylinder masses, tex lines 2861 to 2868: for `y ∈ Σ_Z` with axes
`c_k`, `markov p [y|_n] = v_{c_0} ∏_{k < n} Q_{c_k c_{k+1}} / 2`. The Markov measure starts in the
stationary distribution `v = (p, 1 - p)`, moves between the orientation states with the
transition matrix `Q` and chooses one of the two maps of each transition with probability
`1/2`. -/
theorem markov_cylinder_eq_Q (P : Params) {s : ℝ} (hP : 2 * P.a ^ s + 2 * P.b ^ s = 1)
    {y : ℤ → Fin 4 × ZMod 2} (hy : y ∈ subshift orient) {n : ℕ} (hn : 0 < n) :
    (markov (prob P s)).real (cylinder fun k : Fin n => y k) =
      v (prob P s) (y 0).2 * ∏ k : Fin n, Q P s (y k).2 (y (k + 1)).2 / 2 := by
  obtain ⟨h0, h1⟩ := prob_pos_lt_one P hP
  rw [markov_cylinder h0.le h1.le hy hn]
  simp only [Q_apply P hP]
  set g : ℕ → ℝ := fun k => v (prob P s) (y k).2
  have e1 : ∏ k : Fin n, v (prob P s) (y k).2 / 2 = ∏ k ∈ Finset.range n, (g k / 2) :=
    Fin.prod_univ_eq_prod_range (fun k => g k / 2) n
  have e2 : ∏ k : Fin n, v (prob P s) (y ((k : ℕ) + 1 : ℤ)).2 / 2 =
      ∏ k ∈ Finset.range n, (g (k + 1) / 2) := by
    rw [← Fin.prod_univ_eq_prod_range (fun k => g (k + 1) / 2) n]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp [g]
  rw [e1, e2, Finset.prod_div_distrib, Finset.prod_div_distrib]
  have e3 := Finset.prod_range_succ g n
  have e4 := Finset.prod_range_succ' g n
  change (∏ k ∈ Finset.range n, g k) / _ * g n = g 0 * ((∏ k ∈ Finset.range n, g (k + 1)) / _)
  rw [div_mul_eq_mul_div, ← e3, mul_div_assoc', mul_comm (g 0), e4]

/-! ### The example -/

section Example

variable (P : Params) (t : Fin 8 → ℝ) {s : ℝ}

/-- The system of `ex:projection_double_dimensional` is box-like with rotations: the maps `0`, `1`
are diagonal and `2`, `3` anti-diagonal. -/
theorem withRotations : (sys P t).WithRotations := ⟨⟨0, rfl⟩, ⟨2, rfl⟩⟩

/-- The diagonal generators of `ex:projection_double_dimensional` are proximal, since
`0 < b < a`. -/
theorem hasProximalDiagonal : (sys P t).HasProximalDiagonal := by
  refine ⟨0, rfl, ?_⟩
  change |P.a| ≠ |P.b|
  rw [abs_of_pos P.a_pos, abs_of_pos P.b_pos]
  exact P.b_lt_a.ne'

/-- The system of `ex:projection_double_dimensional` is proximal. -/
theorem proximal : (sys P t).Proximal := (hasProximalDiagonal P t).proximal

/-- The tuple of `ex:projection_double_dimensional` is irreducible, tex lines 2784 to 2785. -/
theorem irreducible : (sys P t).Irreducible :=
  System.irreducible_of_hasProximalDiagonal (withRotations P t) (hasProximalDiagonal P t)

/-- The potential `f_{1,s}` of `sec:gibbs_measures` for `0 < s ≤ 1` and `2 a^s + 2 b^s = 1`:
`f_{1,s}(j_0) = s log r_{c_0} = log(v_{c_0} / 2)`, the potential of `markov p`. -/
theorem potential₁_sys (hs1 : s ≤ 1) (hP : 2 * P.a ^ s + 2 * P.b ^ s = 1)
    (q : Fin 4 × ZMod 2) :
    (sys P t).potential₁ s q = Real.log (v (prob P s) q.2 / 2) := by
  have hpot : (sys P t).potential₁ s q = s * Real.log |(sys P t).ratio q| := by
    unfold System.potential₁
    split_ifs with h
    · rfl
    · obtain rfl : s = 1 := le_antisymm hs1 (not_lt.1 h)
      ring
  rw [hpot, ratio_sys, abs_of_pos (stateRatio_pos P _), v_prob P hP,
    mul_div_cancel_left₀ _ two_ne_zero, Real.log_rpow (stateRatio_pos P _)]

/-- The potential `f_{2,s}` of `sec:gibbs_measures`: `f_{2,s}(j_0) = log(v_{c_0 + 1} / 2)`, the
potential of the Markov measure with the vector `(1 - p, p)`. -/
theorem potential₂_sys (hs1 : s ≤ 1) (hP : 2 * P.a ^ s + 2 * P.b ^ s = 1)
    (q : Fin 4 × ZMod 2) :
    (sys P t).potential₂ s q = Real.log (v (1 - prob P s) q.2 / 2) := by
  rw [System.potential₂, potential₁_sys P t hs1 hP, v_add_one]

/-- The `s`-Gibbs measures of `ex:projection_double_dimensional`, tex lines 2861 to 2866: in
every decomposition of `thm:eq_state_is_sum`, `μ_1` is the Markov measure with the vector
`v = (p, 1 - p)` and `μ_2` the one with `(1 - p, p)`. -/
theorem GibbsDecomposition.eq_markov (hs1 : s ≤ 1) (hP : 2 * P.a ^ s + 2 * P.b ^ s = 1)
    {μ : Measure (ℤ → Fin 4)} {μ₁ μ₂ : Measure (ℤ → Fin 4 × ZMod 2)}
    (hdec : (sys P t).GibbsDecomposition s μ μ₁ μ₂) :
    μ₁ = markov (prob P s) ∧ μ₂ = markov (1 - prob P s) := by
  obtain ⟨h0, h1⟩ := prob_pos_lt_one P hP
  have := hdec.prob₁
  have := hdec.prob₂
  exact ⟨eq_markov_of_isGibbs h0 h1 (potential₁_sys P t hs1 hP) hdec.ergodic₁ hdec.supp₁
      hdec.gibbs₁,
    eq_markov_of_isGibbs (by linarith) (by linarith) (potential₂_sys P t hs1 hP) hdec.ergodic₂
      hdec.supp₂ hdec.gibbs₂⟩

/-- Averaging a function of the axis at time `0` with respect to the Markov measure with the
vector `(q, 1 - q)`: the axis has the distribution `(q, 1 - q)`, tex lines 2872 to 2874. -/
theorem integral_markov_state {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (g : ZMod 2 → ℝ) :
    ∫ y, g (y 0).2 ∂(markov q) = q * g 0 + (1 - q) * g 1 := by
  have := isProbabilityMeasure_rho hq0 hq1
  have hmeas : Measurable fun y : ℤ → Fin 4 × ZMod 2 => g (y 0).2 :=
    (Measurable.of_discrete (f := fun x : Fin 4 × ZMod 2 => g x.2)).comp (measurable_pi_apply 0)
  have hG : Measurable fun x : ZMod 2 × ZMod 2 => g x.1 := Measurable.of_discrete
  rw [markov, integral_map measurable_lift.aemeasurable hmeas.aestronglyMeasurable]
  change ∫ z, g (z 0).1 ∂(bernoulli (rho q)) = _
  have h2 := integral_map (μ := bernoulli (rho q)) (φ := fun z : ℤ → ZMod 2 × ZMod 2 => z 0)
    (measurable_pi_apply 0).aemeasurable (f := fun x : ZMod 2 × ZMod 2 => g x.1)
    hG.aestronglyMeasurable
  rw [← h2, bernoulli, Measure.infinitePi_map_eval, integral_fintype (Integrable.of_finite)]
  simp only [rho_real_singleton hq0 hq1, Fintype.sum_prod_type, sum_zmod_two, v_zero, v_one,
    smul_eq_mul]
  ring

/-- `λ_1` through `μ_1`, tex lines 2872 to 2876: the selected coordinate contracts by `a` in the
first state and by `b` in the second, so `∫ f_{1,1} d(markov q) = q log a + (1 - q) log b`. -/
theorem integral_potential₁_markov {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∫ y, (sys P t).potential₁ 1 (y 0) ∂(markov q) =
      q * Real.log P.a + (1 - q) * Real.log P.b := by
  have e : ∀ y : ℤ → Fin 4 × ZMod 2, (sys P t).potential₁ 1 (y 0) =
      Real.log (stateRatio P (y 0).2) := fun y => by
    simp only [System.potential₁, lt_irrefl, ite_false, sub_self, zero_mul, add_zero, ratio_sys,
      abs_of_pos (stateRatio_pos P _)]
  simp only [e]
  exact (integral_markov_state hq0 hq1 fun c => Real.log (stateRatio P c)).trans
    (by simp [stateRatio])

/-- `λ_2` through `μ_1`, tex lines 2872 to 2877: the other coordinate has the complementary
contraction, so `∫ f_{2,1} d(markov q) = q log b + (1 - q) log a`. -/
theorem integral_potential₂_markov {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∫ y, (sys P t).potential₂ 1 (y 0) ∂(markov q) =
      q * Real.log P.b + (1 - q) * Real.log P.a := by
  have e : ∀ y : ℤ → Fin 4 × ZMod 2, (sys P t).potential₂ 1 (y 0) =
      Real.log (stateRatio P ((y 0).2 + 1)) := fun y => by
    simp only [System.potential₂, System.potential₁, lt_irrefl, ite_false, sub_self, zero_mul,
      add_zero, ratio_sys, abs_of_pos (stateRatio_pos P _)]
  simp only [e]
  exact (integral_markov_state hq0 hq1 fun c => Real.log (stateRatio P (c + 1))).trans
    (by simp [stateRatio, show (1 : ZMod 2) + 1 = 0 from by decide])

/-- The Lyapunov exponent `\overline{λ}(𝖠, markov q) = ∫ log |g_{j_0}'| d(markov q)` of the
Markov measure with the vector `(q, 1 - q)` is `q log a + (1 - q) log b`. -/
theorem lyapBar_markov {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (sys P t).lyapBar (markov q) = q * Real.log P.a + (1 - q) * Real.log P.b := by
  have e : ∀ y : ℤ → Fin 4 × ZMod 2, Real.log |(sys P t).ratio (y 0)| =
      Real.log (stateRatio P (y 0).2) := fun y => by
    rw [ratio_sys, abs_of_pos (stateRatio_pos P _)]
  rw [System.lyapBar]
  simp only [e]
  exact (integral_markov_state hq0 hq1 fun c => Real.log (stateRatio P c)).trans
    (by simp [stateRatio])

/-- `h_0`, `λ_1` and `λ_2` of the `s`-equilibrium state of `ex:projection_double_dimensional`,
tex lines 2858 to 2878, for `0 < s ≤ 1` with `2 a^s + 2 b^s = 1` and `p = 2 a^s`. By
`EquilibriumGibbsStatement` and `FraserJordanJurgaDecomposition`, every invariant `s`-equilibrium
state `μ` has a decomposition of `thm:eq_state_is_sum`, whose Gibbs measures are
`μ_1 = markov p` and `μ_2 = markov (1 - p)` (`GibbsDecomposition.eq_markov`). Hence
`μ = q_*(markov p)`; by `thm:entropy_eq_gibbs`, `h_0(μ) = \overline{h}_0(μ_1) = log 2 + H(p)`,
also in the conditional form `S.dimEntropy μ 0`; and by `thm:eq_state_is_sum`, averaging over
`μ_1` with the weights `(p, 1 - p)`, `λ_1(𝖠, μ) = ∫ f_{1,1} dμ_1 = p log a + (1 - p) log b` and
`λ_2(𝖠, μ) = ∫ f_{2,1} dμ_1 = p log b + (1 - p) log a`. -/
theorem isEquilibriumState_spec (hfk : EquilibriumGibbsStatement.{0})
    (hfjj : FraserJordanJurgaDecomposition.{0}) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hP : 2 * P.a ^ s + 2 * P.b ^ s = 1) (μ : Measure (ℤ → Fin 4)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : (sys P t).IsEquilibriumState s μ) :
    μ = (markov (prob P s)).map unCode ∧
      entropy μ = Real.log 2 + H (prob P s) ∧
      (sys P t).dimEntropy μ 0 = Real.log 2 + H (prob P s) ∧
      (sys P t).lyapunov₁ μ =
        prob P s * Real.log P.a + (1 - prob P s) * Real.log P.b ∧
      (sys P t).lyapunov₂ μ =
        prob P s * Real.log P.b + (1 - prob P s) * Real.log P.a := by
  obtain ⟨h0, h1⟩ := prob_pos_lt_one P hP
  have hs2 : s < 2 := by linarith
  have hgibbs := hfk (sys P t) (withRotations P t) hs0 hs2 μ hinv heq
  obtain ⟨μ₁, μ₂, hdec⟩ := hfjj (sys P t) (withRotations P t) (hasProximalDiagonal P t) hs0 hs2 μ
    hinv hgibbs
  have := hdec.prob₁
  have := hdec.prob₂
  obtain ⟨e₁, -⟩ := GibbsDecomposition.eq_markov P t hs1 hP hdec
  have hent : entropy μ = Real.log 2 + H (prob P s) := by
    rw [← hdec.entropy_eq₁, e₁, entropy_markov h0 h1]
  refine ⟨?_, hent, ?_, ?_, ?_⟩
  · rw [← e₁]
    exact (map_unCode_of_decomposition hdec.supp₁ hdec.eq₁).symm
  · rw [(hdec.zero_entropy_identities).1, (hdec.zero_entropy_identities).2.2.1, hent]
  · rw [hdec.lyapunov₁_eq_integral, e₁, integral_potential₁_markov P t h0.le h1.le]
  · rw [hdec.lyapunov₂_eq_integral_potential₂, e₁, integral_potential₂_markov P t h0.le h1.le]

/-- The `s`-equilibrium state of `ex:projection_double_dimensional` exists and is unique, for
`0 < s ≤ 1` with `2 a^s + 2 b^s = 1`. Existence is `System.exists_isEquilibriumState`;
uniqueness follows from `isEquilibriumState_spec`, which identifies every invariant
`s`-equilibrium state with `q_*(markov p)`, without the uniqueness part of `thm:irred_eq_state`. -/
theorem existsUnique_isEquilibriumState (hfk : EquilibriumGibbsStatement.{0})
    (hfjj : FraserJordanJurgaDecomposition.{0}) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hP : 2 * P.a ^ s + 2 * P.b ^ s = 1) :
    ∃! μ : Measure (ℤ → Fin 4), IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
      (sys P t).IsEquilibriumState s μ := by
  obtain ⟨μ, hprob, hinv, heq⟩ := (sys P t).exists_isEquilibriumState hs0.le
  refine ⟨μ, ⟨hprob, hinv, heq⟩, fun μ' ⟨hprob', hinv', heq'⟩ => ?_⟩
  have h := (isEquilibriumState_spec P t hfk hfjj hs0 hs1 hP μ hinv heq).1
  have h' := (isEquilibriumState_spec P t hfk hfjj hs0 hs1 hP μ' hinv' heq').1
  rw [h, h']

end Example

end Gibbs

end PrescribedExample

end BoxLike
