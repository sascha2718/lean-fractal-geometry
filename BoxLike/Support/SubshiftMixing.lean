module

/-
Topological mixing of the sub-shift of finite type `Σ_Z` of `sec:subshift` (tex lines 817 and
899): "Since `Z²` is a positive matrix, `Σ_Z` is mixing". The article's standing hypothesis in
`sec:subshift` is that the tuple is box-like with rotations, so that both orientations occur;
proximality is not used. The alphabet `ι × ZMod 2` of `Σ_Z` and the transition rule `Trans` are
those of `BoxLike/Coding.lean`.

* `IsTopologicallyMixing`: a self-map `f` of a topological space is topologically mixing when for
  all non-empty open sets `U`, `V` the set `U ∩ f^{-n}(V)` is non-empty for every large `n`.
* `transMatrix`, `transMatrix_eq_one_iff`, `transMatrix_sq_pos`, `transMatrix_pow_pos`: the
  matrix `Z` itself, the positivity of `Z²` and of every power `Zⁿ`, `n ≥ 2`, when both
  orientations occur.
* `subshiftShift`, `coe_iterate_subshiftShift`, `continuous_subshiftShift`: the left shift `σ`
  acting on `Σ_Z` with the subspace topology.
* `glue_mem_subshift`: a point of `Σ_Z` up to time `b - 2`, one bridging symbol at time `b - 1`
  and another point of `Σ_Z` from time `b` on form a point of `Σ_Z`; this is where `Z² > 0`
  enters.
* `exists_forall_abs_le_mem`: every open subset of `Σ_Z` contains, with each of its points, all
  points of `Σ_Z` that agree with it on the coordinates `|k| ≤ M`, for some `M`.
* `isTopologicallyMixing_subshiftShift`: `Σ_Z` is topologically mixing when both orientations
  occur.
* `not_isTopologicallyMixing_of_forall_eq_zero`, `not_isTopologicallyMixing_of_forall_eq_one`,
  `isTopologicallyMixing_subshiftShift_iff`: over a non-empty alphabet the hypothesis is
  necessary. With diagonal generators only, `Σ_Z` splits into two closed invariant halves; with
  anti-diagonal generators only, the axis alternates and `Σ_Z` has period two.
-/
public import BoxLike.Coding
public import BoxLike.Entropy
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.ZMod

@[expose] public section

namespace BoxLike

open Set

/-! ### Topological mixing -/

/-- An element of `ZMod 2` other than `0` is `1`. -/
theorem zmodTwo_eq_one_of_ne_zero {c : ZMod 2} (h : c ≠ 0) : c = 1 := by
  revert c; decide

/-- An element of `ZMod 2` other than `1` is `0`. -/
theorem zmodTwo_eq_zero_of_ne_one {c : ZMod 2} (h : c ≠ 1) : c = 0 := by
  revert c; decide

/-- A self-map `f` of a topological space is topologically mixing: for all non-empty open sets
`U` and `V` there is `N` with `U ∩ f^{-n}(V) ≠ ∅` for every `n ≥ N`. This is the notion of the
sentence "`Σ_Z` is mixing" of `sec:subshift` (tex lines 817 and 818), the hypothesis of the
theorem of Bowen cited in `sec:gibbs_measures`. -/
def IsTopologicallyMixing {X : Type*} [TopologicalSpace X] (f : X → X) : Prop :=
  ∀ U V : Set X, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
    ∃ N : ℕ, ∀ n, N ≤ n → (U ∩ f^[n] ⁻¹' V).Nonempty

/-! ### The transition matrix `Z` and its powers -/

section Matrix

variable {ι : Type*} (o : ι → ZMod 2)

/-- The transition matrix `Z` of `sec:subshift` over the alphabet `ι × ZMod 2`:
`Z((i, c), (j, c')) = 1` exactly when `(i, c)` may be followed by `(j, c')`, that is
`c' = c + o(i)`; see `trans_iff` for the case distinction of the article. -/
def transMatrix : Matrix (ι × ZMod 2) (ι × ZMod 2) ℕ :=
  fun p q => if q.2 = p.2 + o p.1 then 1 else 0

/-- The entry `Z(p, q)` is `1` exactly when `p` may be followed by `q`. -/
theorem transMatrix_eq_one_iff (p q : ι × ZMod 2) : transMatrix o p q = 1 ↔ Trans o p q := by
  unfold transMatrix Trans
  split_ifs with h <;> simp [h]

/-- The entry `Z(p, q)` vanishes exactly when `p` may not be followed by `q`. -/
theorem transMatrix_eq_zero_iff (p q : ι × ZMod 2) : transMatrix o p q = 0 ↔ ¬ Trans o p q := by
  unfold transMatrix Trans
  split_ifs with h <;> simp [h]

variable [Fintype ι] [DecidableEq ι]

/-- Every row of `Zⁿ` has a positive entry: every symbol has a successor. -/
theorem exists_transMatrix_pow_pos [Nonempty ι] (n : ℕ) (p : ι × ZMod 2) :
    ∃ q, 0 < (transMatrix o ^ n) p q := by
  induction n generalizing p with
  | zero => exact ⟨p, by simp⟩
  | succ n ih =>
    obtain ⟨j⟩ := ‹Nonempty ι›
    obtain ⟨q, hq⟩ := ih (j, p.2 + o p.1)
    refine ⟨q, ?_⟩
    rw [pow_succ', Matrix.mul_apply]
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun r _ => Nat.zero_le _)
      (Finset.mem_univ (j, p.2 + o p.1)))
    have h1 : transMatrix o p (j, p.2 + o p.1) = 1 := (transMatrix_eq_one_iff o _ _).2 rfl
    rw [h1, one_mul]
    exact hq

/-- `Z²` is a positive matrix when both orientations occur (tex line 817). -/
theorem transMatrix_sq_pos (h0 : ∃ i, o i = 0) (h1 : ∃ i, o i = 1) (p q : ι × ZMod 2) :
    0 < (transMatrix o ^ 2) p q := by
  obtain ⟨r, hpr, hrq⟩ := exists_trans_trans o h0 h1 p q
  rw [sq, Matrix.mul_apply]
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun r _ => Nat.zero_le _)
    (Finset.mem_univ r))
  rw [(transMatrix_eq_one_iff o _ _).2 hpr, (transMatrix_eq_one_iff o _ _).2 hrq]
  exact one_pos

/-- Every power `Zⁿ` with `n ≥ 2` is a positive matrix when both orientations occur: `Z` is
primitive. -/
theorem transMatrix_pow_pos (h0 : ∃ i, o i = 0) (h1 : ∃ i, o i = 1) {n : ℕ} (hn : 2 ≤ n)
    (p q : ι × ZMod 2) : 0 < (transMatrix o ^ n) p q := by
  have : Nonempty ι := ⟨h0.choose⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨r, hr⟩ := exists_transMatrix_pow_pos o m p
  rw [add_comm, pow_add, Matrix.mul_apply]
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun r _ => Nat.zero_le _)
    (Finset.mem_univ r))
  exact Nat.mul_pos hr (transMatrix_sq_pos o h0 h1 r q)

end Matrix

/-! ### The shift on `Σ_Z` -/

section Shift

variable {ι : Type*} (o : ι → ZMod 2)

/-- The left shift `σ` acting on `Σ_Z` (tex line 817). -/
def subshiftShift (y : subshift o) : subshift o :=
  ⟨shift 1 y.1, shift_mem_subshift o y.2 1⟩

/-- The iterate `σⁿ` of the shift on `Σ_Z` is `shift n`. -/
@[simp] theorem coe_iterate_subshiftShift (n : ℕ) (y : subshift o) :
    ((subshiftShift o)^[n] y : ℤ → ι × ZMod 2) = shift n y.1 := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [subshiftShift, shift_shift, Nat.cast_succ]
    rw [add_comm]

variable [TopologicalSpace ι]

/-- The shift of `Σ_Z` is continuous for the restriction of the product topology. -/
theorem continuous_subshiftShift : Continuous (subshiftShift o) := by
  refine continuous_induced_rng.2 ?_
  change Continuous fun y : subshift o => shift 1 (y : ℤ → ι × ZMod 2)
  exact continuous_pi fun k => (continuous_apply (1 + k)).comp continuous_subtype_val

end Shift

/-! ### Gluing two points of `Σ_Z` -/

section Glue

variable {ι : Type*} {o : ι → ZMod 2}

open Classical in
/-- The point that follows `y` up to time `b - 2`, the symbol `r` at time `b - 1`, and `y'` from
time `b` on. -/
noncomputable def glue (y y' : ℤ → ι × ZMod 2) (b : ℤ) (r : ι × ZMod 2) : ℤ → ι × ZMod 2 :=
  fun k => if k ≤ b - 2 then y k else if k = b - 1 then r else y' k

/-- The glued point follows `y` up to time `b - 2`. -/
theorem glue_of_le {y y' : ℤ → ι × ZMod 2} {b k : ℤ} {r : ι × ZMod 2} (hk : k ≤ b - 2) :
    glue y y' b r k = y k := by
  simp [glue, hk]

/-- The glued point follows `y'` from time `b` on. -/
theorem glue_of_ge {y y' : ℤ → ι × ZMod 2} {b k : ℤ} {r : ι × ZMod 2} (hk : b ≤ k) :
    glue y y' b r k = y' k := by
  have h1 : ¬ k ≤ b - 2 := by omega
  have h2 : k ≠ b - 1 := by omega
  simp [glue, h1, h2]

/-- The glued point has the bridging symbol at time `b - 1`. -/
theorem glue_sub_one {y y' : ℤ → ι × ZMod 2} {b : ℤ} {r : ι × ZMod 2} :
    glue y y' b r (b - 1) = r := by
  have h1 : ¬ b - 1 ≤ b - 2 := by omega
  simp [glue, h1]

/-- Gluing two points of `Σ_Z` through a bridging symbol `r` with `Z(y_{b-2}, r) = 1` and
`Z(r, y'_b) = 1` gives a point of `Σ_Z`. -/
theorem glue_mem_subshift {y y' : ℤ → ι × ZMod 2} (hy : y ∈ subshift o) (hy' : y' ∈ subshift o)
    {b : ℤ} {r : ι × ZMod 2} (h1 : Trans o (y (b - 2)) r) (h2 : Trans o r (y' b)) :
    glue y y' b r ∈ subshift o := by
  intro k
  rcases lt_trichotomy k (b - 2) with hk | hk | hk
  · rw [glue_of_le hk.le, glue_of_le (by omega)]
    exact hy k
  · subst hk
    rw [glue_of_le le_rfl, show b - 2 + 1 = b - 1 by ring, glue_sub_one]
    exact h1
  · rcases eq_or_lt_of_le (show b - 1 ≤ k by omega) with hk' | hk'
    · subst hk'
      rw [glue_sub_one, show b - 1 + 1 = b by ring, glue_of_ge le_rfl]
      exact h2
    · rw [glue_of_ge (by omega), glue_of_ge (by omega)]
      exact hy' k

end Glue

/-! ### Open sets of `Σ_Z` contain symmetric cylinders -/

section Cylinders

variable {ι : Type*} [TopologicalSpace ι] {o : ι → ZMod 2}

/-- Every open subset `U` of `Σ_Z` contains, with each of its points `y`, every point of `Σ_Z`
that agrees with `y` on the coordinates `|k| ≤ M`, for some `M`: the cylinders form a basis of
the topology (tex lines 719 to 721 and 896 to 898). -/
theorem exists_forall_abs_le_mem {U : Set (subshift o)} (hU : IsOpen U) {y : subshift o}
    (hy : y ∈ U) : ∃ M : ℕ, ∀ z : subshift o,
      (∀ k : ℤ, |k| ≤ M → (z : ℤ → ι × ZMod 2) k = (y : ℤ → ι × ZMod 2) k) → z ∈ U := by
  obtain ⟨U', hU', rfl⟩ := isOpen_induced_iff.1 hU
  obtain ⟨I, u, hu, hIU⟩ := isOpen_pi_iff.1 hU' y.1 hy
  refine ⟨I.sup Int.natAbs, fun z hz => hIU fun k hk => ?_⟩
  have hk' : |k| ≤ (I.sup Int.natAbs : ℕ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast Finset.le_sup (f := Int.natAbs) hk
  rw [hz k hk']
  exact (hu k hk).2

end Cylinders

/-! ### Topological mixing of `Σ_Z` -/

section Mixing

variable {ι : Type*} [TopologicalSpace ι] (o : ι → ZMod 2)

/-- `Σ_Z` is topologically mixing when both orientations occur, that is, when the tuple is
box-like with rotations (tex lines 817 and 818): `Z² > 0` supplies the bridge between any two
admissible blocks at every distance at least two. For open sets determined by the coordinates
`|k| ≤ L`, every `n ≥ 2L + 2` works. -/
theorem isTopologicallyMixing_subshiftShift (h0 : ∃ i, o i = 0) (h1 : ∃ i, o i = 1) :
    IsTopologicallyMixing (subshiftShift o) := by
  intro U V hU ⟨y, hyU⟩ hV ⟨y', hyV⟩
  obtain ⟨M, hM⟩ := exists_forall_abs_le_mem hU hyU
  obtain ⟨M', hM'⟩ := exists_forall_abs_le_mem hV hyV
  set L : ℕ := max M M'
  refine ⟨2 * L + 2, fun n hn => ?_⟩
  set y'' : ℤ → ι × ZMod 2 := shift (-(n : ℤ)) y'.1
  have hy'' : y'' ∈ subshift o := shift_mem_subshift o y'.2 _
  set b : ℤ := n - L
  obtain ⟨r, hr1, hr2⟩ := exists_trans_trans o h0 h1 (y.1 (b - 2)) (y'' b)
  set z : subshift o := ⟨glue y.1 y'' b r, glue_mem_subshift y.2 hy'' hr1 hr2⟩
  have hLM : (M : ℤ) ≤ L := by exact_mod_cast le_max_left M M'
  have hLM' : (M' : ℤ) ≤ L := by exact_mod_cast le_max_right M M'
  have hnL : (2 * L + 2 : ℤ) ≤ n := by exact_mod_cast hn
  refine ⟨z, hM z fun k hk => ?_, ?_⟩
  · have hk' := abs_le.1 hk
    exact glue_of_le (by omega)
  · rw [mem_preimage]
    refine hM' _ fun k hk => ?_
    have hk' := abs_le.1 hk
    rw [coe_iterate_subshiftShift, shift_apply]
    change glue y.1 y'' b r (n + k) = y'.1 k
    rw [glue_of_ge (by omega)]
    simp [y'']

/-- The axis component of the symbols of a point of `Σ_Z` is continuous. -/
theorem continuous_snd_apply_subshift (k : ℤ) :
    Continuous fun y : subshift o => ((y : ℤ → ι × ZMod 2) k).2 :=
  continuous_snd.comp ((continuous_apply k).comp continuous_subtype_val)

/-- With diagonal generators only, `Σ_Z` is not topologically mixing over a non-empty
alphabet: the axis is constant along every point, so the clopen sets of the points following
the first and the second axis at time `0` are invariant and disjoint. -/
theorem not_isTopologicallyMixing_of_forall_eq_zero [Nonempty ι] (h : ∀ i, o i = 0) :
    ¬ IsTopologicallyMixing (subshiftShift o) := by
  intro hmix
  obtain ⟨i⟩ := ‹Nonempty ι›
  set U : Set (subshift o) := {y | ((y : ℤ → ι × ZMod 2) 0).2 = 0}
  set V : Set (subshift o) := {y | ((y : ℤ → ι × ZMod 2) 0).2 = 1}
  have hU : IsOpen U := (isOpen_discrete {(0 : ZMod 2)}).preimage
    (continuous_snd_apply_subshift o 0)
  have hV : IsOpen V := (isOpen_discrete {(1 : ZMod 2)}).preimage
    (continuous_snd_apply_subshift o 0)
  have hUne : U.Nonempty := ⟨⟨tau o fun _ => i, tau_mem_subshift _⟩, by simp [U]⟩
  have hVne : V.Nonempty := ⟨⟨omega o fun _ => i, omega_mem_subshift _⟩, by simp [V]⟩
  obtain ⟨N, hN⟩ := hmix U V hU hUne hV hVne
  obtain ⟨z, hzU, hzV⟩ := hN N le_rfl
  have hconst : ∀ k : ℕ, ((z : ℤ → ι × ZMod 2) k).2 = ((z : ℤ → ι × ZMod 2) 0).2 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      have := z.2 (k : ℤ)
      rw [Nat.cast_succ, this, ih, h, add_zero]
  have h1 : ((z : ℤ → ι × ZMod 2) N).2 = 1 := by
    have := hzV
    simp only [V, mem_preimage, mem_ofPred_eq, coe_iterate_subshiftShift, shift_apply,
      add_zero] at this
    exact this
  rw [hconst N, show ((z : ℤ → ι × ZMod 2) 0).2 = 0 from hzU] at h1
  exact absurd h1 (by decide)

/-- With anti-diagonal generators only, `Σ_Z` is not topologically mixing over a non-empty
alphabet: the axis alternates, so no point of the set of points following the first axis at
time `0` returns to it after an odd number of steps. -/
theorem not_isTopologicallyMixing_of_forall_eq_one [Nonempty ι] (h : ∀ i, o i = 1) :
    ¬ IsTopologicallyMixing (subshiftShift o) := by
  intro hmix
  obtain ⟨i⟩ := ‹Nonempty ι›
  set U : Set (subshift o) := {y | ((y : ℤ → ι × ZMod 2) 0).2 = 0}
  have hU : IsOpen U := (isOpen_discrete {(0 : ZMod 2)}).preimage
    (continuous_snd_apply_subshift o 0)
  have hUne : U.Nonempty := ⟨⟨tau o fun _ => i, tau_mem_subshift _⟩, by simp [U]⟩
  obtain ⟨N, hN⟩ := hmix U U hU hUne hU hUne
  obtain ⟨z, hzU, hzV⟩ := hN (2 * N + 1) (by omega)
  have halt : ∀ k : ℕ, ((z : ℤ → ι × ZMod 2) k).2 = ((z : ℤ → ι × ZMod 2) 0).2 + k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := z.2 (k : ℤ)
      rw [Nat.cast_succ, this, ih, h, Nat.cast_succ, add_assoc]
  have h1 : ((z : ℤ → ι × ZMod 2) ((2 * N + 1 : ℕ) : ℤ)).2 = 0 := by
    have := hzV
    simp only [U, mem_preimage, mem_ofPred_eq, coe_iterate_subshiftShift, shift_apply,
      add_zero] at this
    exact this
  rw [halt, show ((z : ℤ → ι × ZMod 2) 0).2 = 0 from hzU, zero_add] at h1
  have h2 : ((2 * N + 1 : ℕ) : ZMod 2) = 1 := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_two,
      show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
  rw [h2] at h1
  exact absurd h1 (by decide)

/-- Over a non-empty alphabet, `Σ_Z` is topologically mixing exactly when both orientations
occur: the hypothesis "box-like with rotations" of `sec:subshift` is necessary for the mixing
claim of tex lines 817 and 818. -/
theorem isTopologicallyMixing_subshiftShift_iff [Nonempty ι] :
    IsTopologicallyMixing (subshiftShift o) ↔ (∃ i, o i = 0) ∧ ∃ i, o i = 1 := by
  refine ⟨fun hmix => ⟨?_, ?_⟩, fun h => isTopologicallyMixing_subshiftShift o h.1 h.2⟩
  · by_contra hne
    push Not at hne
    exact not_isTopologicallyMixing_of_forall_eq_one o
      (fun i => zmodTwo_eq_one_of_ne_zero (hne i)) hmix
  · by_contra hne
    push Not at hne
    exact not_isTopologicallyMixing_of_forall_eq_zero o
      (fun i => zmodTwo_eq_zero_of_ne_one (hne i)) hmix

end Mixing

end BoxLike
