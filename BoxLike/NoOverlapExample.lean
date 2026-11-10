module

/-
`prop:ssc_no_overlap_not_pesc` of `sec:exponential_separation` and the paragraph after its
proof (tex lines 1340 to 1460): a system `Φ = (φ_1, φ_2, φ_3, φ_4)` with three diagonal maps
and one anti-diagonal map that is proximal and irreducible but not strongly irreducible,
satisfies the strong separation condition, whose projective system generates a free semigroup,
and that fails the projective exponential separation condition. The algebraic part of the proof
is in `BoxLike.NoOverlapExampleFree`; strong irreducibility is `TupleStronglyIrreducible` of
`BoxLike.Classification`.

General statements, in the namespace `BoxLike.System`:

* `System.FreeProjective`, `System.gWord_eq_iff`: the maps of `Ψ` generate a free semigroup.
* `System.mulVec_mem_axes`: every `A_i` maps the union of the coordinate axes into itself.
* `System.RatioLowerBound.le_dist_phi`, `System.RatioLowerBound.le_dist_phiWord`,
  `System.StrongSeparation.exists_le_dist`, `System.minSingular`,
  `System.StrongSeparation.exists_le_dist_phiWord`: under strong separation distinct words of
  length `n` satisfy `dist(φ_𝐢(X), φ_𝐣(X)) ≥ δ r^{n-1}` (tex lines 1453 to 1459).

The example, in the namespace `BoxLike.NoOverlap`:

* `homGap`, `homGap_zero`: the minimal gap `Δ_n^{λ,t}` of the homogeneous system.
* `BaranyKaenmakiPair`, `BaranyKaenmakiTheorem`: the theorem of Bárány and Käenmäki, in the
  form the article uses and in the form of the source. The library proves the first
  (`baranyKaenmakiPair_holds` in `BoxLike/BaranyKaenmaki.lean`); the second is false
  (`not_baranyKaenmakiTheorem` in `BoxLike/BaranyKaenmakiCounterexample.lean`), and no result
  takes it.
* `paramLo`, `paramHi`, `Params`, `Params.sys`, `Params.sys_phi_zero` to
  `Params.sys_phi_three`: the intervals of the parameters, the parameters and the system.
* `Params.withRotations`, `Params.hasProximalDiagonal`, `Params.proximal`,
  `Params.irreducible`, `Params.sys_ratio_mem`: the standing hypotheses.
* `Params.rect`, `Params.phi_mem_rect`, `Params.snd_phi_mem_band`, `Params.strongSeparation`,
  `Params.fst_phi_overlap`: strong separation on `R = [0,4] × [0,1]` through four `y`-bands.
* `Params.gWord_firstAxis_conj`, `Params.diagGap_eq_homGap`, `Params.not_projExpSeparation`:
  `Δ_n^{diag} = Δ_n^{λ,t}`, and the failure of projective exponential separation.
* `Params.sys_gDeriv`, `Params.sys_gWord_zero`, `Params.freeProjective`: freeness.
* `exists_params`: parameters in the box of tex lines 1355 to 1363, algebraically independent
  over `ℚ(λ, t)`.
* `exists_system_of_homFree`, `ssc_no_overlap_not_pesc`: the proposition, from the properties
  of `(λ, t)` that the proof uses and from `BaranyKaenmakiPair`.
* `planar_separation_not_pesc`: the paragraph after the proof.
-/
public import BoxLike.Classification
public import BoxLike.NoOverlapExampleFree
public import BoxLike.Pressure
public import BoxLike.Proximal
public import BoxLike.SeparationConditions
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace BoxLike

open Metric Matrix Filter
open scoped ENNReal

namespace System

variable {ι : Type*} (S : System ι)

/-! ### Free semigroups -/

/-- The maps of the projective system `Ψ` generate a free semigroup, as in
`prop:ssc_no_overlap_not_pesc`: distinct finite words over the alphabet `ι × ZMod 2` give
distinct maps `g_𝐣`. All words are meant, not only the admissible words of `Σ_Z`: the proof
takes `𝐢 ≠ 𝐣 ∈ {1, …, 8}^*` (tex line 1411). The empty word is included; this changes nothing,
since `g_𝐣` is a strict contraction for every non-empty word. -/
def FreeProjective : Prop := Function.Injective S.gWord

/-- Two compositions `g_𝐢`, `g_𝐣` agree exactly when their derivatives and their values at `0`
agree. -/
theorem gWord_eq_iff (u u' : List (ι × ZMod 2)) :
    S.gWord u = S.gWord u' ↔ S.gDeriv u = S.gDeriv u' ∧ S.gWord u 0 = S.gWord u' 0 := by
  constructor
  · intro h
    have h0 : S.gWord u 0 = S.gWord u' 0 := by rw [h]
    have h1 : S.gWord u 1 = S.gWord u' 1 := by rw [h]
    rw [S.gWord_apply u 1, S.gWord_apply u' 1, h0] at h1
    exact ⟨by linarith, h0⟩
  · rintro ⟨hd, h0⟩
    funext x
    rw [S.gWord_apply u, S.gWord_apply u', hd, h0]

/-! ### The coordinate axes -/

/-- The union of the coordinate axes is invariant under every `A_i`, so that the set
`{span{e_1}, span{e_2}}` is invariant and the tuple is not strongly irreducible (tex lines
1463 to 1464 and 394 to 396); the last statement is `System.not_tupleStronglyIrreducible`.
This holds for every box-like system. -/
theorem mulVec_mem_axes (i : ι) {v : Fin 2 → ℝ} (hv : v 0 = 0 ∨ v 1 = 0) :
    (S.mat i *ᵥ v) 0 = 0 ∨ (S.mat i *ᵥ v) 1 = 0 := by
  rcases zmod_two_cases (S.o i) with h | h <;> rcases hv with h0 | h1 <;>
    simp [mat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, *]

/-! ### Exponential separation of the planar maps under strong separation -/

variable {S} in
/-- If every `|a_i|` and `|b_i|` is at least `ρ`, then every `φ_i` expands distances by at least
`ρ`. -/
theorem RatioLowerBound.le_dist_phi {ρ : ℝ} (hρ : S.RatioLowerBound ρ) (i : ι) (z w : ℝ × ℝ) :
    ρ * dist z w ≤ dist (S.phi i z) (S.phi i w) :=
  (mul_le_mul_of_nonneg_right (le_min (hρ.2 (i, 0)) (hρ.2 (i, 1))) dist_nonneg).trans
    (S.le_dist_phi i z w)

/-- `φ_𝐢(X) ⊆ X` for every finite word `𝐢`. -/
theorem phiWord_mem_attractor [Finite ι] (w : List ι) {x : ℝ × ℝ} (hx : x ∈ S.attractor) :
    S.phiWord w x ∈ S.attractor := by
  induction w with
  | nil => exact hx
  | cons i w ih => exact S.image_attractor_subset i ⟨_, ih, rfl⟩

variable {S} in
/-- The common-prefix argument of tex lines 1453 to 1459. Let `δ` be a lower bound for the
distances between the first-level pieces `φ_i(X)` and let every `|a_i|`, `|b_i|` be at least
`ρ`. Then distinct words `𝐢, 𝐣` of length `n` satisfy
`dist(φ_𝐢(x), φ_𝐣(y)) ≥ δ ρ^{n-1}` for all `x, y ∈ X`: the common prefix has length at most
`n - 1`, and the first letters that differ contribute `δ`. With `x = y` this is the exponential
lower bound for the distance of the maps `φ_𝐢`, `φ_𝐣` evaluated at a point of `X`. -/
theorem RatioLowerBound.le_dist_phiWord [Finite ι] {δ ρ : ℝ} (hρ : S.RatioLowerBound ρ)
    (hδ : 0 ≤ δ)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ S.attractor, ∀ y ∈ S.attractor,
      δ ≤ dist (S.phi i x) (S.phi j y))
    (w w' : List ι) (hlen : w.length = w'.length) (hne : w ≠ w') {x y : ℝ × ℝ}
    (hx : x ∈ S.attractor) (hy : y ∈ S.attractor) :
    δ * ρ ^ (w.length - 1) ≤ dist (S.phiWord w x) (S.phiWord w' y) := by
  induction w generalizing w' with
  | nil =>
    cases w' with
    | nil => exact absurd rfl hne
    | cons j v' => simp at hlen
  | cons i v ih =>
    cases w' with
    | nil => simp at hlen
    | cons j v' =>
      have hlen' : v.length = v'.length := by simpa using hlen
      have hρ1 : ρ ≤ 1 := (hρ.2 (i, 0)).trans (S.abs_ratio_lt_one _).le
      simp only [phiWord_cons, Function.comp_apply, List.length_cons, Nat.add_sub_cancel]
      by_cases hij : i = j
      · subst hij
        have hne' : v ≠ v' := fun h => hne (by rw [h])
        have hv : v.length ≠ 0 := by
          intro h0
          have h1 : v = [] := List.length_eq_zero_iff.1 h0
          have h2 : v' = [] := List.length_eq_zero_iff.1 (hlen' ▸ h0)
          exact hne' (h1.trans h2.symm)
        have h := ih v' hlen' hne'
        calc δ * ρ ^ v.length = ρ * (δ * ρ ^ (v.length - 1)) := by
              rw [← pow_sub_one_mul hv]; ring
          _ ≤ ρ * dist (S.phiWord v x) (S.phiWord v' y) :=
              mul_le_mul_of_nonneg_left h hρ.1.le
          _ ≤ _ := hρ.le_dist_phi i _ _
      · refine le_trans ?_ (hsep i j hij _ (S.phiWord_mem_attractor v hx) _
          (S.phiWord_mem_attractor v' hy))
        exact mul_le_of_le_one_right hδ (pow_le_one₀ hρ.1.le hρ1)

/-- Under the strong separation condition the first-level pieces are at positive mutual
distance: `δ = min_{i ≠ j} dist(φ_i(X), φ_j(X)) > 0` (tex line 1454). -/
theorem StrongSeparation.exists_le_dist [Finite ι] (h : S.StrongSeparation) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i j, i ≠ j → ∀ x ∈ S.attractor, ∀ y ∈ S.attractor,
      δ ≤ dist (S.phi i x) (S.phi j y) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => (hι.false i).elim⟩
  have hc : ∀ i, IsCompact (S.phi i '' S.attractor) := fun i =>
    S.isCompact_attractor.image (S.continuous_phi i)
  have hδ : ∀ p : ι × ι, ∃ δ : ℝ, 0 < δ ∧ (p.1 ≠ p.2 →
      Disjoint (thickening δ (S.phi p.1 '' S.attractor))
        (thickening δ (S.phi p.2 '' S.attractor))) := by
    intro p
    by_cases hp : p.1 = p.2
    · exact ⟨1, one_pos, fun hne => (hne hp).elim⟩
    · obtain ⟨δ, hδ, hd⟩ := (h hp).exists_thickenings (hc p.1) (hc p.2).isClosed
      exact ⟨δ, hδ, fun _ => hd⟩
  choose δ hδpos hδdisj using hδ
  obtain ⟨p₀, hp₀⟩ := Finite.exists_min δ
  refine ⟨δ p₀, hδpos p₀, fun i j hij x hx y hy => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have h1 : S.phi j y ∈ thickening (δ (i, j)) (S.phi i '' S.attractor) :=
    mem_thickening_iff.2 ⟨S.phi i x, ⟨x, hx, rfl⟩, by
      rw [dist_comm]; exact hlt.trans_le (hp₀ (i, j))⟩
  have h2 : S.phi j y ∈ thickening (δ (i, j)) (S.phi j '' S.attractor) :=
    self_subset_thickening (hδpos _) _ ⟨y, hy, rfl⟩
  exact Set.disjoint_left.1 (hδdisj (i, j) hij) h1 h2

/-- The number `r = min_i α_2(A_i)` of tex line 1455; the smaller singular value of `A_i` is
`α_2(A_i) = min{|a_i|, |b_i|}`. -/
noncomputable def minSingular [Fintype ι] [Nonempty ι] : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i => min |S.a i| |S.b i|

/-- `r = min_i α_2(A_i)` is positive and bounds every `|a_i|` and `|b_i|` from below. -/
theorem ratioLowerBound_minSingular [Fintype ι] [Nonempty ι] :
    S.RatioLowerBound S.minSingular := by
  refine ⟨?_, fun p => ?_⟩
  · rw [minSingular, Finset.lt_inf'_iff]
    intro i _
    exact lt_min (abs_pos.2 (S.a_ne_zero i)) (abs_pos.2 (S.b_ne_zero i))
  · have h := Finset.inf'_le (fun i => min |S.a i| |S.b i|) (Finset.mem_univ p.1)
    unfold ratio
    split_ifs
    · exact h.trans (min_le_left _ _)
    · exact h.trans (min_le_right _ _)

/-- The exponential lower bound of tex lines 1453 to 1459: under the strong separation
condition there is `δ > 0` such that distinct words `𝐢, 𝐣` of length `n` satisfy
`dist(φ_𝐢(X), φ_𝐣(X)) ≥ δ r^{n-1}` with `r = min_i α_2(A_i)`. The distance of the two sets is
written through their points. -/
theorem StrongSeparation.exists_le_dist_phiWord [Fintype ι] [Nonempty ι]
    (h : S.StrongSeparation) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w w' : List ι, w.length = w'.length → w ≠ w' →
      ∀ x ∈ S.attractor, ∀ y ∈ S.attractor,
        δ * S.minSingular ^ (w.length - 1) ≤ dist (S.phiWord w x) (S.phiWord w' y) := by
  obtain ⟨δ, hδ, hsep⟩ := h.exists_le_dist
  exact ⟨δ, hδ, fun w w' hlen hne x hx y hy =>
    S.ratioLowerBound_minSingular.le_dist_phiWord hδ.le hsep w w' hlen hne hx hy⟩

end System

namespace NoOverlap

open BoxLike.System

/-! ### The theorem of Bárány and Käenmäki -/

/-- The minimal gap `Δ_n^{λ,t}` of level `n` of the homogeneous system `(λx, λx + t, λx + 1)`:
the least `|h_𝐢(0) - h_𝐣(0)|` over distinct words `𝐢, 𝐣` of length `n`. The minimum of the
empty set is `⊤`. -/
noncomputable def homGap (lam t : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ⨅ (w : List (Fin 3)) (w' : List (Fin 3)) (_ : w.length = n) (_ : w'.length = n) (_ : w ≠ w'),
    ENNReal.ofReal |homWord lam t w 0 - homWord lam t w' 0|

/-- There is one word of length `0`, so `Δ_0^{λ,t} = ⊤`. An upper bound for `Δ_n^{λ,t}` can
only be required for `n ≥ 1`. -/
theorem homGap_zero (lam t : ℝ) : homGap lam t 0 = ⊤ := by
  simp only [homGap, iInf_eq_top]
  intro w w' hw hw' hne
  exact absurd ((List.length_eq_zero_iff.1 hw).trans (List.length_eq_zero_iff.1 hw').symm) hne

/-- A stronger form of the theorem of Bárány and Käenmäki, retained in the library; the proof of
`prop:ssc_no_overlap_not_pesc` (tex lines 1349 to 1354) uses Theorem 2.1 as the source states it,
`BaranyKaenmakiTheorem`. The form: there are `0 < λ < 1/3` transcendental,
`0 < t < λ/(1-λ)` and `C_0 > 0` such that the homogeneous system `(λx, λx + t, λx + 1)`
generates a free semigroup and `Δ_n^{λ,t} ≤ C_0 exp(-n²)` for every `n ≥ 1`.

Source: B. Bárány and A. Käenmäki, Super-exponential condensation without exact overlaps,
Adv. Math. 379 (2021), Theorem 2.1 and the construction in the proofs of Lemma 3.8 and
Theorem 2.1, read in arXiv:1910.04623v4. For `η` as in Theorem 2.1 the proof of Theorem 2.1
constructs the set `Υ` of pairs `(λ^*(ω), t^*(ω))`, `ω ∈ {0,1}^ℕ`, outside the exact
overlapping set with `Δ_n^{λ,t} < (3/2) δ⁻¹ C η_n` for all `n ≥ 1`, where `δ` is the constant
of Lemma 3.6 and `C` that of (3.12); `λ^*` maps `{0,1}^ℕ` onto the uncountable Cantor set
`F ⊆ (1/4, 1/3)` built from the intervals of Lemma 3.8, and `F` contains transcendental
numbers. The statement of Theorem 2.1 alone gives uncountably many pairs, not uncountably many
`λ`. The transcendence of `λ` is not used in the proof of the proposition, see
`exists_system_of_homFree`. The library proves this statement (`baranyKaenmakiPair_holds` in
`BoxLike/BaranyKaenmaki.lean`), by a Baire category argument at the base crossing of Lemma 3.8
of the source; `ssc_no_overlap_not_pesc` takes it as a hypothesis. -/
def BaranyKaenmakiPair : Prop :=
  ∃ lam t C₀ : ℝ, 0 < lam ∧ lam < 1 / 3 ∧ 0 < t ∧ t < lam / (1 - lam) ∧ Transcendental ℚ lam ∧
    0 < C₀ ∧ HomFree lam t ∧
    ∀ n : ℕ, 1 ≤ n → homGap lam t n ≤ ENNReal.ofReal (C₀ * Real.exp (-(n : ℝ) ^ 2))

/-- Theorem 2.1 of Bárány and Käenmäki (arXiv:1910.04623v4) as the source states it: if
`(η_n)` is a monotone decreasing sequence of positive numbers with `n⁻¹ log η_n → -∞`, then the
set `𝒞_η ∖ ℰ` is uncountable. Here `𝒞_η` is the set of pairs `(λ, t)` with `0 < λ < 1/3`,
`0 < t < λ/(1-λ)` and `Δ_n^{λ,t} < η_n` for all `n ≥ 1`, and `ℰ` is the set of pairs for which
`h_𝐢 = h_𝐣` for some finite words `𝐢 ≠ 𝐣`. The source indexes `η` by `n ≥ 1`; a sequence
indexed by `ℕ` restricts to such a sequence, so this statement follows from the source. The
statement is false: `not_baranyKaenmakiTheorem` in `BoxLike/BaranyKaenmakiCounterexample.lean`
exhibits an admissible `η` for which `𝒞_η ∖ ℰ` is empty, since `Δ_1 = t` forces `t < η_1`, and a
pair with such a small `t` has a length `M` with `Δ_M ≥ λ^{3M}/15 ≥ η_M`. The proof of Theorem 2.1
in the source constructs pairs with `Δ_n < C η_n` for all `n ≥ 1` with a constant `C`, which is
the form `BaranyKaenmakiPair` that the article uses; the corrected statement, for the lengths
`n ≥ 5`, is `not_countable_condensation` in `BoxLike/BaranyKaenmaki.lean`. No result takes this
statement. -/
def BaranyKaenmakiTheorem : Prop :=
  ∀ η : ℕ → ℝ, Antitone η → (∀ n, 0 < η n) →
    Tendsto (fun n : ℕ => Real.log (η n) / n) atTop atBot →
    ¬ {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < 1 / 3 ∧ 0 < p.2 ∧ p.2 < p.1 / (1 - p.1) ∧ HomFree p.1 p.2 ∧
        ∀ n : ℕ, 1 ≤ n → homGap p.1 p.2 n < ENNReal.ofReal (η n)}.Countable

/-- `C_0 exp(-n²)` lies eventually below every exponential `c^n`, so that
`n⁻¹ log Δ_n^{diag} → -∞` (tex lines 1394 to 1397). -/
theorem exists_forall_mul_exp_lt {C₀ c : ℝ} (hC : 0 < C₀) (hc : 0 < c) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, C₀ * Real.exp (-(n : ℝ) ^ 2) < c ^ n := by
  refine ⟨⌈|Real.log C₀| + |Real.log c| + 1⌉₊, fun n hn => ?_⟩
  have hn' : |Real.log C₀| + |Real.log c| + 1 ≤ (n : ℝ) := Nat.ceil_le.1 hn
  have h1 := abs_nonneg (Real.log C₀)
  have h2 := neg_abs_le (Real.log c)
  have h3 := le_abs_self (Real.log C₀)
  have h4 := abs_nonneg (Real.log c)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h5 : -((n : ℝ) * |Real.log c|) ≤ n * Real.log c := by
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left h2 hn0
  have h6 : (n : ℝ) * (|Real.log C₀| + 1) ≤ n * (n - |Real.log c|) :=
    mul_le_mul_of_nonneg_left (by linarith) hn0
  have h7 : 1 * (|Real.log C₀| + 1) ≤ (n : ℝ) * (|Real.log C₀| + 1) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hlog : Real.log C₀ - (n : ℝ) ^ 2 < n * Real.log c := by nlinarith
  calc C₀ * Real.exp (-(n : ℝ) ^ 2) = Real.exp (Real.log C₀ - (n : ℝ) ^ 2) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hC]
    _ < Real.exp (n * Real.log c) := Real.exp_lt_exp.2 hlog
    _ = c ^ n := by rw [Real.exp_nat_mul, Real.exp_log hc]

/-- A gap bounded by `C_0 exp(-n²)` lies eventually below every exponential. -/
theorem homGap_lt_of_le_mul_exp {lam t C₀ : ℝ} (hC : 0 < C₀)
    (hgap : ∀ n : ℕ, 1 ≤ n → homGap lam t n ≤ ENNReal.ofReal (C₀ * Real.exp (-(n : ℝ) ^ 2)))
    {c : ℝ} (hc : 0 < c) : ∃ n₀ : ℕ, ∀ n ≥ n₀, homGap lam t n < ENNReal.ofReal (c ^ n) := by
  obtain ⟨n₀, hn₀⟩ := exists_forall_mul_exp_lt hC hc
  refine ⟨max n₀ 1, fun n hn => (hgap n (le_of_max_le_right hn)).trans_lt ?_⟩
  exact (ENNReal.ofReal_lt_ofReal_iff (pow_pos hc n)).2 (hn₀ n (le_of_max_le_left hn))

/-- The sequence `η_n = exp(-n²)` of `prop:ssc_no_overlap_not_pesc` is monotone decreasing. -/
theorem antitone_exp_neg_sq : Antitone fun n : ℕ => Real.exp (-(n : ℝ) ^ 2) := by
  intro m n hmn
  have h : (m : ℝ) ≤ n := Nat.cast_le.2 hmn
  have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  exact Real.exp_le_exp.2 (by nlinarith)

/-- The sequence `η_n = exp(-n²)` satisfies `n⁻¹ log η_n → -∞`. -/
theorem tendsto_log_exp_neg_sq :
    Tendsto (fun n : ℕ => Real.log (Real.exp (-(n : ℝ) ^ 2)) / n) atTop atBot := by
  have h : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [Real.log_exp]
  field_simp

/-! ### The system -/

/-- The lower end points of the intervals of tex lines 1355 to 1363 for the parameters
`(r_1, r_2, r_3, r_4, r_5, q, u, v, s_1, s_2, s_3)`. -/
noncomputable def paramLo : Fin 11 → ℝ :=
  ![1 / 20, 1 / 20, 1 / 20, 1 / 10, 1 / 25, 1, 3 / 2, 3 / 4, 1 / 25, 1 / 4, 1 / 2]

/-- The upper end points of the intervals of tex lines 1355 to 1363 for the parameters
`(r_1, r_2, r_3, r_4, r_5, q, u, v, s_1, s_2, s_3)`. -/
noncomputable def paramHi : Fin 11 → ℝ :=
  ![1 / 10, 1 / 10, 1 / 10, 1 / 5, 1 / 20, 4 / 3, 8 / 5, 19 / 25, 1 / 20, 3 / 10, 11 / 20]

/-- The intervals of tex lines 1355 to 1363 are non-empty. -/
theorem paramLo_lt_paramHi (k : Fin 11) : paramLo k < paramHi k := by
  fin_cases k <;> norm_num [paramLo, paramHi]

/-- The parameters of the system of `prop:ssc_no_overlap_not_pesc`: a pair `(λ, t)` with
`0 < λ < 1/3` and `0 < t < λ/(1-λ)`, and a tuple
`θ = (r_1, r_2, r_3, r_4, r_5, q, u, v, s_1, s_2, s_3)` in the open box of tex lines 1355 to
1438. Algebraic independence is a separate hypothesis of the statements that use it. -/
structure Params where
  /-- The common first-coordinate ratio `λ` of the three diagonal maps. -/
  lam : ℝ
  /-- The translation `t` of the homogeneous system. -/
  t : ℝ
  /-- The tuple `(r_1, r_2, r_3, r_4, r_5, q, u, v, s_1, s_2, s_3)`. -/
  θ : Fin 11 → ℝ
  lam_pos : 0 < lam
  lam_lt : lam < 1 / 3
  t_pos : 0 < t
  t_lt : t < lam / (1 - lam)
  mem : ∀ k, θ k ∈ Set.Ioo (paramLo k) (paramHi k)

namespace Params

variable (P : Params)

/-- The ratio `r_1 ∈ (1/20, 1/10)`. -/
abbrev r₁ : ℝ := P.θ 0
/-- The ratio `r_2 ∈ (1/20, 1/10)`. -/
abbrev r₂ : ℝ := P.θ 1
/-- The ratio `r_3 ∈ (1/20, 1/10)`. -/
abbrev r₃ : ℝ := P.θ 2
/-- The ratio `r_4 ∈ (1/10, 1/5)`. -/
abbrev r₄ : ℝ := P.θ 3
/-- The ratio `r_5 ∈ (1/25, 1/20)`. -/
abbrev r₅ : ℝ := P.θ 4
/-- The translation `q ∈ (1, 4/3)`. -/
abbrev q : ℝ := P.θ 5
/-- The translation `u ∈ (3/2, 8/5)`. -/
abbrev u : ℝ := P.θ 6
/-- The translation `v ∈ (3/4, 19/25)`. -/
abbrev v : ℝ := P.θ 7
/-- The translation `s_1 ∈ (1/25, 1/20)`. -/
abbrev s₁ : ℝ := P.θ 8
/-- The translation `s_2 ∈ (1/4, 3/10)`. -/
abbrev s₂ : ℝ := P.θ 9
/-- The translation `s_3 ∈ (1/2, 11/20)`. -/
abbrev s₃ : ℝ := P.θ 10

/-- `r_1 ∈ (1/20, 1/10)`. -/
theorem r₁_mem : P.r₁ ∈ Set.Ioo (1 / 20 : ℝ) (1 / 10) := by
  simpa [paramLo, paramHi] using P.mem 0

/-- `r_2 ∈ (1/20, 1/10)`. -/
theorem r₂_mem : P.r₂ ∈ Set.Ioo (1 / 20 : ℝ) (1 / 10) := by
  simpa [paramLo, paramHi] using P.mem 1

/-- `r_3 ∈ (1/20, 1/10)`. -/
theorem r₃_mem : P.r₃ ∈ Set.Ioo (1 / 20 : ℝ) (1 / 10) := by
  simpa [paramLo, paramHi] using P.mem 2

/-- `r_4 ∈ (1/10, 1/5)`. -/
theorem r₄_mem : P.r₄ ∈ Set.Ioo (1 / 10 : ℝ) (1 / 5) := by
  simpa [paramLo, paramHi] using P.mem 3

/-- `r_5 ∈ (1/25, 1/20)`. -/
theorem r₅_mem : P.r₅ ∈ Set.Ioo (1 / 25 : ℝ) (1 / 20) := by
  simpa [paramLo, paramHi] using P.mem 4

/-- `q ∈ (1, 4/3)`. -/
theorem q_mem : P.q ∈ Set.Ioo (1 : ℝ) (4 / 3) := by
  simpa [paramLo, paramHi] using P.mem 5

/-- `u ∈ (3/2, 8/5)`. -/
theorem u_mem : P.u ∈ Set.Ioo (3 / 2 : ℝ) (8 / 5) := by
  simpa [paramLo, paramHi] using P.mem 6

/-- `v ∈ (3/4, 19/25)`. -/
theorem v_mem : P.v ∈ Set.Ioo (3 / 4 : ℝ) (19 / 25) := by
  simpa [paramLo, paramHi] using P.mem 7

/-- `s_1 ∈ (1/25, 1/20)`. -/
theorem s₁_mem : P.s₁ ∈ Set.Ioo (1 / 25 : ℝ) (1 / 20) := by
  simpa [paramLo, paramHi] using P.mem 8

/-- `s_2 ∈ (1/4, 3/10)`. -/
theorem s₂_mem : P.s₂ ∈ Set.Ioo (1 / 4 : ℝ) (3 / 10) := by
  simpa [paramLo, paramHi] using P.mem 9

/-- `s_3 ∈ (1/2, 11/20)`. -/
theorem s₃_mem : P.s₃ ∈ Set.Ioo (1 / 2 : ℝ) (11 / 20) := by
  simpa [paramLo, paramHi] using P.mem 10

/-- `t < λ/(1-λ) < 1/2`, since `λ < 1/3`. -/
theorem t_lt_half : P.t < 1 / 2 := by
  refine P.t_lt.trans ?_
  rw [div_lt_iff₀ (by linarith [P.lam_lt])]
  linarith [P.lam_lt]

/-- The system `Φ = (φ_1, φ_2, φ_3, φ_4)` of `prop:ssc_no_overlap_not_pesc` (tex lines 1368 to
1457), over the alphabet `Fin 4`: the indices `0, 1, 2` are the diagonal maps `φ_1, φ_2, φ_3`
with `A_i = diag(λ, r_i)`, and the index `3` is the anti-diagonal map `φ_4`. -/
noncomputable def sys : System (Fin 4) where
  o := ![0, 0, 0, 1]
  a := ![P.lam, P.lam, P.lam, P.r₄]
  b := ![P.r₁, P.r₂, P.r₃, P.r₅]
  v := ![(P.q, P.s₁), (P.q + P.t, P.s₂), (P.q + 1, P.s₃), (P.u, P.v)]
  a_ne_zero i := by
    have := P.lam_pos
    have := P.r₄_mem.1
    fin_cases i <;> simp <;> linarith
  b_ne_zero i := by
    have := P.r₁_mem.1
    have := P.r₂_mem.1
    have := P.r₃_mem.1
    have := P.r₅_mem.1
    fin_cases i <;> simp <;> linarith
  abs_a_lt_one i := by
    have := P.lam_pos
    have := P.lam_lt
    have := P.r₄_mem.1
    have := P.r₄_mem.2
    fin_cases i <;> simp [abs_lt] <;> constructor <;> linarith
  abs_b_lt_one i := by
    obtain ⟨h1, h1'⟩ := P.r₁_mem
    obtain ⟨h2, h2'⟩ := P.r₂_mem
    obtain ⟨h3, h3'⟩ := P.r₃_mem
    obtain ⟨h5, h5'⟩ := P.r₅_mem
    fin_cases i <;> simp [abs_lt] <;> constructor <;> linarith

/-! ### The maps and the standing hypotheses -/

/-- `φ_1(x, y) = (λx + q, r_1 y + s_1)`. -/
@[simp] theorem sys_phi_zero (z : ℝ × ℝ) :
    P.sys.phi 0 z = (P.lam * z.1 + P.q, P.r₁ * z.2 + P.s₁) := by
  ext <;> simp [System.phi, sys]

/-- `φ_2(x, y) = (λx + q + t, r_2 y + s_2)`. -/
@[simp] theorem sys_phi_one (z : ℝ × ℝ) :
    P.sys.phi 1 z = (P.lam * z.1 + (P.q + P.t), P.r₂ * z.2 + P.s₂) := by
  ext <;> simp [System.phi, sys]

/-- `φ_3(x, y) = (λx + q + 1, r_3 y + s_3)`. -/
@[simp] theorem sys_phi_two (z : ℝ × ℝ) :
    P.sys.phi 2 z = (P.lam * z.1 + (P.q + 1), P.r₃ * z.2 + P.s₃) := by
  ext <;> simp [System.phi, sys]

/-- `φ_4(x, y) = (r_4 y + u, r_5 x + v)`. -/
@[simp] theorem sys_phi_three (z : ℝ × ℝ) :
    P.sys.phi 3 z = (P.r₄ * z.2 + P.u, P.r₅ * z.1 + P.v) := by
  ext <;> simp [System.phi, sys, show (1 : ZMod 2) + 1 = 0 from by decide]

/-- `N = 4` and `ℓ = 3`: the first three maps are diagonal and the fourth is anti-diagonal. -/
theorem sys_o : P.sys.o = ![0, 0, 0, 1] := rfl

/-- The system is box-like with rotations: `φ_1` is diagonal and `φ_4` is anti-diagonal. -/
theorem withRotations : P.sys.WithRotations := ⟨⟨0, rfl⟩, ⟨3, rfl⟩⟩

/-- All `a_i, b_i` lie in `(0, 1)` (tex line 1382). -/
theorem sys_ratio_mem (p : Fin 4 × ZMod 2) : P.sys.ratio p ∈ Set.Ioo (0 : ℝ) 1 := by
  have := P.lam_pos
  have := P.lam_lt
  obtain ⟨h1, h1'⟩ := P.r₁_mem
  obtain ⟨h2, h2'⟩ := P.r₂_mem
  obtain ⟨h3, h3'⟩ := P.r₃_mem
  obtain ⟨h4, h4'⟩ := P.r₄_mem
  obtain ⟨h5, h5'⟩ := P.r₅_mem
  obtain ⟨i, c⟩ := p
  fin_cases i <;> rcases zmod_two_cases c with rfl | rfl <;>
    simp [System.ratio, sys] <;> constructor <;> linarith

/-- `|a_1| = λ ≠ r_1 = |b_1|` with `i_0 = 1 ≤ ℓ` (tex lines 1384 to 1385). The inequality
`λ ≠ r_1` follows from the algebraic independence, see `lam_ne_r₁`. -/
theorem hasProximalDiagonal (h : P.lam ≠ P.r₁) : P.sys.HasProximalDiagonal := by
  refine ⟨0, rfl, ?_⟩
  change |P.lam| ≠ |P.r₁|
  rwa [abs_of_pos P.lam_pos, abs_of_pos (by linarith [P.r₁_mem.1])]

/-- `A_1` has the two real eigenvalues `λ, r_1` of distinct modulus, so the tuple is proximal
(tex lines 1385 to 1386). -/
theorem proximal (h : P.lam ≠ P.r₁) : P.sys.Proximal := (P.hasProximalDiagonal h).proximal

/-- The only lines invariant under `A_1` are the coordinate axes, which `A_4` interchanges, so
the tuple is irreducible (tex lines 1387 to 1388). -/
theorem irreducible (h : P.lam ≠ P.r₁) : P.sys.Irreducible :=
  irreducible_of_hasProximalDiagonal P.withRotations (P.hasProximalDiagonal h)

/-! ### Strong separation -/

/-- The rectangle `R = [0,4] × [0,1]` of tex line 1369. -/
def rect : Set (ℝ × ℝ) := Set.Icc 0 4 ×ˢ Set.Icc 0 1

/-- The lower ends of four pairwise disjoint open intervals that contain the `y`-bands
`[s_1, s_1 + r_1]`, `[s_2, s_2 + r_2]`, `[s_3, s_3 + r_3]` and `[v, v + 4r_5]` of tex lines
1474 to 1475. -/
noncomputable def bandLo : Fin 4 → ℝ := ![1 / 25, 1 / 4, 1 / 2, 3 / 4]

/-- The upper ends of four pairwise disjoint open intervals that contain the `y`-bands. -/
noncomputable def bandHi : Fin 4 → ℝ := ![3 / 20, 2 / 5, 13 / 20, 24 / 25]

/-- The four intervals are pairwise disjoint and increasing: `3/20 < 1/4`, `2/5 < 1/2` and
`13/20 < 3/4`. -/
theorem bandHi_lt_bandLo {i j : Fin 4} (h : i < j) : bandHi i < bandLo j := by
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd h (by decide)
    | norm_num [bandLo, bandHi]

/-- The images `φ_i(R)` are contained in `R` (tex line 1398). -/
theorem phi_mem_rect (i : Fin 4) {z : ℝ × ℝ} (hz : z ∈ rect) : P.sys.phi i z ∈ rect := by
  obtain ⟨⟨hx0, hx4⟩, ⟨hy0, hy1⟩⟩ := hz
  have hlam := P.lam_pos
  have hlam' := P.lam_lt
  have ht := P.t_pos
  have ht' := P.t_lt_half
  obtain ⟨hq, hq'⟩ := P.q_mem
  have hlx : 0 ≤ P.lam * z.1 := mul_nonneg hlam.le hx0
  have hlx' : P.lam * z.1 ≤ 1 / 3 * 4 := mul_le_mul hlam'.le hx4 hx0 (by norm_num)
  fin_cases i
  · obtain ⟨hr, hr'⟩ := P.r₁_mem
    obtain ⟨hs, hs'⟩ := P.s₁_mem
    have h1 : 0 ≤ P.r₁ * z.2 := mul_nonneg (by linarith) hy0
    have h2 : P.r₁ * z.2 ≤ 1 / 10 * 1 := mul_le_mul hr'.le hy1 hy0 (by norm_num)
    simp only [rect, Fin.zero_eta, sys_phi_zero, Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · obtain ⟨hr, hr'⟩ := P.r₂_mem
    obtain ⟨hs, hs'⟩ := P.s₂_mem
    have h1 : 0 ≤ P.r₂ * z.2 := mul_nonneg (by linarith) hy0
    have h2 : P.r₂ * z.2 ≤ 1 / 10 * 1 := mul_le_mul hr'.le hy1 hy0 (by norm_num)
    simp only [rect, Fin.mk_one, sys_phi_one, Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · obtain ⟨hr, hr'⟩ := P.r₃_mem
    obtain ⟨hs, hs'⟩ := P.s₃_mem
    have h1 : 0 ≤ P.r₃ * z.2 := mul_nonneg (by linarith) hy0
    have h2 : P.r₃ * z.2 ≤ 1 / 10 * 1 := mul_le_mul hr'.le hy1 hy0 (by norm_num)
    change P.sys.phi 2 z ∈ rect
    simp only [rect, sys_phi_two, Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · obtain ⟨hr, hr'⟩ := P.r₄_mem
    obtain ⟨hr5, hr5'⟩ := P.r₅_mem
    obtain ⟨hu, hu'⟩ := P.u_mem
    obtain ⟨hv, hv'⟩ := P.v_mem
    have h1 : 0 ≤ P.r₄ * z.2 := mul_nonneg (by linarith) hy0
    have h2 : P.r₄ * z.2 ≤ 1 / 5 * 1 := mul_le_mul hr'.le hy1 hy0 (by norm_num)
    have h3 : 0 ≤ P.r₅ * z.1 := mul_nonneg (by linarith) hx0
    have h4 : P.r₅ * z.1 ≤ 1 / 20 * 4 := mul_le_mul hr5'.le hx4 hx0 (by norm_num)
    change P.sys.phi 3 z ∈ rect
    simp only [rect, sys_phi_three, Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- The second coordinates of `φ_i(R)` lie in the `i`-th of four pairwise disjoint intervals
(tex lines 1398 to 1401). -/
theorem snd_phi_mem_band (i : Fin 4) {z : ℝ × ℝ} (hz : z ∈ rect) :
    (P.sys.phi i z).2 ∈ Set.Ioo (bandLo i) (bandHi i) := by
  obtain ⟨⟨hx0, hx4⟩, ⟨hy0, hy1⟩⟩ := hz
  fin_cases i
  · obtain ⟨hr, hr'⟩ := P.r₁_mem
    obtain ⟨hs, hs'⟩ := P.s₁_mem
    have h1 : 0 ≤ P.r₁ * z.2 := mul_nonneg (by linarith) hy0
    have h2 : P.r₁ * z.2 ≤ 1 / 10 * 1 := mul_le_mul hr'.le hy1 hy0 (by norm_num)
    simp only [Fin.zero_eta, sys_phi_zero, bandLo, bandHi, Set.mem_Ioo, Matrix.cons_val_zero]
    constructor <;> linarith
  · obtain ⟨hr, hr'⟩ := P.r₂_mem
    obtain ⟨hs, hs'⟩ := P.s₂_mem
    have h1 : 0 ≤ P.r₂ * z.2 := mul_nonneg (by linarith) hy0
    have h2 : P.r₂ * z.2 ≤ 1 / 10 * 1 := mul_le_mul hr'.le hy1 hy0 (by norm_num)
    simp only [Fin.mk_one, sys_phi_one, bandLo, bandHi, Set.mem_Ioo, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    constructor <;> linarith
  · obtain ⟨hr, hr'⟩ := P.r₃_mem
    obtain ⟨hs, hs'⟩ := P.s₃_mem
    have h1 : 0 ≤ P.r₃ * z.2 := mul_nonneg (by linarith) hy0
    have h2 : P.r₃ * z.2 ≤ 1 / 10 * 1 := mul_le_mul hr'.le hy1 hy0 (by norm_num)
    change (P.sys.phi 2 z).2 ∈ Set.Ioo (bandLo 2) (bandHi 2)
    simp [bandLo, bandHi]
    constructor <;> linarith
  · obtain ⟨hr5, hr5'⟩ := P.r₅_mem
    obtain ⟨hv, hv'⟩ := P.v_mem
    have h3 : 0 ≤ P.r₅ * z.1 := mul_nonneg (by linarith) hx0
    have h4 : P.r₅ * z.1 ≤ 1 / 20 * 4 := mul_le_mul hr5'.le hx4 hx0 (by norm_num)
    change (P.sys.phi 3 z).2 ∈ Set.Ioo (bandLo 3) (bandHi 3)
    simp [bandLo, bandHi]
    constructor <;> linarith

/-- The images `φ_i(R)` and `φ_j(R)` are disjoint for `i < j`: the separation is carried by the
`y`-bands. -/
theorem phi_ne_of_lt {i j : Fin 4} (h : i < j) {z z' : ℝ × ℝ} (hz : z ∈ rect)
    (hz' : z' ∈ rect) : P.sys.phi i z ≠ P.sys.phi j z' := by
  intro he
  have h1 := (P.snd_phi_mem_band i hz).2
  have h2 := (P.snd_phi_mem_band j hz').1
  rw [he] at h1
  linarith [bandHi_lt_bandLo h]

/-- The strong separation condition holds (tex lines 1398 to 1405). -/
theorem strongSeparation : P.sys.StrongSeparation := by
  refine P.sys.strongSeparation_of_invariant (L := rect)
    (isCompact_Icc.prod isCompact_Icc) ⟨(0, 0), by simp [rect]⟩ ?_ ?_
  · rintro i _ ⟨z, hz, rfl⟩
    exact P.phi_mem_rect i hz
  · intro i j hij
    rw [Set.disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ ⟨z', hz', he⟩
    rcases lt_or_gt_of_ne hij with h | h
    · exact P.phi_ne_of_lt h hz hz' he.symm
    · exact P.phi_ne_of_lt h hz' hz he

/-- The `x`-images `[q, q + 4λ]` and `[q + t, q + t + 4λ]` of `φ_1` and `φ_2` overlap, since
`t < λ/(1-λ) < 4λ` (tex lines 1402 to 1403): the point `q + t` lies in both. -/
theorem fst_phi_overlap :
    ∃ z ∈ rect, ∃ z' ∈ rect, (P.sys.phi 0 z).1 = (P.sys.phi 1 z').1 := by
  have hlam := P.lam_pos
  have hlam' := P.lam_lt
  have ht4 : P.t < 4 * P.lam := by
    refine P.t_lt.trans ?_
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  refine ⟨(P.t / P.lam, 0), ⟨⟨div_nonneg P.t_pos.le hlam.le, ?_⟩, by simp⟩, (0, 0),
    by simp [rect], ?_⟩
  · rw [div_le_iff₀ hlam]
    linarith
  · simp only [sys_phi_zero, sys_phi_one, mul_zero, zero_add]
    field_simp
    ring

/-! ### The gap -/

/-- The index set `{1, 2, 3}` of the diagonal maps, as a subset of `Fin 4`. -/
def lamSet : Set (Fin 4) := Set.range (Fin.castSucc : Fin 3 → Fin 4)

/-- The three diagonal maps share the first-coordinate ratio `λ`. -/
theorem sys_a_of_mem : ∀ i ∈ lamSet, P.sys.a i = P.lam := by
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> simp [sys]

/-- The induced first-coordinate maps `g_1(x) = λx + q`, `g_2(x) = λx + q + t` and
`g_3(x) = λx + q + 1` (tex lines 1391 to 1392). -/
theorem sys_g_castSucc (i : Fin 3) (y : ℝ) :
    P.sys.g (i.castSucc, 0) y = P.lam * y + (P.q + homTrans P.t i) := by
  fin_cases i <;> simp [System.g, System.trans, sys, homTrans]

/-- The maps `g_1, g_2, g_3` are conjugate to the homogeneous system by the translation by
`q/(1-λ)` (tex lines 1391 to 1393). -/
theorem gWord_firstAxis_conj (w : List (Fin 3)) (x : ℝ) :
    P.sys.gWord (firstAxis (w.map Fin.castSucc)) (x + P.q / (1 - P.lam)) =
      homWord P.lam P.t w x + P.q / (1 - P.lam) := by
  have hlam : 1 - P.lam ≠ 0 := by linarith [P.lam_lt]
  induction w with
  | nil => simp [firstAxis]
  | cons i w ih =>
    simp only [firstAxis, List.map_cons, gWord_cons, Function.comp_apply, homWord_cons] at ih ⊢
    rw [ih, sys_g_castSucc]
    field_simp
    ring

/-- Two words of the same length over `{1, 2, 3}` have the same translation difference in the
system `(g_1, g_2, g_3)` and in the homogeneous system. -/
theorem gWord_firstAxis_sub {w w' : List (Fin 3)} (h : w.length = w'.length) :
    P.sys.gWord (firstAxis (w.map Fin.castSucc)) 0 -
        P.sys.gWord (firstAxis (w'.map Fin.castSucc)) 0 =
      homWord P.lam P.t w 0 - homWord P.lam P.t w' 0 := by
  have h1 := P.gWord_firstAxis_conj w (-(P.q / (1 - P.lam)))
  have h2 := P.gWord_firstAxis_conj w' (-(P.q / (1 - P.lam)))
  rw [neg_add_cancel] at h1 h2
  rw [h1, h2, homWord_apply P.lam P.t w, homWord_apply P.lam P.t w', h]
  ring

/-- A word over `{1, 2, 3} ⊆ Fin 4` is the image of a word over `Fin 3`. -/
theorem exists_map_castSucc {w : List (Fin 4)} (hw : ∀ i ∈ w, i ∈ lamSet) :
    ∃ w₃ : List (Fin 3), w = w₃.map Fin.castSucc := by
  induction w with
  | nil => exact ⟨[], rfl⟩
  | cons i w ih =>
    obtain ⟨j, rfl⟩ := hw i (by simp)
    obtain ⟨w₃, rfl⟩ := ih fun k hk => hw k (by simp [hk])
    exact ⟨j :: w₃, rfl⟩

/-- The minimal gap `Δ_n^{diag}` over `{1, 2, 3}^n` equals `Δ_n^{λ,t}` (tex lines 1393 to
1469). -/
theorem diagGap_eq_homGap (n : ℕ) : P.sys.diagGap lamSet n = homGap P.lam P.t n := by
  have hinj : Function.Injective (List.map (Fin.castSucc : Fin 3 → Fin 4)) :=
    List.map_injective_iff.2 (Fin.castSucc_injective 3)
  apply le_antisymm
  · refine le_iInf fun w => le_iInf fun w' => le_iInf fun hw => le_iInf fun hw' =>
      le_iInf fun hne => ?_
    rw [← P.gWord_firstAxis_sub (hw.trans hw'.symm)]
    exact iInf_le_of_le (w.map Fin.castSucc) <| iInf_le_of_le (w'.map Fin.castSucc) <|
      iInf_le_of_le (by simp [hw]) <| iInf_le_of_le (by simp [hw']) <|
      iInf_le_of_le (by simp [lamSet]) <| iInf_le_of_le (by simp [lamSet]) <|
      iInf_le _ (hinj.ne hne)
  · refine le_iInf fun w => le_iInf fun w' => le_iInf fun hw => le_iInf fun hw' =>
      le_iInf fun hwJ => le_iInf fun hwJ' => le_iInf fun hne => ?_
    obtain ⟨w₃, rfl⟩ := exists_map_castSucc hwJ
    obtain ⟨w₃', rfl⟩ := exists_map_castSucc hwJ'
    rw [List.length_map] at hw hw'
    rw [P.gWord_firstAxis_sub (hw.trans hw'.symm)]
    exact iInf_le_of_le w₃ <| iInf_le_of_le w₃' <| iInf_le_of_le hw <| iInf_le_of_le hw' <|
      iInf_le _ fun h => hne (by rw [h])

/-- The projective exponential separation condition fails (tex lines 1438 to 1444), by
`lem:proj_gap_dominated` with `m = 3`, when the gap of the homogeneous system lies eventually
below every exponential. -/
theorem not_projExpSeparation
    (hgap : ∀ c : ℝ, 0 < c → ∃ n₀ : ℕ, ∀ n ≥ n₀, homGap P.lam P.t n < ENNReal.ofReal (c ^ n)) :
    ¬ P.sys.ProjExpSeparation := by
  refine P.sys.not_projExpSeparation_of_diagGap (J := lamSet) P.sys_a_of_mem fun c hc => ?_
  obtain ⟨n₀, h⟩ := hgap c hc
  exact ⟨n₀, fun n hn => (P.diagGap_eq_homGap n).le.trans_lt (h n hn)⟩

/-! ### Freeness -/

/-- The ratios of the projective system are the functions `genRatio` of the parameters (tex
lines 1484 to 1485). -/
theorem sys_ratio (p : Fin 4 × ZMod 2) : P.sys.ratio p = genRatio P.lam P.θ p := by
  obtain ⟨i, c⟩ := p
  fin_cases i <;> rcases zmod_two_cases c with rfl | rfl <;> simp [System.ratio, sys, genRatio]

/-- The translations of the projective system are the functions `genTrans` of the parameters
(tex lines 1409 to 1410). -/
theorem sys_trans (p : Fin 4 × ZMod 2) : P.sys.trans p = genTrans P.t P.θ p := by
  obtain ⟨i, c⟩ := p
  fin_cases i <;> rcases zmod_two_cases c with rfl | rfl <;> simp [System.trans, sys, genTrans]

/-- The derivative of `g_𝐣` is the polynomial function `genDeriv` of the parameters. -/
theorem sys_gDeriv (u : List (Fin 4 × ZMod 2)) : P.sys.gDeriv u = genDeriv P.lam P.θ u := by
  induction u with
  | nil => rfl
  | cons p u ih => rw [gDeriv_cons, genDeriv_cons, ih, sys_ratio]

/-- The value `g_𝐣(0)` is the polynomial function `genVal` of the parameters. -/
theorem sys_gWord_zero (u : List (Fin 4 × ZMod 2)) :
    P.sys.gWord u 0 = genVal P.lam P.t P.θ u := by
  induction u with
  | nil => rfl
  | cons p u ih =>
    rw [gWord_cons, Function.comp_apply, System.g, ih, sys_ratio, sys_trans, genVal_cons]

/-- The maps of the projective system `Ψ` generate a free semigroup (tex lines 1407 to 1436),
when the homogeneous system does and the parameters are algebraically independent over a
subfield `K ∋ λ, t` of `ℝ`. -/
theorem freeProjective {K : Subfield ℝ} (hlamK : P.lam ∈ K) (htK : P.t ∈ K)
    (hfree : HomFree P.lam P.t) (hx : AlgebraicIndependent K P.θ) : P.sys.FreeProjective := by
  intro u u' h
  obtain ⟨hD, hV⟩ := (P.sys.gWord_eq_iff u u').1 h
  rw [sys_gDeriv, sys_gDeriv] at hD
  rw [sys_gWord_zero, sys_gWord_zero] at hV
  exact eq_of_genDeriv_eq_of_genVal_eq P.lam_pos (by linarith [P.lam_lt]) hfree hlamK htK hx
    hD hV

/-- `r_1` is transcendental over `K ∋ λ`, so `λ ≠ r_1` (tex lines 1384 to 1385). -/
theorem lam_ne_r₁ {K : Subfield ℝ} (hlamK : P.lam ∈ K) (hx : AlgebraicIndependent K P.θ) :
    P.lam ≠ P.r₁ := by
  intro h
  refine hx.transcendental 0 ?_
  change IsAlgebraic K P.r₁
  rw [← h]
  exact isAlgebraic_algebraMap (⟨P.lam, hlamK⟩ : K)

end Params

/-- The choice of the parameters in the proof of `prop:ssc_no_overlap_not_pesc` (tex lines 1354
to 1443): for `0 < λ < 1/3` and `0 < t < λ/(1-λ)` there are `r_1, …, r_5, q, u, v, s_1, s_2, s_3`
in the open intervals of tex lines 1355 to 1363, algebraically independent over `ℚ(λ, t)`, the
subfield of `ℝ` generated by `λ` and `t`. -/
theorem exists_params {lam t : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 3) (ht0 : 0 < t)
    (ht1 : t < lam / (1 - lam)) :
    ∃ P : Params, P.lam = lam ∧ P.t = t ∧
      AlgebraicIndependent (Subfield.closure ({lam, t} : Set ℝ)) P.θ := by
  have : Countable (Subfield.closure ({lam, t} : Set ℝ)) :=
    countable_closure (Set.to_countable _)
  obtain ⟨x, hx, hmem⟩ := exists_algebraicIndependent_mem_Ioo
    (Subfield.closure ({lam, t} : Set ℝ)) 11 paramLo paramHi paramLo_lt_paramHi
  exact ⟨⟨lam, t, x, hlam0, hlam1, ht0, ht1, hmem⟩, rfl, rfl, hx⟩

/-- The paragraph after `prop:ssc_no_overlap_not_pesc` (tex lines 1447 to 1450): the chosen
contraction ratios give `∑_i |det A_i| = λ(r_1 + r_2 + r_3) + r_4 r_5 < 11/100 < 1`. -/
theorem Params.sum_abs_det_lt_one (P : Params) : ∑ i, |(P.sys.mat i).det| < 1 := by
  have h1 := P.r₁_mem
  have h2 := P.r₂_mem
  have h3 := P.r₃_mem
  have h4 := P.r₄_mem
  have h5 := P.r₅_mem
  have hl0 := P.lam_pos
  have hl1 := P.lam_lt
  have hr₁ : (0 : ℝ) < P.r₁ := by linarith [h1.1]
  have hr₂ : (0 : ℝ) < P.r₂ := by linarith [h2.1]
  have hr₃ : (0 : ℝ) < P.r₃ := by linarith [h3.1]
  have hr₄ : (0 : ℝ) < P.r₄ := by linarith [h4.1]
  have hr₅ : (0 : ℝ) < P.r₅ := by linarith [h5.1]
  have e : ∑ i, |(P.sys.mat i).det| =
      P.lam * P.r₁ + P.lam * P.r₂ + P.lam * P.r₃ + P.r₄ * P.r₅ := by
    simp [Fin.sum_univ_four, System.mat, Params.sys, abs_det_boxMat, abs_of_pos hl0,
      abs_of_pos hr₁, abs_of_pos hr₂, abs_of_pos hr₃, abs_of_pos hr₄, abs_of_pos hr₅]
  rw [e]
  nlinarith [h1.2, h2.2, h3.2, h4.2, h5.2]

/-! ### The proposition -/

/-- `prop:ssc_no_overlap_not_pesc` from the properties of the pair `(λ, t)` that the proof
uses: `0 < λ < 1/3`, `0 < t < λ/(1-λ)`, the homogeneous system `(λx, λx + t, λx + 1)` generates
a free semigroup, and its gap `Δ_n^{λ,t}` lies eventually below every exponential `c^n`. The
transcendence of `λ` is not used. The parameters are chosen algebraically independent over
`ℚ(λ, t)`, the subfield of `ℝ` generated by `λ` and `t`, in the box of tex lines 1355 to 1363.

The conclusions are: `N = 4` and `ℓ = 3`; the tuple is proximal and irreducible; it is not
strongly irreducible, since the union of the coordinate axes is invariant under every `A_i`;
`|a_{i_0}| ≠ |b_{i_0}|` for a diagonal generator; the strong separation condition; the maps of
`Ψ` generate a free semigroup; the projective exponential separation condition fails. -/
theorem exists_system_of_homFree {lam t : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 3)
    (ht0 : 0 < t) (ht1 : t < lam / (1 - lam)) (hfree : HomFree lam t)
    (hgap : ∀ c : ℝ, 0 < c → ∃ n₀ : ℕ, ∀ n ≥ n₀, homGap lam t n < ENNReal.ofReal (c ^ n)) :
    ∃ S : System (Fin 4), S.o = ![0, 0, 0, 1] ∧ S.Proximal ∧ S.Irreducible ∧
      ¬ TupleStronglyIrreducible S.mat ∧
      (∀ i (v : Fin 2 → ℝ), v 0 = 0 ∨ v 1 = 0 → (S.mat i *ᵥ v) 0 = 0 ∨ (S.mat i *ᵥ v) 1 = 0) ∧
      (∃ i₀, S.o i₀ = 0 ∧ |S.a i₀| ≠ |S.b i₀|) ∧
      S.StrongSeparation ∧ S.FreeProjective ∧ ¬ S.ProjExpSeparation ∧
      ∑ i, |(S.mat i).det| < 1 := by
  obtain ⟨P, rfl, rfl, hx⟩ := exists_params hlam0 hlam1 ht0 ht1
  have hlamK : P.lam ∈ Subfield.closure ({P.lam, P.t} : Set ℝ) :=
    Subfield.subset_closure (by simp)
  have htK : P.t ∈ Subfield.closure ({P.lam, P.t} : Set ℝ) := Subfield.subset_closure (by simp)
  have hne : P.lam ≠ P.r₁ := P.lam_ne_r₁ hlamK hx
  exact ⟨P.sys, rfl, P.proximal hne, P.irreducible hne, P.sys.not_tupleStronglyIrreducible,
    fun i _ hv => P.sys.mulVec_mem_axes i hv, P.hasProximalDiagonal hne, P.strongSeparation,
    P.freeProjective hlamK htK hfree hx, P.not_projExpSeparation hgap, P.sum_abs_det_lt_one⟩

/-- `prop:ssc_no_overlap_not_pesc`, from the theorem of Bárány and Käenmäki in the form the
article uses: there is a system `Φ = (φ_1, φ_2, φ_3, φ_4)` with `N = 4` and `ℓ = 3` for which
`(A_1, A_2, A_3, A_4)` is proximal and irreducible but not strongly irreducible and
`|a_{i_0}| ≠ |b_{i_0}|` for some `i_0 ≤ ℓ`, such that `X` satisfies the strong separation
condition and the maps of `Ψ` generate a free semigroup, yet `X` does not satisfy the
projective exponential separation condition. The only hypothesis is the theorem of Bárány and
Käenmäki in the form `BaranyKaenmakiPair`; the choice of the parameters, the standing
hypotheses, the strong separation condition and the freeness are proved. -/
theorem ssc_no_overlap_not_pesc (h : BaranyKaenmakiPair) :
    ∃ S : System (Fin 4), S.o = ![0, 0, 0, 1] ∧ S.Proximal ∧ S.Irreducible ∧
      ¬ TupleStronglyIrreducible S.mat ∧
      (∀ i (v : Fin 2 → ℝ), v 0 = 0 ∨ v 1 = 0 → (S.mat i *ᵥ v) 0 = 0 ∨ (S.mat i *ᵥ v) 1 = 0) ∧
      (∃ i₀, S.o i₀ = 0 ∧ |S.a i₀| ≠ |S.b i₀|) ∧
      S.StrongSeparation ∧ S.FreeProjective ∧ ¬ S.ProjExpSeparation ∧
      ∑ i, |(S.mat i).det| < 1 := by
  obtain ⟨lam, t, C₀, hlam0, hlam1, ht0, ht1, -, hC, hfree, hgap⟩ := h
  exact exists_system_of_homFree hlam0 hlam1 ht0 ht1 hfree fun c hc =>
    homGap_lt_of_le_mul_exp hC hgap hc

/-- The paragraph after `prop:ssc_no_overlap_not_pesc` (tex lines 1452 to 1460): exponential
separation of the planar affine maps does not imply projective exponential separation. The
system of the proposition satisfies the strong separation condition, hence
`dist(φ_𝐢(X), φ_𝐣(X)) ≥ δ r^{n-1}` for distinct words of length `n`, with `δ > 0` and
`r = min_i α_2(A_i)`; it fails the projective exponential separation condition, and it is not
strongly irreducible, so the strong irreducibility hypothesis of Hochman and Rapaport fails.
The distance is the sup metric of `ℝ × ℝ`, which is at most the Euclidean distance. -/
theorem planar_separation_not_pesc (h : BaranyKaenmakiPair) :
    ∃ S : System (Fin 4), S.StrongSeparation ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ w w' : List (Fin 4), w.length = w'.length →
        w ≠ w' → ∀ x ∈ S.attractor, ∀ y ∈ S.attractor,
          δ * S.minSingular ^ (w.length - 1) ≤ dist (S.phiWord w x) (S.phiWord w' y)) ∧
      ¬ S.ProjExpSeparation ∧ ¬ TupleStronglyIrreducible S.mat := by
  obtain ⟨S, -, -, -, hsi, -, -, hsep, -, hpesc, -⟩ := ssc_no_overlap_not_pesc h
  exact ⟨S, hsep, hsep.exists_le_dist_phiWord, hpesc, hsi⟩

end NoOverlap

end BoxLike
