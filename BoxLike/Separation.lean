module

/-
The projective gap `Δ_n^Ψ` and the projective exponential separation condition of
`sec:exponential_separation`.

* `System.gWord`, `System.gWord_apply`: the composition `g_𝐣 = g_{j_0} ∘ ⋯ ∘ g_{j_{n-1}}`,
  an affine map with slope `gDeriv 𝐣`.
* `System.gap`: the gap `Δ_n^Ψ`, an element of `ℝ≥0∞`, with `⊤` for the empty minimum.
* `System.ProjExpSeparation`: the projective exponential separation condition.
* `System.gap_succ_le`: `Δ_{m+1}^Ψ ≤ Δ_m^Ψ`, used in the proof of
  `thm:two-block-normalisation`.
* `System.diagGap`, `System.gap_le_diagGap`: `lem:proj_gap_dominated`.
* `System.not_projExpSeparation_of_diagGap`: a sub-collection whose gap decays faster than
  every exponential rules out the condition, the last step of
  `prop:ssc_no_overlap_not_pesc`.
-/
public import BoxLike.System
public import Mathlib.Basic.ENNReal.Real

@[expose] public section

namespace BoxLike

open scoped ENNReal

namespace System

variable {ι : Type*} (S : System ι)

/-- The composition `g_𝐣 = g_{j_0} ∘ ⋯ ∘ g_{j_{n-1}}` of `sec:exponential_separation`. -/
def gWord : List (ι × ZMod 2) → ℝ → ℝ
  | [] => id
  | p :: u => S.g p ∘ gWord u

@[simp] theorem gWord_nil : S.gWord [] = id := rfl

@[simp] theorem gWord_cons (p : ι × ZMod 2) (u : List (ι × ZMod 2)) :
    S.gWord (p :: u) = S.g p ∘ S.gWord u := rfl

/-- `g_𝐣` is affine with slope `g_𝐣'`. -/
theorem gWord_apply (u : List (ι × ZMod 2)) (t : ℝ) :
    S.gWord u t = S.gDeriv u * t + S.gWord u 0 := by
  induction u with
  | nil => simp
  | cons p u ih =>
    simp only [gWord_cons, Function.comp_apply, gDeriv_cons, g]
    rw [ih]; ring

theorem gWord_append (u u' : List (ι × ZMod 2)) :
    S.gWord (u ++ u') = S.gWord u ∘ S.gWord u' := by
  induction u with
  | nil => rfl
  | cons p u ih => simp [ih, Function.comp_assoc]

theorem gDeriv_append (u u' : List (ι × ZMod 2)) :
    S.gDeriv (u ++ u') = S.gDeriv u * S.gDeriv u' := by
  simp [gDeriv]

/-- The projective gap `Δ_n^Ψ`: the least `|g_𝐢(0) - g_𝐣(0)|` over distinct words `𝐢, 𝐣` of
length `n` with `g_𝐢' = g_𝐣'`. The minimum of the empty set is `⊤`. -/
noncomputable def gap (n : ℕ) : ℝ≥0∞ :=
  ⨅ (u : List (ι × ZMod 2)) (u' : List (ι × ZMod 2)) (_ : u.length = n) (_ : u'.length = n)
    (_ : u ≠ u') (_ : S.gDeriv u = S.gDeriv u'), ENNReal.ofReal |S.gWord u 0 - S.gWord u' 0|

/-- The projective exponential separation condition of `sec:exponential_separation`: there
are `c > 0` and a strictly increasing sequence `(n_k)` with `Δ_{n_k}^Ψ ≥ c^{n_k}`. -/
def ProjExpSeparation : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n : ℕ → ℕ, StrictMono n ∧ ∀ k, ENNReal.ofReal (c ^ n k) ≤ S.gap (n k)

/-- The projective system has no exact overlaps (`sec:exponential_separation`): `g_𝐢 ≠ g_𝐣` for
any two distinct finite words `𝐢`, `𝐣` over the alphabet of `Ψ`, that is, the maps of `Ψ`
generate a free semigroup. The separation hypothesis of `thm:main2`. -/
def NoExactOverlaps : Prop := ∀ u u' : List (ι × ZMod 2), u ≠ u' → S.gWord u ≠ S.gWord u'

/-- The absence of exact overlaps is the injectivity of `𝐢 ↦ g_𝐢`. -/
theorem noExactOverlaps_iff : S.NoExactOverlaps ↔ Function.Injective S.gWord := by
  constructor
  · intro h u u' huu'
    by_contra hne
    exact h u u' hne huu'
  · intro h u u' hne huu'
    exact hne (h huu')

theorem gap_le {n : ℕ} {u u' : List (ι × ZMod 2)} (hu : u.length = n) (hu' : u'.length = n)
    (hne : u ≠ u') (hd : S.gDeriv u = S.gDeriv u') :
    S.gap n ≤ ENNReal.ofReal |S.gWord u 0 - S.gWord u' 0| :=
  iInf_le_of_le u <| iInf_le_of_le u' <| iInf_le_of_le hu <| iInf_le_of_le hu' <|
    iInf_le_of_le hne <| iInf_le _ hd

/-- Appending the same symbol to two words with equal derivatives preserves their
translation difference; hence `Δ_{m+1}^Ψ ≤ Δ_m^Ψ`. -/
theorem gap_succ_le [Nonempty ι] (m : ℕ) : S.gap (m + 1) ≤ S.gap m := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine le_iInf fun u => le_iInf fun u' => le_iInf fun hu => le_iInf fun hu' =>
    le_iInf fun hne => le_iInf fun hd => ?_
  have key : S.gWord (u ++ [(i, 0)]) 0 - S.gWord (u' ++ [(i, 0)]) 0 =
      S.gWord u 0 - S.gWord u' 0 := by
    rw [gWord_append, gWord_append, Function.comp_apply, Function.comp_apply,
      S.gWord_apply u, S.gWord_apply u', hd]
    ring
  rw [← key]
  refine S.gap_le (by simp [hu]) (by simp [hu']) ?_ ?_
  · simpa using hne
  · rw [gDeriv_append, gDeriv_append, hd]

/-- The symbols of the projective system following the first axis over a word of `ι`. -/
def firstAxis (w : List ι) : List (ι × ZMod 2) := w.map fun i => (i, (0 : ZMod 2))

/-- The minimal first-coordinate gap `Δ_n^{diag}` of the sub-collection `J` of
`lem:proj_gap_dominated`. -/
noncomputable def diagGap (J : Set ι) (n : ℕ) : ℝ≥0∞ :=
  ⨅ (w : List ι) (w' : List ι) (_ : w.length = n) (_ : w'.length = n) (_ : ∀ i ∈ w, i ∈ J)
    (_ : ∀ i ∈ w', i ∈ J) (_ : w ≠ w'),
    ENNReal.ofReal |S.gWord (firstAxis w) 0 - S.gWord (firstAxis w') 0|

theorem gDeriv_firstAxis {J : Set ι} {a : ℝ} (hJ : ∀ i ∈ J, S.a i = a) {w : List ι}
    (hw : ∀ i ∈ w, i ∈ J) : S.gDeriv (firstAxis w) = a ^ w.length := by
  induction w with
  | nil => simp [firstAxis]
  | cons i w ih =>
    have hi : S.a i = a := hJ i (hw i (by simp))
    have hw' : ∀ j ∈ w, j ∈ J := fun j hj => hw j (by simp [hj])
    have ih' := ih hw'
    simp only [firstAxis, List.map_cons, gDeriv_cons, ratio_zero, List.length_cons] at ih' ⊢
    rw [ih', hi, pow_succ']

/-- `lem:proj_gap_dominated`: if the maps indexed by `J` have a common first-coordinate
ratio `a`, then `Δ_n^Ψ ≤ Δ_n^{diag}` for every `n`. The statement does not use that the
maps indexed by `J` are diagonal. -/
theorem gap_le_diagGap {J : Set ι} {a : ℝ} (hJ : ∀ i ∈ J, S.a i = a) (n : ℕ) :
    S.gap n ≤ S.diagGap J n := by
  refine le_iInf fun w => le_iInf fun w' => le_iInf fun hw => le_iInf fun hw' =>
    le_iInf fun hwJ => le_iInf fun hwJ' => le_iInf fun hne => ?_
  refine S.gap_le (by simp [firstAxis, hw]) (by simp [firstAxis, hw']) ?_ ?_
  · intro h
    refine hne (List.map_injective_iff.mpr ?_ h)
    intro i j hij
    exact (Prod.ext_iff.mp hij).1
  · rw [S.gDeriv_firstAxis hJ hwJ, S.gDeriv_firstAxis hJ hwJ', hw, hw']

/-- The last step of `prop:ssc_no_overlap_not_pesc`: if the gap of a sub-collection with a
common first-coordinate ratio lies eventually below every exponential, then the projective
exponential separation condition fails. -/
theorem not_projExpSeparation_of_diagGap {J : Set ι} {a : ℝ} (hJ : ∀ i ∈ J, S.a i = a)
    (hgap : ∀ c : ℝ, 0 < c → ∃ n₀ : ℕ, ∀ n ≥ n₀, S.diagGap J n < ENNReal.ofReal (c ^ n)) :
    ¬ S.ProjExpSeparation := by
  rintro ⟨c, hc, n, hn, hsep⟩
  obtain ⟨n₀, hn₀⟩ := hgap c hc
  have hk : n₀ ≤ n n₀ := hn.id_le n₀
  exact absurd ((hsep n₀).trans (S.gap_le_diagGap hJ (n n₀))) (not_le.mpr (hn₀ _ hk))

end System

/-! ### Compositions of similarities of the line -/

/-- The composition `g_{j_0} ∘ ⋯ ∘ g_{j_{n-1}}` of the similarities `g_j(x) = r_j x + t_j` of
the line indexed by `κ`. For the projective system `Ψ` it is `g_𝐣`
(`System.gWord_eq_simWord`); the finite diagonal subsystems in the proof of `thm:main2` use it
for the coordinate maps of the subsystem. -/
def simWord {κ : Type*} (r t : κ → ℝ) : List κ → ℝ → ℝ
  | [] => id
  | j :: u => (fun x => r j * x + t j) ∘ simWord r t u

@[simp] theorem simWord_nil {κ : Type*} (r t : κ → ℝ) : simWord r t [] = id := rfl

@[simp] theorem simWord_cons {κ : Type*} (r t : κ → ℝ) (j : κ) (u : List κ) :
    simWord r t (j :: u) = (fun x => r j * x + t j) ∘ simWord r t u := rfl

theorem simWord_append {κ : Type*} (r t : κ → ℝ) (u u' : List κ) :
    simWord r t (u ++ u') = simWord r t u ∘ simWord r t u' := by
  induction u with
  | nil => rfl
  | cons j u ih => simp [ih, Function.comp_assoc]

/-- The composition of similarities is affine with slope the product of the ratios. -/
theorem simWord_apply {κ : Type*} (r t : κ → ℝ) (u : List κ) (x : ℝ) :
    simWord r t u x = (u.map r).prod * x + simWord r t u 0 := by
  induction u with
  | nil => simp
  | cons j u ih =>
    simp only [simWord_cons, Function.comp_apply, List.map_cons, List.prod_cons]
    rw [ih]; ring

/-- `g_𝐣` is the composition of the similarities `g_j(x) = g_j'(0) x + g_j(0)`. -/
theorem System.gWord_eq_simWord (S : System ι) : S.gWord = simWord S.ratio S.trans := by
  funext u
  induction u with
  | nil => rfl
  | cons p u ih => rw [System.gWord_cons, ih]; rfl

end BoxLike
