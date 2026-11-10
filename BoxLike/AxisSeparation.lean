module

/-
Exponential separation of the systems a diagonal box-like system induces on the coordinate axes:
the definition before `thm:rapaport` in `sec:intro_setting`. For a system `Φ` whose linear parts
are all diagonal, the system induced on the axis `c` consists of the similarities `g_{(i, c)}`,
`i : ι`, of the projective system `Ψ`, and a planar word `𝐢 = i_0 ⋯ i_{n-1}` acts on the axis by
`g_𝐢 = g_{(i_0, c)} ∘ ⋯ ∘ g_{(i_{n-1}, c)}`, the coordinate map `S.gWord` of the projective word
`(i_0, c) ⋯ (i_{n-1}, c)`. The induced system is exponentially separated if there is `c > 0`
such that, for infinitely many `n`, the minimum of `|g_𝐢(0) - g_𝐣(0)|` over distinct words of
length `n` with `g_𝐢' = g_𝐣'` is at least `c^n`; the minimum of the empty set is `∞`.

* `axisWord`: the projective word `(i_0, c) ⋯ (i_{n-1}, c)` of a planar word.
* `System.codeWord_eq_axisWord`, `System.gDeriv_axisWord_zero`, `System.gDeriv_axisWord_one`:
  in a system without rotations the path of `Σ_Z` over `𝐢` starting on the axis `c` is
  `axisWord c 𝐢`, and the derivatives of the induced maps are `a_{i_0} ⋯ a_{i_{n-1}}` and
  `b_{i_0} ⋯ b_{i_{n-1}}`.
* `System.axisGap`: the gap `Δ_n` of the system induced on the axis `c`.
* `System.axisGap_le`, `System.axisGap_succ_le`, `System.axisGap_anti`: the gap is bounded by
  each admissible pair and is non-increasing.
* `System.AxisExpSeparation`: exponential separation of the system induced on the axis `c`.
* `System.axisExpSeparation_iff_frequently`, `System.axisExpSeparation_of_frequently`: the
  condition in the form `Δ_n ≥ r^n` for infinitely many `n`.
* `System.axisGap_eq_top_of_subsingleton`, `System.axisExpSeparation_of_subsingleton`: for one
  map the gap is `⊤` and the condition holds.
-/
public import BoxLike.Separation
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

namespace BoxLike

open scoped ENNReal

/-- The projective word `(i_0, c) ⋯ (i_{n-1}, c)` over the planar word `𝐢 = i_0 ⋯ i_{n-1}`: the
path of `Σ_Z` over `𝐢` in a system with diagonal linear parts, starting in the orientation `c`. -/
def axisWord {ι : Type*} (c : ZMod 2) (u : List ι) : List (ι × ZMod 2) := u.map fun i => (i, c)

section AxisWord

variable {ι : Type*}

@[simp] theorem axisWord_nil (c : ZMod 2) : axisWord c ([] : List ι) = [] := rfl

@[simp] theorem axisWord_cons (c : ZMod 2) (i : ι) (u : List ι) :
    axisWord c (i :: u) = (i, c) :: axisWord c u := rfl

theorem axisWord_append (c : ZMod 2) (u u' : List ι) :
    axisWord c (u ++ u') = axisWord c u ++ axisWord c u' := List.map_append ..

@[simp] theorem length_axisWord (c : ZMod 2) (u : List ι) : (axisWord c u).length = u.length :=
  List.length_map ..

theorem axisWord_injective (c : ZMod 2) : Function.Injective (axisWord (ι := ι) c) :=
  List.map_injective_iff.2 fun _ _ h => (Prod.mk.inj h).1

end AxisWord

namespace System

variable {ι : Type*} (S : System ι)

/-- The gap `Δ_n` of the system induced on the axis `c`: the least `|g_𝐢(0) - g_𝐣(0)|` over
distinct planar words `𝐢, 𝐣` of length `n` with `g_𝐢' = g_𝐣'` along the axis `c`. The minimum of
the empty set is `⊤`. -/
noncomputable def axisGap (c : ZMod 2) (n : ℕ) : ℝ≥0∞ :=
  ⨅ (u : List ι) (u' : List ι) (_ : u.length = n) (_ : u'.length = n) (_ : u ≠ u')
    (_ : S.gDeriv (axisWord c u) = S.gDeriv (axisWord c u')),
    ENNReal.ofReal |S.gWord (axisWord c u) 0 - S.gWord (axisWord c u') 0|

/-- The system induced on the axis `c` is exponentially separated: there are `r > 0` and a
strictly increasing sequence `(n_k)` with `Δ_{n_k} ≥ r^{n_k}`, the definition before
`thm:rapaport`. -/
def AxisExpSeparation (c : ZMod 2) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ n : ℕ → ℕ, StrictMono n ∧ ∀ k, ENNReal.ofReal (r ^ n k) ≤ S.axisGap c (n k)

/-! ### Systems without rotations -/

/-- In a system without rotations the path of `Σ_Z` over `𝐢` starting on the axis `c` stays on
the axis `c`: `codeWord c 𝐢 = axisWord c 𝐢`. -/
theorem codeWord_eq_axisWord (h : ∀ i, S.o i = 0) (c : ZMod 2) (w : List ι) :
    S.codeWord c w = axisWord c w := by
  induction w generalizing c with
  | nil => rfl
  | cons i w ih => rw [codeWord_cons, axisWord_cons, h i, add_zero, ih]

/-- The derivative of the induced map on the first axis is `a_{i_0} ⋯ a_{i_{n-1}}`. -/
theorem gDeriv_axisWord_zero (w : List ι) : S.gDeriv (axisWord 0 w) = (w.map S.a).prod := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [axisWord_cons, gDeriv_cons, ratio_zero, ih, List.map_cons, List.prod_cons]

/-- The derivative of the induced map on the second axis is `b_{i_0} ⋯ b_{i_{n-1}}`. -/
theorem gDeriv_axisWord_one (w : List ι) : S.gDeriv (axisWord 1 w) = (w.map S.b).prod := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [axisWord_cons, gDeriv_cons, ratio_one, ih, List.map_cons, List.prod_cons]

/-! ### Properties of the gap -/

/-- The gap of the induced system is at most the translation difference of any two distinct
planar words of length `n` with equal derivatives along the axis `c`. -/
theorem axisGap_le {c : ZMod 2} {n : ℕ} {u u' : List ι} (hu : u.length = n) (hu' : u'.length = n)
    (hne : u ≠ u') (hd : S.gDeriv (axisWord c u) = S.gDeriv (axisWord c u')) :
    S.axisGap c n ≤ ENNReal.ofReal |S.gWord (axisWord c u) 0 - S.gWord (axisWord c u') 0| :=
  iInf_le_of_le u <| iInf_le_of_le u' <| iInf_le_of_le hu <| iInf_le_of_le hu' <|
    iInf_le_of_le hne <| iInf_le _ hd

/-- Appending the same symbol to two planar words with equal derivatives along the axis `c`
preserves their translation difference; hence `Δ_{m+1} ≤ Δ_m` for the induced system. -/
theorem axisGap_succ_le [Nonempty ι] (c : ZMod 2) (m : ℕ) :
    S.axisGap c (m + 1) ≤ S.axisGap c m := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine le_iInf fun u => le_iInf fun u' => le_iInf fun hu => le_iInf fun hu' =>
    le_iInf fun hne => le_iInf fun hd => ?_
  have key : S.gWord (axisWord c (u ++ [i])) 0 - S.gWord (axisWord c (u' ++ [i])) 0 =
      S.gWord (axisWord c u) 0 - S.gWord (axisWord c u') 0 := by
    rw [axisWord_append, axisWord_append, gWord_append, gWord_append, Function.comp_apply,
      Function.comp_apply, S.gWord_apply (axisWord c u), S.gWord_apply (axisWord c u'), hd]
    ring
  rw [← key]
  refine S.axisGap_le (by simp [hu]) (by simp [hu']) (by simpa using hne) ?_
  rw [axisWord_append, axisWord_append, gDeriv_append, gDeriv_append, hd]

/-- The gap of the induced system is non-increasing. -/
theorem axisGap_anti [Nonempty ι] (c : ZMod 2) : Antitone (S.axisGap c) :=
  antitone_nat_of_succ_le (S.axisGap_succ_le c)

/-- Exponential separation of the induced system in the form: `Δ_n ≥ r^n` for infinitely
many `n`. -/
theorem axisExpSeparation_iff_frequently (c : ZMod 2) :
    S.AxisExpSeparation c ↔
      ∃ r : ℝ, 0 < r ∧ ∃ᶠ n : ℕ in Filter.atTop, ENNReal.ofReal (r ^ n) ≤ S.axisGap c n := by
  constructor
  · rintro ⟨r, hr, n, hn, h⟩
    exact ⟨r, hr, Filter.frequently_atTop.2 fun N => ⟨n N, hn.id_le N, h N⟩⟩
  · rintro ⟨r, hr, h⟩
    obtain ⟨φ, hφ, hP⟩ := Filter.extraction_of_frequently_atTop h
    exact ⟨r, hr, φ, hφ, hP⟩

/-- Exponential separation of the induced system from `Δ_n ≥ r^n` for infinitely many `n`. -/
theorem axisExpSeparation_of_frequently {c : ZMod 2} {r : ℝ} (hr : 0 < r)
    (h : ∃ᶠ n : ℕ in Filter.atTop, ENNReal.ofReal (r ^ n) ≤ S.axisGap c n) :
    S.AxisExpSeparation c :=
  (S.axisExpSeparation_iff_frequently c).2 ⟨r, hr, h⟩

/-! ### One map -/

/-- For one map there is one planar word of each length, so the gap of the induced system is
the minimum of the empty set, `⊤`. -/
theorem axisGap_eq_top_of_subsingleton [Subsingleton ι] (c : ZMod 2) (n : ℕ) :
    S.axisGap c n = ⊤ := by
  refine le_antisymm le_top ?_
  refine le_iInf fun u => le_iInf fun u' => le_iInf fun hu => le_iInf fun hu' =>
    le_iInf fun hne => le_iInf fun _ => ?_
  exact absurd (List.ext_get (hu.trans hu'.symm) fun k _ _ => Subsingleton.elim _ _) hne

/-- For one map both induced systems are exponentially separated: every gap is `⊤`. -/
theorem axisExpSeparation_of_subsingleton [Subsingleton ι] (c : ZMod 2) :
    S.AxisExpSeparation c :=
  ⟨1, one_pos, id, strictMono_id, fun n => by rw [S.axisGap_eq_top_of_subsingleton]; exact le_top⟩

end System

end BoxLike
