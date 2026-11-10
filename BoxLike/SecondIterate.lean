module

/-
The second iterate `Φ^(2) = (φ_i ∘ φ_j)` of `sec:irreducibility` and the algebraic part of
`thm:two-block-normalisation`.

* `System.sq`: the system `Φ^(2)` over the alphabet `ι × ι`, again box-like.
* `System.sq_mat`, `System.sq_phi`, `System.sq_g`: its matrices are `A_i A_j`, its maps are
  `φ_i ∘ φ_j`, and its projective maps are `g^{(2)}_{(i,j),c} = g_{i,c} ∘ g_{j,c+o(i)}`.
* `System.flat`, `System.gWord_flat`, `System.gDeriv_flat`, `System.flat_injective`: a word of
  `Ψ^(2)` is a word of twice the length of `Ψ`, with the same map.
* `System.gap_two_mul_le_gap_sq`: `Δ_n^{Ψ^(2)} ≥ Δ_{2n}^Ψ`.
* `System.gap_anti`, `System.projExpSeparation_iff_frequently`: the gap is non-increasing, and
  the projective exponential separation condition in its `∃ᶠ` form.
* `System.ProjExpSeparation.sq`: the condition passes from `Φ` to `Φ^(2)`.
-/
public import BoxLike.Separation
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

namespace BoxLike

open Filter
open scoped ENNReal

namespace System

variable {ι : Type*} (S : System ι)

/-- The second iterate `Φ^(2) = (φ_i ∘ φ_j)_{i,j}` of `sec:irreducibility`. -/
def sq : System (ι × ι) where
  o p := S.o p.1 + S.o p.2
  a p := S.a p.1 * S.ratio (p.2, S.o p.1)
  b p := S.b p.1 * S.ratio (p.2, S.o p.1 + 1)
  v p := S.phi p.1 (S.v p.2)
  a_ne_zero p := mul_ne_zero (S.a_ne_zero _) (S.ratio_ne_zero _)
  b_ne_zero p := mul_ne_zero (S.b_ne_zero _) (S.ratio_ne_zero _)
  abs_a_lt_one p := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) (S.abs_ratio_lt_one _).le).trans_lt
      (S.abs_a_lt_one _)
  abs_b_lt_one p := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) (S.abs_ratio_lt_one _).le).trans_lt
      (S.abs_b_lt_one _)

/-- The linear parts of `Φ^(2)` are the products `A_i A_j`. -/
theorem sq_mat (p : ι × ι) : S.sq.mat p = S.mat p.1 * S.mat p.2 := by
  rw [mat, mat, mat, boxMat_mul]
  rcases zmod_two_cases (S.o p.1) with h | h <;>
    simp [sq, ratio, h, show (1 : ZMod 2) + 1 = 0 from by decide]

theorem sq_ratio (p : ι × ι) (c : ZMod 2) :
    S.sq.ratio (p, c) = S.ratio (p.1, c) * S.ratio (p.2, c + S.o p.1) := by
  rcases zmod_two_cases c with rfl | rfl
  · simp [ratio, sq]
  · simp [ratio, sq, add_comm]

theorem sq_trans (p : ι × ι) (c : ZMod 2) :
    S.sq.trans (p, c) = S.g (p.1, c) (S.trans (p.2, c + S.o p.1)) := by
  change coord c (S.phi p.1 (S.v p.2)) = _
  rw [coord_phi]
  rfl

/-- `g^{(2)}_{(i,j),c} = g_{i,c} ∘ g_{j,c+o(i)}`, from the proof of
`thm:two-block-normalisation`. -/
theorem sq_g (p : ι × ι) (c : ZMod 2) (t : ℝ) :
    S.sq.g (p, c) t = S.g (p.1, c) (S.g (p.2, c + S.o p.1) t) := by
  rw [g, sq_ratio, sq_trans]
  simp only [g]
  ring

/-- The maps of `Φ^(2)` are the compositions `φ_i ∘ φ_j`. -/
theorem sq_phi (p : ι × ι) (z : ℝ × ℝ) : S.sq.phi p z = S.phi p.1 (S.phi p.2 z) := by
  have h : ∀ c : ZMod 2, coord c (S.sq.phi p z) = coord c (S.phi p.1 (S.phi p.2 z)) := by
    intro c
    rw [coord_phi, coord_phi, coord_phi, sq_g]
    change S.g _ (S.g _ (coord (c + (S.o p.1 + S.o p.2)) z)) = _
    rw [add_assoc]
  exact Prod.ext (h 0) (h 1)

/-- A word of `Ψ^(2)` as a word of twice the length of `Ψ`. -/
def flat : List ((ι × ι) × ZMod 2) → List (ι × ZMod 2)
  | [] => []
  | q :: u => (q.1.1, q.2) :: (q.1.2, q.2 + S.o q.1.1) :: flat u

@[simp] theorem flat_nil : S.flat [] = [] := rfl

@[simp] theorem flat_cons (q : (ι × ι) × ZMod 2) (u : List ((ι × ι) × ZMod 2)) :
    S.flat (q :: u) = (q.1.1, q.2) :: (q.1.2, q.2 + S.o q.1.1) :: S.flat u := rfl

@[simp] theorem length_flat (u : List ((ι × ι) × ZMod 2)) :
    (S.flat u).length = 2 * u.length := by
  induction u with
  | nil => rfl
  | cons q u ih => simp [ih]; ring

theorem gWord_flat (u : List ((ι × ι) × ZMod 2)) : S.gWord (S.flat u) = S.sq.gWord u := by
  induction u with
  | nil => rfl
  | cons q u ih =>
    funext t
    simp only [flat_cons, gWord_cons, Function.comp_apply, ih]
    exact (S.sq_g q.1 q.2 _).symm

theorem gDeriv_flat (u : List ((ι × ι) × ZMod 2)) : S.gDeriv (S.flat u) = S.sq.gDeriv u := by
  induction u with
  | nil => rfl
  | cons q u ih =>
    simp only [flat_cons, gDeriv_cons, ih]
    rw [show q = (q.1, q.2) from rfl, sq_ratio, mul_assoc]

theorem flat_injective : Function.Injective S.flat := by
  intro u
  induction u with
  | nil =>
    intro u' h
    cases u' with
    | nil => rfl
    | cons q' u' => simp at h
  | cons q u ih =>
    intro u' h
    cases u' with
    | nil => simp at h
    | cons q' u' =>
      simp only [flat_cons, List.cons.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨h1, h2⟩, ⟨h3, -⟩, h5⟩ := h
      have hq : q = q' := Prod.ext (Prod.ext h1 h3) h2
      rw [hq, ih h5]

/-- `Δ_n^{Ψ^(2)} ≥ Δ_{2n}^Ψ`: distinct words of length `n` of `Ψ^(2)` give distinct words of
length `2n` of `Ψ` with the same maps. -/
theorem gap_two_mul_le_gap_sq (n : ℕ) : S.gap (2 * n) ≤ S.sq.gap n := by
  refine le_iInf fun u => le_iInf fun u' => le_iInf fun hu => le_iInf fun hu' =>
    le_iInf fun hne => le_iInf fun hd => ?_
  rw [← gWord_flat, ← gWord_flat]
  refine S.gap_le (by simp [hu]) (by simp [hu']) (fun h => hne (S.flat_injective h)) ?_
  rw [gDeriv_flat, gDeriv_flat, hd]

/-- The projective gap is non-increasing. -/
theorem gap_anti [Nonempty ι] : Antitone S.gap :=
  antitone_nat_of_succ_le S.gap_succ_le

/-- The projective exponential separation condition in the form: `Δ_n^Ψ ≥ c^n` for
infinitely many `n`. -/
theorem projExpSeparation_iff_frequently :
    S.ProjExpSeparation ↔
      ∃ c : ℝ, 0 < c ∧ ∃ᶠ n : ℕ in atTop, ENNReal.ofReal (c ^ n) ≤ S.gap n := by
  constructor
  · rintro ⟨c, hc, n, hn, h⟩
    refine ⟨c, hc, frequently_atTop.2 fun N => ⟨n N, hn.id_le N, h N⟩⟩
  · rintro ⟨c, hc, h⟩
    obtain ⟨φ, hφ, hP⟩ := extraction_of_frequently_atTop h
    exact ⟨c, hc, φ, hφ, hP⟩

/-- The absence of projective exact overlaps passes from `Φ` to `Φ^(2)` (proof of `thm:main2`,
tex lines 3456 to 3458): a word of `Ψ^(2)` is a word of `Ψ` of twice the length with the same
map, and this correspondence is injective. -/
theorem NoExactOverlaps.sq (h : S.NoExactOverlaps) : S.sq.NoExactOverlaps := by
  rw [noExactOverlaps_iff] at h ⊢
  intro u u' huu'
  exact S.flat_injective (h (by rw [S.gWord_flat, S.gWord_flat, huu']))

/-- `thm:two-block-normalisation`, separation part: the projective exponential separation
condition passes from `Φ` to `Φ^(2)`. -/
theorem ProjExpSeparation.sq [Nonempty ι] (h : S.ProjExpSeparation) :
    S.sq.ProjExpSeparation := by
  obtain ⟨c₀, hc₀, hfreq⟩ := S.projExpSeparation_iff_frequently.1 h
  -- The constant may be taken at most one.
  set c : ℝ := min c₀ 1 with hc_def
  have hc : 0 < c := lt_min hc₀ one_pos
  have hc1 : c ≤ 1 := min_le_right _ _
  have hfreq' : ∃ᶠ n : ℕ in atTop, ENNReal.ofReal (c ^ n) ≤ S.gap n :=
    hfreq.mono fun n hn =>
      (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hc.le (min_le_left _ _) n)).trans hn
  refine S.sq.projExpSeparation_iff_frequently.2 ⟨c ^ 3, pow_pos hc 3, ?_⟩
  refine frequently_atTop.2 fun N => ?_
  obtain ⟨n, hnN, hn⟩ := frequently_atTop.1 hfreq' (2 * N + 2)
  refine ⟨n / 2, by omega, ?_⟩
  have hm1 : 1 ≤ n / 2 := by omega
  have h2m : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  have hle : n ≤ 3 * (n / 2) := by omega
  calc ENNReal.ofReal ((c ^ 3) ^ (n / 2))
      = ENNReal.ofReal (c ^ (3 * (n / 2))) := by rw [← pow_mul]
    _ ≤ ENNReal.ofReal (c ^ n) :=
        ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hc.le hc1 hle)
    _ ≤ S.gap n := hn
    _ ≤ S.gap (2 * (n / 2)) := S.gap_anti h2m
    _ ≤ S.sq.gap (n / 2) := S.gap_two_mul_le_gap_sq (n / 2)

end System

end BoxLike
