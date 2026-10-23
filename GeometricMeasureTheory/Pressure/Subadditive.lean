/-
# Section 7.1: Subadditivity and limits

Fekete's lemma and its quasi-subadditive form. Fekete's lemma itself is in Mathlib as
`Subadditive.tendsto_lim`; the quasi-subadditive corollary and the quasi-multiplicative form used
for the partition sums of Section 7.2 are proved here.

| Notes | Lean declaration | Location |
|---|---|---|
| Definition 7.4 (subadditive) | `Subadditive` | `Mathlib/Analysis/Subadditive.lean` |
| Definition 7.4 (quasi-subadditive) | `IsQuasiSubadditive` | here |
| Lemma 7.5 (Fekete's lemma) | `Subadditive.tendsto_lim`, `Subadditive.lim_le_div` | `Mathlib/Analysis/Subadditive.lean` |
| Corollary 7.6 (`thm:quasi-subadditive-limit`) | `quasi_subadditive_limit` | here |
| Equation (7.1), the two-sided bound on the partition sums | `exists_tendsto_log_div_of_quasiMultiplicative` | here |
-/
import GeometricMeasureTheory.CookieCutter.Basic

open Filter Topology Set

open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

/-- Definition 7.4: a sequence is quasi-subadditive with constant `c` if
`a (n + m) ≤ a n + a m + c`. -/
def IsQuasiSubadditive (u : ℕ → ℝ) (c : ℝ) : Prop := ∀ m n, u (m + n) ≤ u m + u n + c

/-- Lemma 7.5 (Fekete's lemma) is Mathlib's `Subadditive.tendsto_lim`. -/
example (u : ℕ → ℝ) (h : Subadditive u) (hbdd : BddBelow (Set.range fun n => u n / n)) :
    Tendsto (fun n => u n / n) atTop (𝓝 h.lim) := h.tendsto_lim hbdd

/-- If the slopes `u n / n` are bounded below along the positive integers then the whole range of
slopes is bounded below, because the term at `n = 0` is `u 0 / 0 = 0`. -/
private theorem bddBelow_range_div_of_forall_pos {u : ℕ → ℝ} {C : ℝ}
    (h : ∀ n : ℕ, 0 < n → C ≤ u n / n) : BddBelow (Set.range fun n : ℕ => u n / n) := by
  refine ⟨min C 0, fun x hx => ?_⟩
  obtain ⟨n, rfl⟩ := hx
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (min_le_left C 0).trans (h n hn)

/-- Corollary 7.6 (`thm:quasi-subadditive-limit`): a quasi-subadditive sequence bounded below has a
limiting slope, and every term is at least that slope minus the constant. -/
theorem quasi_subadditive_limit {u : ℕ → ℝ} {c : ℝ} (h : IsQuasiSubadditive u c)
    (hbdd : BddBelow (Set.range fun n => u n / n)) :
    ∃ a : ℝ, Tendsto (fun n => u n / n) atTop (𝓝 a) ∧ ∀ n : ℕ, 0 < n → n * a - c ≤ u n := by
  -- shifting by the constant turns quasi-subadditivity into subadditivity
  have hsub : Subadditive fun n => u n + c := fun m n => by
    have hmn := h m n
    show u (m + n) + c ≤ u m + c + (u n + c)
    linarith
  obtain ⟨B, hB⟩ := hbdd
  have hBle : ∀ n : ℕ, B ≤ u n / n := fun n => hB ⟨n, rfl⟩
  have hbdd' : BddBelow (Set.range fun n : ℕ => (u n + c) / n) := by
    refine bddBelow_range_div_of_forall_pos (C := B - |c|) fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have habs : |c / (n : ℝ)| ≤ |c| := by
      rw [abs_div, abs_of_pos hn0]
      exact div_le_self (abs_nonneg c) hn1
    have hcn : -|c| ≤ c / (n : ℝ) := (neg_le_neg habs).trans (neg_abs_le _)
    have hsplit : (u n + c) / (n : ℝ) = u n / n + c / n := by ring
    rw [hsplit]
    linarith [hBle n]
  refine ⟨hsub.lim, ?_, fun n hn => ?_⟩
  · have hlim : Tendsto (fun n : ℕ => (u n + c) / n) atTop (𝓝 hsub.lim) := hsub.tendsto_lim hbdd'
    have hc0 : Tendsto (fun n : ℕ => c / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat c
    have hdiff := hlim.sub hc0
    rw [sub_zero] at hdiff
    refine hdiff.congr fun n => ?_
    show (u n + c) / (n : ℝ) - c / n = u n / n
    ring
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hle : hsub.lim ≤ (u n + c) / n := hsub.lim_le_div hbdd' hn.ne'
    rw [le_div_iff₀ hn0] at hle
    linarith

/-- Equation (7.1): a quasi-multiplicative sequence of positive reals grows exponentially at a
well-defined rate, and each term is within a fixed factor of the exponential. This is the form in
which Fekete's lemma is used for the partition sums of Section 7.2. -/
theorem exists_tendsto_log_div_of_quasiMultiplicative {s : ℕ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hpos : ∀ k, 0 < s k)
    (h : ∀ k m, Real.exp (-b) * (s k * s m) ≤ s (k + m) ∧ s (k + m) ≤ Real.exp b * (s k * s m)) :
    ∃ P : ℝ, Tendsto (fun k : ℕ => Real.log (s k) / k) atTop (𝓝 P) ∧
      ∀ k : ℕ, Real.exp (-b) * Real.exp (k * P) ≤ s k ∧ s k ≤ Real.exp b * Real.exp (k * P) := by
  have hexp : Real.exp (-b) * Real.exp b = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hs1 : (0 : ℝ) < s 1 := hpos 1
  -- the hypothesis at `k = m = 0` pins `s 0` into the interval `[exp (-b), exp b]`
  have h0lb : Real.exp (-b) * (s 0 * s 0) ≤ s 0 := (h 0 0).1
  have h0ub : s 0 ≤ Real.exp b * (s 0 * s 0) := (h 0 0).2
  have hs0lb : Real.exp (-b) ≤ s 0 := by
    have hkey : (1 : ℝ) ≤ Real.exp b * s 0 := by nlinarith [hpos 0, h0ub]
    nlinarith [Real.exp_pos b, Real.exp_pos (-b), hexp, hkey]
  have hs0ub : s 0 ≤ Real.exp b := by
    have hkey : Real.exp (-b) * s 0 ≤ 1 := by nlinarith [hpos 0, h0lb]
    nlinarith [Real.exp_pos b, Real.exp_pos (-b), hexp, hkey]
  -- geometric bounds obtained by iterating the hypothesis in the step `k ↦ k + 1`
  have hApos : (0 : ℝ) < Real.exp (-b) * s 1 := mul_pos (Real.exp_pos _) hs1
  have hBpos : (0 : ℝ) < Real.exp b * s 1 := mul_pos (Real.exp_pos _) hs1
  have hlow : ∀ k : ℕ, Real.exp (-b) * (Real.exp (-b) * s 1) ^ k ≤ s k := by
    intro k
    induction k with
    | zero => simpa using hs0lb
    | succ k ih =>
      calc Real.exp (-b) * (Real.exp (-b) * s 1) ^ (k + 1)
          = Real.exp (-b) * (Real.exp (-b) * s 1) ^ k * (Real.exp (-b) * s 1) := by ring
        _ ≤ s k * (Real.exp (-b) * s 1) := mul_le_mul_of_nonneg_right ih hApos.le
        _ = Real.exp (-b) * (s k * s 1) := by ring
        _ ≤ s (k + 1) := (h k 1).1
  have hhigh : ∀ k : ℕ, s k ≤ Real.exp b * (Real.exp b * s 1) ^ k := by
    intro k
    induction k with
    | zero => simpa using hs0ub
    | succ k ih =>
      calc s (k + 1) ≤ Real.exp b * (s k * s 1) := (h k 1).2
        _ = s k * (Real.exp b * s 1) := by ring
        _ ≤ Real.exp b * (Real.exp b * s 1) ^ k * (Real.exp b * s 1) :=
            mul_le_mul_of_nonneg_right ih hBpos.le
        _ = Real.exp b * (Real.exp b * s 1) ^ (k + 1) := by ring
  -- the two quasi-subadditive sequences and their bounded-below slopes
  have hL : IsQuasiSubadditive (fun k => Real.log (s k)) b := by
    intro m n
    have hlg := Real.log_le_log (hpos (m + n)) (h m n).2
    rw [Real.log_mul (Real.exp_ne_zero b) (mul_pos (hpos m) (hpos n)).ne', Real.log_exp,
      Real.log_mul (hpos m).ne' (hpos n).ne'] at hlg
    show Real.log (s (m + n)) ≤ Real.log (s m) + Real.log (s n) + b
    linarith
  have hLneg : IsQuasiSubadditive (fun k => -Real.log (s k)) b := by
    intro m n
    have hlg := Real.log_le_log
      (mul_pos (Real.exp_pos (-b)) (mul_pos (hpos m) (hpos n))) (h m n).1
    rw [Real.log_mul (Real.exp_ne_zero _) (mul_pos (hpos m) (hpos n)).ne', Real.log_exp,
      Real.log_mul (hpos m).ne' (hpos n).ne'] at hlg
    show -Real.log (s (m + n)) ≤ -Real.log (s m) + -Real.log (s n) + b
    linarith
  have hbddL : BddBelow (Set.range fun k : ℕ => Real.log (s k) / k) := by
    refine bddBelow_range_div_of_forall_pos
      (C := Real.log (Real.exp (-b) * s 1) - b) fun k hk => ?_
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [le_div_iff₀ hk0]
    have hlg := Real.log_le_log (mul_pos (Real.exp_pos (-b)) (pow_pos hApos k)) (hlow k)
    rw [Real.log_mul (Real.exp_ne_zero _) (pow_pos hApos k).ne', Real.log_exp,
      Real.log_pow] at hlg
    nlinarith [hlg, mul_nonneg hb (by linarith : (0 : ℝ) ≤ (k : ℝ) - 1)]
  have hbddU : BddBelow (Set.range fun k : ℕ => -Real.log (s k) / k) := by
    refine bddBelow_range_div_of_forall_pos
      (C := -Real.log (Real.exp b * s 1) - b) fun k hk => ?_
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [le_div_iff₀ hk0]
    have hlg := Real.log_le_log (hpos k) (hhigh k)
    rw [Real.log_mul (Real.exp_ne_zero _) (pow_pos hBpos k).ne', Real.log_exp,
      Real.log_pow] at hlg
    nlinarith [hlg, mul_nonneg hb (by linarith : (0 : ℝ) ≤ (k : ℝ) - 1)]
  obtain ⟨P, hPtend, hPle⟩ := quasi_subadditive_limit hL hbddL
  obtain ⟨Q, hQtend, hQle⟩ := quasi_subadditive_limit hLneg hbddU
  have hQP : Q = -P := by
    refine tendsto_nhds_unique hQtend ?_
    refine hPtend.neg.congr fun k => ?_
    show -(Real.log (s k) / (k : ℝ)) = -Real.log (s k) / k
    rw [neg_div]
  refine ⟨P, hPtend, fun k => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨by simpa using hs0lb, by simpa using hs0ub⟩
  · have h1 : (k : ℝ) * P - b ≤ Real.log (s k) := hPle k hk
    have h2 : (k : ℝ) * Q - b ≤ -Real.log (s k) := hQle k hk
    rw [hQP] at h2
    refine ⟨?_, ?_⟩
    · calc Real.exp (-b) * Real.exp ((k : ℝ) * P)
          = Real.exp ((k : ℝ) * P - b) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ s k := (Real.le_log_iff_exp_le (hpos k)).1 h1
    · calc s k ≤ Real.exp ((k : ℝ) * P + b) :=
          (Real.log_le_iff_le_exp (hpos k)).1 (by linarith)
        _ = Real.exp b * Real.exp ((k : ℝ) * P) := by rw [← Real.exp_add]; congr 1; ring

end GeometricMeasureTheory
