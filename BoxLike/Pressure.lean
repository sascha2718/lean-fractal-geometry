module

/-
The singular value pressure `P(𝖠, s)` of `sec:affinity_dim`.

* `sum_ofFn_add`: sums over words of length `k + n` as iterated sums, copied from
  `GeometricMeasureTheory/Pressure/Gibbs.lean` of the `GeometricMeasureTheory` library.
* `System.svfSum`, `System.svfSum_add_le`: the sums `∑_{|𝐢| = n} φ^s(A_𝐢)` and their
  sub-multiplicativity.
* `System.RatioLowerBound`, `System.exists_ratioLowerBound`,
  `System.RatioLowerBound.le_svf_matWord`: `φ^s(A_𝐢) ≥ δ^{s|𝐢|}` when every
  `|a_i|, |b_i| ≥ δ`, and such a `δ > 0` exists for a finite system.
* `System.pressure`, `System.RatioLowerBound.tendsto_pressure`: the pressure, and the
  existence of the limit defining it by Fekete's lemma.
-/
public import BoxLike.SingularValue
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace BoxLike

open Filter Topology

/-- Splitting a word of length `k + n` into its first `k` and its last `n` letters reindexes a
sum over the words of length `k + n` as an iterated sum over the two halves. -/
theorem sum_ofFn_add {ι M : Type*} [Fintype ι] [AddCommMonoid M] (k n : ℕ) (G : List ι → M) :
    ∑ f : Fin (k + n) → ι, G (List.ofFn f)
      = ∑ g : Fin k → ι, ∑ h : Fin n → ι, G (List.ofFn g ++ List.ofFn h) :=
  calc ∑ f : Fin (k + n) → ι, G (List.ofFn f)
      = ∑ p : (Fin k → ι) × (Fin n → ι), G (List.ofFn p.1 ++ List.ofFn p.2) :=
        (Fintype.sum_equiv (Fin.appendEquiv k n) _ _ fun x => by simp [Fin.appendEquiv]).symm
    _ = ∑ g : Fin k → ι, ∑ h : Fin n → ι, G (List.ofFn g ++ List.ofFn h) :=
        Fintype.sum_prod_type _

namespace System

variable {ι : Type*} (S : System ι)

theorem matWord_append (w w' : List ι) : S.matWord (w ++ w') = S.matWord w * S.matWord w' := by
  simp [matWord]

/-- Every `|a_i|` and `|b_i|` is at least `δ`. -/
def RatioLowerBound (δ : ℝ) : Prop := 0 < δ ∧ ∀ p, δ ≤ |S.ratio p|

/-- A finite non-empty system has a positive lower bound for its contraction ratios. -/
theorem exists_ratioLowerBound [Finite ι] [Nonempty ι] : ∃ δ, S.RatioLowerBound δ := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨p, -, hp⟩ := Finset.exists_min_image Finset.univ (fun p => |S.ratio p|)
    Finset.univ_nonempty
  exact ⟨|S.ratio p|, abs_pos.2 (S.ratio_ne_zero p), fun q => hp q (Finset.mem_univ _)⟩

variable {S} {δ : ℝ}

theorem RatioLowerBound.le_abs_gDeriv (hδ : S.RatioLowerBound δ) (u : List (ι × ZMod 2)) :
    δ ^ u.length ≤ |S.gDeriv u| := by
  induction u with
  | nil => simp
  | cons p u ih =>
    rw [gDeriv_cons, abs_mul, List.length_cons, pow_succ']
    exact mul_le_mul (hδ.2 p) ih (pow_nonneg hδ.1.le _) (abs_nonneg _)

/-- `φ^s(A) ≥ α_2(A)^s` for a diagonal or anti-diagonal matrix with non-zero entries. -/
theorem _root_.BoxLike.le_svf_boxMat {s : ℝ} (hs : 0 ≤ s) (c : ZMod 2) {a b : ℝ} (ha : a ≠ 0)
    (hb : b ≠ 0) : min |a| |b| ^ s ≤ svf s (boxMat c a b) := by
  have hmin : 0 < min |a| |b| := lt_min (abs_pos.2 ha) (abs_pos.2 hb)
  have hle : min |a| |b| ≤ max |a| |b| := min_le_max
  rcases le_or_gt s 1 with h1 | h1
  · rw [svf_boxMat_of_le_one h1]
    exact Real.rpow_le_rpow hmin.le hle hs
  rcases le_or_gt s 2 with h2 | h2
  · rw [svf_boxMat_of_le_two h1 h2 c b ha]
    calc min |a| |b| ^ s = min |a| |b| ^ (1 + (s - 1)) := by ring_nf
      _ = min |a| |b| * min |a| |b| ^ (s - 1) := by
        rw [Real.rpow_add hmin, Real.rpow_one]
      _ ≤ max |a| |b| * min |a| |b| ^ (s - 1) :=
        mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hmin.le _)
  · rw [svf_boxMat_of_two_lt h2]
    calc min |a| |b| ^ s = min |a| |b| ^ (s / 2 + s / 2) := by ring_nf
      _ = (min |a| |b| * min |a| |b|) ^ (s / 2) := by
        rw [Real.rpow_add hmin, Real.mul_rpow hmin.le hmin.le]
      _ ≤ (max |a| |b| * min |a| |b|) ^ (s / 2) :=
        Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_right hle hmin.le)
          (by linarith)

/-- `φ^s(A_𝐢) ≥ δ^{s |𝐢|}` when every `|a_i|` and `|b_i|` is at least `δ`. -/
theorem RatioLowerBound.le_svf_matWord (hδ : S.RatioLowerBound δ) {s : ℝ} (hs : 0 ≤ s)
    (w : List ι) : (δ ^ w.length) ^ s ≤ svf s (S.matWord w) := by
  rw [matWord_eq]
  refine le_trans ?_ (le_svf_boxMat hs _ (S.gDeriv_ne_zero _) (S.gDeriv_ne_zero _))
  refine Real.rpow_le_rpow (pow_nonneg hδ.1.le _) (le_min ?_ ?_) hs
  · simpa using hδ.le_abs_gDeriv (S.codeWord 0 w)
  · simpa using hδ.le_abs_gDeriv (S.codeWord 1 w)

variable (S) [Fintype ι]

/-- The sum `∑_{|𝐢| = n} φ^s(A_𝐢)` of `sec:affinity_dim`. -/
noncomputable def svfSum (s : ℝ) (n : ℕ) : ℝ :=
  ∑ w : Fin n → ι, svf s (S.matWord (List.ofFn w))

/-- The sums `∑_{|𝐢| = n} φ^s(A_𝐢)` are sub-multiplicative in `n`. -/
theorem svfSum_add_le {s : ℝ} (hs : 0 ≤ s) (m n : ℕ) :
    S.svfSum s (m + n) ≤ S.svfSum s m * S.svfSum s n := by
  rw [svfSum, sum_ofFn_add m n fun w => svf s (S.matWord w), svfSum, svfSum,
    Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun h _ => ?_
  rw [matWord_append]
  exact svf_mul_le hs _ _

variable {S}

theorem RatioLowerBound.le_svfSum [Nonempty ι] (hδ : S.RatioLowerBound δ) {s : ℝ} (hs : 0 ≤ s)
    (n : ℕ) : (δ ^ n) ^ s ≤ S.svfSum s n := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have h := hδ.le_svf_matWord hs (List.ofFn fun _ : Fin n => i)
  rw [List.length_ofFn] at h
  refine h.trans ?_
  exact Finset.single_le_sum (f := fun w : Fin n → ι => svf s (S.matWord (List.ofFn w)))
    (fun w _ => svf_nonneg _ _) (Finset.mem_univ _)

theorem RatioLowerBound.svfSum_pos [Nonempty ι] (hδ : S.RatioLowerBound δ) {s : ℝ} (hs : 0 ≤ s)
    (n : ℕ) : 0 < S.svfSum s n :=
  lt_of_lt_of_le (Real.rpow_pos_of_pos (pow_pos hδ.1 _) _) (hδ.le_svfSum hs n)

/-- The sequence `log ∑_{|𝐢| = n} φ^s(A_𝐢)` is sub-additive. -/
theorem RatioLowerBound.subadditive [Nonempty ι] (hδ : S.RatioLowerBound δ) {s : ℝ}
    (hs : 0 ≤ s) : Subadditive fun n => Real.log (S.svfSum s n) := by
  intro m n
  rw [← Real.log_mul (hδ.svfSum_pos hs m).ne' (hδ.svfSum_pos hs n).ne']
  exact Real.log_le_log (hδ.svfSum_pos hs _) (S.svfSum_add_le hs m n)

theorem RatioLowerBound.bddBelow [Nonempty ι] (hδ : S.RatioLowerBound δ) {s : ℝ} (hs : 0 ≤ s) :
    BddBelow (Set.range fun n : ℕ => Real.log (S.svfSum s n) / n) := by
  refine ⟨min 0 (s * Real.log δ), ?_⟩
  rintro _ ⟨n, rfl⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    refine (min_le_right _ _).trans ?_
    rw [le_div_iff₀ hn']
    have h := Real.log_le_log (Real.rpow_pos_of_pos (pow_pos hδ.1 _) _) (hδ.le_svfSum hs n)
    rw [Real.log_rpow (pow_pos hδ.1 _), Real.log_pow] at h
    linarith [h, mul_comm (s * Real.log δ) (n : ℝ), mul_assoc s (n : ℝ) (Real.log δ),
      mul_left_comm s (n : ℝ) (Real.log δ)]

variable (S)

/-- The singular value pressure `P(𝖠, s)` of `sec:affinity_dim`. -/
noncomputable def pressure (s : ℝ) : ℝ :=
  sInf ((fun n : ℕ => Real.log (S.svfSum s n) / n) '' Set.Ici 1)

variable {S}

/-- The limit defining `P(𝖠, s)` exists, by Fekete's lemma. -/
theorem RatioLowerBound.tendsto_pressure [Nonempty ι] (hδ : S.RatioLowerBound δ) {s : ℝ}
    (hs : 0 ≤ s) :
    Tendsto (fun n : ℕ => Real.log (S.svfSum s n) / n) atTop (𝓝 (S.pressure s)) := by
  have h := (hδ.subadditive hs).tendsto_lim (hδ.bddBelow hs)
  rwa [Subadditive.lim] at h

end System

end BoxLike
