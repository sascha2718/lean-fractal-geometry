/-
# Section 4.5: Different behaviour at different scales

The digit-position sets of the notes: prescribing which binary digits are free produces a compact
set whose lower and upper box dimensions are the lower and upper densities of the set of free
positions. Choosing the free positions in long alternating blocks separates the two box dimensions,
and shows that the lower box dimension is not finitely stable.

| Notes | Lean declaration | Location |
|---|---|---|
| The digit-position set `E_A` | `digitSet`, `isCompact_digitSet` | here |
| The coding map and its covers | `digitCode`, `digitSum`, `digitCover`, `digitPoints` | here |
| The counting function `k(n)` | `freeFinset`, `freeDensity` | here |
| Its box dimensions | `box_digitSet`, `lowerBoxDim_digitSet`, `upperBoxDim_digitSet` | here |
| The alternating blocks of free positions | `blockEnd`, `blockSet` | here |
| Affine copies of the tail set | `shiftSet`, `digitCode_append`, `affine_tail_subset` | here |
| Separating the two box dimensions | `exists_lowerBoxDim_zero_upperBoxDim_one` | here |
| Failure of finite stability for the lower box dimension | `exists_lowerBoxDim_union_lt` | here |
-/
import GeometricMeasureTheory.Box.ModifiedBox

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

/-- The set of numbers in `[0, 1]` whose binary digits vanish outside the position set `A`. -/
def digitSet (A : Set ℕ) : Set ℝ :=
  {x | ∃ a : ℕ → Bool, (∀ j, a j = true → j ∈ A) ∧
    x = ∑' j : ℕ, if a j then (2 : ℝ) ^ (-(j : ℝ) - 1) else 0}

/-! ## The coding map

The digit weights `2^{-j-1}` are handled as ordinary powers rather than as real powers, and the
coding map is the sum of the retained weights. -/

/-- The real power in the definition of `digitSet` is an ordinary power. -/
theorem two_rpow_neg_sub_one (j : ℕ) : (2 : ℝ) ^ (-(j : ℝ) - 1) = ((2 : ℝ) ^ (j + 1))⁻¹ := by
  rw [show -(j : ℝ) - 1 = -((j + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg (by norm_num),
    Real.rpow_natCast]

/-- The admissible digit sequences for the position set `A`. -/
def digitSeqs (A : Set ℕ) : Set (ℕ → Bool) := {a | ∀ j, a j = true → j ∈ A}

/-- The coding map: the number with binary digits `a`. -/
def digitCode (a : ℕ → Bool) : ℝ := ∑' j : ℕ, if a j then ((2 : ℝ) ^ (j + 1))⁻¹ else 0

theorem digitTerm_nonneg (a : ℕ → Bool) (j : ℕ) :
    0 ≤ if a j then ((2 : ℝ) ^ (j + 1))⁻¹ else 0 := by
  split_ifs <;> positivity

theorem digitTerm_le (a : ℕ → Bool) (j : ℕ) :
    (if a j then ((2 : ℝ) ^ (j + 1))⁻¹ else 0) ≤ ((2 : ℝ) ^ (j + 1))⁻¹ := by
  split_ifs
  · exact le_rfl
  · positivity

/-- The digit weights form a convergent geometric series. -/
theorem summable_inv_two_pow_succ : Summable fun j : ℕ => ((2 : ℝ) ^ (j + 1))⁻¹ := by
  have h : ∀ j : ℕ, ((2 : ℝ) ^ (j + 1))⁻¹ = (2 : ℝ)⁻¹ ^ j * 2⁻¹ := by
    intro j; rw [← inv_pow, pow_succ]
  simp_rw [h]
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _

/-- The digit weights from position `n` on sum to `2^{-n}`. -/
theorem tsum_inv_two_pow_succ_add (n : ℕ) :
    ∑' i : ℕ, ((2 : ℝ) ^ (i + n + 1))⁻¹ = ((2 : ℝ) ^ n)⁻¹ := by
  have h : ∀ i : ℕ, ((2 : ℝ) ^ (i + n + 1))⁻¹ = ((2 : ℝ)⁻¹ ^ i * 2⁻¹) * ((2 : ℝ) ^ n)⁻¹ := by
    intro i
    rw [← inv_pow, ← inv_pow, pow_add, pow_succ]
    ring
  simp_rw [h, tsum_mul_right,
    tsum_geometric_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)]
  norm_num

/-- All the digit weights sum to one. -/
theorem tsum_inv_two_pow_succ : ∑' j : ℕ, ((2 : ℝ) ^ (j + 1))⁻¹ = 1 := by
  simpa using tsum_inv_two_pow_succ_add 0

theorem summable_digitCode (a : ℕ → Bool) :
    Summable fun j : ℕ => if a j then ((2 : ℝ) ^ (j + 1))⁻¹ else 0 :=
  Summable.of_nonneg_of_le (digitTerm_nonneg a) (digitTerm_le a) summable_inv_two_pow_succ

/-- The coding map takes values in `[0, 1]`. -/
theorem digitCode_mem_Icc (a : ℕ → Bool) : digitCode a ∈ Icc (0 : ℝ) 1 := by
  refine ⟨tsum_nonneg (digitTerm_nonneg a), ?_⟩
  calc digitCode a ≤ ∑' j : ℕ, ((2 : ℝ) ^ (j + 1))⁻¹ :=
        Summable.tsum_le_tsum (digitTerm_le a) (summable_digitCode a) summable_inv_two_pow_succ
    _ = 1 := tsum_inv_two_pow_succ

theorem digitCode_nonneg (a : ℕ → Bool) : 0 ≤ digitCode a := (digitCode_mem_Icc a).1

theorem digitCode_le_one (a : ℕ → Bool) : digitCode a ≤ 1 := (digitCode_mem_Icc a).2

/-- The digit-position set is the image of the admissible sequences under the coding map. -/
theorem digitSet_eq_image (A : Set ℕ) : digitSet A = digitCode '' digitSeqs A := by
  ext x
  simp only [digitSet, digitSeqs, digitCode, mem_setOf_eq, mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, by simp_rw [two_rpow_neg_sub_one]⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, by simp_rw [two_rpow_neg_sub_one]⟩

theorem digitCode_mem_digitSet {A : Set ℕ} {a : ℕ → Bool} (ha : a ∈ digitSeqs A) :
    digitCode a ∈ digitSet A := by
  rw [digitSet_eq_image]; exact mem_image_of_mem _ ha

theorem digitSet_subset_Icc (A : Set ℕ) : digitSet A ⊆ Icc (0 : ℝ) 1 := by
  rw [digitSet_eq_image]
  rintro _ ⟨a, -, rfl⟩
  exact digitCode_mem_Icc a

theorem zero_mem_digitSet (A : Set ℕ) : (0 : ℝ) ∈ digitSet A := by
  have h : digitCode (fun _ => false) = 0 := by simp [digitCode]
  simpa [h] using digitCode_mem_digitSet (A := A) (a := fun _ => false) (by simp [digitSeqs])

theorem digitSet_nonempty (A : Set ℕ) : (digitSet A).Nonempty := ⟨0, zero_mem_digitSet A⟩

/-- The coding map is continuous. -/
theorem continuous_digitCode : Continuous digitCode := by
  show Continuous fun a : ℕ → Bool => ∑' j : ℕ, if a j then ((2 : ℝ) ^ (j + 1))⁻¹ else 0
  refine continuous_tsum (u := fun j : ℕ => ((2 : ℝ) ^ (j + 1))⁻¹) (fun j => ?_)
    summable_inv_two_pow_succ (fun j a => ?_)
  · exact (continuous_of_discreteTopology
      (f := fun b : Bool => if b then ((2 : ℝ) ^ (j + 1))⁻¹ else 0)).comp (continuous_apply j)
  · rw [Real.norm_eq_abs, abs_of_nonneg (digitTerm_nonneg a j)]
    exact digitTerm_le a j

/-- The admissible sequences form a closed subset of the compact space `ℕ → Bool`. -/
theorem isClosed_digitSeqs (A : Set ℕ) : IsClosed (digitSeqs A) := by
  have h : digitSeqs A = ⋂ j : ℕ, (fun a : ℕ → Bool => a j) ⁻¹' {b : Bool | b = true → j ∈ A} := by
    ext a; simp [digitSeqs, Set.mem_iInter]
  rw [h]
  exact isClosed_iInter fun j => (isClosed_discrete _).preimage (continuous_apply j)

/-- The digit-position set is compact. -/
theorem isCompact_digitSet (A : Set ℕ) : IsCompact (digitSet A) := by
  rw [digitSet_eq_image]
  exact (isClosed_digitSeqs A).isCompact.image continuous_digitCode

/-! ## Finite digit sums

A finite set `s` of positions names the number `∑_{j ∈ s} 2^{-j-1}`. Distinct sets of positions
below `n` name points at distance at least `2^{-n}`, because `2^n ∑_{j ∈ s} 2^{-j-1}` is the natural
number whose binary digits are those of `s` in reversed order. -/

/-- The number named by a finite set of digit positions. -/
def digitSum (s : Finset ℕ) : ℝ := ∑ j ∈ s, ((2 : ℝ) ^ (j + 1))⁻¹

theorem digitSum_nonneg (s : Finset ℕ) : 0 ≤ digitSum s :=
  Finset.sum_nonneg fun j _ => by positivity

/-- Reversal of the positions below `n`. -/
private def revPos (n j : ℕ) : ℕ := n - 1 - j

private theorem revPos_injOn {n : ℕ} {s : Finset ℕ} (hs : s ⊆ Finset.range n) :
    ∀ x ∈ s, ∀ y ∈ s, revPos n x = revPos n y → x = y := by
  intro x hx y hy h
  have hx' := Finset.mem_range.1 (hs hx)
  have hy' := Finset.mem_range.1 (hs hy)
  simp only [revPos] at h
  omega

/-- Scaling by `2^n` turns a finite digit sum into the natural number with the reversed digits. -/
private theorem two_pow_mul_digitSum {n : ℕ} {s : Finset ℕ} (hs : s ⊆ Finset.range n) :
    (2 : ℝ) ^ n * digitSum s = ((∑ i ∈ s.image (revPos n), 2 ^ i : ℕ) : ℝ) := by
  rw [Finset.sum_image (revPos_injOn hs), digitSum, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < n := Finset.mem_range.1 (hs hj)
  have h2 : (2 : ℝ) ^ n = (2 : ℝ) ^ revPos n j * (2 : ℝ) ^ (j + 1) := by
    rw [← pow_add]; congr 1; simp only [revPos]; omega
  rw [h2, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]

private theorem image_revPos_inj {n : ℕ} {s t : Finset ℕ} (hs : s ⊆ Finset.range n)
    (ht : t ⊆ Finset.range n) (h : s.image (revPos n) = t.image (revPos n)) : s = t := by
  have key : ∀ u v : Finset ℕ, u ⊆ Finset.range n → v ⊆ Finset.range n →
      u.image (revPos n) = v.image (revPos n) → ∀ j ∈ u, j ∈ v := by
    intro u v hu hv huv j hj
    have hmem : revPos n j ∈ v.image (revPos n) := by
      rw [← huv]; exact Finset.mem_image_of_mem _ hj
    obtain ⟨k, hk, hkj⟩ := Finset.mem_image.1 hmem
    have hj' := Finset.mem_range.1 (hu hj)
    have hk' := Finset.mem_range.1 (hv hk)
    have : k = j := by simp only [revPos] at hkj; omega
    exact this ▸ hk
  exact Finset.ext fun j => ⟨key s t hs ht h j, key t s ht hs h.symm j⟩

/-- Distinct sets of digit positions below `n` name points at distance at least `2^{-n}`. -/
theorem inv_two_pow_le_abs_digitSum_sub {n : ℕ} {s t : Finset ℕ} (hs : s ⊆ Finset.range n)
    (ht : t ⊆ Finset.range n) (hst : s ≠ t) :
    ((2 : ℝ) ^ n)⁻¹ ≤ |digitSum s - digitSum t| := by
  have hne : (∑ i ∈ s.image (revPos n), 2 ^ i : ℕ) ≠ ∑ i ∈ t.image (revPos n), 2 ^ i := fun h =>
    hst (image_revPos_inj hs ht (Finset.geomSum_injective le_rfl h))
  have hone : (1 : ℝ) ≤ |((∑ i ∈ s.image (revPos n), 2 ^ i : ℕ) : ℝ)
      - ((∑ i ∈ t.image (revPos n), 2 ^ i : ℕ) : ℝ)| := by
    rcases hne.lt_or_gt with h | h
    · have h' : ((∑ i ∈ s.image (revPos n), 2 ^ i : ℕ) : ℝ) + 1
          ≤ ((∑ i ∈ t.image (revPos n), 2 ^ i : ℕ) : ℝ) := by exact_mod_cast h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · have h' : ((∑ i ∈ t.image (revPos n), 2 ^ i : ℕ) : ℝ) + 1
          ≤ ((∑ i ∈ s.image (revPos n), 2 ^ i : ℕ) : ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; linarith
  have hmul : (2 : ℝ) ^ n * |digitSum s - digitSum t| =
      |((∑ i ∈ s.image (revPos n), 2 ^ i : ℕ) : ℝ)
        - ((∑ i ∈ t.image (revPos n), 2 ^ i : ℕ) : ℝ)| := by
    rw [← abs_of_nonneg (show (0 : ℝ) ≤ 2 ^ n by positivity), ← abs_mul, mul_sub,
      two_pow_mul_digitSum hs, two_pow_mul_digitSum ht]
  rw [inv_eq_one_div, div_le_iff₀ (show (0 : ℝ) < 2 ^ n by positivity)]
  calc (1 : ℝ) ≤ _ := hone
    _ = (2 : ℝ) ^ n * |digitSum s - digitSum t| := hmul.symm
    _ = |digitSum s - digitSum t| * (2 : ℝ) ^ n := mul_comm _ _

theorem digitSum_injOn (n : ℕ) : Set.InjOn digitSum {s : Finset ℕ | s ⊆ Finset.range n} := by
  intro s hs t ht h
  by_contra hst
  have hsep := inv_two_pow_le_abs_digitSum_sub hs ht hst
  rw [h, sub_self, abs_zero] at hsep
  have : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by positivity
  linarith

theorem digitSum_mem_digitSet {A : Set ℕ} {s : Finset ℕ} (hs : (s : Set ℕ) ⊆ A) :
    digitSum s ∈ digitSet A := by
  have hcode : digitCode (fun j => decide (j ∈ s)) = digitSum s :=
    calc digitCode (fun j => decide (j ∈ s))
        = ∑ b ∈ s, (if decide (b ∈ s) then ((2 : ℝ) ^ (b + 1))⁻¹ else 0) :=
          tsum_eq_sum fun b hb => by simp [hb]
      _ = digitSum s := Finset.sum_congr rfl fun j hj => by simp [hj]
  rw [← hcode]
  exact digitCode_mem_digitSet fun j hj => hs (by simpa using hj)

/-! ## The counting function and the covers at dyadic scales -/

open scoped Classical in
/-- The free positions below `n`. -/
def freeFinset (A : Set ℕ) (n : ℕ) : Finset ℕ := (Finset.range n).filter (· ∈ A)

theorem mem_freeFinset {A : Set ℕ} {n j : ℕ} : j ∈ freeFinset A n ↔ j < n ∧ j ∈ A := by
  simp only [freeFinset, Finset.mem_filter, Finset.mem_range]

theorem freeFinset_subset_range (A : Set ℕ) (n : ℕ) : freeFinset A n ⊆ Finset.range n :=
  fun _ hj => Finset.mem_range.2 (mem_freeFinset.1 hj).1

theorem freeFinset_card_le (A : Set ℕ) (n : ℕ) : (freeFinset A n).card ≤ n := by
  simpa using Finset.card_le_card (freeFinset_subset_range A n)

theorem coe_freeFinset (A : Set ℕ) (n : ℕ) :
    (freeFinset A n : Set ℕ) = A ∩ (Finset.range n : Set ℕ) := by
  ext j
  simp only [Finset.mem_coe, mem_freeFinset, mem_inter_iff, Finset.mem_coe, Finset.mem_range]
  tauto

/-- The counting function of the notes: `#(A ∩ {0, …, n-1})`. -/
theorem freeFinset_card (A : Set ℕ) (n : ℕ) :
    Nat.card (A ∩ (Finset.range n : Set ℕ) : Set ℕ) = (freeFinset A n).card := by
  rw [Nat.card_coe_set_eq, ← coe_freeFinset, Set.ncard_coe_finset]

/-- The positions below `n` at which the digit sequence `a` is `1`. -/
def digitPrefix (a : ℕ → Bool) (n : ℕ) : Finset ℕ := (Finset.range n).filter fun j => a j = true

theorem digitPrefix_subset_freeFinset {A : Set ℕ} {a : ℕ → Bool} (ha : a ∈ digitSeqs A) (n : ℕ) :
    digitPrefix a n ⊆ freeFinset A n := fun j hj => by
  rw [digitPrefix, Finset.mem_filter, Finset.mem_range] at hj
  exact mem_freeFinset.2 ⟨hj.1, ha j hj.2⟩

private theorem summable_inv_two_pow_succ_add (n : ℕ) :
    Summable fun i : ℕ => ((2 : ℝ) ^ (i + n + 1))⁻¹ := by
  have h : ∀ i : ℕ, ((2 : ℝ) ^ (i + n + 1))⁻¹ = ((2 : ℝ)⁻¹ ^ i * 2⁻¹) * ((2 : ℝ) ^ n)⁻¹ := by
    intro i
    rw [← inv_pow, ← inv_pow, pow_add, pow_succ]
    ring
  simp_rw [h]
  exact ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _).mul_right _

/-- The digits below `n` determine the number to within `2^{-n}`. -/
theorem digitCode_sub_digitSum_mem (a : ℕ → Bool) (n : ℕ) :
    digitCode a - digitSum (digitPrefix a n) ∈ Icc (0 : ℝ) (((2 : ℝ) ^ n)⁻¹) := by
  have hpre : ∑ j ∈ Finset.range n, (if a j then ((2 : ℝ) ^ (j + 1))⁻¹ else 0)
      = digitSum (digitPrefix a n) := by
    rw [digitSum, digitPrefix, Finset.sum_filter]
  have key : digitCode a - digitSum (digitPrefix a n)
      = ∑' i : ℕ, (if a (i + n) then ((2 : ℝ) ^ (i + n + 1))⁻¹ else 0) := by
    rw [digitCode, ← (summable_digitCode a).sum_add_tsum_nat_add n, hpre]
    ring
  rw [key]
  refine ⟨tsum_nonneg fun i => digitTerm_nonneg a (i + n), ?_⟩
  calc ∑' i : ℕ, (if a (i + n) then ((2 : ℝ) ^ (i + n + 1))⁻¹ else 0)
      ≤ ∑' i : ℕ, ((2 : ℝ) ^ (i + n + 1))⁻¹ :=
        Summable.tsum_le_tsum (fun i => digitTerm_le a (i + n))
          (Summable.of_nonneg_of_le (fun i => digitTerm_nonneg a (i + n))
            (fun i => digitTerm_le a (i + n)) (summable_inv_two_pow_succ_add n))
          (summable_inv_two_pow_succ_add n)
    _ = ((2 : ℝ) ^ n)⁻¹ := tsum_inv_two_pow_succ_add n

/-- The centres of the covering balls of radius `2^{-n-1}`. -/
def digitCover (A : Set ℕ) (n : ℕ) : Set ℝ :=
  (fun s : Finset ℕ => digitSum s + ((2 : ℝ) ^ (n + 1))⁻¹) ''
    ((freeFinset A n).powerset : Set (Finset ℕ))

theorem isCover_digitCover {A : Set ℕ} {n : ℕ} {ε : ℝ≥0} (hε : ((2 : ℝ) ^ (n + 1))⁻¹ ≤ (ε : ℝ)) :
    Metric.IsCover ε (digitSet A) (digitCover A n) := by
  intro x hx
  rw [digitSet_eq_image] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨digitSum (digitPrefix a n) + ((2 : ℝ) ^ (n + 1))⁻¹,
    ⟨digitPrefix a n, Finset.mem_coe.2 (Finset.mem_powerset.2 (digitPrefix_subset_freeFinset ha n)),
      rfl⟩, ?_⟩
  obtain ⟨h0, h1⟩ := digitCode_sub_digitSum_mem a n
  have h2 : ((2 : ℝ) ^ n)⁻¹ = 2 * ((2 : ℝ) ^ (n + 1))⁻¹ := by rw [pow_succ]; field_simp
  have habs : |digitCode a - (digitSum (digitPrefix a n) + ((2 : ℝ) ^ (n + 1))⁻¹)|
      ≤ ((2 : ℝ) ^ (n + 1))⁻¹ := by
    rw [abs_le]
    constructor <;> linarith
  show edist (digitCode a) (digitSum (digitPrefix a n) + ((2 : ℝ) ^ (n + 1))⁻¹) ≤ (ε : ℝ≥0∞)
  rw [edist_dist, Real.dist_eq]
  exact (ENNReal.ofReal_le_ofReal (habs.trans hε)).trans_eq ENNReal.ofReal_coe_nnreal

/-- At scale `2^{-n-1}` the digit-position set needs at most `2^{k(n)}` balls. -/
theorem externalCoveringNumber_digitSet_le {A : Set ℕ} {n : ℕ} {ε : ℝ≥0}
    (hε : ((2 : ℝ) ^ (n + 1))⁻¹ ≤ (ε : ℝ)) :
    Metric.externalCoveringNumber ε (digitSet A) ≤ ((2 ^ (freeFinset A n).card : ℕ) : ℕ∞) := by
  refine (isCover_digitCover hε).externalCoveringNumber_le_encard.trans ?_
  refine (Set.encard_image_le _ _).trans ?_
  rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_powerset]

/-- The left endpoints of the covering intervals of length `2^{-n}`. -/
def digitPoints (A : Set ℕ) (n : ℕ) : Set ℝ :=
  digitSum '' ((freeFinset A n).powerset : Set (Finset ℕ))

private theorem subset_range_of_mem_powerset {A : Set ℕ} {n : ℕ} {s : Finset ℕ}
    (hs : s ∈ ((freeFinset A n).powerset : Set (Finset ℕ))) : s ⊆ Finset.range n :=
  (Finset.mem_powerset.1 (Finset.mem_coe.1 hs)).trans (freeFinset_subset_range A n)

theorem digitPoints_subset (A : Set ℕ) (n : ℕ) : digitPoints A n ⊆ digitSet A := by
  rintro _ ⟨s, hs, rfl⟩
  exact digitSum_mem_digitSet fun j hj =>
    (mem_freeFinset.1 (Finset.mem_powerset.1 (Finset.mem_coe.1 hs) hj)).2

theorem encard_digitPoints (A : Set ℕ) (n : ℕ) :
    (digitPoints A n).encard = ((2 ^ (freeFinset A n).card : ℕ) : ℕ∞) := by
  have hinj : Set.InjOn digitSum ((freeFinset A n).powerset : Set (Finset ℕ)) :=
    fun _ hs _ ht h =>
      digitSum_injOn n (subset_range_of_mem_powerset hs) (subset_range_of_mem_powerset ht) h
  rw [digitPoints, hinj.encard_image, Set.encard_coe_eq_coe_finsetCard, Finset.card_powerset]

theorem isSeparated_digitPoints {A : Set ℕ} {n : ℕ} {ε : ℝ≥0} (hε : (ε : ℝ) < ((2 : ℝ) ^ n)⁻¹) :
    Metric.IsSeparated (ε : ℝ≥0∞) (digitPoints A n) := by
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩ hne
  have hst : s ≠ t := fun h => hne (by rw [h])
  have hsep := inv_two_pow_le_abs_digitSum_sub (subset_range_of_mem_powerset hs)
    (subset_range_of_mem_powerset ht) hst
  rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_coe_nnreal]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ε.coe_nonneg).2 (lt_of_lt_of_le hε hsep)

/-- At scale `2^{-n-2}` the digit-position set needs at least `2^{k(n)}` balls: the left endpoints
lie on the `2^{-n}` mesh, so a ball of radius `2^{-n-2}` contains at most one of them. -/
theorem le_externalCoveringNumber_digitSet {A : Set ℕ} {n : ℕ} {ε : ℝ≥0}
    (hε : 2 * (ε : ℝ) < ((2 : ℝ) ^ n)⁻¹) :
    ((2 ^ (freeFinset A n).card : ℕ) : ℕ∞) ≤ Metric.externalCoveringNumber ε (digitSet A) := by
  rw [← encard_digitPoints A n]
  refine (Metric.IsSeparated.encard_le_packingNumber (digitPoints_subset A n) ?_).trans
    (Metric.packingNumber_two_mul_le_externalCoveringNumber ε (digitSet A))
  refine isSeparated_digitPoints (ε := 2 * ε) ?_
  rw [NNReal.coe_mul, NNReal.coe_ofNat]
  exact hε

/-! ## From the counting function to the box dimensions

The counting bounds hold at the geometric scales `2^{-n}`; the two elementary lemmas below transfer
them to all small scales, with a bounded loss in the constant. -/

/-- Every `r` in `(0, 1)` lies in a dyadic window `[2^{-n-1}, 2^{-n})`. -/
theorem exists_dyadic_window {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    ∃ n : ℕ, ((2 : ℝ) ^ (n + 1))⁻¹ ≤ r ∧ r < ((2 : ℝ) ^ n)⁻¹ := by
  classical
  have hex : ∃ n : ℕ, ((2 : ℝ) ^ (n + 1))⁻¹ ≤ r := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr₀ (show ((2 : ℝ)⁻¹) < 1 by norm_num)
    refine ⟨n, ?_⟩
    have hle : ((2 : ℝ) ^ (n + 1))⁻¹ ≤ ((2 : ℝ) ^ n)⁻¹ := by
      rw [inv_le_inv₀ (by positivity) (by positivity), pow_succ]
      nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) n]
    rw [inv_pow] at hn
    linarith
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h]; simpa using hr₁
  · have hmin := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
    rw [not_le] at hmin
    have heq : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rwa [heq] at hmin

private theorem le_of_inv_two_pow_le {n N : ℕ} {r : ℝ} (h1 : ((2 : ℝ) ^ (n + 1))⁻¹ ≤ r)
    (h2 : r < ((2 : ℝ) ^ N)⁻¹) : N ≤ n := by
  have hlt : ((2 : ℝ) ^ (n + 1))⁻¹ < ((2 : ℝ) ^ N)⁻¹ := lt_of_le_of_lt h1 h2
  rw [inv_lt_inv₀ (by positivity) (by positivity)] at hlt
  by_contra hc
  rw [not_le] at hc
  exact absurd hlt (not_lt.2 (pow_le_pow_right₀ (by norm_num) hc))

private theorem two_pow_le_rpow_neg {r t : ℝ} {k m : ℕ} (hr : 0 < r)
    (hrm : r ≤ ((2 : ℝ) ^ m)⁻¹) (ht : 0 ≤ t) (hk : (k : ℝ) ≤ (m : ℝ) * t) :
    (2 : ℝ) ^ k ≤ r ^ (-t) := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hbase : ((2 : ℝ) ^ m)⁻¹ = (2 : ℝ) ^ (-(m : ℝ)) := by
    rw [Real.rpow_neg h2, Real.rpow_natCast]
  have hrt : r ^ t ≤ (2 : ℝ) ^ (-(m : ℝ) * t) := by
    rw [Real.rpow_mul h2]
    exact Real.rpow_le_rpow hr.le (hbase ▸ hrm) ht
  calc (2 : ℝ) ^ k = (2 : ℝ) ^ ((k : ℕ) : ℝ) := (Real.rpow_natCast 2 k).symm
    _ ≤ (2 : ℝ) ^ ((m : ℝ) * t) := by rw [Real.rpow_le_rpow_left_iff (by norm_num)]; exact hk
    _ = ((2 : ℝ) ^ (-(m : ℝ) * t))⁻¹ := by rw [← Real.rpow_neg h2, neg_mul, neg_neg]
    _ ≤ (r ^ t)⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hr t) hrt
    _ = r ^ (-t) := (Real.rpow_neg hr.le t).symm

private theorem rpow_neg_le_two_pow {r t : ℝ} {k m d : ℕ} (hr : 0 < r)
    (hrm : ((2 : ℝ) ^ (m + d))⁻¹ ≤ r) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hk : (m : ℝ) * t ≤ (k : ℝ)) : r ^ (-t) ≤ (2 : ℝ) ^ (k + d) := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hbase : ((2 : ℝ) ^ (m + d))⁻¹ = (2 : ℝ) ^ (-((m + d : ℕ) : ℝ)) := by
    rw [Real.rpow_neg h2, Real.rpow_natCast]
  have hrt : (2 : ℝ) ^ (-((m + d : ℕ) : ℝ) * t) ≤ r ^ t := by
    rw [Real.rpow_mul h2]
    exact Real.rpow_le_rpow (by positivity) (hbase ▸ hrm) ht₀
  calc r ^ (-t) = (r ^ t)⁻¹ := Real.rpow_neg hr.le t
    _ ≤ ((2 : ℝ) ^ (-((m + d : ℕ) : ℝ) * t))⁻¹ :=
        inv_anti₀ (Real.rpow_pos_of_pos (by norm_num) _) hrt
    _ = (2 : ℝ) ^ (((m + d : ℕ) : ℝ) * t) := by rw [← Real.rpow_neg h2, neg_mul, neg_neg]
    _ ≤ (2 : ℝ) ^ (((k + d : ℕ) : ℝ)) := by
        rw [Real.rpow_le_rpow_left_iff (by norm_num)]
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) d]
    _ = (2 : ℝ) ^ (k + d) := Real.rpow_natCast 2 (k + d)

private theorem enat_two_pow_cast (k : ℕ) :
    (((2 ^ k : ℕ) : ℕ∞) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ k) := by
  rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast (2 ^ k)]
  norm_num

private theorem tendsto_inv_two_pow_add (c : ℕ) :
    Tendsto (fun n : ℕ => ((2 : ℝ) ^ (n + c))⁻¹) atTop (𝓝[>] 0) := by
  have h : (fun n : ℕ => ((2 : ℝ) ^ (n + c))⁻¹) = fun n : ℕ => ((2 : ℝ)⁻¹) ^ (n + c) := by
    funext n; rw [inv_pow]
  rw [tendsto_nhdsWithin_iff, h]
  refine ⟨?_, Filter.Eventually.of_forall fun n => Set.mem_Ioi.2 (by positivity)⟩
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
    (tendsto_add_atTop_nat c)

private theorem eventually_lt_nhdsGT {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r < δ :=
  mem_nhdsWithin.2 ⟨Set.Iio δ, isOpen_Iio, hδ, fun _ hx => hx.1⟩

private theorem two_mul_inv_two_pow_lt (n : ℕ) {c : ℕ} (hc : 2 ≤ c) :
    2 * ((2 : ℝ) ^ (n + c))⁻¹ < ((2 : ℝ) ^ n)⁻¹ := by
  have hcpos : (0 : ℝ) < (2 : ℝ) ^ c := by positivity
  have hc2 : (4 : ℝ) ≤ (2 : ℝ) ^ c := by
    calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (2 : ℝ) ^ c := pow_le_pow_right₀ (by norm_num) hc
  have h1 : (2 : ℝ) * ((2 : ℝ) ^ c)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hcpos]
    linarith
  have hinv : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by positivity
  calc 2 * ((2 : ℝ) ^ (n + c))⁻¹ = (2 * ((2 : ℝ) ^ c)⁻¹) * ((2 : ℝ) ^ n)⁻¹ := by
        rw [pow_add, mul_inv]; ring
    _ < 1 * ((2 : ℝ) ^ n)⁻¹ := mul_lt_mul_of_pos_right h1 hinv
    _ = ((2 : ℝ) ^ n)⁻¹ := one_mul _

private theorem ennreal_const_mul_le {c : ℝ≥0} {x : ℝ} {k : ℕ}
    (h : (c : ℝ) * x ≤ (2 : ℝ) ^ k) :
    (c : ℝ≥0∞) * ENNReal.ofReal x ≤ (((2 ^ k : ℕ) : ℕ∞) : ℝ≥0∞) := by
  rw [enat_two_pow_cast, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul c.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal h

/-- An upper bound `2^{k(n)}` on the covering counts at all small scales bounds the upper box
dimension. -/
theorem upperBoxDim_le_of_le_two_pow {S : Set ℝ} {k : ℕ → ℕ} {t : ℝ≥0}
    (hcount : ∀ n : ℕ, ∀ ε : ℝ≥0, ((2 : ℝ) ^ (n + 1))⁻¹ ≤ (ε : ℝ) →
      Metric.externalCoveringNumber ε S ≤ ((2 ^ k n : ℕ) : ℕ∞))
    (h : ∀ᶠ n : ℕ in atTop, (k n : ℝ) ≤ (n : ℝ) * t) : upperBoxDim S ≤ (t : ℝ≥0∞) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  refine upperBoxDim_le_of_forall (C := 1) one_pos ?_
  have hδ : (0 : ℝ) < ((2 : ℝ) ^ (N + 1))⁻¹ := by positivity
  filter_upwards [self_mem_nhdsWithin, eventually_lt_nhdsGT hδ] with r hr0 hrm
  have hr0' : (0 : ℝ) < r := hr0
  have hone : ((2 : ℝ) ^ (N + 1))⁻¹ ≤ 1 := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (N + 1) := one_le_pow₀ (by norm_num)
    simpa using inv_anti₀ zero_lt_one h1
  obtain ⟨n, hn1, hn2⟩ := exists_dyadic_window hr0' (lt_of_lt_of_le hrm hone)
  have hnN : N ≤ n := le_trans (Nat.le_succ N) (le_of_inv_two_pow_le hn1 hrm)
  have hcov := hcount n r.toNNReal (by rw [Real.coe_toNNReal r hr0'.le]; exact hn1)
  calc ((Metric.externalCoveringNumber r.toNNReal S : ℕ∞) : ℝ≥0∞)
      ≤ (((2 ^ k n : ℕ) : ℕ∞) : ℝ≥0∞) := ENat.toENNReal_le.2 hcov
    _ = ENNReal.ofReal ((2 : ℝ) ^ k n) := enat_two_pow_cast _
    _ ≤ ENNReal.ofReal (r ^ (-(t : ℝ))) :=
        ENNReal.ofReal_le_ofReal
          (two_pow_le_rpow_neg hr0' hn2.le t.coe_nonneg (hN n hnN))
    _ = (1 : ℝ≥0) * ENNReal.ofReal (r ^ (-(t : ℝ))) := by simp

/-- An upper bound `2^{k(n)}` on the covering counts at arbitrarily small scales bounds the lower
box dimension. -/
theorem lowerBoxDim_le_of_le_two_pow {S : Set ℝ} {k : ℕ → ℕ} {t : ℝ≥0}
    (hcount : ∀ n : ℕ, ∀ ε : ℝ≥0, ((2 : ℝ) ^ (n + 1))⁻¹ ≤ (ε : ℝ) →
      Metric.externalCoveringNumber ε S ≤ ((2 ^ k n : ℕ) : ℕ∞))
    (h : ∃ᶠ n : ℕ in atTop, (k n : ℝ) ≤ (n : ℝ) * t) : lowerBoxDim S ≤ (t : ℝ≥0∞) := by
  refine lowerBoxDim_le_of_frequently (C := 1) one_pos ?_
  refine (tendsto_inv_two_pow_add 1).frequently (h.mono fun n hn => ?_)
  have hr0 : (0 : ℝ) < ((2 : ℝ) ^ (n + 1))⁻¹ := by positivity
  have hle : ((2 : ℝ) ^ (n + 1))⁻¹ ≤ ((2 : ℝ) ^ n)⁻¹ := by
    rw [inv_le_inv₀ (by positivity) (by positivity), pow_succ]
    nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) n]
  have hcov := hcount n (((2 : ℝ) ^ (n + 1))⁻¹).toNNReal
    (by rw [Real.coe_toNNReal _ hr0.le])
  calc ((Metric.externalCoveringNumber (((2 : ℝ) ^ (n + 1))⁻¹).toNNReal S : ℕ∞) : ℝ≥0∞)
      ≤ (((2 ^ k n : ℕ) : ℕ∞) : ℝ≥0∞) := ENat.toENNReal_le.2 hcov
    _ = ENNReal.ofReal ((2 : ℝ) ^ k n) := enat_two_pow_cast _
    _ ≤ ENNReal.ofReal ((((2 : ℝ) ^ (n + 1))⁻¹) ^ (-(t : ℝ))) :=
        ENNReal.ofReal_le_ofReal (two_pow_le_rpow_neg hr0 hle t.coe_nonneg hn)
    _ = (1 : ℝ≥0) * ENNReal.ofReal ((((2 : ℝ) ^ (n + 1))⁻¹) ^ (-(t : ℝ))) := by simp

/-- A lower bound `2^{k(n)}` on the covering counts at all small scales bounds the lower box
dimension from below. -/
theorem le_lowerBoxDim_of_two_pow_le {S : Set ℝ} {k : ℕ → ℕ} {t : ℝ≥0} (ht : t ≤ 1)
    (hcount : ∀ n : ℕ, ∀ ε : ℝ≥0, 2 * (ε : ℝ) < ((2 : ℝ) ^ n)⁻¹ →
      ((2 ^ k n : ℕ) : ℕ∞) ≤ Metric.externalCoveringNumber ε S)
    (h : ∀ᶠ n : ℕ in atTop, (n : ℝ) * t ≤ (k n : ℝ)) : (t : ℝ≥0∞) ≤ lowerBoxDim S := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  refine le_lowerBoxDim_of_forall (C := 1 / 32) (by norm_num) ?_
  have hδ : (0 : ℝ) < ((2 : ℝ) ^ (N + 5))⁻¹ := by positivity
  filter_upwards [self_mem_nhdsWithin, eventually_lt_nhdsGT hδ] with r hr0 hrm
  have hr0' : (0 : ℝ) < r := hr0
  have hone : ((2 : ℝ) ^ (N + 5))⁻¹ ≤ 1 := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (N + 5) := one_le_pow₀ (by norm_num)
    simpa using inv_anti₀ zero_lt_one h1
  obtain ⟨m, hm1, hm2⟩ := exists_dyadic_window hr0' (lt_of_lt_of_le hrm hone)
  have hmN : N + 5 ≤ m := le_of_inv_two_pow_le hm1 hrm
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 4 := ⟨m - 4, by omega⟩
  have hnN : N ≤ n := by omega
  have hsep : 2 * ((r.toNNReal : ℝ)) < ((2 : ℝ) ^ n)⁻¹ := by
    rw [Real.coe_toNNReal r hr0'.le]
    calc 2 * r < 2 * ((2 : ℝ) ^ (n + 4))⁻¹ := by linarith
      _ < ((2 : ℝ) ^ n)⁻¹ := two_mul_inv_two_pow_lt n (by norm_num)
  have hm1' : ((2 : ℝ) ^ (n + 5))⁻¹ ≤ r := by
    have hnn : n + 5 = n + 4 + 1 := by omega
    rw [hnn]; exact hm1
  have hrpow : r ^ (-(t : ℝ)) ≤ (2 : ℝ) ^ (k n + 5) :=
    rpow_neg_le_two_pow hr0' hm1' t.coe_nonneg (by exact_mod_cast ht) (hN n hnN)
  refine le_trans ?_ (ENat.toENNReal_le.2 (hcount n r.toNNReal hsep))
  refine ennreal_const_mul_le ?_
  have hc : ((1 / 32 : ℝ≥0) : ℝ) = 1 / 32 := by push_cast; ring
  have h32 : (2 : ℝ) ^ (k n + 5) = 32 * (2 : ℝ) ^ k n := by rw [pow_add]; ring
  rw [hc]
  linarith

/-- A lower bound `2^{k(n)}` on the covering counts at arbitrarily small scales bounds the upper box
dimension from below. -/
theorem le_upperBoxDim_of_two_pow_le {S : Set ℝ} {k : ℕ → ℕ} {t : ℝ≥0} (ht : t ≤ 1)
    (hcount : ∀ n : ℕ, ∀ ε : ℝ≥0, 2 * (ε : ℝ) < ((2 : ℝ) ^ n)⁻¹ →
      ((2 ^ k n : ℕ) : ℕ∞) ≤ Metric.externalCoveringNumber ε S)
    (h : ∃ᶠ n : ℕ in atTop, (n : ℝ) * t ≤ (k n : ℝ)) : (t : ℝ≥0∞) ≤ upperBoxDim S := by
  refine le_upperBoxDim_of_frequently (C := 1 / 4) (by norm_num) ?_
  refine (tendsto_inv_two_pow_add 2).frequently (h.mono fun n hn => ?_)
  have hr0 : (0 : ℝ) < ((2 : ℝ) ^ (n + 2))⁻¹ := by positivity
  have hsep : 2 * ((((2 : ℝ) ^ (n + 2))⁻¹).toNNReal : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by
    rw [Real.coe_toNNReal _ hr0.le]
    exact two_mul_inv_two_pow_lt n (by norm_num)
  have hrpow : (((2 : ℝ) ^ (n + 2))⁻¹) ^ (-(t : ℝ)) ≤ (2 : ℝ) ^ (k n + 2) :=
    rpow_neg_le_two_pow hr0 le_rfl t.coe_nonneg (by exact_mod_cast ht) hn
  refine le_trans ?_ (ENat.toENNReal_le.2 (hcount n _ hsep))
  refine ennreal_const_mul_le ?_
  have hc : ((1 / 4 : ℝ≥0) : ℝ) = 1 / 4 := by push_cast; ring
  have h4 : (2 : ℝ) ^ (k n + 2) = 4 * (2 : ℝ) ^ k n := by rw [pow_add]; ring
  rw [hc]
  linarith

/-! ## The box dimensions of a digit-position set -/

/-- The density of the free positions below `n`. -/
def freeDensity (A : Set ℕ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Nat.card (A ∩ Finset.range n : Set ℕ) : ℝ) / n)

theorem freeDensity_eq (A : Set ℕ) (n : ℕ) :
    freeDensity A n = ENNReal.ofReal (((freeFinset A n).card : ℝ) / n) := by
  rw [freeDensity, freeFinset_card]

theorem freeDensity_le_one (A : Set ℕ) (n : ℕ) : freeDensity A n ≤ 1 := by
  rw [freeDensity_eq]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_one (by exact_mod_cast hn)]
    exact_mod_cast freeFinset_card_le A n

theorem card_le_of_freeDensity_lt {A : Set ℕ} {t : ℝ≥0} {n : ℕ} (hn : 0 < n)
    (h : freeDensity A n < (t : ℝ≥0∞)) : ((freeFinset A n).card : ℝ) ≤ (n : ℝ) * t := by
  rw [freeDensity_eq, ← ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity),
    div_lt_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)] at h
  nlinarith [h]

theorem le_card_of_lt_freeDensity {A : Set ℕ} {t : ℝ≥0} {n : ℕ} (hn : 0 < n)
    (h : (t : ℝ≥0∞) < freeDensity A n) : (n : ℝ) * t ≤ ((freeFinset A n).card : ℝ) := by
  rw [freeDensity_eq, ← ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg t.coe_nonneg,
    lt_div_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)] at h
  nlinarith [h]

private theorem nnreal_le_one_of_lt_freeDensity {A : Set ℕ} {t : ℝ≥0} {n : ℕ}
    (h : (t : ℝ≥0∞) < freeDensity A n) : t ≤ 1 := by
  refine ENNReal.coe_le_coe.1 ?_
  rw [ENNReal.coe_one]
  exact le_of_lt (lt_of_lt_of_le h (freeDensity_le_one A n))

/-- The lower box dimension of a digit-position set is the lower density of the position set. -/
theorem lowerBoxDim_digitSet (A : Set ℕ) :
    lowerBoxDim (digitSet A) = liminf (freeDensity A) atTop := by
  refine le_antisymm ?_ ?_
  · by_contra hcon
    rw [not_le] at hcon
    obtain ⟨t, ht1, ht2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hcon
    have hfreq : ∃ᶠ n in atTop, freeDensity A n < (t : ℝ≥0∞) :=
      Filter.frequently_lt_of_liminf_lt (h := ht1)
    refine absurd ht2 (not_lt.2 ?_)
    exact lowerBoxDim_le_of_le_two_pow (k := fun n => (freeFinset A n).card)
      (fun _ _ hε => externalCoveringNumber_digitSet_le hε)
      ((hfreq.and_eventually (eventually_gt_atTop 0)).mono
        fun _ hn => card_le_of_freeDensity_lt hn.2 hn.1)
  · by_contra hcon
    rw [not_le] at hcon
    obtain ⟨t, ht1, ht2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hcon
    have hev : ∀ᶠ n in atTop, (t : ℝ≥0∞) < freeDensity A n :=
      Filter.eventually_lt_of_lt_liminf ht2
    obtain ⟨n₀, hn₀⟩ := hev.exists
    refine absurd ht1 (not_lt.2 ?_)
    exact le_lowerBoxDim_of_two_pow_le (k := fun n => (freeFinset A n).card)
      (nnreal_le_one_of_lt_freeDensity hn₀)
      (fun _ _ hε => le_externalCoveringNumber_digitSet hε)
      ((hev.and (eventually_gt_atTop 0)).mono
        fun _ hn => le_card_of_lt_freeDensity hn.2 hn.1)

/-- The upper box dimension of a digit-position set is the upper density of the position set. -/
theorem upperBoxDim_digitSet (A : Set ℕ) :
    upperBoxDim (digitSet A) = limsup (freeDensity A) atTop := by
  refine le_antisymm ?_ ?_
  · by_contra hcon
    rw [not_le] at hcon
    obtain ⟨t, ht1, ht2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hcon
    have hev : ∀ᶠ n in atTop, freeDensity A n < (t : ℝ≥0∞) :=
      Filter.eventually_lt_of_limsup_lt ht1
    refine absurd ht2 (not_lt.2 ?_)
    exact upperBoxDim_le_of_le_two_pow (k := fun n => (freeFinset A n).card)
      (fun _ _ hε => externalCoveringNumber_digitSet_le hε)
      ((hev.and (eventually_gt_atTop 0)).mono
        fun _ hn => card_le_of_freeDensity_lt hn.2 hn.1)
  · by_contra hcon
    rw [not_le] at hcon
    obtain ⟨t, ht1, ht2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hcon
    have hfreq : ∃ᶠ n in atTop, (t : ℝ≥0∞) < freeDensity A n :=
      Filter.frequently_lt_of_lt_limsup (h := ht2)
    obtain ⟨n₀, hn₀⟩ := hfreq.exists
    refine absurd ht1 (not_lt.2 ?_)
    exact le_upperBoxDim_of_two_pow_le (k := fun n => (freeFinset A n).card)
      (nnreal_le_one_of_lt_freeDensity hn₀)
      (fun _ _ hε => le_externalCoveringNumber_digitSet hε)
      ((hfreq.and_eventually (eventually_gt_atTop 0)).mono
        fun _ hn => le_card_of_lt_freeDensity hn.2 hn.1)

/-- The box dimensions of a digit-position set are the lower and upper densities of the position
set. -/
theorem box_digitSet (A : Set ℕ) :
    lowerBoxDim (digitSet A) =
        liminf (fun n : ℕ => ENNReal.ofReal ((Nat.card (A ∩ Finset.range n : Set ℕ) : ℝ) / n))
          atTop ∧
      upperBoxDim (digitSet A) =
        limsup (fun n : ℕ => ENNReal.ofReal ((Nat.card (A ∩ Finset.range n : Set ℕ) : ℝ) / n))
          atTop :=
  ⟨lowerBoxDim_digitSet A, upperBoxDim_digitSet A⟩

/-! ## Alternating blocks of free positions

The block endpoints are `n_j = (j+1)!`, so that `n_{j+1} = (j+2) n_j` and the ratio of consecutive
endpoints tends to infinity. The free positions are the even blocks `[n_{2i}, n_{2i+1})`. At the end
of a free block almost every position below the level is free, and at the end of a fixed block
almost none is. -/

/-- The positions of `A` seen from `m`. -/
def shiftSet (m : ℕ) (A : Set ℕ) : Set ℕ := {j | m + j ∈ A}

@[simp]
theorem shiftSet_zero (A : Set ℕ) : shiftSet 0 A = A := by ext j; simp [shiftSet]

/-- The block endpoints `n_j = (j+1)!`. -/
def blockEnd (j : ℕ) : ℕ := Nat.factorial (j + 1)

theorem blockEnd_pos (j : ℕ) : 0 < blockEnd j := Nat.factorial_pos _

theorem blockEnd_succ (j : ℕ) : blockEnd (j + 1) = (j + 2) * blockEnd j := Nat.factorial_succ _

theorem blockEnd_mono {j k : ℕ} (h : j ≤ k) : blockEnd j ≤ blockEnd k :=
  Nat.factorial_le (by omega)

theorem self_lt_blockEnd (j : ℕ) : j < blockEnd j :=
  lt_of_lt_of_le (Nat.lt_succ_self j) (Nat.self_le_factorial _)

theorem blockEnd_lt_blockEnd_succ (j : ℕ) : blockEnd j < blockEnd (j + 1) := by
  have h := blockEnd_pos j
  rw [blockEnd_succ]
  nlinarith

/-- The position set of the notes: the union of the even blocks. -/
def blockSet : Set ℕ := ⋃ i : ℕ, Set.Ico (blockEnd (2 * i)) (blockEnd (2 * i + 1))

/-- At the end of a fixed block, only the positions below the previous block endpoint are free. -/
theorem freeFinset_blockSet_le (i : ℕ) :
    (freeFinset blockSet (blockEnd (2 * i + 2))).card ≤ blockEnd (2 * i + 1) := by
  have hsub : freeFinset blockSet (blockEnd (2 * i + 2)) ⊆
      Finset.range (blockEnd (2 * i + 1)) := by
    intro j hj
    obtain ⟨hjlt, hjA⟩ := mem_freeFinset.1 hj
    simp only [blockSet, Set.mem_iUnion, Set.mem_Ico] at hjA
    obtain ⟨l, hl1, hl2⟩ := hjA
    rw [Finset.mem_range]
    rcases le_or_gt l i with hli | hli
    · exact lt_of_lt_of_le hl2 (blockEnd_mono (by omega))
    · exact absurd hjlt (not_lt.2 (le_trans (blockEnd_mono (by omega : 2 * i + 2 ≤ 2 * l)) hl1))
  simpa using Finset.card_le_card hsub

/-- At the end of a free block, every position of that block is free, even after a shift. -/
theorem le_freeFinset_shift_blockSet {m i : ℕ} (hm : m ≤ blockEnd (2 * i)) :
    blockEnd (2 * i + 1) - blockEnd (2 * i) ≤
      (freeFinset (shiftSet m blockSet) (blockEnd (2 * i + 1) - m)).card := by
  have hmono : blockEnd (2 * i) ≤ blockEnd (2 * i + 1) := blockEnd_mono (by omega)
  have hsub : Finset.Ico (blockEnd (2 * i) - m) (blockEnd (2 * i + 1) - m) ⊆
      freeFinset (shiftSet m blockSet) (blockEnd (2 * i + 1) - m) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    refine mem_freeFinset.2 ⟨hj.2, ?_⟩
    have hmem : m + j ∈ blockSet := by
      simp only [blockSet, Set.mem_iUnion, Set.mem_Ico]
      exact ⟨i, by omega, by omega⟩
    exact hmem
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hcard
  omega

/-- The free positions and the fixed positions below `n` partition `{0, …, n-1}`. -/
theorem freeFinset_compl (A : Set ℕ) (n : ℕ) :
    freeFinset Aᶜ n = Finset.range n \ freeFinset A n := by
  ext j
  simp only [mem_freeFinset, Finset.mem_sdiff, Finset.mem_range, Set.mem_compl_iff]
  tauto

theorem freeFinset_card_add_compl (A : Set ℕ) (n : ℕ) :
    (freeFinset A n).card + (freeFinset Aᶜ n).card = n := by
  have hsub := freeFinset_subset_range A n
  have hle := Finset.card_le_card hsub
  rw [Finset.card_range] at hle
  rw [freeFinset_compl, Finset.card_sdiff_of_subset hsub, Finset.card_range]
  omega

/-! ### The densities of the block construction -/

private theorem freeDensity_le_of_le_card {A : Set ℕ} {n k : ℕ} {x : ℝ} (hn : 0 < n)
    (hcard : (freeFinset A n).card ≤ k) (hx : (k : ℝ) ≤ x * n) :
    freeDensity A n ≤ ENNReal.ofReal x := by
  rw [freeDensity_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)]
  calc ((freeFinset A n).card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hcard
    _ ≤ x * n := hx

private theorem le_freeDensity_of_card_le {A : Set ℕ} {n k : ℕ} {x : ℝ} (hn : 0 < n)
    (hcard : k ≤ (freeFinset A n).card) (hx : x * n ≤ (k : ℝ)) :
    ENNReal.ofReal x ≤ freeDensity A n := by
  rw [freeDensity_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)]
  calc x * n ≤ (k : ℝ) := hx
    _ ≤ ((freeFinset A n).card : ℝ) := by exact_mod_cast hcard

private theorem frequently_of_blockEnd {p : ℕ → Prop} {f : ℕ → ℕ}
    (h : ∀ a, ∃ i, a ≤ f i ∧ p (f i)) : ∃ᶠ n in atTop, p n := by
  rw [Filter.frequently_atTop]
  intro a
  obtain ⟨i, hi, hp⟩ := h a
  exact ⟨f i, hi, hp⟩

/-- At the end of a free block almost every position below the level is free, uniformly in the
shift: the upper density of the free positions is one. -/
theorem one_le_limsup_freeDensity_shift (m : ℕ) :
    1 ≤ limsup (freeDensity (shiftSet m blockSet)) atTop := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨c, hc1, hc2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hcon
  have hx1 : (c : ℝ) < 1 := by
    have h : ((c : ℝ≥0) : ℝ≥0∞) < ((1 : ℝ≥0) : ℝ≥0∞) := by rwa [ENNReal.coe_one]
    exact_mod_cast ENNReal.coe_lt_coe.1 h
  have hx0 : (0 : ℝ) ≤ (c : ℝ) := c.coe_nonneg
  have hpos : (0 : ℝ) < 1 - (c : ℝ) := by linarith
  obtain ⟨i₀, hi₀⟩ := exists_nat_gt (1 / (1 - (c : ℝ)))
  refine absurd hc1 (not_lt.2 ?_)
  rw [← ENNReal.ofReal_coe_nnreal]
  refine Filter.le_limsup_of_frequently_le' (frequently_of_blockEnd
    (f := fun i => blockEnd (2 * i + 1) - m) fun a => ?_)
  set i : ℕ := max (max i₀ a) m with hidef
  have hia : a ≤ i := le_max_of_le_left (le_max_right _ _)
  have him : m ≤ i := le_max_right _ _
  have hii : i₀ ≤ i := le_max_of_le_left (le_max_left _ _)
  have hmb : m ≤ blockEnd (2 * i) := le_trans (by omega) (self_lt_blockEnd (2 * i)).le
  have hmono : blockEnd (2 * i) ≤ blockEnd (2 * i + 1) := blockEnd_mono (by omega)
  have hlt : blockEnd (2 * i) < blockEnd (2 * i + 1) := blockEnd_lt_blockEnd_succ _
  refine ⟨i, ?_, ?_⟩
  · have h3 := self_lt_blockEnd (2 * i + 1)
    omega
  · refine le_freeDensity_of_card_le (by omega) (le_freeFinset_shift_blockSet hmb) ?_
    have hcast1 : ((blockEnd (2 * i + 1) - m : ℕ) : ℝ)
        = (blockEnd (2 * i + 1) : ℝ) - (m : ℝ) := by rw [Nat.cast_sub (by omega)]
    have hcast2 : ((blockEnd (2 * i + 1) - blockEnd (2 * i) : ℕ) : ℝ)
        = (blockEnd (2 * i + 1) : ℝ) - (blockEnd (2 * i) : ℝ) := by rw [Nat.cast_sub hmono]
    have hb1 : (blockEnd (2 * i + 1) : ℝ) = (2 * (i : ℝ) + 2) * (blockEnd (2 * i) : ℝ) := by
      rw [blockEnd_succ (2 * i)]; push_cast; ring
    have hb0 : (0 : ℝ) < (blockEnd (2 * i) : ℝ) := by exact_mod_cast blockEnd_pos _
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hkey : (1 : ℝ) ≤ (1 - (c : ℝ)) * (2 * (i : ℝ) + 2) := by
      have hi0 : ((i₀ : ℕ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast hii
      have hin : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      have h1 : (1 : ℝ) / (1 - (c : ℝ)) < 2 * (i : ℝ) + 2 := by linarith
      rw [div_lt_iff₀ hpos] at h1
      linarith
    rw [hcast1, hcast2, hb1]
    nlinarith [mul_nonneg hx0 hm0,
      mul_nonneg hb0.le (by linarith : (0 : ℝ) ≤ (1 - (c : ℝ)) * (2 * (i : ℝ) + 2) - 1)]

theorem limsup_freeDensity_le_one (A : Set ℕ) : limsup (freeDensity A) atTop ≤ 1 :=
  Filter.limsup_le_of_le (by isBoundedDefault) (Filter.Eventually.of_forall (freeDensity_le_one A))

/-- At the end of a fixed block almost no position below the level is free: the lower density of
the free positions is zero. -/
theorem liminf_freeDensity_blockSet : liminf (freeDensity blockSet) atTop = 0 := by
  refine le_antisymm ?_ (by simp)
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨c, hc1, hc2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hcon
  have hcpos : (0 : ℝ) < (c : ℝ) := NNReal.coe_pos.2 (ENNReal.coe_pos.1 hc1)
  obtain ⟨i₀, hi₀⟩ := exists_nat_gt (1 / (c : ℝ))
  refine absurd hc2 (not_lt.2 ?_)
  rw [← ENNReal.ofReal_coe_nnreal]
  refine Filter.liminf_le_of_frequently_le' (frequently_of_blockEnd
    (f := fun i => blockEnd (2 * i + 2)) fun a => ?_)
  set i : ℕ := max i₀ a with hidef
  have hia : a ≤ i := le_max_right _ _
  have hii : i₀ ≤ i := le_max_left _ _
  have h3 := self_lt_blockEnd (2 * i + 2)
  refine ⟨i, by omega, ?_⟩
  refine freeDensity_le_of_le_card (by omega) (freeFinset_blockSet_le i) ?_
  have hb2 : (blockEnd (2 * i + 2) : ℝ) = (2 * (i : ℝ) + 3) * (blockEnd (2 * i + 1) : ℝ) := by
    rw [blockEnd_succ (2 * i + 1)]; push_cast; ring
  have hb1 : (0 : ℝ) < (blockEnd (2 * i + 1) : ℝ) := by exact_mod_cast blockEnd_pos _
  have hkey : (1 : ℝ) ≤ (c : ℝ) * (2 * (i : ℝ) + 3) := by
    have hi0 : ((i₀ : ℕ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast hii
    have hin : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have h1 : (1 : ℝ) / (c : ℝ) < 2 * (i : ℝ) + 3 := by linarith
    rw [div_lt_iff₀ hcpos] at h1
    linarith
  rw [hb2]
  nlinarith [mul_nonneg hb1.le (by linarith : (0 : ℝ) ≤ (c : ℝ) * (2 * (i : ℝ) + 3) - 1)]

theorem freeFinset_compl_blockSet_le (i : ℕ) :
    (freeFinset blockSetᶜ (blockEnd (2 * i + 1))).card ≤ blockEnd (2 * i) := by
  have h0 := le_freeFinset_shift_blockSet (m := 0) (i := i) (Nat.zero_le _)
  rw [shiftSet_zero, Nat.sub_zero] at h0
  have hsum := freeFinset_card_add_compl blockSet (blockEnd (2 * i + 1))
  have hmono : blockEnd (2 * i) ≤ blockEnd (2 * i + 1) := blockEnd_mono (by omega)
  omega

/-- The complementary position set also has lower density zero: its favourable scales are the ends
of the free blocks. -/
theorem liminf_freeDensity_compl_blockSet : liminf (freeDensity blockSetᶜ) atTop = 0 := by
  refine le_antisymm ?_ (by simp)
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨c, hc1, hc2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hcon
  have hcpos : (0 : ℝ) < (c : ℝ) := NNReal.coe_pos.2 (ENNReal.coe_pos.1 hc1)
  obtain ⟨i₀, hi₀⟩ := exists_nat_gt (1 / (c : ℝ))
  refine absurd hc2 (not_lt.2 ?_)
  rw [← ENNReal.ofReal_coe_nnreal]
  refine Filter.liminf_le_of_frequently_le' (frequently_of_blockEnd
    (f := fun i => blockEnd (2 * i + 1)) fun a => ?_)
  set i : ℕ := max i₀ a with hidef
  have hia : a ≤ i := le_max_right _ _
  have hii : i₀ ≤ i := le_max_left _ _
  have h3 := self_lt_blockEnd (2 * i + 1)
  refine ⟨i, by omega, ?_⟩
  refine freeDensity_le_of_le_card (by omega) (freeFinset_compl_blockSet_le i) ?_
  have hb1 : (blockEnd (2 * i + 1) : ℝ) = (2 * (i : ℝ) + 2) * (blockEnd (2 * i) : ℝ) := by
    rw [blockEnd_succ (2 * i)]; push_cast; ring
  have hb0 : (0 : ℝ) < (blockEnd (2 * i) : ℝ) := by exact_mod_cast blockEnd_pos _
  have hkey : (1 : ℝ) ≤ (c : ℝ) * (2 * (i : ℝ) + 2) := by
    have hi0 : ((i₀ : ℕ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast hii
    have hin : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have h1 : (1 : ℝ) / (c : ℝ) < 2 * (i : ℝ) + 2 := by linarith
    rw [div_lt_iff₀ hcpos] at h1
    linarith
  rw [hb1]
  nlinarith [mul_nonneg hb0.le (by linarith : (0 : ℝ) ≤ (c : ℝ) * (2 * (i : ℝ) + 2) - 1)]

/-! ## Affine copies of the tail set

Every relative neighbourhood of a point of `digitSet A` contains an affine copy of a tail set
`digitSet (shiftSet m A)`. Since all the tail sets of the block construction have upper box
dimension one, Proposition 4.17 gives the packing dimension. -/

/-- The upper box dimension is unchanged by a similarity of the line. -/
theorem upperBoxDim_affine_image {c d : ℝ} (hd : 0 < d) (S : Set ℝ) :
    upperBoxDim ((fun y : ℝ => c + d * y) '' S) = upperBoxDim S := by
  have hdne : d ≠ 0 := hd.ne'
  have hginv : (0 : ℝ) < d⁻¹ := by positivity
  have hdiff : ∀ u v : ℝ, (u - c) / d - (v - c) / d = d⁻¹ * (u - v) := fun u v => by
    rw [div_sub_div_same, div_eq_inv_mul]; ring
  have hf : LipschitzOnWith d.toNNReal (fun y : ℝ => c + d * y) S := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x _ y _
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal d hd.le,
      show c + d * x - (c + d * y) = d * (x - y) from by ring, abs_mul, abs_of_pos hd]
  have hg : LipschitzOnWith (d⁻¹).toNNReal (fun y : ℝ => (y - c) / d)
      ((fun y : ℝ => c + d * y) '' S) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x _ y _
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hginv.le, hdiff x y, abs_mul,
      abs_of_pos hginv]
  have hfun : (fun y : ℝ => (c + d * y - c) / d) = fun y : ℝ => y := by
    funext y
    rw [show c + d * y - c = d * y from by ring, mul_div_cancel_left₀ _ hdne]
  have himg : (fun y : ℝ => (y - c) / d) '' ((fun y : ℝ => c + d * y) '' S) = S := by
    rw [Set.image_image, hfun, Set.image_id']
  refine le_antisymm (upperBoxDim_image_le hf) ?_
  calc upperBoxDim S
      = upperBoxDim ((fun y : ℝ => (y - c) / d) '' ((fun y : ℝ => c + d * y) '' S)) := by
        rw [himg]
    _ ≤ upperBoxDim ((fun y : ℝ => c + d * y) '' S) := upperBoxDim_image_le hg

/-- The digits of `a` below `m` followed by the digits of `c`. -/
theorem digitCode_append (a c : ℕ → Bool) (m : ℕ) :
    digitCode (fun j => if j < m then a j else c (j - m)) =
      digitSum (digitPrefix a m) + ((2 : ℝ) ^ m)⁻¹ * digitCode c := by
  set b : ℕ → Bool := fun j => if j < m then a j else c (j - m) with hb
  have h1 : ∑ j ∈ Finset.range m, (if b j then ((2 : ℝ) ^ (j + 1))⁻¹ else 0)
      = digitSum (digitPrefix a m) := by
    rw [digitSum, digitPrefix, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    simp [hb, hj]
  have h2 : ∀ i : ℕ, (if b (i + m) then ((2 : ℝ) ^ (i + m + 1))⁻¹ else 0)
      = ((2 : ℝ) ^ m)⁻¹ * (if c i then ((2 : ℝ) ^ (i + 1))⁻¹ else 0) := by
    intro i
    have hbi : b (i + m) = c i := by
      simp only [hb]
      rw [if_neg (by omega), Nat.add_sub_cancel]
    have hw : ((2 : ℝ) ^ (i + m + 1))⁻¹ = ((2 : ℝ) ^ m)⁻¹ * ((2 : ℝ) ^ (i + 1))⁻¹ := by
      rw [← mul_inv, ← pow_add]
      congr 2
      omega
    rw [hbi]
    split_ifs
    · exact hw
    · rw [mul_zero]
  rw [digitCode, ← (summable_digitCode b).sum_add_tsum_nat_add m, h1, digitCode, ← tsum_mul_left]
  congr 1
  exact tsum_congr h2

/-- A relative neighbourhood of a point of `digitSet A` contains an affine copy of the tail set. -/
theorem affine_tail_subset {A : Set ℕ} {a : ℕ → Bool} (ha : a ∈ digitSeqs A) (m : ℕ) :
    (fun y : ℝ => digitSum (digitPrefix a m) + ((2 : ℝ) ^ m)⁻¹ * y) ''
        digitSet (shiftSet m A) ⊆
      digitSet A ∩ Metric.ball (digitCode a) (2 * ((2 : ℝ) ^ m)⁻¹) := by
  rintro _ ⟨z, hz, rfl⟩
  have hzIcc := digitSet_subset_Icc _ hz
  refine ⟨?_, ?_⟩
  · rw [digitSet_eq_image] at hz
    obtain ⟨c, hc, rfl⟩ := hz
    show digitSum (digitPrefix a m) + ((2 : ℝ) ^ m)⁻¹ * digitCode c ∈ digitSet A
    rw [← digitCode_append a c m]
    refine digitCode_mem_digitSet fun j hj => ?_
    split_ifs at hj with hjm
    · exact ha j hj
    · have hm : m + (j - m) = j := by omega
      exact hm ▸ hc (j - m) hj
  · obtain ⟨h0, h1⟩ := digitCode_sub_digitSum_mem a m
    obtain ⟨hz0, hz1⟩ := hzIcc
    have hp : (0 : ℝ) < ((2 : ℝ) ^ m)⁻¹ := by positivity
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;>
      nlinarith [mul_nonneg hp.le hz0, mul_le_mul_of_nonneg_left hz1 hp.le]

/-- If every tail set has upper box dimension at least one, then so has every relative
neighbourhood. -/
theorem one_le_upperBoxDim_digitSet_inter (A : Set ℕ) {U : Set ℝ} (hU : IsOpen U)
    (hne : (digitSet A ∩ U).Nonempty)
    (hone : ∀ m : ℕ, 1 ≤ upperBoxDim (digitSet (shiftSet m A))) :
    1 ≤ upperBoxDim (digitSet A ∩ U) := by
  obtain ⟨x, hxE, hxU⟩ := hne
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU x hxU
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < δ / 2 by linarith)
    (show ((2 : ℝ)⁻¹) < 1 by norm_num)
  rw [inv_pow] at hm
  rw [digitSet_eq_image] at hxE
  obtain ⟨a, ha, rfl⟩ := hxE
  have hball' : Metric.ball (digitCode a) (2 * ((2 : ℝ) ^ m)⁻¹) ⊆ U :=
    subset_trans (Metric.ball_subset_ball (by linarith)) hball
  calc (1 : ℝ≥0∞) ≤ upperBoxDim (digitSet (shiftSet m A)) := hone m
    _ = upperBoxDim ((fun y : ℝ => digitSum (digitPrefix a m) + ((2 : ℝ) ^ m)⁻¹ * y) ''
          digitSet (shiftSet m A)) := (upperBoxDim_affine_image (by positivity) _).symm
    _ ≤ upperBoxDim (digitSet A ∩ U) :=
        upperBoxDim_mono (subset_trans (affine_tail_subset ha m)
          (Set.inter_subset_inter_right _ hball'))

/-- A compact set with lower box dimension zero, upper box dimension one, and packing dimension
one. -/
theorem exists_lowerBoxDim_zero_upperBoxDim_one :
    ∃ E : Set ℝ, IsCompact E ∧ lowerBoxDim E = 0 ∧ upperBoxDim E = 1 ∧ packingDim E = 1 := by
  have hone : ∀ m : ℕ, 1 ≤ upperBoxDim (digitSet (shiftSet m blockSet)) := fun m => by
    rw [upperBoxDim_digitSet]; exact one_le_limsup_freeDensity_shift m
  have hupper : upperBoxDim (digitSet blockSet) = 1 := by
    rw [upperBoxDim_digitSet]
    refine le_antisymm (limsup_freeDensity_le_one _) ?_
    simpa using one_le_limsup_freeDensity_shift 0
  have hpack : packingDim (digitSet blockSet) = 1 := by
    rw [← hupper]
    refine local_box_packing (isCompact_digitSet _) (digitSet_nonempty _) fun U hU hne => ?_
    refine le_antisymm (upperBoxDim_mono Set.inter_subset_left) ?_
    rw [hupper]
    exact one_le_upperBoxDim_digitSet_inter blockSet hU hne hone
  exact ⟨digitSet blockSet, isCompact_digitSet _,
    by rw [lowerBoxDim_digitSet, liminf_freeDensity_blockSet], hupper, hpack⟩

/-- The lower box dimension is not finitely stable: two compact sets of lower box dimension zero
whose union has lower box dimension at least `1/2`. -/
theorem exists_lowerBoxDim_union_lt :
    ∃ E F : Set ℝ, IsCompact E ∧ IsCompact F ∧ lowerBoxDim E = 0 ∧ lowerBoxDim F = 0 ∧
      ENNReal.ofReal (1 / 2) ≤ lowerBoxDim (E ∪ F) := by
  refine ⟨digitSet blockSet, digitSet blockSetᶜ, isCompact_digitSet _, isCompact_digitSet _,
    by rw [lowerBoxDim_digitSet, liminf_freeDensity_blockSet],
    by rw [lowerBoxDim_digitSet, liminf_freeDensity_compl_blockSet], ?_⟩
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    norm_num
  rw [hhalf]
  refine le_lowerBoxDim_of_two_pow_le
    (k := fun n => max (freeFinset blockSet n).card (freeFinset blockSetᶜ n).card)
    (by norm_num) (fun n ε hε => ?_) (Filter.Eventually.of_forall fun n => ?_)
  · show ((2 ^ max (freeFinset blockSet n).card (freeFinset blockSetᶜ n).card : ℕ) : ℕ∞) ≤ _
    rcases le_total (freeFinset blockSet n).card (freeFinset blockSetᶜ n).card with hle | hle
    · rw [max_eq_right hle]
      exact le_trans (le_externalCoveringNumber_digitSet hε)
        (Metric.externalCoveringNumber_mono_set Set.subset_union_right)
    · rw [max_eq_left hle]
      exact le_trans (le_externalCoveringNumber_digitSet hε)
        (Metric.externalCoveringNumber_mono_set Set.subset_union_left)
  · show (n : ℝ) * ((1 / 2 : ℝ≥0) : ℝ) ≤
      ((max (freeFinset blockSet n).card (freeFinset blockSetᶜ n).card : ℕ) : ℝ)
    have hsum := freeFinset_card_add_compl blockSet n
    have hnat : n ≤ 2 * max (freeFinset blockSet n).card (freeFinset blockSetᶜ n).card := by
      rcases le_total (freeFinset blockSet n).card (freeFinset blockSetᶜ n).card with hle | hle
      · rw [max_eq_right hle]; omega
      · rw [max_eq_left hle]; omega
    have hcast : (n : ℝ) ≤ 2 * ((max (freeFinset blockSet n).card
        (freeFinset blockSetᶜ n).card : ℕ) : ℝ) := by exact_mod_cast hnat
    have hc : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by push_cast; ring
    rw [hc]
    linarith

end GeometricMeasureTheory
