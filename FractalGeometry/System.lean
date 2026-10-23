/-
Self-similar systems of contracting similarities of the line, their attractors
and their natural measures.

* `System`: finitely many similarities `S_i(x) = r_i x + b_i` with `0 < r_i < 1`
  mapping `[0,1]` into itself.
* `IsAttractor`, `StronglySeparated`: an invariant compact `K = ⋃ S_i K` in
  `[0,1]`, and the condition that the pieces `S_i K` stay a fixed distance
  `ρ > 0` apart.
* `IsDimension`, `IsNatural`: the similarity dimension `∑ r_i^s = 1` and a
  natural measure carried by the attractor and satisfying
  `μ = ∑ r_i^s (S_i)_*μ`.
* `logRatio`, `NonArithmetic`: the log-ratios `a_i = log(1/r_i)` and the density
  of the group they generate.
* `renewalLaw`, `renewalMean`: the law `∑ r_i^s δ_{a_i}` on the log-ratios and
  its mean `m = ∑ r_i^s a_i`, positive for a nonempty system.
* `sCantor`: the exponent `log 2 / log 3`.
* `homogeneousSystem`, `cantorSystem`, `pairSystem`: the homogeneous system of
  ratio `λ`, the middle-thirds system, and the paired system with ratios `1/2`
  and `c`, together with their dimensions and separation gaps.
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Tactic

namespace FractalGeometry

open Real MeasureTheory
open scoped ENNReal NNReal Topology

/-! ### The Cantor exponent -/

/-- The similarity dimension `s = log 2 / log 3` of the middle-thirds Cantor set. -/
noncomputable def sCantor : ℝ := Real.log 2 / Real.log 3

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem log_three_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)

theorem sCantor_pos : 0 < sCantor := div_pos log_two_pos log_three_pos

/-- `3^s = 2`, the defining property of the Cantor exponent. -/
theorem rpow_three_sCantor : (3 : ℝ) ^ sCantor = 2 := by
  rw [sCantor, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3), mul_div_assoc', mul_comm,
    mul_div_assoc, div_self log_three_pos.ne', mul_one, Real.exp_log (by norm_num)]

/-- `s < 2/3`, proved from `8 < 9`. -/
theorem sCantor_lt_two_thirds : sCantor < 2 / 3 := by
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2 ^ (3:ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have h9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9:ℝ) = 3 ^ (2:ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hlt : Real.log 8 < Real.log 9 := Real.log_lt_log (by norm_num) (by norm_num)
  rw [h8, h9] at hlt
  rw [sCantor, div_lt_iff₀ log_three_pos]
  linarith

theorem sCantor_lt_one : sCantor < 1 := by
  have := sCantor_lt_two_thirds; linarith

/-- `2^{2/3} < 5/3`, proved from `108 < 125`. -/
theorem two_rpow_two_thirds_lt : (2 : ℝ) ^ ((2:ℝ)/3) < 5 / 3 := by
  have hcube : ((2:ℝ) ^ ((2:ℝ)/3)) ^ (3:ℕ) = 4 := by
    rw [← Real.rpow_natCast ((2:ℝ) ^ ((2:ℝ)/3)) 3, ← Real.rpow_mul (by norm_num)]
    norm_num
  refine lt_of_pow_lt_pow_left₀ 3 (by norm_num) ?_
  rw [hcube]; norm_num

/-- The numeric separation `(3/5)·2^s < 1` of the Cantor profile values. -/
theorem three_fifths_two_rpow_lt_one : (3/5 : ℝ) * (2:ℝ) ^ sCantor < 1 := by
  have h1 : (2:ℝ) ^ sCantor < (2:ℝ) ^ ((2:ℝ)/3) :=
    (Real.rpow_lt_rpow_left_iff (by norm_num)).mpr sCantor_lt_two_thirds
  have h2 := two_rpow_two_thirds_lt
  linarith



open MeasureTheory

/-- A self-similar system on `[0,1]`: finitely many similarities
`S_i(x) = r_i x + b_i` with ratios in `(0,1)`, each mapping `[0,1]` into itself. -/
structure System (ι : Type*) [Fintype ι] where
  /-- The contraction ratios. -/
  ratio : ι → ℝ
  /-- The translation parts. -/
  shift : ι → ℝ
  /-- Each ratio is positive. -/
  ratio_pos : ∀ i, 0 < ratio i
  /-- Each ratio is a contraction. -/
  ratio_lt_one : ∀ i, ratio i < 1
  /-- Each similarity maps the unit interval into itself. -/
  mapsTo : ∀ i, Set.MapsTo (fun x => ratio i * x + shift i) (Set.Icc 0 1) (Set.Icc 0 1)

namespace System

variable {ι : Type*} [Fintype ι] (S : System ι)

/-- The similarity attached to a letter, `S_i(x) = r_i x + b_i`. -/
def map (i : ι) (x : ℝ) : ℝ := S.ratio i * x + S.shift i

theorem measurable_map (i : ι) : Measurable (S.map i) := by
  unfold map; fun_prop

/-- An attractor of the system: a nonempty compact subset `K` of `[0,1]` satisfying
`K = ⋃ i, S_i K`. The module `FractalGeometry.Hutchinson` constructs this set and proves
that it is unique. -/
def IsAttractor (K : Set ℝ) : Prop :=
  IsCompact K ∧ K.Nonempty ∧ K ⊆ Set.Icc 0 1 ∧ K = ⋃ i, S.map i '' K

/-- Strong separation on `K` with gap `ρ`: one has `ρ > 0`, and points in distinct pieces
`S_i K` and `S_j K` are at least `ρ` apart. This is a condition on the images of `K`, not
on the generally larger first-level intervals `S_i([0,1])`. -/
def StronglySeparated (K : Set ℝ) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ i j, i ≠ j → ∀ x ∈ K, ∀ y ∈ K, ρ ≤ |S.map i x - S.map j y|

/-- Separation on a larger set restricts. -/
theorem StronglySeparated.mono {K K' : Set ℝ} {ρ : ℝ} (h : K' ⊆ K)
    (hs : S.StronglySeparated K ρ) : S.StronglySeparated K' ρ :=
  ⟨hs.1, fun i j hij x hx y hy => hs.2 i j hij x (h hx) y (h hy)⟩

/-- The similarity dimension equation `∑ r_i^s = 1`. -/
def IsDimension (s : ℝ) : Prop := ∑ i, S.ratio i ^ s = 1

/-- A natural measure at exponent `s`: a self-similar probability measure carried by an
attractor, with weights `p_i = r_i^s`. -/
structure IsNatural (K : Set ℝ) (s : ℝ) (μ : Measure ℝ) : Prop where
  /-- It is a probability measure. -/
  isProbability : IsProbabilityMeasure μ
  /-- `K` is an attractor of the system. -/
  attractor : S.IsAttractor K
  /-- The measure is carried by the attractor. -/
  support : μ Kᶜ = 0
  /-- Hutchinson's identity with weights `p_i = r_i^s`. -/
  selfSimilar : μ = ∑ i, ENNReal.ofReal (S.ratio i ^ s) • μ.map (S.map i)

/-- A natural measure is a probability measure. -/
theorem IsNatural.isProbabilityMeasure {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (h : S.IsNatural K s μ) : IsProbabilityMeasure μ := h.isProbability

/-- The natural measure sits on `[0,1]`. -/
theorem IsNatural.support_Icc {K : Set ℝ} {s : ℝ} {μ : Measure ℝ}
    (h : S.IsNatural K s μ) : μ (Set.Icc (0:ℝ) 1)ᶜ = 0 :=
  measure_mono_null (Set.compl_subset_compl.mpr h.attractor.2.2.1) h.support

/-- The log-ratios `a_i = log(1/r_i)`, the atoms of the renewal measure `F`. -/
noncomputable def logRatio (i : ι) : ℝ := Real.log (S.ratio i)⁻¹

theorem logRatio_pos (i : ι) : 0 < S.logRatio i := by
  rw [logRatio, Real.log_inv, neg_pos]
  exact Real.log_neg (S.ratio_pos i) (S.ratio_lt_one i)

/-- The system is non-arithmetic: the additive group generated by the log-ratios is
dense in `ℝ`.  This is the hypothesis of the key renewal theorem. -/
def NonArithmetic : Prop :=
  Dense ((AddSubgroup.closure (Set.range S.logRatio) : AddSubgroup ℝ) : Set ℝ)

/-- The renewal convolution `F * g` of the key renewal theorem, where
`F = ∑ p_i δ_{a_i}`: `(F * g)(w) = ∑ p_i g(w - a_i)`. -/
noncomputable def renewalConv (s : ℝ) (g : ℝ → ℝ) (w : ℝ) : ℝ :=
  ∑ i, S.ratio i ^ s * g (w - S.logRatio i)

/-- The renewal measure `F = ∑ p_i δ_{a_i}` of the key renewal theorem, whose atoms are
the log-ratios and whose weights are `p_i = r_i^s`.  This is the measure the key renewal
theorem is applied to. -/
noncomputable def renewalLaw (s : ℝ) : Measure ℝ :=
  ∑ i, ENNReal.ofReal (S.ratio i ^ s) • Measure.dirac (S.logRatio i)

theorem renewalLaw_apply (s : ℝ) (A : Set ℝ) :
    S.renewalLaw s A = ∑ i, ENNReal.ofReal (S.ratio i ^ s) * (Measure.dirac (S.logRatio i)) A := by
  simp [renewalLaw]

/-- The weights sum to one exactly when `s` is the similarity dimension. -/
theorem sum_ofReal_ratio_rpow {s : ℝ} (hdim : S.IsDimension s) :
    ∑ i, ENNReal.ofReal (S.ratio i ^ s) = 1 := by
  have hnn : ∀ i ∈ Finset.univ, (0:ℝ) ≤ S.ratio i ^ s := fun i _ =>
    (Real.rpow_pos_of_pos (S.ratio_pos i) s).le
  rw [← ENNReal.ofReal_sum_of_nonneg hnn, hdim, ENNReal.ofReal_one]

/-- The renewal measure is a probability measure at the similarity dimension. -/
theorem isProbabilityMeasure_renewalLaw {s : ℝ} (hdim : S.IsDimension s) :
    IsProbabilityMeasure (S.renewalLaw s) := by
  constructor
  rw [renewalLaw_apply S s Set.univ]
  simp only [Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_of_mem, Set.mem_univ,
    Pi.one_apply, mul_one]
  exact S.sum_ofReal_ratio_rpow hdim

/-- The renewal mean `m = ∑ p_i a_i` of the key renewal theorem. -/
noncomputable def renewalMean (s : ℝ) : ℝ := ∑ i, S.ratio i ^ s * S.logRatio i

/-- The renewal mean is the first moment of `F`: this is the `∫ x ∂μ` the key renewal
theorem divides by. -/
theorem integral_id_renewalLaw (s : ℝ) :
    ∫ x, x ∂(S.renewalLaw s) = S.renewalMean s := by
  have hint : ∀ i ∈ (Finset.univ : Finset ι), Integrable (fun x : ℝ => x)
      (ENNReal.ofReal (S.ratio i ^ s) • Measure.dirac (S.logRatio i)) := by
    intro i _
    refine (integrable_smul_measure ?_ (by simp)).mpr (integrable_dirac (by simp))
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.rpow_pos_of_pos (S.ratio_pos i) s
  rw [renewalMean, renewalLaw, integral_finsetSum_measure hint]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_ofReal (Real.rpow_pos_of_pos (S.ratio_pos i) s).le]

theorem renewalMean_pos (s : ℝ) [Nonempty ι] :
    0 < S.renewalMean s := by
  refine Finset.sum_pos' (fun i _ => ?_) ?_
  · exact mul_nonneg (Real.rpow_pos_of_pos (S.ratio_pos i) s).le (S.logRatio_pos i).le
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine ⟨i, Finset.mem_univ i, ?_⟩
  have : (0:ℝ) < S.ratio i ^ s := Real.rpow_pos_of_pos (S.ratio_pos i) s
  have := S.logRatio_pos i
  positivity

end System

/-! ### The systems of the application -/

/-- The homogeneous two-map system `S_0(x) = λx` and
`S_1(x) = λx + 1 - λ`, for `0 < λ < 1/2`. -/
noncomputable def homogeneousSystem (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam < 1/2) :
    System (Fin 2) where
  ratio _ := lam
  shift i := if i = 0 then 0 else 1 - lam
  ratio_pos _ := hlam0
  ratio_lt_one _ := by linarith
  mapsTo i x hx := by
    obtain ⟨h0, h1⟩ := hx
    fin_cases i <;> constructor <;> simp <;> nlinarith

/-- The similarity dimension `log 2 / log (1/λ)` of the homogeneous system. -/
noncomputable def homogeneousDim (lam : ℝ) : ℝ := Real.log 2 / Real.log lam⁻¹

/-- The middle-thirds system `S_0(x) = x/3` and `S_1(x) = x/3 + 2/3`. -/
noncomputable def cantorSystem : System (Fin 2) where
  ratio _ := 1/3
  shift i := if i = 0 then 0 else 2/3
  ratio_pos _ := by norm_num
  ratio_lt_one _ := by norm_num
  mapsTo i x hx := by
    obtain ⟨h0, h1⟩ := hx
    fin_cases i <;> constructor <;> simp <;> linarith

/-- The two-map system `S_0(x) = x/2` and `S_1(x) = cx + 1 - c`, for
`0 < c < 1/2`. -/
noncomputable def pairSystem (c : ℝ) (hc0 : 0 < c) (hc : c < 1/2) : System (Fin 2) where
  ratio i := if i = 0 then 1/2 else c
  shift i := if i = 0 then 0 else 1 - c
  ratio_pos i := by
    fin_cases i
    · norm_num
    · simpa using hc0
  ratio_lt_one i := by
    fin_cases i
    · norm_num
    · simpa using by linarith
  mapsTo i x hx := by
    obtain ⟨h0, h1⟩ := hx
    fin_cases i <;> constructor <;> simp <;> nlinarith


/-! ### The middle-thirds system -/

/-! ### The homogeneous system -/

theorem log_inv_pos {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2) :
    0 < Real.log lam⁻¹ := by
  rw [Real.log_pos_iff (inv_nonneg.mpr hlam0.le), one_lt_inv₀ hlam0]
  linarith

theorem homogeneousDim_pos {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2) :
    0 < homogeneousDim lam :=
  div_pos log_two_pos (log_inv_pos hlam0 hlam)

theorem homogeneousDim_lt_one {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2) :
    homogeneousDim lam < 1 := by
  have hlog := log_inv_pos hlam0 hlam
  rw [homogeneousDim, div_lt_one hlog]
  have h2inv : (2 : ℝ) < lam⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ hlam0]
    nlinarith
  exact Real.strictMonoOn_log (by norm_num) (inv_pos.mpr hlam0) h2inv

/-- The identity `λ^s = 1/2` for `s = log 2 / log (1/λ)`. -/
theorem rpow_homogeneousDim {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2) :
    lam ^ homogeneousDim lam = 1/2 := by
  have hlog := log_inv_pos hlam0 hlam
  have hloglam : Real.log lam = -Real.log lam⁻¹ := by
    rw [Real.log_inv]
    ring
  rw [homogeneousDim, Real.rpow_def_of_pos hlam0, hloglam]
  rw [show (-Real.log lam⁻¹) * (Real.log 2 / Real.log lam⁻¹) = -Real.log 2 by
    rw [div_eq_mul_inv]
    calc
      -Real.log lam⁻¹ * (Real.log 2 * (Real.log lam⁻¹)⁻¹)
          = -Real.log 2 * (Real.log lam⁻¹ * (Real.log lam⁻¹)⁻¹) := by ring
      _ = -Real.log 2 := by rw [mul_inv_cancel₀ hlog.ne', mul_one]]
  rw [Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

theorem homogeneousSystem_isDimension {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2) :
    (homogeneousSystem lam hlam0 hlam).IsDimension (homogeneousDim lam) := by
  simp only [System.IsDimension, homogeneousSystem, Fin.sum_univ_two,
    rpow_homogeneousDim hlam0 hlam]
  norm_num

theorem homogeneousSystem_map_zero {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    (x : ℝ) : (homogeneousSystem lam hlam0 hlam).map 0 x = lam * x := by
  simp [System.map, homogeneousSystem]

theorem homogeneousSystem_map_one {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    (x : ℝ) : (homogeneousSystem lam hlam0 hlam).map 1 x = lam * x + (1 - lam) := by
  simp [System.map, homogeneousSystem]

/-- The homogeneous system is strongly separated, with first-level gap `1 - 2λ`. -/
theorem homogeneousSystem_stronglySeparated {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1/2) {K : Set ℝ} (hK : K ⊆ Set.Icc 0 1) :
    (homogeneousSystem lam hlam0 hlam).StronglySeparated K (1 - 2 * lam) := by
  refine ⟨by linarith, fun i j hij x hx y hy => ?_⟩
  obtain ⟨hx0, hx1⟩ := hK hx
  obtain ⟨hy0, hy1⟩ := hK hy
  have hij' : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
  rcases hij' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [homogeneousSystem_map_zero, homogeneousSystem_map_one, le_abs]
    right
    nlinarith
  · rw [homogeneousSystem_map_one, homogeneousSystem_map_zero, le_abs]
    left
    nlinarith

theorem half_rpow (s : ℝ) : ((1:ℝ)/2) ^ s = (2:ℝ) ^ (-s) := by
  rw [one_div, Real.inv_rpow (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]

/-- `cantorSystem` has similarity dimension `s = log 2 / log 3`. -/
theorem cantorSystem_isDimension : cantorSystem.IsDimension sCantor := by
  have h : ((1:ℝ)/3) ^ sCantor = 1/2 := by
    rw [one_div, Real.inv_rpow (by norm_num), rpow_three_sCantor]
    norm_num
  simp only [System.IsDimension, cantorSystem, Fin.sum_univ_two, h]
  norm_num

theorem cantorSystem_map_zero (x : ℝ) : cantorSystem.map 0 x = 1/3 * x := by
  simp [System.map, cantorSystem]

theorem cantorSystem_map_one (x : ℝ) : cantorSystem.map 1 x = 1/3 * x + 2/3 := by
  simp [System.map, cantorSystem]

/-- `cantorSystem` is strongly separated with gap `1/3` on every subset of `[0,1]`. -/
theorem cantorSystem_stronglySeparated {K : Set ℝ} (hK : K ⊆ Set.Icc 0 1) :
    cantorSystem.StronglySeparated K (1/3) := by
  refine ⟨by norm_num, fun i j hij x hx y hy => ?_⟩
  obtain ⟨hx0, hx1⟩ := hK hx
  obtain ⟨hy0, hy1⟩ := hK hy
  have hij' : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
  rcases hij' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [cantorSystem_map_zero, cantorSystem_map_one, le_abs]; right; linarith
  · rw [cantorSystem_map_one, cantorSystem_map_zero, le_abs]; left; linarith

/-! ### The paired system -/

/-- The contraction ratio `c = (1 - 2^{-s})^{1/s}` of the paired system. -/
noncomputable def pairRatio (s : ℝ) : ℝ := (1 - (2:ℝ) ^ (-s)) ^ s⁻¹

theorem one_sub_two_rpow_pos {s : ℝ} (hs : 0 < s) : 0 < 1 - (2:ℝ) ^ (-s) := by
  have h : (2:ℝ) ^ (-s) < 2 ^ (0:ℝ) :=
    (Real.rpow_lt_rpow_left_iff (by norm_num)).mpr (by linarith)
  simpa using h

theorem pairRatio_pos {s : ℝ} (hs : 0 < s) : 0 < pairRatio s :=
  Real.rpow_pos_of_pos (one_sub_two_rpow_pos hs) _

/-- The paired ratio satisfies `c^s = 1 - 2^{-s}`. -/
theorem pairRatio_rpow {s : ℝ} (hs : 0 < s) : (pairRatio s) ^ s = 1 - (2:ℝ) ^ (-s) := by
  rw [pairRatio, ← Real.rpow_mul (one_sub_two_rpow_pos hs).le, inv_mul_cancel₀ hs.ne',
    Real.rpow_one]

/-- If `0 < s < 1`, then the paired ratio satisfies `c < 1/2`. -/
theorem pairRatio_lt_half {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : pairRatio s < 1/2 := by
  have hhalf : (1:ℝ)/2 < (2:ℝ) ^ (-s) := by
    have h : (2:ℝ) ^ (-(1:ℝ)) < (2:ℝ) ^ (-s) :=
      (Real.rpow_lt_rpow_left_iff (by norm_num)).mpr (by linarith)
    rwa [Real.rpow_neg_one, ← one_div] at h
  have hlt : (pairRatio s) ^ s < ((1:ℝ)/2) ^ s := by
    rw [pairRatio_rpow hs0, half_rpow]; linarith
  exact (Real.rpow_lt_rpow_iff (pairRatio_pos hs0).le (by norm_num) hs0).mp hlt

/-- The paired system has similarity dimension `s`: `2^{-s} + c^s = 1`. -/
theorem pairSystem_isDimension {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    (pairSystem (pairRatio s) (pairRatio_pos hs0)
      (pairRatio_lt_half hs0 hs1)).IsDimension s := by
  simp only [System.IsDimension, pairSystem, Fin.sum_univ_two]
  norm_num
  rw [half_rpow, pairRatio_rpow hs0]
  ring

theorem pairSystem_map_zero {c : ℝ} (hc0 : 0 < c) (hc : c < 1/2) (x : ℝ) :
    (pairSystem c hc0 hc).map 0 x = 1/2 * x := by
  simp [System.map, pairSystem]

theorem pairSystem_map_one {c : ℝ} (hc0 : 0 < c) (hc : c < 1/2) (x : ℝ) :
    (pairSystem c hc0 hc).map 1 x = c * x + (1 - c) := by
  simp [System.map, pairSystem]

/-- The log-ratios of the paired system are `log(1/c)` and `log 2`. -/
theorem pairSystem_range_logRatio {c : ℝ} (hc0 : 0 < c) (hc : c < 1/2) :
    Set.range (pairSystem c hc0 hc).logRatio = {Real.log c⁻¹, Real.log 2} := by
  have h0 : (pairSystem c hc0 hc).logRatio 0 = Real.log 2 := by
    simp [System.logRatio, pairSystem]
  have h1 : (pairSystem c hc0 hc).logRatio 1 = Real.log c⁻¹ := by
    simp [System.logRatio, pairSystem]
  ext x
  simp only [Set.mem_range, Fin.exists_fin_two, h0, h1, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro (h | h)
    · exact Or.inr h.symm
    · exact Or.inl h.symm
  · rintro (h | h)
    · exact Or.inr h.symm
    · exact Or.inl h.symm

/-- The paired system is non-arithmetic precisely when `log(1/c) / log 2` is
irrational. -/
theorem pairSystem_nonArithmetic_iff {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    (pairSystem (pairRatio s) (pairRatio_pos hs0)
        (pairRatio_lt_half hs0 hs1)).NonArithmetic
      ↔ Irrational (Real.log (pairRatio s)⁻¹ / Real.log 2) := by
  rw [System.NonArithmetic,
    pairSystem_range_logRatio (pairRatio_pos hs0) (pairRatio_lt_half hs0 hs1)]
  exact dense_addSubgroupClosure_pair_iff

/-- The paired system is strongly separated with gap `1/2 - c` on every subset of
`[0,1]`: the first-level hulls are `[0,1/2]` and `[1-c,1]`. -/
theorem pairSystem_stronglySeparated {c : ℝ} (hc0 : 0 < c) (hc : c < 1/2) {K : Set ℝ}
    (hK : K ⊆ Set.Icc 0 1) : (pairSystem c hc0 hc).StronglySeparated K (1/2 - c) := by
  refine ⟨by linarith, fun i j hij x hx y hy => ?_⟩
  obtain ⟨hx0, hx1⟩ := hK hx
  obtain ⟨hy0, hy1⟩ := hK hy
  have hij' : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
  rcases hij' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [pairSystem_map_zero, pairSystem_map_one, le_abs]; right; nlinarith
  · rw [pairSystem_map_one, pairSystem_map_zero, le_abs]; left; nlinarith


end FractalGeometry
