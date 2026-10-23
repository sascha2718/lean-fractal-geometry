import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.Dimension.BallMassBounds
import FractalGeometry.Dimension.ComparisonOfLocalDimensions
import FractalGeometry.Dimension.Exact
import FractalGeometry.Dimension.LocalBounds
import FractalGeometry.Dimension.LogMassRatios
import FractalGeometry.Entropy.Lq.Statement
import FractalGeometry.Ergodic.ShannonMcMillanBreiman
import FractalGeometry.Symbolic.BernoulliMeasure
import FractalGeometry.SelfSimilar.Line.Coding
import FractalGeometry.SelfSimilar.Line.Defs
import FractalGeometry.SelfSimilar.Line.JordanRapaportStatement
import FractalGeometry.SelfSimilar.Line.LogProducts
import FractalGeometry.SelfSimilar.Line.Lyapunov
import FractalGeometry.SelfSimilar.Line.Measurable
import FractalGeometry.SelfSimilar.Line.Separation
import FractalGeometry.SelfSimilar.Line.Words
import FractalGeometry.SelfSimilar.SimilarityWords
import FractalGeometry.SelfSimilar.Shmerkin
import FractalGeometry.Symbolic.BernoulliShift
import FractalGeometry.Symbolic.BlockConcatenation
import FractalGeometry.Symbolic.BlockEntropyBounds
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.FutureWords
import FractalGeometry.Symbolic.NonnegativeEntropy
import FractalGeometry.Symbolic.Shift
import FractalGeometry.Symbolic.TypicalBlocks
import FractalGeometry.Symbolic.TypicalWords
import FractalGeometry.Symbolic.WordAverages

/-!
Thomas Jordan and Ariel Rapaport, "Dimension of ergodic measures projected onto
self-similar sets with overlaps", Proceedings of the London Mathematical Society
(3) 122(2) (2021), 191–206. DOI: 10.1112/plms.12337; arXiv:1908.00271v2, Theorem 1.1.

For a finite real-line similarity IFS with nonzero contracting ratios and
exponential separation, every ergodic invariant probability measure on the
symbolic shift projects to an exact-dimensional measure of dimension
`min 1 (-entropy / lyapunov)`. Ratios may have either sign. The formulation uses
the two-sided shift and the nonnegative-coordinate coding map.
-/

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology Metric Set

open scoped ENNReal

universe u

theorem frostman_of_lq {μ : Measure ℝ} [IsFiniteMeasure μ] {q α : ℝ} (hq : 1 < q)
    (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (h : ∀ᶠ M : ℕ in atTop, ∀ s : Finset ℤ,
      ∑ k ∈ s, (μ.real (Ico ((k : ℝ) / 2 ^ M) ((k + 1) / 2 ^ M))) ^ q ≤
        (2 : ℝ) ^ (-((M : ℝ) * ((q - 1) * α)))) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ x : ℝ, ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      μ.real (closedBall x ρ) ≤ 6 * ρ ^ ((q - 1) * α / q) := by
  obtain ⟨M₀, hM₀⟩ := h.exists_forall_of_atTop
  set γ := (q - 1) * α / q with hγ
  have hq0 : 0 < q := by linarith
  have hγ0 : 0 ≤ γ := div_nonneg (mul_nonneg (by linarith) hα) hq0.le
  have hγ1 : γ ≤ α := by
    rw [hγ, div_le_iff₀ hq0]; nlinarith

  have hI : ∀ M : ℕ, M₀ ≤ M → ∀ k : ℤ,
      μ.real (Ico ((k : ℝ) / 2 ^ M) ((k + 1) / 2 ^ M)) ≤ (2 : ℝ) ^ (-((M : ℝ) * γ)) := by
    intro M hM k
    have h1 := hM₀ M hM {k}
    rw [Finset.sum_singleton] at h1
    have hnn := (measureReal_nonneg (μ := μ)
      (s := Ico ((k : ℝ) / 2 ^ M) ((k + 1) / 2 ^ M)))
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hnn q) h1 (inv_nonneg.2 hq0.le)
    rw [← Real.rpow_mul hnn, mul_inv_cancel₀ hq0.ne', Real.rpow_one,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at h2
    convert h2 using 2
    rw [hγ]; field_simp
  refine ⟨(2 : ℝ) ^ (-((M₀ : ℝ) + 1)), by positivity, fun x ρ hρ hρ₀ => ?_⟩

  set M : ℕ := ⌊Real.logb 2 (1 / ρ)⌋₊ with hMdef
  have hlog : (M₀ : ℝ) + 1 ≤ Real.logb 2 (1 / ρ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), one_div,
      le_inv_comm₀ (by positivity) hρ, ← Real.rpow_neg (by norm_num)]
    exact hρ₀
  have hlog0 : 0 ≤ Real.logb 2 (1 / ρ) := le_trans (by positivity) hlog
  have hMM₀ : M₀ ≤ M := by
    rw [hMdef]; exact Nat.le_floor (by linarith)
  have hM1 : (M : ℝ) ≤ Real.logb 2 (1 / ρ) := Nat.floor_le hlog0
  have hM2 : Real.logb 2 (1 / ρ) < M + 1 := Nat.lt_floor_add_one _

  have hρle : ρ ≤ (2 : ℝ) ^ (-(M : ℝ)) := by
    have := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (by positivity)).1 hM1
    rw [one_div] at this
    rw [Real.rpow_neg (by norm_num)]
    exact (le_inv_comm₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _) hρ).1 this
  have hρgt : (2 : ℝ) ^ (-((M : ℝ) + 1)) < ρ := by
    have := (Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) (by positivity)).1 hM2
    rw [one_div] at this
    rw [Real.rpow_neg (by norm_num)]
    exact (inv_lt_comm₀ hρ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)).1 this

  set e : ℝ := (2 : ℝ) ^ M with he
  have hepos : 0 < e := by positivity
  set k₀ : ℤ := ⌊(x - ρ) * e⌋ with hk₀
  set I : ℤ → Set ℝ := fun k => Ico ((k : ℝ) / e) (((k : ℝ) + 1) / e) with hIdef
  have hcover : closedBall x ρ ⊆ I k₀ ∪ I (k₀ + 1) ∪ I (k₀ + 2) := by
    intro z hz
    rw [mem_closedBall, Real.dist_eq, abs_le] at hz
    have hρe : ρ * e ≤ 1 := by
      rw [he, ← Real.rpow_natCast]
      calc ρ * (2 : ℝ) ^ (M : ℝ) ≤ (2 : ℝ) ^ (-(M : ℝ)) * (2 : ℝ) ^ (M : ℝ) :=
            mul_le_mul_of_nonneg_right hρle (by positivity)
        _ = 1 := by rw [← Real.rpow_add (by norm_num)]; simp
    have hfl1 : (k₀ : ℝ) ≤ (x - ρ) * e := Int.floor_le _
    have hfl2 : (x - ρ) * e < k₀ + 1 := Int.lt_floor_add_one _
    have hz1 : (k₀ : ℝ) ≤ z * e := by nlinarith
    have hz2 : z * e < k₀ + 3 := by nlinarith
    simp only [hIdef, mem_union, mem_Ico, div_le_iff₀ hepos, lt_div_iff₀ hepos]
    push_cast
    by_cases h1 : z * e < k₀ + 1
    · exact Or.inl (Or.inl ⟨hz1, h1⟩)
    · by_cases h2 : z * e < k₀ + 2
      · exact Or.inl (Or.inr ⟨by linarith, by linarith⟩)
      · exact Or.inr ⟨by linarith, by linarith⟩
  have hbound : ∀ k : ℤ, μ.real (I k) ≤ (2 : ℝ) ^ (-((M : ℝ) * γ)) :=
    fun k => hI M hMM₀ k
  have hsum : μ.real (closedBall x ρ) ≤ 3 * (2 : ℝ) ^ (-((M : ℝ) * γ)) := by
    calc μ.real (closedBall x ρ) ≤ μ.real (I k₀ ∪ I (k₀ + 1) ∪ I (k₀ + 2)) :=
          measureReal_mono hcover
      _ ≤ μ.real (I k₀) + μ.real (I (k₀ + 1)) + μ.real (I (k₀ + 2)) := by
          refine (measureReal_union_le _ _).trans ?_
          gcongr
          exact measureReal_union_le _ _
      _ ≤ _ := by linarith [hbound k₀, hbound (k₀ + 1), hbound (k₀ + 2)]

  have hpow : (2 : ℝ) ^ (-((M : ℝ) * γ)) ≤ 2 * ρ ^ γ := by
    have h1 : (2 : ℝ) ^ (-((M : ℝ) * γ)) = ((2 : ℝ) ^ (-((M : ℝ) + 1))) ^ γ * 2 ^ γ := by
      rw [← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
      congr 1; ring
    rw [h1]
    have h2 : ((2 : ℝ) ^ (-((M : ℝ) + 1))) ^ γ ≤ ρ ^ γ :=
      Real.rpow_le_rpow (by positivity) hρgt.le hγ0
    have h3 : (2 : ℝ) ^ γ ≤ 2 := by
      calc (2 : ℝ) ^ γ ≤ 2 ^ (1 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            rw [hγ, div_le_one hq0]; nlinarith
        _ = 2 := Real.rpow_one 2
    calc ((2 : ℝ) ^ (-((M : ℝ) + 1))) ^ γ * 2 ^ γ ≤ ρ ^ γ * 2 :=
          mul_le_mul h2 h3 (by positivity) (by positivity)
      _ = 2 * ρ ^ γ := mul_comm _ _
  linarith

namespace LineIFS

variable {ι : Type*} {S : LineIFS ι} {r M : ℝ}

theorem Bounds.code_eq_gWord (hS : S.Bounds r M) (y : ℤ → ι) (n : ℕ) :
    S.code y = S.gWord (futureWord y n) (S.code (shift n y)) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    have e : ((n + 1 : ℕ) : ℤ) = 1 + (n : ℤ) := by push_cast; ring
    rw [futureWord_succ', gWord_cons, Function.comp_apply, hS.code_eq y, ih (shift 1 y),
      shift_shift, e]

theorem Bounds.abs_code_le_div (hS : S.Bounds r M) (y : ℤ → ι) :
    |S.code y| ≤ M / (1 - r) := by
  have hg : HasSum (fun k : ℕ => r ^ k * M) (M / (1 - r)) := by
    have := (hasSum_geometric_of_lt_one hS.r_nonneg hS.r_lt_one).mul_right M
    simpa [div_eq_inv_mul, mul_comm] using this
  have h := tsum_of_norm_bounded (f := S.codeTerm y) hg fun k => by
    rw [codeTerm, Real.norm_eq_abs, abs_mul]
    have h := hS.abs_gDeriv_le (futureWord y k)
    rw [length_futureWord] at h
    exact mul_le_mul h (hS.abs_trans_le _) (abs_nonneg _) (pow_nonneg hS.r_nonneg _)
  simpa [code, Real.norm_eq_abs] using h

theorem abs_gWord_sub (S : LineIFS ι) (u : List (ι)) (a b : ℝ) :
    |S.gWord u a - S.gWord u b| = |S.gDeriv u| * |a - b| := by
  rw [S.gWord_apply u a, S.gWord_apply u b, ← abs_mul]
  congr 1; ring

theorem Bounds.abs_code_sub_le (hS : S.Bounds r M) {y y' : ℤ → ι} {n : ℕ}
    (h : ∀ k : ℕ, k < n → y k = y' k) :
    |S.code y - S.code y'| ≤ |S.gDeriv (futureWord y n)| * (2 * M / (1 - r)) := by
  have hw : futureWord y n = futureWord y' n := by
    simp only [futureWord]
    refine List.map_congr_left fun k hk => h k (List.mem_range.1 hk)
  rw [hS.code_eq_gWord y n, hS.code_eq_gWord y' n, ← hw, S.abs_gWord_sub]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h1 := hS.abs_code_le_div (shift (n : ℤ) y)
  have h2 := hS.abs_code_le_div (shift (n : ℤ) y')
  calc |S.code (shift (n : ℤ) y) - S.code (shift (n : ℤ) y')|
      ≤ |S.code (shift (n : ℤ) y)| + |S.code (shift (n : ℤ) y')| := abs_sub _ _
    _ ≤ M / (1 - r) + M / (1 - r) := add_le_add h1 h2
    _ = 2 * M / (1 - r) := by ring

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem Bounds.measureReal_map_shift_closedBall_le (hS : S.Bounds r M)
    (ν' : Measure (ℤ → ι)) [IsFiniteMeasure ν'] (j : ℕ) (x ρ : ℝ) :
    ((ν'.map (shift (j : ℤ))).map S.code).real (closedBall x ρ) ≤
      ∑ u : Fin j → ι, (ν'.map S.code).real
        (closedBall (S.gWord (List.ofFn u) x) (|S.gDeriv (List.ofFn u)| * ρ)) := by
  have hmeas := hS.measurable_code
  rw [Measure.map_map hmeas (measurable_shift _),
    map_measureReal_apply (hmeas.comp (measurable_shift _)) measurableSet_closedBall]
  rw [← sum_measureReal_inter_preimage_singleton ν' (f := block j)
    (fun c => measurable_block j (measurableSet_singleton c))]
  refine Finset.sum_le_sum fun u _ => ?_
  rw [map_measureReal_apply hmeas measurableSet_closedBall]
  refine measureReal_mono fun z hz => ?_
  obtain ⟨hz1, hz2⟩ := hz
  simp only [mem_preimage, Function.comp_apply, mem_closedBall, Real.dist_eq,
    mem_singleton_iff] at hz1 hz2 ⊢
  rw [hS.code_eq_gWord z j, futureWord_eq_ofFn_block, hz2, S.abs_gWord_sub]
  exact mul_le_mul_of_nonneg_left hz1 (abs_nonneg _)

theorem Bounds.frostman_map_shift (hS : S.Bounds r M) (ν' : Measure (ℤ → ι))
    [IsFiniteMeasure ν'] {C γ ρ₀ : ℝ} (hγ : 0 ≤ γ)
    (h : ∀ x : ℝ, ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → (ν'.map S.code).real (closedBall x ρ) ≤ C * ρ ^ γ)
    (j : ℕ) (x ρ : ℝ) (hρ : 0 < ρ) (hρ₀ : ρ ≤ ρ₀) :
    ((ν'.map (shift (j : ℤ))).map S.code).real (closedBall x ρ) ≤
      (Fintype.card (ι) : ℝ) ^ j * (C * ρ ^ γ) := by
  refine (hS.measureReal_map_shift_closedBall_le ν' j x ρ).trans ?_
  have hC : 0 ≤ C := by
    have := h x ρ hρ hρ₀
    have h0 : 0 < ρ ^ γ := Real.rpow_pos_of_pos hρ γ
    by_contra hneg
    push Not at hneg
    have : C * ρ ^ γ < 0 := mul_neg_of_neg_of_pos hneg h0
    linarith [measureReal_nonneg (μ := ν'.map S.code) (s := closedBall x ρ)]
  calc ∑ u : Fin j → ι, (ν'.map S.code).real
        (closedBall (S.gWord (List.ofFn u) x) (|S.gDeriv (List.ofFn u)| * ρ))
      ≤ ∑ _u : Fin j → ι, C * ρ ^ γ := by
        refine Finset.sum_le_sum fun u _ => ?_
        have hd0 : 0 < |S.gDeriv (List.ofFn u)| := abs_pos.2 (S.gDeriv_ne_zero _)
        have hd1 : |S.gDeriv (List.ofFn u)| ≤ 1 := by
          have := hS.abs_gDeriv_le (List.ofFn u)
          exact this.trans (pow_le_one₀ hS.r_nonneg hS.r_lt_one.le)
        refine (h _ _ (mul_pos hd0 hρ) ((mul_le_of_le_one_left hρ.le hd1).trans hρ₀)).trans ?_
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
          (mul_le_of_le_one_left hρ.le hd1) hγ) hC
    _ = (Fintype.card (ι) : ℝ) ^ j * (C * ρ ^ γ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

end LineIFS

theorem prod_pow_length_eq_of_append_comm {κ : Type*} (r : κ → ℝ) :
    ∀ (n : ℕ) (u v : List κ), u.length + v.length ≤ n → u ++ v = v ++ u →
      ((u.map r).prod) ^ v.length = ((v.map r).prod) ^ u.length := by
  intro n
  induction n with
  | zero =>
    intro u v h _
    have hu : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hv : v = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [hu, hv]
  | succ n ih =>

    have key : ∀ u v : List κ, u.length + v.length ≤ n + 1 → u ++ v = v ++ u →
        u.length ≤ v.length →
        ((u.map r).prod) ^ v.length = ((v.map r).prod) ^ u.length := by
      intro u v h huv hle
      rcases eq_or_ne u [] with hu | hu
      · simp [hu]
      have hpos : 0 < u.length := List.length_pos_iff.2 hu
      have htake : v.take u.length = u := by
        have h1 : (u ++ v).take u.length = u := List.take_left
        rw [huv, List.take_append_of_le_length hle] at h1
        exact h1
      set v' := v.drop u.length with hv'
      have hv : v = u ++ v' := by
        conv_lhs => rw [← List.take_append_drop u.length v]
        rw [htake]
      have hcomm : u ++ v' = v' ++ u := by
        have h1 : u ++ (u ++ v') = u ++ (v' ++ u) := by
          have h2 := huv
          rw [hv] at h2
          simpa [List.append_assoc] using h2
        exact List.append_cancel_left h1
      have hlen : v.length = u.length + v'.length := by rw [hv, List.length_append]
      have hIH := ih u v' (by omega) hcomm
      rw [hv, List.map_append, List.prod_append, mul_pow, ← hIH, ← pow_add, ← hlen, hv]
    intro u v h huv
    rcases le_total u.length v.length with hle | hle
    · exact key u v h huv hle
    · exact (key v u (by omega) huv.symm hle).symm

def flatBlocks {α : Type*} {m : ℕ} (U : List (Fin m → α)) : List α := (U.map List.ofFn).flatten

@[simp] theorem flatBlocks_nil {α : Type*} {m : ℕ} :
    flatBlocks ([] : List (Fin m → α)) = [] := rfl

@[simp] theorem flatBlocks_cons {α : Type*} {m : ℕ} (w : Fin m → α) (U : List (Fin m → α)) :
    flatBlocks (w :: U) = List.ofFn w ++ flatBlocks U := rfl

theorem flatBlocks_append {α : Type*} {m : ℕ} (U V : List (Fin m → α)) :
    flatBlocks (U ++ V) = flatBlocks U ++ flatBlocks V := by
  simp [flatBlocks, List.flatten_append]

theorem length_flatBlocks {α : Type*} {m : ℕ} (U : List (Fin m → α)) :
    (flatBlocks U).length = m * U.length := by
  induction U with
  | nil => simp
  | cons w U ih => simp [ih]; ring

theorem flatBlocks_injective {α : Type*} {m : ℕ} (hm : 0 < m) :
    Function.Injective (flatBlocks : List (Fin m → α) → List α) := by
  intro U
  induction U with
  | nil =>
    intro V h
    rcases V with _ | ⟨w, V⟩
    · rfl
    · have := congrArg List.length h
      simp at this
      omega
  | cons w U ih =>
    intro V h
    rcases V with _ | ⟨w', V⟩
    · have := congrArg List.length h
      simp at this
      omega
    · simp only [flatBlocks_cons] at h
      obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
      rw [List.ofFn_injective h1, ih h2]

namespace LineIFS

variable {ι : Type*} (S : LineIFS ι) (m : ℕ)

def blockRatio (w : Fin m → ι) : ℝ := S.gDeriv (List.ofFn w)

def blockTrans (w : Fin m → ι) : ℝ := S.gWord (List.ofFn w) 0

theorem simWord_block (U : List (Fin m → ι)) :
    simWord (S.blockRatio m) (S.blockTrans m) U = S.gWord (flatBlocks U) := by
  induction U with
  | nil => rfl
  | cons w U ih =>
    rw [simWord_cons, ih, flatBlocks_cons, gWord_append]
    funext x
    simp only [Function.comp_apply, blockRatio, blockTrans]
    rw [S.gWord_apply (List.ofFn w) (S.gWord (flatBlocks U) x)]

theorem prod_blockRatio (U : List (Fin m → ι)) :
    (U.map (S.blockRatio m)).prod = S.gDeriv (flatBlocks U) := by
  induction U with
  | nil => rfl
  | cons w U ih => rw [List.map_cons, List.prod_cons, ih, flatBlocks_cons, gDeriv_append]; rfl

variable {S} {m}

theorem ExpSeparation.shmerkinExpSeparation [Fintype ι] [Nonempty ι]
    (h : S.ExpSeparation) (hm : 0 < m) :
    ShmerkinExpSeparation (S.blockRatio m) (S.blockTrans m) := by
  obtain ⟨c, hc, n, hn, hsep⟩ := h
  obtain ⟨r₀, M₀, hS⟩ := S.exists_bounds
  obtain ⟨p₀⟩ : Nonempty (ι) := inferInstance
  have hr₀pos : 0 < r₀ := lt_of_lt_of_le (abs_pos.2 (S.ratio_ne_zero p₀)) (hS.abs_ratio_le p₀)
  have hr₀1 : r₀ < 1 := hS.r_lt_one
  set c' := min c (1 / 2) with hc'
  have hc'pos : 0 < c' := lt_min hc (by norm_num)
  have hc'1 : c' ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hc'le : c' ≤ c := min_le_left _ _
  have hlogr : 0 < Real.log (1 / r₀) :=
    Real.log_pos (by rw [one_div]; exact one_lt_inv₀ hr₀pos |>.2 hr₀1)
  set K₀ := Real.log 2 / Real.log (1 / r₀) with hK₀
  have hK₀pos : 0 < K₀ := div_pos (Real.log_pos (by norm_num)) hlogr
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm

  have hlen : ∀ (M : ℕ) (U : List (Fin m → ι)),
      ShmerkinStopping (S.blockRatio m) M U → (m : ℝ) * U.length ≤ m + K₀ * M := by
    intro M U ⟨hU, _, hgt⟩
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℕ, U.length = ℓ + 1 :=
      ⟨U.length - 1, by have := List.length_pos_iff.2 hU; omega⟩
    have hgt' : (2 : ℝ) ^ (-(M : ℝ)) < |S.gDeriv (flatBlocks U.dropLast)| := by
      rw [← prod_blockRatio]
      exact hgt
    have h1 := hS.abs_gDeriv_le (flatBlocks U.dropLast)
    rw [length_flatBlocks, List.length_dropLast, hℓ, Nat.add_sub_cancel] at h1
    have h2 : (2 : ℝ) ^ (-(M : ℝ)) < r₀ ^ (m * ℓ) := hgt'.trans_le h1
    have h3 := Real.log_lt_log (by positivity) h2
    rw [Real.log_rpow (by norm_num), Real.log_pow] at h3
    have hlogr' : Real.log r₀ = -Real.log (1 / r₀) := by rw [one_div, Real.log_inv, neg_neg]
    rw [hlogr'] at h3
    have h4 : (m : ℝ) * ℓ * Real.log (1 / r₀) < M * Real.log 2 := by push_cast at h3; linarith
    have h5 : (m : ℝ) * ℓ < K₀ * M := by
      rw [hK₀, div_mul_eq_mul_div, lt_div_iff₀ hlogr]
      linarith
    rw [hℓ]
    push_cast
    linarith

  set A₀ := c' ^ (2 * (m : ℝ) + 2 * K₀) / 2 with hA₀
  set B₀ := c' ^ (2 * K₀) with hB₀
  have hA₀pos : 0 < A₀ := by positivity
  have hA₀1 : A₀ ≤ 1 := by
    rw [hA₀, div_le_one (by norm_num)]
    exact (Real.rpow_le_one hc'pos.le hc'1 (by positivity)).trans (by norm_num)
  have hB₀pos : 0 < B₀ := by positivity
  have hB₀1 : B₀ ≤ 1 := Real.rpow_le_one hc'pos.le hc'1 (by positivity)
  have hAB1 : A₀ * B₀ < 1 := by
    have : A₀ < 1 := by
      rw [hA₀, div_lt_one (by norm_num)]
      exact (Real.rpow_le_one hc'pos.le hc'1 (by positivity)).trans_lt (by norm_num)
    nlinarith
  set R := Real.logb 2 (1 / (A₀ * B₀)) with hR
  have hRpos : 0 < R := by
    rw [hR]
    exact Real.logb_pos (by norm_num) (by rw [one_div]; exact one_lt_inv₀ (by positivity) |>.2 hAB1)
  have h2R : ∀ M : ℕ, (2 : ℝ) ^ (-(R * M)) = (A₀ * B₀) ^ M := by
    intro M
    rw [show -(R * M) = R * (-(M : ℝ)) by ring, Real.rpow_mul (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) (by positivity), Real.rpow_neg (by positivity),
      Real.rpow_natCast, one_div, inv_pow, inv_inv]
  refine ⟨R, hRpos, ?_⟩
  rw [Filter.frequently_atTop]
  intro M₁
  obtain ⟨k, hk⟩ : ∃ k, 2 * (m : ℝ) + 2 * K₀ * (M₁ + 2) ≤ n k := by
    obtain ⟨k, hk⟩ := exists_nat_ge (2 * (m : ℝ) + 2 * K₀ * (M₁ + 2))
    exact ⟨k, hk.trans (by exact_mod_cast hn.id_le k)⟩
  set Mk : ℕ := ⌊((n k : ℝ) - 2 * m) / (2 * K₀)⌋₊ with hMk
  have hval : (M₁ : ℝ) + 2 ≤ ((n k : ℝ) - 2 * m) / (2 * K₀) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hMk1 : M₁ + 1 ≤ Mk := by
    rw [hMk]
    exact Nat.le_floor (by push_cast; linarith)
  have hval0 : 0 ≤ ((n k : ℝ) - 2 * m) / (2 * K₀) := le_trans (by positivity) hval
  have hMk2 : 2 * (m : ℝ) + 2 * K₀ * Mk ≤ n k := by
    have := Nat.floor_le hval0
    rw [← hMk, le_div_iff₀ (by positivity)] at this
    linarith
  have hMk3 : (n k : ℝ) < 2 * m + 2 * K₀ * (Mk + 1) := by
    have := Nat.lt_floor_add_one (((n k : ℝ) - 2 * m) / (2 * K₀))
    rw [← hMk, div_lt_iff₀ (by positivity)] at this
    linarith
  refine ⟨Mk, by omega, ?_⟩
  intro U V hUV hU hV hrat
  rw [simWord_block, simWord_block]
  rw [prod_blockRatio, prod_blockRatio] at hrat
  set lamU := S.gDeriv (flatBlocks U) with hlamU
  set tU := S.gWord (flatBlocks U) 0 with htU
  set tV := S.gWord (flatBlocks V) 0 with htV

  set X := flatBlocks (U ++ V) with hX
  set Y := flatBlocks (V ++ U) with hY
  set L : ℕ := m * (U.length + V.length) with hL
  have hXlen : X.length = L := by rw [hX, length_flatBlocks, List.length_append]
  have hYlen : Y.length = L := by rw [hY, length_flatBlocks, List.length_append, add_comm]
  have hLle : L ≤ n k := by
    have h1 := hlen Mk U hU
    have h2 := hlen Mk V hV
    have : (L : ℝ) ≤ n k := by
      rw [hL]; push_cast; linarith
    exact_mod_cast this
  have hlamabs : |lamU| < 1 := by
    have h1 := hU.2.1
    rw [prod_blockRatio] at h1
    refine h1.trans_lt ?_
    rw [Real.rpow_neg (by norm_num)]
    refine inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) ?_)
    exact_mod_cast (show 0 < Mk by omega)
  have hlampos : 0 < |lamU| := abs_pos.2 (S.gDeriv_ne_zero _)
  have hXY : X ≠ Y := by
    intro hXY
    have hcomm : U ++ V = V ++ U := flatBlocks_injective hm hXY
    have hpow := prod_pow_length_eq_of_append_comm (S.blockRatio m) _ U V le_rfl hcomm
    rw [prod_blockRatio, prod_blockRatio, ← hrat] at hpow
    have habs : |lamU| ^ V.length = |lamU| ^ U.length := by rw [← abs_pow, ← abs_pow, hpow]
    have hlenUV : V.length = U.length := (pow_right_strictAnti₀ hlampos hlamabs).injective habs
    exact hUV (List.append_inj hcomm hlenUV.symm).1
  have hderiv : S.gDeriv X = S.gDeriv Y := by
    rw [hX, hY, flatBlocks_append, flatBlocks_append, gDeriv_append, gDeriv_append, mul_comm]
  have htrans : S.gWord X 0 - S.gWord Y 0 = (1 - lamU) * (tU - tV) := by
    have e1 : S.gWord X 0 = lamU * tV + tU := by
      rw [hX, flatBlocks_append, gWord_append, Function.comp_apply,
        S.gWord_apply (flatBlocks U)]
    have e2 : S.gWord Y 0 = lamU * tU + tV := by
      rw [hY, flatBlocks_append, gWord_append, Function.comp_apply,
        S.gWord_apply (flatBlocks V), ← hrat]
    rw [e1, e2]
    ring

  have hgap : ENNReal.ofReal (c ^ n k) ≤ ENNReal.ofReal |S.gWord X 0 - S.gWord Y 0| :=
    (hsep k).trans ((antitone_nat_of_succ_le S.gap_succ_le hLle).trans
      (S.gap_le hXlen hYlen hXY hderiv))
  have hgap' : c' ^ n k ≤ 2 * |tU - tV| := by
    have h1 := (ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)).1 hgap
    rw [htrans, abs_mul] at h1
    have h2 : |1 - lamU| ≤ 2 := by
      have := abs_sub (1 : ℝ) lamU
      rw [abs_one] at this
      linarith
    calc c' ^ n k ≤ c ^ n k := pow_le_pow_left₀ hc'pos.le hc'le _
      _ ≤ |1 - lamU| * |tU - tV| := h1
      _ ≤ 2 * |tU - tV| := mul_le_mul_of_nonneg_right h2 (abs_nonneg _)

  have hexp : 2 * A₀ * B₀ ^ Mk ≤ c' ^ n k := by
    have h1 : c' ^ (2 * (m : ℝ) + 2 * K₀ * (Mk + 1)) ≤ c' ^ ((n k : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hc'pos hc'1 hMk3.le
    rw [Real.rpow_natCast] at h1
    refine le_trans (le_of_eq ?_) h1
    rw [hA₀, hB₀, ← Real.rpow_natCast, ← Real.rpow_mul hc'pos.le, mul_div_cancel₀ _ (by norm_num),
      ← Real.rpow_add hc'pos]
    congr 1
    ring
  have hAB : (A₀ * B₀) ^ Mk ≤ A₀ * B₀ ^ Mk := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_of_le_one hA₀pos.le hA₀1 (by omega))
      (by positivity)
  rw [h2R]
  linarith

end LineIFS

section BlockBernoulli

open ProbabilityTheory

theorem bernoulli_inter_tail {β : Type*} [MeasurableSpace β] (P : Measure β)
    [IsProbabilityMeasure P] {A : Set β} (hA : MeasurableSet A) {B : Set (ℕ → β)}
    (hB : MeasurableSet B) :
    bernoulli P ({y | y 0 ∈ A} ∩ {y | (fun i : ℕ => y ((i : ℤ) + 1)) ∈ B}) =
      bernoulli P {y | y 0 ∈ A} * bernoulli P {y | (fun i : ℕ => y ((i : ℤ) + 1)) ∈ B} := by
  set mc : ℤ → MeasurableSpace (ℤ → β) :=
    fun i => MeasurableSpace.comap (fun y : ℤ → β => y i) inferInstance with hmc
  have hind : iIndep mc (bernoulli P) :=
    (iIndepFun_infinitePi (P := fun _ : ℤ => P) (X := fun _ (ω : β) => ω)
      (fun _ => measurable_id)).iIndep
  have hle : ∀ i : ℤ, mc i ≤ MeasurableSpace.pi := fun i => (measurable_pi_apply i).comap_le
  have hdisj : Disjoint ({0} : Set ℤ) {i : ℤ | 0 < i} := by
    rw [Set.disjoint_singleton_left]
    simp
  have h := indep_iSup_of_disjoint hle hind hdisj
  rw [Indep_iff] at h
  apply h
  · have h0 : MeasurableSet[mc 0] {y : ℤ → β | y 0 ∈ A} := ⟨A, hA, rfl⟩
    exact (le_iSup₂ (f := fun i (_ : i ∈ ({0} : Set ℤ)) => mc i) 0 rfl) _ h0
  · have hR : MeasurableSpace.comap (fun y : ℤ → β => fun i : ℕ => y ((i : ℤ) + 1))
        MeasurableSpace.pi ≤ ⨆ i ∈ {i : ℤ | 0 < i}, mc i := by
      rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
      refine iSup_le fun i => ?_
      rw [MeasurableSpace.comap_comp]
      exact le_iSup₂ (f := fun i (_ : i ∈ {i : ℤ | 0 < i}) => mc i) ((i : ℤ) + 1)
        (by simp only [mem_ofPred_eq]; omega)
    exact hR _ ⟨B, hB, rfl⟩

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

noncomputable def blockBernoulli (m : ℕ) [NeZero m] (p : (Fin m → α) → ℝ) :
    Measure (ℤ → α) :=
  (bernoulli (weightMeasure p)).map (concat m)

omit [MeasurableSingletonClass α] in

theorem isProbabilityMeasure_blockBernoulli (m : ℕ) [NeZero m] {p : (Fin m → α) → ℝ}
    (hp : ∀ w, 0 ≤ p w) (hsum : ∑ w, p w = 1) : IsProbabilityMeasure (blockBernoulli m p) := by
  have := isProbabilityMeasure_weightMeasure hp hsum
  rw [blockBernoulli]
  infer_instance

end BlockBernoulli

def extendLeft {β : Type*} (b : β) (z : ℕ → β) : ℤ → β :=
  fun k => if 0 ≤ k then z k.toNat else b

theorem measurable_extendLeft {β : Type*} [MeasurableSpace β] (b : β) :
    Measurable (extendLeft b : (ℕ → β) → ℤ → β) := by
  refine Measurable.of_eval fun k => ?_
  by_cases hk : 0 ≤ k
  · simp only [extendLeft, hk, ite_true]
    exact measurable_pi_apply _
  · simp only [extendLeft, hk, ite_false]
    exact measurable_const

theorem extendLeft_natCast {β : Type*} (b : β) (z : ℕ → β) (k : ℕ) :
    extendLeft b z k = z k := by
  simp [extendLeft]

theorem concat_natCast {β : Type*} (m : ℕ) [NeZero m] (y : ℤ → (Fin m → β)) (k : ℕ) :
    concat m y k = y ((k / m : ℕ) : ℤ)
      ⟨k % m, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))⟩ := by
  have h1 : ((k : ℤ) / (m : ℤ)) = ((k / m : ℕ) : ℤ) := (Int.natCast_div k m).symm
  have h2 : ((k : ℤ) % (m : ℤ)).toNat % m = k % m := by
    rw [← Int.natCast_mod, Int.toNat_natCast, Nat.mod_mod]
  simp only [concat, h1]
  congr 1
  exact Fin.ext h2

namespace LineIFS

variable {ι : Type*} {S : LineIFS ι} {r M : ℝ}

theorem Bounds.code_concat (hS : S.Bounds r M) (m : ℕ) [NeZero m]
    (y : ℤ → (Fin m → ι)) :
    S.code (concat m y) = S.gWord (List.ofFn (y 0)) (S.code (concat m (shift 1 y))) := by
  rw [hS.code_eq_gWord (concat m y) m, futureWord_eq_ofFn_block, concat_shift]
  congr 2
  funext k
  simp [block, concat_coe]

theorem code_concat_congr (S : LineIFS ι) (m : ℕ) [NeZero m]
    {y y' : ℤ → (Fin m → ι)} (h : ∀ k : ℕ, y k = y' k) :
    S.code (concat m y) = S.code (concat m y') := by
  refine S.code_congr fun k => ?_
  rw [concat_natCast, concat_natCast, h]

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem Bounds.map_code_blockBernoulli (hS : S.Bounds r M) (m : ℕ) [NeZero m]
    {p : (Fin m → ι) → ℝ} (hp : ∀ w, 0 ≤ p w) (hsum : ∑ w, p w = 1) :
    (blockBernoulli m p).map S.code = ∑ w, ENNReal.ofReal (p w) •
      ((blockBernoulli m p).map S.code).map
        (fun x => S.blockRatio m w * x + S.blockTrans m w) := by
  classical
  have hP := isProbabilityMeasure_weightMeasure hp hsum
  obtain ⟨d⟩ := nonempty_of_isProbabilityMeasure (weightMeasure p)
  have hmeas := hS.measurable_code
  set PB : (ℤ → (Fin m → ι)) → ℝ := fun y => S.code (concat m y) with hPB
  have hPBm : Measurable PB := hmeas.comp (measurable_concat m)
  set G : (ℕ → (Fin m → ι)) → ℝ := fun z => PB (extendLeft d z) with hG
  have hGm : Measurable G := hPBm.comp (measurable_extendLeft d)
  set bern := bernoulli (weightMeasure p) with hbern
  have hφ : ∀ w, (fun x => S.blockRatio m w * x + S.blockTrans m w) = S.gWord (List.ofFn w) := by
    intro w; funext x; rw [S.gWord_apply]; rfl
  have hφm : ∀ w, Measurable (fun x : ℝ => S.blockRatio m w * x + S.blockTrans m w) :=
    fun w => (measurable_const.mul measurable_id).add measurable_const

  have hsplit : ∀ y, PB y = S.gWord (List.ofFn (y 0)) (G fun i : ℕ => y ((i : ℤ) + 1)) := by
    intro y
    show S.code (concat m y) = _
    rw [hS.code_concat m y]
    congr 1
    refine S.code_concat_congr m fun k => ?_
    rw [extendLeft_natCast, shift_apply, add_comm]
  have hsplit' : ∀ y, PB y = S.blockRatio m (y 0) * (G fun i : ℕ => y ((i : ℤ) + 1)) +
      S.blockTrans m (y 0) := by
    intro y
    rw [hsplit y, S.gWord_apply]
    rfl
  have hfront : ∀ y, PB y = G fun i : ℕ => y i := by
    intro y
    refine S.code_concat_congr m fun k => ?_
    rw [extendLeft_natCast]
  have hmap : (blockBernoulli m p).map S.code = bern.map PB := by
    rw [blockBernoulli, Measure.map_map hmeas (measurable_concat m)]; rfl
  rw [hmap]
  refine Measure.ext fun A hA => ?_
  rw [Measure.finsetSum_apply, Measure.map_apply hPBm hA]
  simp only [Measure.smul_apply, smul_eq_mul]
  have hterm : ∀ w, bern ({y | y 0 ∈ ({w} : Set _)} ∩ PB ⁻¹' A) =
      ENNReal.ofReal (p w) * (bern.map PB)
        ((fun x => S.blockRatio m w * x + S.blockTrans m w) ⁻¹' A) := by
    intro w
    have hset : {y : ℤ → (Fin m → ι) | y 0 ∈ ({w} : Set _)} ∩ PB ⁻¹' A =
        {y | y 0 ∈ ({w} : Set _)} ∩ {y | (fun i : ℕ => y ((i : ℤ) + 1)) ∈
          G ⁻¹' ((fun x => S.blockRatio m w * x + S.blockTrans m w) ⁻¹' A)} := by
      ext y
      simp only [mem_inter_iff, mem_ofPred_eq, mem_singleton_iff, mem_preimage]
      constructor
      · rintro ⟨h0, h1⟩
        refine ⟨h0, ?_⟩
        rwa [hsplit', h0] at h1
      · rintro ⟨h0, h1⟩
        refine ⟨h0, ?_⟩
        rwa [hsplit', h0]
    rw [hset, bernoulli_inter_tail _ (measurableSet_singleton w)
      (hGm (hφm w hA))]
    congr 1
    · have := bernoulli_cylinder (weightMeasure p) 0 (![w] : Fin 1 → _)
      simp only [zero_add, Fin.prod_univ_one, Matrix.cons_val_zero, weightMeasure_singleton]
        at this
      rw [← this]
      congr 1
      ext y
      simp
    · rw [Measure.map_apply hPBm (hφm w hA)]
      have hshift := (measurePreserving_shift_bernoulli (weightMeasure p) 1).measure_preimage
        ((hGm.comp (Measurable.of_eval (f := fun y : ℤ → (Fin m → ι) => fun i : ℕ => y i)
          fun i => measurable_pi_apply _)) (hφm w hA)).nullMeasurableSet
      have hPBeq : PB = G ∘ (fun y : ℤ → (Fin m → ι) => fun i : ℕ => y i) :=
        funext hfront
      rw [hPBeq, ← hshift]
      congr 1
      ext y
      simp only [mem_preimage, mem_ofPred_eq, Function.comp_apply, shift_apply]
      rw [show (fun i : ℕ => y ((i : ℤ) + 1)) = fun i : ℕ => y (1 + (i : ℤ)) by
        funext i; rw [add_comm]]
  have hmapφ : ∀ w, (Measure.map (fun x => S.blockRatio m w * x + S.blockTrans m w)
      (Measure.map PB bern)) A = (Measure.map PB bern)
        ((fun x => S.blockRatio m w * x + S.blockTrans m w) ⁻¹' A) :=
    fun w => Measure.map_apply (hφm w) hA
  simp only [hmapφ]
  rw [← Finset.sum_congr rfl fun w _ => hterm w]
  have hunion : PB ⁻¹' A = ⋃ w ∈ (Finset.univ : Finset (Fin m → ι)),
      {y | y 0 ∈ ({w} : Set _)} ∩ PB ⁻¹' A := by
    ext y; simp
  have hdisj : (↑(Finset.univ : Finset (Fin m → ι)) : Set _).PairwiseDisjoint
      (fun w => {y : ℤ → (Fin m → ι) | y 0 ∈ ({w} : Set _)} ∩ PB ⁻¹' A) := by
    intro w _ w' _ hww'
    refine Set.disjoint_left.2 fun y hy hy' => hww' ?_
    simp only [mem_inter_iff, mem_ofPred_eq, mem_singleton_iff] at hy hy'
    rw [← hy.1, ← hy'.1]
  have hm' : ∀ w ∈ (Finset.univ : Finset (Fin m → ι)),
      MeasurableSet ({y : ℤ → (Fin m → ι) | y 0 ∈ ({w} : Set _)} ∩ PB ⁻¹' A) :=
    fun w _ => ((measurable_pi_apply 0) (measurableSet_singleton w)).inter (hPBm hA)
  rw [show bern (PB ⁻¹' A) = bern (⋃ w ∈ (Finset.univ : Finset (Fin m → ι)),
      {y | y 0 ∈ ({w} : Set _)} ∩ PB ⁻¹' A) from congrArg bern hunion,
    measure_biUnion_finset hdisj hm']

end LineIFS

section Alignment

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

def blocksOf (m : ℕ) {β : Type*} (z : ℤ → β) : ℤ → (Fin m → β) :=
  fun k r => z (k * m + r)

theorem blockBernoulli_shift_cylinder_ge (m : ℕ) [NeZero m] {p : (Fin m → α) → ℝ}
    (hp : ∀ w, 0 ≤ p w) (hsum : ∑ w, p w = 1) {pmin : ℝ} (hpmin : ∀ w, pmin ≤ p w)
    (y : ℤ → α) (n s : ℕ) (hs : s < m) :
    pmin * ∏ k ∈ Finset.range n, p (block m (shift ((k * m + s : ℕ) : ℤ) y)) ≤
      ((blockBernoulli m p).map (shift ((m - s : ℕ) : ℤ))).real (cylinder (block (n * m) y)) := by
  have hP := isProbabilityMeasure_weightMeasure hp hsum
  set j : ℕ := m - s with hj
  set z : ℤ → α := shift (-(j : ℤ)) y with hz
  set Y : ℤ → (Fin m → α) := blocksOf m z with hY
  set C : Set (ℤ → (Fin m → α)) := {Y' | ∀ i : Fin (n + 1), Y' (0 + i) = Y i} with hC
  have hCm : bernoulli (weightMeasure p) C = ∏ i : Fin (n + 1), ENNReal.ofReal (p (Y i)) := by
    rw [hC, bernoulli_cylinder (weightMeasure p) 0 (fun i : Fin (n + 1) => Y i)]
    simp only [weightMeasure_singleton]
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hsub : C ⊆ concat m ⁻¹' (shift (j : ℤ) ⁻¹' cylinder (block (n * m) y)) := by
    intro Y' hY'
    simp only [mem_preimage, mem_cylinder, shift_apply, block]
    intro t
    set P : ℕ := j + t with hP
    have hPZ : (j : ℤ) + ((t : ℕ) : ℤ) = (P : ℤ) := by rw [hP]; push_cast; ring
    rw [hPZ, concat_natCast]
    have hPlt : P / m < n + 1 := by
      rw [Nat.div_lt_iff_lt_mul hm0]
      have := t.2
      have hjm : j ≤ m := Nat.sub_le m s
      rw [hP]
      nlinarith
    have h1 := hY' ⟨P / m, hPlt⟩
    simp only [zero_add] at h1
    rw [h1, hY, blocksOf, hz, shift_apply]
    congr 1
    have hdm := Nat.div_add_mod' P m
    have : ((P / m : ℕ) : ℤ) * (m : ℤ) + ((P % m : ℕ) : ℤ) = (P : ℤ) := by exact_mod_cast hdm
    rw [this, hP]
    push_cast
    ring

  have hmeas : MeasurableSet (shift (j : ℤ) ⁻¹' cylinder (block (n * m) y)) :=
    measurable_shift _ (measurableSet_cylinder _)
  rw [map_measureReal_apply (measurable_shift _) (measurableSet_cylinder _), blockBernoulli,
    map_measureReal_apply (measurable_concat m) hmeas]
  have hle : (bernoulli (weightMeasure p)).real C ≤ (bernoulli (weightMeasure p)).real
      (concat m ⁻¹' (shift (j : ℤ) ⁻¹' cylinder (block (n * m) y))) := measureReal_mono hsub
  refine le_trans ?_ hle
  rw [measureReal_def, hCm, ENNReal.toReal_prod]
  simp only [ENNReal.toReal_ofReal (hp _)]
  rw [Fin.prod_univ_succ]
  have hblock : ∀ i : Fin n,
      p (Y ((i.succ : ℕ) : ℤ)) = p (block m (shift ((i * m + s : ℕ) : ℤ) y)) := by
    intro i
    congr 1
    funext r
    simp only [hY, blocksOf, hz, block, shift_apply, Fin.val_succ]
    congr 1
    rw [hj, Nat.cast_sub hs.le]
    push_cast
    ring
  rw [Finset.prod_congr rfl fun i _ => hblock i,
    Fin.prod_univ_eq_prod_range (fun k => p (block m (shift ((k * m + s : ℕ) : ℤ) y))) n]
  exact mul_le_mul_of_nonneg_right (hpmin _) (Finset.prod_nonneg fun _ _ => hp _)

end Alignment

theorem lq_sum_lt_one {K : Type*} [Fintype K] (p rr : K → ℝ) (W : Finset K)
    {q α m L h a δ ℓ₁ ℓA : ℝ} (hp : ∀ w, 0 < p w) (hsum : ∑ w, p w = 1) (hr : ∀ w, 0 < rr w)
    (hW : ∀ w ∈ W, p w ≤ 2 * Real.exp (-(m * (h - δ))) ∧ Real.exp (-(m * (a + δ))) ≤ rr w)
    (hWc : ∀ w ∉ W, p w ≤ 2 * Real.exp (-(m * L)) ∧ Real.exp (-(m * ℓ₁)) ≤ rr w)
    (hcard : (Fintype.card K : ℝ) ≤ Real.exp (m * ℓA)) (hℓ₁ : 0 ≤ ℓ₁) (hℓA : 0 ≤ ℓA)
    (hq : 3 ≤ q) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hαh : α * (a + δ) ≤ h - 2 * δ)
    (hmδ : 1 + Real.log 2 ≤ m * δ) (hL : ℓ₁ + ℓA + 1 ≤ L) (hm2 : 3 ≤ m) :
    ∑ w, p w ^ q * rr w ^ (-((q - 1) * α)) < 1 := by
  classical
  have hq1 : 0 ≤ q - 1 := by linarith
  have he : (0 : ℝ) ≤ (q - 1) * α := mul_nonneg hq1 hα0

  have hWterm : ∀ w ∈ W, p w ^ q * rr w ^ (-((q - 1) * α)) ≤ p w * Real.exp (-2) := by
    intro w hw
    obtain ⟨h1, h2⟩ := hW w hw
    have hpq : p w ^ q = p w * p w ^ (q - 1) := by
      rw [← Real.rpow_one_add' (hp w).le (by linarith)]; congr 1; ring
    rw [hpq, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hp w).le
    have h3 : p w ^ (q - 1) ≤ (2 * Real.exp (-(m * (h - δ)))) ^ (q - 1) :=
      Real.rpow_le_rpow (hp w).le h1 hq1
    have h4 : rr w ^ (-((q - 1) * α)) ≤ (Real.exp (-(m * (a + δ)))) ^ (-((q - 1) * α)) :=
      Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) h2 (by linarith)
    have h5 : (2 * Real.exp (-(m * (h - δ)))) ^ (q - 1) *
        (Real.exp (-(m * (a + δ)))) ^ (-((q - 1) * α)) =
        Real.exp ((q - 1) * (Real.log 2 - m * (h - δ) + m * (a + δ) * α)) := by
      rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.exp_mul, ← Real.exp_mul,
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    have h6 : (q - 1) * (Real.log 2 - m * (h - δ) + m * (a + δ) * α) ≤ -2 := by
      have h7 : Real.log 2 - m * (h - δ) + m * (a + δ) * α ≤ -1 := by
        have : m * (a + δ) * α ≤ m * (h - 2 * δ) := by
          rw [mul_assoc, mul_comm (a + δ) α]
          exact mul_le_mul_of_nonneg_left hαh (by linarith)
        nlinarith
      nlinarith
    calc p w ^ (q - 1) * rr w ^ (-((q - 1) * α))
        ≤ (2 * Real.exp (-(m * (h - δ)))) ^ (q - 1) *
            (Real.exp (-(m * (a + δ)))) ^ (-((q - 1) * α)) :=
            mul_le_mul h3 h4 (Real.rpow_pos_of_pos (hr w) _).le (by positivity)
      _ = Real.exp ((q - 1) * (Real.log 2 - m * (h - δ) + m * (a + δ) * α)) := h5
      _ ≤ Real.exp (-2) := Real.exp_le_exp.2 h6

  have hWcterm : ∀ w ∉ W, p w ^ q * rr w ^ (-((q - 1) * α)) ≤
      Real.exp (q * Real.log 2 - q * m * (ℓA + 1)) := by
    intro w hw
    obtain ⟨h1, h2⟩ := hWc w hw
    have h3 : p w ^ q ≤ (2 * Real.exp (-(m * L))) ^ q :=
      Real.rpow_le_rpow (hp w).le h1 (by linarith)
    have h4 : rr w ^ (-((q - 1) * α)) ≤ (Real.exp (-(m * ℓ₁))) ^ (-((q - 1) * α)) :=
      Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) h2 (by linarith)
    have h5 : (2 * Real.exp (-(m * L))) ^ q * (Real.exp (-(m * ℓ₁))) ^ (-((q - 1) * α)) =
        Real.exp (q * Real.log 2 - q * m * L + m * ℓ₁ * ((q - 1) * α)) := by
      rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.exp_mul, ← Real.exp_mul,
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    have h6 : q * Real.log 2 - q * m * L + m * ℓ₁ * ((q - 1) * α) ≤
        q * Real.log 2 - q * m * (ℓA + 1) := by
      have h7 : (q - 1) * α ≤ q := by nlinarith
      have h8 : m * ℓ₁ * ((q - 1) * α) ≤ m * ℓ₁ * q :=
        mul_le_mul_of_nonneg_left h7 (by nlinarith)
      have h9 : q * m * (ℓ₁ + ℓA + 1) ≤ q * m * L :=
        mul_le_mul_of_nonneg_left hL (by nlinarith)
      nlinarith
    calc p w ^ q * rr w ^ (-((q - 1) * α))
        ≤ (2 * Real.exp (-(m * L))) ^ q * (Real.exp (-(m * ℓ₁))) ^ (-((q - 1) * α)) :=
          mul_le_mul h3 h4 (Real.rpow_pos_of_pos (hr w) _).le (by positivity)
      _ = _ := h5
      _ ≤ _ := Real.exp_le_exp.2 h6
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun w => w ∈ W)
    (fun w => p w ^ q * rr w ^ (-((q - 1) * α)))
  rw [← hsplit]
  have hA : ∑ w ∈ Finset.univ.filter (fun w => w ∈ W), p w ^ q * rr w ^ (-((q - 1) * α)) ≤
      Real.exp (-2) := by
    calc _ ≤ ∑ w ∈ Finset.univ.filter (fun w => w ∈ W), p w * Real.exp (-2) :=
          Finset.sum_le_sum fun w hw => hWterm w (Finset.mem_filter.1 hw).2
      _ = (∑ w ∈ Finset.univ.filter (fun w => w ∈ W), p w) * Real.exp (-2) := by
          rw [Finset.sum_mul]
      _ ≤ (∑ w, p w) * Real.exp (-2) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun w _ _ => (hp w).le
      _ = Real.exp (-2) := by rw [hsum, one_mul]
  have hB : ∑ w ∈ Finset.univ.filter (fun w => w ∉ W), p w ^ q * rr w ^ (-((q - 1) * α)) ≤
      2 * Real.exp (-m) := by
    calc _ ≤ ∑ w ∈ Finset.univ.filter (fun w => w ∉ W),
          Real.exp (q * Real.log 2 - q * m * (ℓA + 1)) :=
          Finset.sum_le_sum fun w hw => hWcterm w (Finset.mem_filter.1 hw).2
      _ ≤ ∑ _w : K, Real.exp (q * Real.log 2 - q * m * (ℓA + 1)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => (Real.exp_pos _).le
      _ = (Fintype.card K : ℝ) * Real.exp (q * Real.log 2 - q * m * (ℓA + 1)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ Real.exp (m * ℓA) * Real.exp (q * Real.log 2 - q * m * (ℓA + 1)) :=
          mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
      _ = Real.exp (q * (Real.log 2 - m) - (q - 1) * m * ℓA) := by
          rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (Real.log 2 - m) := by
          refine Real.exp_le_exp.2 ?_
          have h1 : 0 ≤ (q - 1) * m * ℓA := by
            have : 0 ≤ (q - 1) * m := mul_nonneg hq1 (by linarith)
            exact mul_nonneg this hℓA
          have h2 : Real.log 2 - m ≤ 0 := by
            have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
          nlinarith
      _ = 2 * Real.exp (-m) := by
          rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num)]
  have hfin : Real.exp (-2) + 2 * Real.exp (-m) < 1 := by
    have h1 : Real.exp (-m) ≤ Real.exp (-3) := Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (-2) ≤ 1 / 3 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 2) (by norm_num)]
      have := Real.add_one_le_exp (2 : ℝ)
      norm_num at this ⊢
      linarith
    have h3 : Real.exp (-3) ≤ 1 / 4 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 3) (by norm_num)]
      have := Real.add_one_le_exp (3 : ℝ)
      norm_num at this ⊢
      linarith
    linarith
  linarith

theorem eventually_measureReal_ge_of_ae_eventually {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {T : ℕ → Set X} (hT : ∀ m, MeasurableSet (T m))
    (h : ∀ᵐ y ∂μ, ∀ᶠ m in atTop, y ∈ T m) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m in atTop, 1 - ε ≤ μ.real (T m) := by
  set S : ℕ → Set X := fun N => ⋂ m ∈ Ici N, T m with hS
  have hSm : ∀ N, MeasurableSet (S N) := fun N =>
    MeasurableSet.biInter (to_countable _) fun m _ => hT m
  have hmono : Monotone S := by
    intro N N' hNN' y hy
    simp only [hS, mem_iInter, mem_Ici] at hy ⊢
    exact fun m hm => hy m (hNN'.trans hm)
  have hfull : μ (⋃ N, S N) = 1 := by
    rw [← prob_compl_eq_zero_iff (MeasurableSet.iUnion hSm)]
    have h' : ∀ᵐ y ∂μ, y ∈ ⋃ N, S N := by
      filter_upwards [h] with y hy
      obtain ⟨N, hN⟩ := hy.exists_forall_of_atTop
      exact mem_iUnion.2 ⟨N, by simp only [hS, mem_iInter, mem_Ici]; exact hN⟩
    rw [ae_iff] at h'
    simpa only [compl_def] using h'
  have hT' := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [hfull] at hT'
  have hlt : ENNReal.ofReal (1 - ε) < 1 := by
    rw [ENNReal.ofReal_lt_one]; linarith
  obtain ⟨N₀, hN₀⟩ := (hT'.eventually_const_lt hlt).exists_forall_of_atTop
  filter_upwards [eventually_ge_atTop N₀] with m hm
  have h1 : μ (S N₀) ≤ μ (T m) := measure_mono fun y hy => by
    simp only [hS, mem_iInter, mem_Ici] at hy
    exact hy m hm
  have h2 := (hN₀ N₀ le_rfl).le.trans h1
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 h2

theorem sum_measureReal_cylinder_eq {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {m : ℕ} (μ : Measure (ℤ → α)) [IsFiniteMeasure μ] (W : Finset (Fin m → α)) :
    ∑ w ∈ W, μ.real (cylinder w) = μ.real {y | block m y ∈ W} := by
  have hset : {y : ℤ → α | block m y ∈ W} = ⋃ w ∈ W, cylinder w := by
    ext y
    simp only [mem_ofPred_eq, mem_iUnion, cylinder_eq_preimage, mem_preimage, mem_singleton_iff,
      exists_prop, exists_eq_right']
  rw [hset, measureReal_biUnion_finset]
  · intro w _ w' _ hww'
    refine Set.disjoint_left.2 fun y hy hy' => hww' ?_
    rw [cylinder_eq_preimage] at hy hy'
    rw [← hy, ← hy']
  · exact fun w _ => measurableSet_cylinder w

theorem sum_range_mul_eq_sum_sum {M : Type*} [AddCommMonoid M] (g : ℕ → M) (n m : ℕ) :
    ∑ t ∈ Finset.range (n * m), g t =
      ∑ s ∈ Finset.range m, ∑ k ∈ Finset.range n, g (k * m + s) := by
  rw [Finset.sum_comm]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem eventually_le_rpow_of_scales {f : ℝ → ℝ} {a b s C : ℝ} (ha : 0 < a) (hs : 0 ≤ s)
    (hb : a * s < b) {N : ℕ}
    (h : ∀ n : ℕ, N ≤ n → ∀ ρ : ℝ, 0 < ρ → ρ ≤ Real.exp (-(n * a)) →
      f ρ ≤ C * Real.exp (-(n * b))) :
    ∀ᶠ ρ : ℝ in 𝓝[>] 0, f ρ ≤ ρ ^ s := by

  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n →
      C * Real.exp (-(n * b)) ≤ Real.exp (-((n + 1) * a * s)) := by
    have hpos : 0 < b - a * s := by linarith
    obtain ⟨N₁, hN₁⟩ := exists_nat_ge ((abs (Real.log C) + a * s) / (b - a * s))
    refine ⟨N₁, fun n hn => ?_⟩
    rcases le_or_gt C 0 with hC | hC
    · exact le_trans (mul_nonpos_of_nonpos_of_nonneg hC (Real.exp_pos _).le) (Real.exp_pos _).le
    · rw [← Real.exp_log hC, ← Real.exp_add, Real.exp_le_exp]
      have h1 : (abs (Real.log C) + a * s) / (b - a * s) ≤ n :=
        hN₁.trans (by exact_mod_cast hn)
      rw [div_le_iff₀ hpos] at h1
      have h2 : Real.log C ≤ abs (Real.log C) := le_abs_self _
      nlinarith
  set N₂ := max N N₁ with hN₂
  have hpos : 0 < Real.exp (-(N₂ * a)) := Real.exp_pos _
  filter_upwards [Ioo_mem_nhdsGT hpos] with ρ hρ
  obtain ⟨hρ0, hρ1⟩ := hρ
  set t : ℝ := Real.log (1 / ρ) / a with ht
  have h1ρ : 0 < 1 / ρ := one_div_pos.2 hρ0
  have hNt : (N₂ : ℝ) ≤ t := by
    rw [ht, le_div_iff₀ ha]
    have : Real.exp (N₂ * a) < 1 / ρ := by
      rw [lt_div_iff₀ hρ0]
      calc Real.exp (N₂ * a) * ρ < Real.exp (N₂ * a) * Real.exp (-(N₂ * a)) :=
            mul_lt_mul_of_pos_left hρ1 (Real.exp_pos _)
        _ = 1 := by rw [← Real.exp_add]; simp
    have := (Real.lt_log_iff_exp_lt h1ρ).2 this
    linarith
  have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg _) hNt
  set n : ℕ := ⌊t⌋₊ with hn
  have hnN : N₂ ≤ n := Nat.le_floor hNt
  have hnt : (n : ℝ) ≤ t := Nat.floor_le ht0
  have htn : t < n + 1 := Nat.lt_floor_add_one t
  have hρn : ρ ≤ Real.exp (-(n * a)) := by
    have : (n : ℝ) * a ≤ Real.log (1 / ρ) := by
      rw [ht, le_div_iff₀ ha] at hnt; linarith
    rw [← Real.exp_log hρ0, Real.exp_le_exp]
    rw [one_div, Real.log_inv] at this
    linarith
  have hρn1 : Real.exp (-((n + 1) * a)) < ρ := by
    have : Real.log (1 / ρ) < (n + 1) * a := by
      rw [ht, div_lt_iff₀ ha] at htn; linarith
    rw [← Real.exp_log hρ0, Real.exp_lt_exp]
    rw [one_div, Real.log_inv] at this
    linarith
  calc f ρ ≤ C * Real.exp (-(n * b)) := h n (le_trans (le_max_left _ _) hnN) ρ hρ0 hρn
    _ ≤ Real.exp (-((n + 1) * a * s)) := hN₁ n (le_trans (le_max_right _ _) hnN)
    _ = (Real.exp (-((n + 1) * a))) ^ s := by rw [← Real.exp_mul]; ring_nf
    _ ≤ ρ ^ s := Real.rpow_le_rpow (Real.exp_pos _).le hρn1.le hs

namespace LineIFS

theorem birkhoffSum_log_abs_ratio {ι : Type*} (S : LineIFS ι) (y : ℤ → ι) (n : ℕ) :
    birkhoffSum (shift 1) (fun y : ℤ → ι => Real.log |S.ratio (y 0)|) n y =
      Real.log |S.gDeriv (futureWord y n)| := by
  rw [birkhoffSum, S.log_abs_gDeriv_futureWord]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iterate_shift_one]
  simp

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem integrable_log_abs_ratio (S : LineIFS ι) (ν : Measure (ℤ → ι))
    [IsProbabilityMeasure ν] :
    Integrable (fun y : ℤ → ι => Real.log |S.ratio (y 0)|) ν := by
  have hmeas : Measurable fun y : ℤ → ι => Real.log |S.ratio (y 0)| :=
    (Measurable.of_discrete (f := fun p : ι => Real.log |S.ratio p|)).comp
      (measurable_pi_apply 0)
  refine Integrable.mono' (integrable_const (∑ p : ι, abs (Real.log |S.ratio p|)))
    hmeas.aestronglyMeasurable (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun p : ι => abs (Real.log |S.ratio p|))
    (fun _ _ => abs_nonneg _) (Finset.mem_univ (y 0))

noncomputable def typicalBlocks (S : LineIFS ι) (ν : Measure (ℤ → ι)) (h a δ : ℝ)
    (m : ℕ) : Finset (Fin m → ι) := by
  classical
  exact Finset.univ.filter fun w => Real.exp (-(m * (h + δ))) ≤ ν.real (cylinder w) ∧
    ν.real (cylinder w) ≤ Real.exp (-(m * (h - δ))) ∧
    Real.exp (-(m * (a + δ))) ≤ |S.gDeriv (List.ofFn w)|

omit [MeasurableSingletonClass ι] in

theorem mem_typicalBlocks {S : LineIFS ι} {ν : Measure (ℤ → ι)} {h a δ : ℝ} {m : ℕ}
    {w : Fin m → ι} :
    w ∈ S.typicalBlocks ν h a δ m ↔ Real.exp (-(m * (h + δ))) ≤ ν.real (cylinder w) ∧
      ν.real (cylinder w) ≤ Real.exp (-(m * (h - δ))) ∧
      Real.exp (-(m * (a + δ))) ≤ |S.gDeriv (List.ofFn w)| := by
  classical
  simp [typicalBlocks]

theorem eventually_sum_typicalBlocks (S : LineIFS ι) (ν : Measure (ℤ → ι))
    [IsProbabilityMeasure ν] (herg : Ergodic (shift 1) ν) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, 1 - δ ≤
      ∑ w ∈ S.typicalBlocks ν (entropy ν) (-S.lyapunov ν) δ m, ν.real (cylinder w) := by
  have hT : ∀ m : ℕ, MeasurableSet
      {y : ℤ → ι | block m y ∈ S.typicalBlocks ν (entropy ν) (-S.lyapunov ν) δ m} :=
    fun m => measurable_block m (Finset.measurableSet _)
  have hae : ∀ᵐ y ∂ν, ∀ᶠ m in atTop,
      y ∈ {y : ℤ → ι | block m y ∈ S.typicalBlocks ν (entropy ν) (-S.lyapunov ν) δ m} := by
    filter_upwards [ae_eventually_block_mem_typicalWords herg hδ,
      birkhoff_ergodic herg (S.integrable_log_abs_ratio ν)] with y hy hbk
    have hbk' : ∀ᶠ m : ℕ in atTop, birkhoffAverage ℝ (shift 1)
        (fun y : ℤ → ι => Real.log |S.ratio (y 0)|) m y > S.lyapunov ν - δ := by
      refine hbk.eventually_const_lt ?_
      rw [lyapunov]
      linarith
    filter_upwards [hy, hbk', eventually_gt_atTop 0] with m hm hbm hm0
    rw [mem_typicalWords] at hm
    have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 hm0
    rw [birkhoffAverage, birkhoffSum_log_abs_ratio, smul_eq_mul, gt_iff_lt,
      lt_inv_mul_iff₀ hmpos] at hbm
    simp only [mem_typicalBlocks]
    refine ⟨hm.1, hm.2, ?_⟩
    rw [← futureWord_eq_ofFn_block]
    have hpos : 0 < |S.gDeriv (futureWord y m)| := abs_pos.2 (S.gDeriv_ne_zero _)
    rw [← Real.exp_log hpos, Real.exp_le_exp]
    linarith
  filter_upwards [eventually_measureReal_ge_of_ae_eventually hT hae hδ] with m hm
  rwa [sum_measureReal_cylinder_eq]

end LineIFS

theorem exists_blockWeights {K : Type*} [Fintype K] (μw : K → ℝ) (W : Finset K) {δ e : ℝ}
    (hμ0 : ∀ w, 0 ≤ μw w) (hμsum : ∑ w, μw w = 1) (hpos : ∀ w ∈ W, 0 < μw w)
    (hW : 1 - δ ≤ ∑ w ∈ W, μw w) (hδ : δ ≤ 1 / 2) (he : 0 < e)
    (hcard : (Fintype.card K : ℝ) * e ≤ 1) :
    ∃ p : K → ℝ, (∀ w, 0 < p w) ∧ ∑ w, p w = 1 ∧
      (∀ w ∈ W, μw w / 2 ≤ p w ∧ p w ≤ 2 * μw w) ∧ (∀ w ∉ W, e / 2 ≤ p w ∧ p w ≤ 2 * e) := by
  classical
  set g : K → ℝ := fun w => if w ∈ W then μw w else e with hg
  set Z := ∑ w, g w with hZ
  have hgpos : ∀ w, 0 < g w := by
    intro w; simp only [hg]; split_ifs with h
    · exact hpos w h
    · exact he
  have hZsplit : Z = ∑ w ∈ W, μw w + ∑ w ∈ Finset.univ.filter (fun w => w ∉ W), e := by
    rw [hZ, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun w => w ∈ W)]
    congr 1
    · rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact Finset.sum_congr rfl fun w hw => by simp [hg, hw]
    · exact Finset.sum_congr rfl fun w hw => by simp [hg, (Finset.mem_filter.1 hw).2]
  have hWle : ∑ w ∈ W, μw w ≤ 1 := by
    rw [← hμsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun w _ _ => hμ0 w
  have hcle : ∑ w ∈ Finset.univ.filter (fun w => w ∉ W), e ≤ 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    refine le_trans (mul_le_mul_of_nonneg_right ?_ he.le) hcard
    exact_mod_cast Finset.card_le_univ _
  have hcnn : 0 ≤ ∑ w ∈ Finset.univ.filter (fun w => w ∉ W), e :=
    Finset.sum_nonneg fun _ _ => he.le
  have hZ1 : 1 / 2 ≤ Z := by rw [hZsplit]; linarith
  have hZ2 : Z ≤ 2 := by rw [hZsplit]; linarith
  have hZpos : 0 < Z := by linarith
  refine ⟨fun w => g w / Z, fun w => div_pos (hgpos w) hZpos, ?_, ?_, ?_⟩
  · rw [← Finset.sum_div, ← hZ, div_self hZpos.ne']
  · intro w hw
    have hgw : g w = μw w := by simp [hg, hw]
    simp only [hgw]
    have hμw := hpos w hw
    constructor
    · rw [div_le_div_iff₀ (by norm_num) hZpos]; nlinarith
    · rw [div_le_iff₀ hZpos]; nlinarith
  · intro w hw
    have hgw : g w = e := by simp [hg, hw]
    simp only [hgw]
    constructor
    · rw [div_le_div_iff₀ (by norm_num) hZpos]; nlinarith
    · rw [div_le_iff₀ hZpos]; nlinarith

theorem integral_neg_log_weight_le {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure (ℤ → α)) [IsProbabilityMeasure ν] (m : ℕ)
    (p : (Fin m → α) → ℝ) (W : Finset (Fin m → α)) {B₁ B₂ δ : ℝ}
    (hW : ∀ w ∈ W, -Real.log (p w) ≤ B₁) (hWc : ∀ w ∉ W, -Real.log (p w) ≤ B₂)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hmass : 1 - δ ≤ ∑ w ∈ W, ν.real (cylinder w)) :
    ∫ y, -Real.log (p (block m y)) ∂ν ≤ B₁ + δ * B₂ := by
  classical
  have hmap : ∫ y, -Real.log (p (block m y)) ∂ν =
      ∫ w, -Real.log (p w) ∂(ν.map (block m)) :=
    (integral_map (measurable_block m).aemeasurable
      (Measurable.of_discrete
        (f := fun w : Fin m → α => -Real.log (p w))).aestronglyMeasurable).symm
  rw [hmap, integral_fintype (Integrable.of_finite)]
  have hcyl : ∀ w : Fin m → α, (ν.map (block m)).real {w} = ν.real (cylinder w) := by
    intro w
    rw [map_measureReal_apply (measurable_block m) (measurableSet_singleton w),
      cylinder_eq_preimage]
  simp only [hcyl, smul_eq_mul]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun w => w ∈ W)]
  have htot := sum_measureReal_cylinder ν m
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun w => w ∈ W)] at htot
  have hfW : Finset.univ.filter (fun w => w ∈ W) = W := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [hfW] at htot ⊢
  have h1 : ∑ w ∈ W, ν.real (cylinder w) * -Real.log (p w) ≤ ∑ w ∈ W, ν.real (cylinder w) * B₁ :=
    Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left (hW w hw) measureReal_nonneg
  have h2 : ∑ w ∈ Finset.univ.filter (fun w => w ∉ W), ν.real (cylinder w) * -Real.log (p w) ≤
      ∑ w ∈ Finset.univ.filter (fun w => w ∉ W), ν.real (cylinder w) * B₂ :=
    Finset.sum_le_sum fun w hw =>
      mul_le_mul_of_nonneg_left (hWc w (Finset.mem_filter.1 hw).2) measureReal_nonneg
  rw [← Finset.sum_mul] at h1 h2
  have hnn : 0 ≤ ∑ w ∈ Finset.univ.filter (fun w => w ∉ W), ν.real (cylinder w) :=
    Finset.sum_nonneg fun w _ => measureReal_nonneg
  have hnn' : 0 ≤ ∑ w ∈ W, ν.real (cylinder w) := Finset.sum_nonneg fun w _ => measureReal_nonneg
  have h3 : ∑ w ∈ W, ν.real (cylinder w) ≤ 1 := by linarith
  have h4 : ∑ w ∈ Finset.univ.filter (fun w => w ∉ W), ν.real (cylinder w) ≤ δ := by linarith
  have h5 : (∑ w ∈ W, ν.real (cylinder w)) * B₁ ≤ B₁ := mul_le_of_le_one_left hB₁ h3
  have h6 : (∑ w ∈ Finset.univ.filter (fun w => w ∉ W), ν.real (cylinder w)) * B₂ ≤ δ * B₂ :=
    mul_le_mul_of_nonneg_right h4 hB₂
  linarith

namespace LineIFS

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem exists_typicalSet (S : LineIFS ι) (ν : Measure (ℤ → ι)) [IsProbabilityMeasure ν]
    (herg : Ergodic (shift 1) ν) (m : ℕ) [NeZero m] (F : (Fin m → ι) → ℝ) {δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) :
    ∃ N : ℕ, ∃ Ω : Set (ℤ → ι), MeasurableSet Ω ∧ ν.real Ωᶜ ≤ η ∧
      ∀ y ∈ Ω, ∀ n : ℕ, N ≤ n →
        ν.real (cylinder (block (n * m) y)) ≤ Real.exp (-((n * m : ℕ) * (entropy ν - δ))) ∧
        |S.gDeriv (futureWord y (n * m))| ≤
          Real.exp (-((n * m : ℕ) * (-S.lyapunov ν - δ))) ∧
        ∑ t ∈ Finset.range (n * m), F (block m (shift (t : ℤ) y)) ≤
          (n * m : ℕ) * (∫ z, F (block m z) ∂ν + δ) := by
  set h := entropy ν with hh
  set χ := S.lyapunov ν with hχ
  set f : (ℤ → ι) → ℝ := fun z => F (block m z) with hf
  have hfm : Measurable f := (Measurable.of_discrete (f := F)).comp (measurable_block m)
  have hfint : Integrable f ν := by
    refine Integrable.mono' (integrable_const (∑ w, abs (F w))) hfm.aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun w => abs (F w)) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ _)
  set C : ℕ → Set (ℤ → ι) := fun n => {y |
    ν.real (cylinder (block (n * m) y)) ≤ Real.exp (-((n * m : ℕ) * (h - δ))) ∧
    |S.gDeriv (futureWord y (n * m))| ≤ Real.exp (-((n * m : ℕ) * (-χ - δ))) ∧
    ∑ t ∈ Finset.range (n * m), F (block m (shift (t : ℤ) y)) ≤
      (n * m : ℕ) * (∫ z, F (block m z) ∂ν + δ)} with hC
  have hCm : ∀ n, MeasurableSet (C n) := by
    intro n
    refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
    · exact measurableSet_le ((Measurable.of_discrete
        (f := fun w : Fin (n * m) → ι => ν.real (cylinder w))).comp
        (measurable_block _)) measurable_const
    · exact measurableSet_le (continuous_abs.measurable.comp (S.measurable_gDeriv_futureWord _))
        measurable_const
    · exact measurableSet_le (Finset.measurable_sum _ fun t _ => hfm.comp (measurable_shift _))
        measurable_const
  set G : ℕ → Set (ℤ → ι) := fun N => ⋂ n ∈ Ici N, C n with hG
  have hGm : ∀ N, MeasurableSet (G N) := fun N =>
    MeasurableSet.biInter (to_countable _) fun n _ => hCm n
  have hk : Tendsto (fun n : ℕ => n * m) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun n hn =>
      le_trans hn (Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero (NeZero.ne m)))⟩
  have hae : ∀ᵐ y ∂ν, ∀ᶠ N in atTop, y ∈ G N := by
    filter_upwards [tendsto_neg_log_cylinder_entropy herg,
      birkhoff_ergodic herg (S.integrable_log_abs_ratio ν), birkhoff_ergodic herg hfint]
      with y h1 h2 h3
    have e1 := (h1.comp hk).eventually_const_lt (show h - δ < h by linarith)
    have e2 := (h2.comp hk).eventually_lt_const (show S.lyapunov ν < χ + δ by rw [hχ]; linarith)
    have e3 := (h3.comp hk).eventually_lt_const
      (show ∫ z, f z ∂ν < ∫ z, F (block m z) ∂ν + δ by rw [hf]; linarith)
    obtain ⟨N₀, hN₀⟩ := (e1.and (e2.and (e3.and (eventually_gt_atTop 0)))).exists_forall_of_atTop
    filter_upwards [eventually_ge_atTop N₀] with N hN
    simp only [hG, mem_iInter, mem_Ici]
    intro n hn
    obtain ⟨a1, a2, a3, hn0⟩ := hN₀ n (hN.trans hn)
    simp only [Function.comp_apply] at a1 a2 a3
    have hnm : (0 : ℝ) < ((n * m : ℕ) : ℝ) := by
      have : 0 < n * m := Nat.mul_pos hn0 (Nat.pos_of_ne_zero (NeZero.ne m))
      exact_mod_cast this
    refine ⟨?_, ?_, ?_⟩
    · rcases (measureReal_nonneg (μ := ν) (s := cylinder (block (n * m) y))).eq_or_lt with h0 | hpos
      · rw [← h0]; exact (Real.exp_pos _).le
      · rw [lt_div_iff₀ hnm] at a1
        rw [← Real.exp_log hpos, Real.exp_le_exp]
        linarith
    · rw [birkhoffAverage, birkhoffSum_log_abs_ratio, smul_eq_mul, inv_mul_lt_iff₀ hnm] at a2
      have hpos : 0 < |S.gDeriv (futureWord y (n * m))| := abs_pos.2 (S.gDeriv_ne_zero _)
      rw [← Real.exp_log hpos, Real.exp_le_exp]
      linarith
    · rw [birkhoffAverage, smul_eq_mul, inv_mul_lt_iff₀ hnm, birkhoffSum] at a3
      have e : ∑ t ∈ Finset.range (n * m), f ((shift 1)^[t] y) =
          ∑ t ∈ Finset.range (n * m), F (block m (shift (t : ℤ) y)) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [iterate_shift_one]
      rw [e] at a3
      exact a3.le
  obtain ⟨N, hN⟩ := (eventually_measureReal_ge_of_ae_eventually hGm hae hη).exists
  refine ⟨N, G N, hGm N, ?_, fun y hy n hn => ?_⟩
  · rw [measureReal_compl (hGm N), probReal_univ]
    linarith
  · simp only [hG, mem_iInter, mem_Ici] at hy
    exact hy n hn

end LineIFS

theorem exists_shift_cylinder_ge {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (m : ℕ) [NeZero m] {p : (Fin m → α) → ℝ} (hp : ∀ w, 0 < p w)
    (hsum : ∑ w, p w = 1) {pmin : ℝ} (hpmin0 : 0 ≤ pmin) (hpmin : ∀ w, pmin ≤ p w)
    (y : ℤ → α) (n : ℕ) {B : ℝ}
    (hB : ∑ t ∈ Finset.range (n * m), -Real.log (p (block m (shift (t : ℤ) y))) ≤ (n * m : ℕ) * B) :
    ∃ s < m, pmin * Real.exp (-(n * B)) ≤
      ((blockBernoulli m p).map (shift ((m - s : ℕ) : ℤ))).real (cylinder (block (n * m) y)) := by
  set g : ℕ → ℝ := fun t => -Real.log (p (block m (shift (t : ℤ) y))) with hg
  rw [sum_range_mul_eq_sum_sum g n m] at hB
  have hB' : ∑ s ∈ Finset.range m, ∑ k ∈ Finset.range n, g (k * m + s) ≤
      ∑ _s ∈ Finset.range m, (n : ℝ) * B := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc _ ≤ ((n * m : ℕ) : ℝ) * B := hB
      _ = (m : ℝ) * (n * B) := by push_cast; ring
  have hne : (Finset.range m).Nonempty := Finset.nonempty_range_iff.2 (NeZero.ne m)
  obtain ⟨s, hs, hsB⟩ := Finset.exists_le_of_sum_le hne hB'
  rw [Finset.mem_range] at hs
  refine ⟨s, hs, ?_⟩
  refine le_trans ?_ (blockBernoulli_shift_cylinder_ge m (fun w => (hp w).le) hsum hpmin y n s hs)
  refine mul_le_mul_of_nonneg_left ?_ hpmin0
  have hprod : ∏ k ∈ Finset.range n, p (block m (shift ((k * m + s : ℕ) : ℤ) y)) =
      Real.exp (-(∑ k ∈ Finset.range n, g (k * m + s))) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [hg, neg_neg]
    rw [Real.exp_log (hp _)]
  rw [hprod, Real.exp_le_exp]
  linarith

namespace LineIFS

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem Bounds.measureReal_restrict_closedBall_le {r₀ M₀ : ℝ} {S : LineIFS ι}
    (hS : S.Bounds r₀ M₀) (ν : Measure (ℤ → ι)) [IsProbabilityMeasure ν] (m : ℕ)
    [NeZero m] {p : (Fin m → ι) → ℝ} (hp : ∀ w, 0 < p w) (hsum : ∑ w, p w = 1)
    {pmin : ℝ} (hpmin0 : 0 < pmin) (hpmin : ∀ w, pmin ≤ p w) {Ω : Set (ℤ → ι)}
    {h' a' B γ ρ₀ : ℝ} (hγ : 0 ≤ γ) (n : ℕ)
    (hΩ : ∀ y ∈ Ω, ν.real (cylinder (block (n * m) y)) ≤ Real.exp (-((n * m : ℕ) * h')) ∧
      |S.gDeriv (futureWord y (n * m))| ≤ Real.exp (-((n * m : ℕ) * a')) ∧
      ∑ t ∈ Finset.range (n * m), -Real.log (p (block m (shift (t : ℤ) y))) ≤ (n * m : ℕ) * B)
    (hfr : ∀ x ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ((blockBernoulli m p).map S.code).real (closedBall x ρ) ≤ 6 * ρ ^ γ)
    (x ρ : ℝ) (hρ : 0 < ρ) (hρR : ρ ≤ Real.exp (-((n * m : ℕ) * a')))
    (hR₀ : (1 + 2 * M₀ / (1 - r₀)) * Real.exp (-((n * m : ℕ) * a')) ≤ ρ₀) :
    ((ν.restrict Ω).map S.code).real (closedBall x ρ) ≤
      m * ((Fintype.card (ι) : ℝ) ^ m *
        (6 * ((1 + 2 * M₀ / (1 - r₀)) * Real.exp (-((n * m : ℕ) * a'))) ^ γ)) /
        (pmin * Real.exp (-(n * B))) * Real.exp (-((n * m : ℕ) * h')) := by
  classical
  have hP := isProbabilityMeasure_blockBernoulli m (fun w => (hp w).le) hsum
  have hmeas := hS.measurable_code
  set D := 2 * M₀ / (1 - r₀) with hD
  set R := Real.exp (-((n * m : ℕ) * a')) with hR
  have hD0 : 0 ≤ D := by
    obtain ⟨y₀⟩ := nonempty_of_isProbabilityMeasure ν
    have hM : 0 ≤ M₀ := (abs_nonneg _).trans (hS.abs_trans_le (y₀ 0))
    exact div_nonneg (by linarith) (by linarith [hS.r_lt_one])
  set A := (Fintype.card (ι) : ℝ) with hA
  set c := pmin * Real.exp (-(n * B)) with hc
  have hcpos : 0 < c := mul_pos hpmin0 (Real.exp_pos _)
  set ρ' := ρ + D * R with hρ'
  have hρ'pos : 0 < ρ' := by have := Real.exp_pos (-((n * m : ℕ) * a')); positivity
  have hρ'le : ρ' ≤ (1 + D) * R := by rw [hρ']; nlinarith
  have hρ'₀ : ρ' ≤ ρ₀ := hρ'le.trans hR₀

  set U : Finset (Fin (n * m) → ι) := Finset.univ.filter fun w =>
    ∃ y ∈ Ω, block (n * m) y = w ∧ S.code y ∈ closedBall x ρ with hU
  have hwit : ∀ w ∈ U, ∃ y ∈ Ω, block (n * m) y = w ∧ S.code y ∈ closedBall x ρ :=
    fun w hw => (Finset.mem_filter.1 hw).2

  have hcyl : ∀ w ∈ U, cylinder w ⊆ S.code ⁻¹' closedBall x ρ' := by
    intro w hw y' hy'
    obtain ⟨y, hyΩ, hyw, hyx⟩ := hwit w hw
    rw [← hyw, mem_cylinder] at hy'
    have hagree : ∀ k : ℕ, k < n * m → y k = y' k := fun k hk => (hy' ⟨k, hk⟩).symm
    have h1 := hS.abs_code_sub_le hagree
    have h2 := (hΩ y hyΩ).2.1
    rw [mem_closedBall, Real.dist_eq] at hyx
    rw [mem_preimage, mem_closedBall, Real.dist_eq]
    calc |S.code y' - x| ≤ |S.code y' - S.code y| + |S.code y - x| :=
          abs_sub_le _ _ _
      _ ≤ |S.gDeriv (futureWord y (n * m))| * D + ρ := by
          rw [abs_sub_comm]; exact add_le_add h1 hyx
      _ ≤ R * D + ρ := by gcongr
      _ = ρ' := by rw [hρ']; ring

  have hstep1 : ((ν.restrict Ω).map S.code).real (closedBall x ρ) ≤
      U.card * Real.exp (-((n * m : ℕ) * h')) := by
    rw [map_measureReal_apply hmeas measurableSet_closedBall,
      measureReal_restrict_apply (hmeas measurableSet_closedBall)]
    have hsub : S.code ⁻¹' closedBall x ρ ∩ Ω ⊆ ⋃ w ∈ U, cylinder w := by
      intro y ⟨hy1, hy2⟩
      refine mem_iUnion₂.2 ⟨block (n * m) y, Finset.mem_filter.2 ⟨Finset.mem_univ _,
        y, hy2, rfl, hy1⟩, ?_⟩
      rw [cylinder_eq_preimage]; rfl
    refine (measureReal_mono hsub (measure_ne_top _ _)).trans
      ((measureReal_biUnion_finset_le U _).trans ?_)
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun w hw => ?_
    obtain ⟨y, hyΩ, hyw, -⟩ := hwit w hw
    rw [← hyw]
    exact (hΩ y hyΩ).1

  set P : ℕ → (Fin (n * m) → ι) → Prop := fun s w =>
    c ≤ ((blockBernoulli m p).map (shift ((m - s : ℕ) : ℤ))).real (cylinder w) with hPdef
  have hcover : U ⊆ (Finset.range m).biUnion fun s => U.filter (P s) := by
    intro w hw
    obtain ⟨y, hyΩ, hyw, -⟩ := hwit w hw
    obtain ⟨s, hs, hsc⟩ := exists_shift_cylinder_ge m hp hsum hpmin0.le hpmin y n
      (hΩ y hyΩ).2.2
    rw [hyw] at hsc
    exact Finset.mem_biUnion.2 ⟨s, Finset.mem_range.2 hs, Finset.mem_filter.2 ⟨hw, hsc⟩⟩

  have hstep3 : ∀ s ∈ Finset.range m, ((U.filter (P s)).card : ℝ) ≤ A ^ m * (6 * ρ' ^ γ) / c := by
    intro s hs
    rw [le_div_iff₀ hcpos]
    set j : ℕ := m - s with hj
    have hsum_le : ∑ w ∈ U.filter (P s), ((blockBernoulli m p).map (shift (j : ℤ))).real
        (cylinder w) ≤ (((blockBernoulli m p).map (shift (j : ℤ))).map S.code).real
          (closedBall x ρ') := by
      rw [← measureReal_biUnion_finset]
      · rw [map_measureReal_apply hmeas measurableSet_closedBall]
        refine measureReal_mono ?_
        intro y hy
        obtain ⟨w, hw, hyw⟩ := mem_iUnion₂.1 hy
        exact hcyl w (Finset.mem_filter.1 hw).1 hyw
      · intro w _ w' _ hww'
        refine Set.disjoint_left.2 fun y hy hy' => hww' ?_
        rw [cylinder_eq_preimage] at hy hy'
        rw [← hy, ← hy']
      · exact fun w _ => measurableSet_cylinder w
    have hfr' := hS.frostman_map_shift (blockBernoulli m p) hγ hfr j x ρ' hρ'pos hρ'₀
    have hAj : A ^ j ≤ A ^ m := by
      have hA1 : 1 ≤ A := by
        rw [hA]
        obtain ⟨y₀⟩ := nonempty_of_isProbabilityMeasure ν
        exact_mod_cast Fintype.card_pos_iff.2 ⟨y₀ 0⟩
      exact pow_le_pow_right₀ hA1 (Nat.sub_le m s)
    have hlow : ((U.filter (P s)).card : ℝ) * c ≤ ∑ w ∈ U.filter (P s),
        ((blockBernoulli m p).map (shift (j : ℤ))).real (cylinder w) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun w hw => (Finset.mem_filter.1 hw).2
    calc ((U.filter (P s)).card : ℝ) * c ≤ _ := hlow
      _ ≤ _ := hsum_le
      _ ≤ A ^ j * (6 * ρ' ^ γ) := hfr'
      _ ≤ A ^ m * (6 * ρ' ^ γ) :=
          mul_le_mul_of_nonneg_right hAj (by positivity)
  have hstep2 : (U.card : ℝ) ≤ m * (A ^ m * (6 * ρ' ^ γ) / c) := by
    have h1 : U.card ≤ ((Finset.range m).biUnion fun s => U.filter (P s)).card :=
      Finset.card_le_card hcover
    have h2 := Finset.card_biUnion_le (s := Finset.range m) (t := fun s => U.filter (P s))
    have h3 : (U.card : ℝ) ≤ ∑ s ∈ Finset.range m, ((U.filter (P s)).card : ℝ) := by
      exact_mod_cast h1.trans h2
    refine h3.trans ?_
    calc ∑ s ∈ Finset.range m, ((U.filter (P s)).card : ℝ)
        ≤ ∑ _s ∈ Finset.range m, A ^ m * (6 * ρ' ^ γ) / c := Finset.sum_le_sum hstep3
      _ = m * (A ^ m * (6 * ρ' ^ γ) / c) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hρ'γ : ρ' ^ γ ≤ ((1 + D) * R) ^ γ := Real.rpow_le_rpow hρ'pos.le hρ'le hγ
  calc ((ν.restrict Ω).map S.code).real (closedBall x ρ)
      ≤ U.card * Real.exp (-((n * m : ℕ) * h')) := hstep1
    _ ≤ m * (A ^ m * (6 * ρ' ^ γ) / c) * Real.exp (-((n * m : ℕ) * h')) :=
        mul_le_mul_of_nonneg_right hstep2 (Real.exp_pos _).le
    _ ≤ m * (A ^ m * (6 * ((1 + D) * R) ^ γ) / c) * Real.exp (-((n * m : ℕ) * h')) := by
        gcongr
    _ = _ := by rw [hc]; ring

end LineIFS

def JordanRapaportFrostman : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : LineIFS ι),
    S.ExpSeparation → ∀ (ν : Measure (ℤ → ι)) [IsProbabilityMeasure ν],
    Ergodic (shift 1) ν → ∀ θ : ℝ, 0 < θ → ∀ η : ℝ, 0 < η →
    ∃ Ω : Set (ℤ → ι), MeasurableSet Ω ∧ ν.real Ωᶜ ≤ η ∧
      ∀ x : ℝ, ∀ᶠ r : ℝ in 𝓝[>] 0, ((ν.restrict Ω).map S.code).real (closedBall x r) ≤
        r ^ (min 1 (-entropy ν / S.lyapunov ν) - θ)

theorem LineIFS.pow_le_abs_gDeriv {ι : Type*} (S : LineIFS ι) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ p, ρ ≤ |S.ratio p|) (u : List (ι)) : ρ ^ u.length ≤ |S.gDeriv u| := by
  induction u with
  | nil => simp
  | cons p u ih =>
    rw [LineIFS.gDeriv_cons, abs_mul, List.length_cons, pow_succ']
    exact mul_le_mul (h p) ih (pow_nonneg hρ _) (abs_nonneg _)

theorem jr_exponent_gap {m a δ γ β θ h L : ℝ} (hm : 0 < m) (ha : 0 < a) (hδ1 : δ ≤ 1 / 2)
    (hδa : δ ≤ a / 2) (hγ : β - 5 * θ / 8 ≤ γ) (hθ : 0 < θ) (hδL : δ * (16 * (2 + L)) ≤ a * θ)
    (hmθ : 48 ≤ m * (a * θ)) (hlog : Real.log 2 ≤ 1) :
    m * (a - δ) * (β - θ) < m * (a - δ) * γ -
      ((Real.log 2 + m * (h + δ)) + δ * (Real.log 2 + m * L) + δ) + m * (h - δ) := by
  have hX : 3 * θ / 8 ≤ γ - (β - θ) := by linarith
  have hY : a / 2 ≤ a - δ := by linarith
  have h1 : m * (a / 2) * (3 * θ / 8) ≤ m * (a - δ) * (γ - (β - θ)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hY hm.le) hX (by positivity) (by nlinarith)
  have h2 : m * (δ * (16 * (2 + L))) ≤ m * (a * θ) := mul_le_mul_of_nonneg_left hδL hm.le
  have h3 : δ * Real.log 2 ≤ 1 / 2 := by nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have e1 : m * (a / 2) * (3 * θ / 8) = 3 / 16 * (m * (a * θ)) := by ring
  have e2 : m * (δ * (16 * (2 + L))) = 16 * (m * δ * (2 + L)) := by ring
  have e3 : m * (a - δ) * γ - ((Real.log 2 + m * (h + δ)) + δ * (Real.log 2 + m * L) + δ) +
      m * (h - δ) - m * (a - δ) * (β - θ) = m * (a - δ) * (γ - (β - θ)) - m * δ * (2 + L) -
      (Real.log 2 + δ * Real.log 2 + δ) := by ring
  have : 0 < m * (a - δ) * γ - ((Real.log 2 + m * (h + δ)) + δ * (Real.log 2 + m * L) + δ) +
      m * (h - δ) - m * (a - δ) * (β - θ) := by
    rw [e3]
    linarith
  linarith

theorem jr_exponent_scale {n m a' γ h δ Bt B : ℝ} (hn : 0 ≤ n) (hB : Bt ≤ B) :
    -(n * (m * a')) * γ + -(n * m * (h - δ)) ≤
      -(n * (m * a' * γ - B + m * (h - δ))) + -(n * Bt) := by
  have := mul_le_mul_of_nonneg_left hB hn
  linarith

theorem jordanRapaportFrostman_of_shmerkin (hsh : ShmerkinLqDimension.{u}) :
    JordanRapaportFrostman.{u} := by
  intro ι _ _ _ S hsep ν _ herg θ hθ η hη
  classical
  set h := entropy ν with hh
  set a := -S.lyapunov ν with ha
  have ha0 : 0 < a := by rw [ha]; linarith [S.lyapunov_neg ν]
  have hh0 : 0 ≤ h := entropy_nonneg herg.toMeasurePreserving
  have hβeq : -entropy ν / S.lyapunov ν = h / a := by rw [ha, hh, div_neg, neg_div]
  rw [hβeq]
  set β := min 1 (h / a) with hβ
  have hβ1 : β ≤ 1 := min_le_left _ _
  have hβh : β ≤ h / a := min_le_right _ _

  by_cases hβθ : β - θ ≤ 0
  · refine ⟨univ, MeasurableSet.univ, by simp [hη.le], fun x => ?_⟩
    filter_upwards [Ioc_mem_nhdsGT one_pos] with r ⟨hr0, hr1⟩
    have h1 : ((ν.restrict univ).map S.code).real (closedBall x r) ≤ 1 := by
      rw [Measure.restrict_univ]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    exact h1.trans (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr0 hr1 hβθ)
  push Not at hβθ
  have hθβ : θ < β := by linarith
  have hθ1 : θ < 1 := lt_of_lt_of_le hθβ hβ1

  obtain ⟨y₀⟩ := nonempty_of_isProbabilityMeasure ν
  have : Nonempty (ι) := ⟨y₀ 0⟩
  obtain ⟨r₀, M₀, hS⟩ := S.exists_bounds
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans (hS.abs_trans_le (y₀ 0))
  set D := 2 * M₀ / (1 - r₀) with hD
  have hD0 : 0 ≤ D := div_nonneg (by linarith) (by linarith [hS.r_lt_one])
  obtain ⟨p₁, -, hp₁⟩ := Finset.exists_min_image Finset.univ (fun p : ι => |S.ratio p|)
    Finset.univ_nonempty
  set ρ₁ := |S.ratio p₁| with hρ₁
  have hρ₁pos : 0 < ρ₁ := abs_pos.2 (S.ratio_ne_zero p₁)
  have hρ₁1 : ρ₁ ≤ 1 := (S.abs_ratio_lt_one p₁).le
  have hρ₁le : ∀ p, ρ₁ ≤ |S.ratio p| := fun p => hp₁ p (Finset.mem_univ p)
  set ℓ₁ := Real.log (1 / ρ₁) with hℓ₁
  have hℓ₁0 : 0 ≤ ℓ₁ := Real.log_nonneg (by rw [one_div]; exact one_le_inv₀ hρ₁pos |>.2 hρ₁1)
  have hρ₁exp : ρ₁ = Real.exp (-ℓ₁) := by
    rw [hℓ₁, one_div, Real.log_inv, neg_neg, Real.exp_log hρ₁pos]
  set A := (Fintype.card (ι) : ℝ) with hA
  have hA1 : 1 ≤ A := by rw [hA]; exact_mod_cast Fintype.card_pos
  set ℓA := Real.log A with hℓA
  have hℓA0 : 0 ≤ ℓA := Real.log_nonneg hA1
  set L := ℓ₁ + ℓA + 1 with hL
  have hL0 : 0 < L := by positivity

  set α := β - θ / 2 with hα
  set q := 3 + 8 / θ with hq
  have hq3 : 3 ≤ q := by rw [hq]; have : 0 < 8 / θ := by positivity
                         linarith
  have hq0 : 0 < q := by linarith
  have hqθ : 1 / q ≤ θ / 8 := by
    rw [one_div_le hq0 (by positivity), one_div_div, hq]
    linarith
  have hα0 : 0 ≤ α := by rw [hα]; linarith
  have hα1 : α ≤ 1 := by rw [hα]; linarith
  have hαlt1 : α < 1 := by rw [hα]; linarith
  set γ := (q - 1) * α / q with hγ
  have hγ0 : 0 ≤ γ := div_nonneg (mul_nonneg (by linarith) hα0) hq0.le
  have hγβ : β - 5 * θ / 8 ≤ γ := by
    have h1 : γ = α - α / q := by rw [hγ]; field_simp
    have h2 : α / q ≤ 1 / q := div_le_div_of_nonneg_right hα1 hq0.le
    rw [h1, hα]; linarith

  set δ := min (1 / 2) (min (a / 2) (min (θ * a / (2 * (h / a + 2))) (a * θ / (16 * (2 + L)))))
    with hδ
  have hδpos : 0 < δ := by
    have h1 : 0 < θ * a / (2 * (h / a + 2)) := by positivity
    have h2 : 0 < a * θ / (16 * (2 + L)) := by positivity
    exact lt_min (by norm_num) (lt_min (by linarith) (lt_min h1 h2))
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδa : δ ≤ a / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδθ : δ ≤ θ * a / (2 * (h / a + 2)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδL : δ ≤ a * θ / (16 * (2 + L)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hαh : α * (a + δ) ≤ h - 2 * δ := by
    have h1 : δ * (h / a + 2) ≤ θ * a / 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (h / a + 2))] at hδθ
      linarith
    have h2 : α ≤ h / a - θ / 2 := by rw [hα]; linarith
    have h3 : α * (a + δ) ≤ (h / a - θ / 2) * (a + δ) :=
      mul_le_mul_of_nonneg_right h2 (by linarith)
    have h4 : (h / a - θ / 2) * (a + δ) = h + δ * (h / a) - θ * a / 2 - θ * δ / 2 := by
      field_simp; ring
    nlinarith

  obtain ⟨m, hmW, hmbig⟩ := ((S.eventually_sum_typicalBlocks ν herg hδpos).and
    (eventually_ge_atTop ⌈max 3 (max (2 / δ) (48 / (a * θ)))⌉₊)).exists
  have hmR : max 3 (max (2 / δ) (48 / (a * θ))) ≤ (m : ℝ) := Nat.ceil_le.1 hmbig
  have hm3 : (3 : ℝ) ≤ m := (le_max_left _ _).trans hmR
  have hmδ' : 2 / δ ≤ m := ((le_max_left _ _).trans (le_max_right _ _)).trans hmR
  have hmθ : 48 / (a * θ) ≤ m := ((le_max_right _ _).trans (le_max_right _ _)).trans hmR
  have hm0 : 0 < m := by exact_mod_cast (show (0 : ℝ) < m by linarith)
  have : NeZero m := ⟨hm0.ne'⟩
  have hmpos : (0 : ℝ) < m := by linarith
  have hmδ : 1 + Real.log 2 ≤ m * δ := by
    have h1 : 2 ≤ m * δ := by rwa [div_le_iff₀ hδpos] at hmδ'
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  set W := S.typicalBlocks ν h a δ m with hW
  have hWpos : ∀ w ∈ W, 0 < ν.real (cylinder w) := fun w hw =>
    lt_of_lt_of_le (Real.exp_pos _) (LineIFS.mem_typicalBlocks.1 hw).1

  have hcardK : (Fintype.card (Fin m → ι) : ℝ) = Real.exp (m * ℓA) := by
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, mul_comm, Real.exp_mul, hℓA,
      Real.exp_log (by linarith), Real.rpow_natCast]
  have hcardL : (Fintype.card (Fin m → ι) : ℝ) * Real.exp (-(m * L)) ≤ 1 := by
    rw [hcardK, ← Real.exp_add, Real.exp_le_one_iff]
    have : (m : ℝ) * ℓA ≤ m * L := mul_le_mul_of_nonneg_left (by linarith) hmpos.le
    linarith
  obtain ⟨p, hp, hpsum, hpW, hpWc⟩ := exists_blockWeights (fun w => ν.real (cylinder w)) W
    (δ := δ) (e := Real.exp (-(m * L))) (fun w => measureReal_nonneg)
    (sum_measureReal_cylinder ν m) hWpos (by rw [hW]; exact hmW) hδ1 (Real.exp_pos _) hcardL
  obtain ⟨w₀, -, hw₀⟩ := Finset.exists_min_image Finset.univ p Finset.univ_nonempty
  set pmin := p w₀ with hpmin
  have hpmin0 : 0 < pmin := hp w₀
  have hpminle : ∀ w, pmin ≤ p w := fun w => hw₀ w (Finset.mem_univ w)

  have hlq : ∑ w, p w ^ q * |S.blockRatio m w| ^ (-((q - 1) * α)) < 1 := by
    refine lq_sum_lt_one p (fun w => |S.blockRatio m w|) W (q := q) (α := α) (m := m) (L := L)
      (h := h) (a := a) (δ := δ) (ℓ₁ := ℓ₁) (ℓA := ℓA) hp hpsum
      (fun w => abs_pos.2 (S.gDeriv_ne_zero _)) ?_ ?_ hcardK.le hℓ₁0 hℓA0 hq3 hα0 hα1 hαh hmδ
      le_rfl hm3
    · intro w hw
      obtain ⟨-, h2, h3⟩ := LineIFS.mem_typicalBlocks.1 hw
      exact ⟨(hpW w hw).2.trans (by linarith), h3⟩
    · intro w hw
      refine ⟨(hpWc w hw).2, ?_⟩
      have h1 := S.pow_le_abs_gDeriv hρ₁pos.le hρ₁le (List.ofFn w)
      rw [List.length_ofFn, hρ₁exp, ← Real.exp_nat_mul] at h1
      have e : (m : ℝ) * -ℓ₁ = -(m * ℓ₁) := by ring
      rw [e] at h1
      exact h1

  have hP := isProbabilityMeasure_blockBernoulli m (fun w => (hp w).le) hpsum
  have hstat := hS.map_code_blockBernoulli m (fun w => (hp w).le) hpsum
  have hsep' := hsep.shmerkinExpSeparation (m := m) hm0
  have hr1 : ∀ w, |S.blockRatio m w| < 1 := by
    intro w
    have h1 := hS.abs_gDeriv_le (List.ofFn w)
    rw [List.length_ofFn] at h1
    exact h1.trans_lt (pow_lt_one₀ hS.r_nonneg hS.r_lt_one hm0.ne')
  have hev := hsh (S.blockRatio m) (S.blockTrans m) p (fun w => S.gDeriv_ne_zero _) hr1 hp hpsum
    hsep' ((blockBernoulli m p).map S.code) hstat q (by linarith) α hαlt1 hlq
  obtain ⟨ρ₀, hρ₀, hfr⟩ := frostman_of_lq (by linarith : 1 < q) hα0 hα1 hev

  set F : (Fin m → ι) → ℝ := fun w => -Real.log (p w) with hF
  set B₁ := Real.log 2 + m * (h + δ) with hB₁
  set B₂ := Real.log 2 + m * L with hB₂
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hB₁0 : 0 ≤ B₁ := by rw [hB₁]; positivity
  have hB₂0 : 0 ≤ B₂ := by rw [hB₂]; positivity
  have hint : ∫ z, F (block m z) ∂ν ≤ B₁ + δ * B₂ := by
    refine integral_neg_log_weight_le ν m p W ?_ ?_ hB₁0 hB₂0 (by rw [hW]; exact hmW)
    · intro w hw
      have h1 := (hpW w hw).1
      have h2 := (LineIFS.mem_typicalBlocks.1 hw).1
      have h3 : Real.exp (-(m * (h + δ))) / 2 ≤ p w := le_trans (by linarith) h1
      have h4 := Real.log_le_log (by positivity) h3
      rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at h4
      rw [hB₁]; linarith
    · intro w hw
      have h1 := (hpWc w hw).1
      have h4 := Real.log_le_log (by positivity) h1
      rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at h4
      rw [hB₂]; linarith

  obtain ⟨N, Ω, hΩm, hΩc, hΩ⟩ := S.exists_typicalSet ν herg m F hδpos hη
  refine ⟨Ω, hΩm, hΩc, fun x => ?_⟩

  set a' := a - δ with ha'
  have ha'pos : 0 < a' := by rw [ha']; linarith
  set Bt := ∫ z, F (block m z) ∂ν + δ with hBt
  set C := m * (A ^ m * (6 * (1 + D) ^ γ)) / pmin with hC
  set b := m * a' * γ - (B₁ + δ * B₂ + δ) + m * (h - δ) with hb

  have hgap : m * a' * (β - θ) < b := by
    have hlog : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    have hδL' : δ * (16 * (2 + L)) ≤ a * θ := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (2 + L))] at hδL
      linarith
    have hmθ' : 48 ≤ m * (a * θ) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < a * θ)] at hmθ
      linarith
    exact jr_exponent_gap hmpos ha0 hδ1 hδa hγβ hθ hδL' hmθ' hlog

  have hRlim : Tendsto (fun n : ℕ => Real.exp (-(n * (m * a')))) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    refine tendsto_neg_atTop_atBot.comp ?_
    exact tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
  obtain ⟨N₂, hN₂⟩ := (hRlim.eventually (gt_mem_nhds (by positivity :
    (0 : ℝ) < ρ₀ / (1 + D)))).exists_forall_of_atTop
  have hscale := eventually_le_rpow_of_scales (f := fun ρ =>
      ((ν.restrict Ω).map S.code).real (closedBall x ρ)) (C := C)
    (by positivity : (0 : ℝ) < m * a') hβθ.le hgap (N := max N N₂) ?_
  · exact hscale
  intro n hn ρ hρ hρR
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnN₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have hcast : ((n * m : ℕ) : ℝ) * a' = n * (m * a') := by push_cast; ring
  have hRn : Real.exp (-((n * m : ℕ) * a')) = Real.exp (-(n * (m * a'))) := by rw [hcast]
  have hR₀ : (1 + D) * Real.exp (-((n * m : ℕ) * a')) ≤ ρ₀ := by
    rw [hRn]
    have := hN₂ n hnN₂
    rw [lt_div_iff₀ (by positivity)] at this
    linarith
  have hcount := hS.measureReal_restrict_closedBall_le ν m hp hpsum hpmin0 hpminle (Ω := Ω)
    (h' := h - δ) (a' := a') (B := Bt) hγ0 n
    (fun y hy => by
      obtain ⟨c1, c2, c3⟩ := hΩ y hy n hnN
      exact ⟨c1, c2, c3⟩) hfr x ρ hρ (by rw [hRn]; exact hρR) hR₀
  refine hcount.trans ?_
  set K := (m : ℝ) * (A ^ m * (6 * (1 + D) ^ γ)) with hK
  have hK0 : 0 ≤ K := by positivity
  set e1 := Real.exp (-(n * (m * a')) * γ) with he1
  set e2 := Real.exp (-(n * Bt)) with he2
  set e3 := Real.exp (-((n * m : ℕ) * (h - δ))) with he3
  set e4 := Real.exp (-(n * b)) with he4
  have hR' : ((1 + D) * Real.exp (-((n * m : ℕ) * a'))) ^ γ = (1 + D) ^ γ * e1 := by
    rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, hRn, ← Real.exp_mul]
  have key : e1 * e3 ≤ e4 * e2 := by
    rw [he1, he2, he3, he4, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    have hBt : Bt ≤ B₁ + δ * B₂ + δ := by rw [hBt]; linarith
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hc2 : ((n * m : ℕ) : ℝ) = n * m := by push_cast; ring
    rw [hc2, hb]
    exact jr_exponent_scale hn0 hBt
  rw [hR']
  calc (m : ℝ) * (A ^ m * (6 * ((1 + D) ^ γ * e1))) / (pmin * e2) * e3
      = K * (e1 * e3) / (pmin * e2) := by rw [hK]; ring
    _ ≤ K * (e4 * e2) / (pmin * e2) := by gcongr
    _ = C * e4 := by
        have he2 : e2 ≠ 0 := (Real.exp_pos _).ne'
        rw [hC, hK]
        field_simp

theorem upperSemicontinuous_measure_closedBall {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] (ρ : ℝ) :
    UpperSemicontinuous fun x : X => μ (closedBall x ρ) := by
  intro x c hc
  have hT : Tendsto (fun t => μ (closedBall x t)) (𝓝[>] ρ)
      (𝓝 (μ (⋂ t > ρ, closedBall x t))) :=
    tendsto_measure_biInter_gt (fun _ _ => measurableSet_closedBall.nullMeasurableSet)
      (fun _ _ _ hij => closedBall_subset_closedBall hij)
      ⟨ρ + 1, by linarith, measure_ne_top _ _⟩
  have hI : (⋂ t > ρ, closedBall x t) = closedBall x ρ := by
    ext z
    simp only [mem_iInter, mem_closedBall]
    exact ⟨fun h => le_of_forall_gt_imp_ge_of_dense h, fun h t ht => h.trans ht.le⟩
  rw [hI] at hT
  obtain ⟨t, hlt, ht⟩ := ((hT.eventually (Iio_mem_nhds hc)).and self_mem_nhdsWithin).exists
  have ht : ρ < t := ht
  filter_upwards [ball_mem_nhds x (sub_pos.2 ht)] with x' hx'
  refine lt_of_le_of_lt (measure_mono (closedBall_subset_closedBall' ?_)) hlt
  rw [mem_ball] at hx'
  linarith

theorem isClosed_setOf_le_measureReal_closedBall {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] (ρ c : ℝ) :
    IsClosed {x : X | c ≤ μ.real (closedBall x ρ)} := by
  by_cases hc : c ≤ 0
  · have : {x : X | c ≤ μ.real (closedBall x ρ)} = univ :=
      eq_univ_of_forall fun x => hc.trans measureReal_nonneg
    rw [this]
    exact isClosed_univ
  · push Not at hc
    have : {x : X | c ≤ μ.real (closedBall x ρ)} =
        (fun x => μ (closedBall x ρ)) ⁻¹' Ici (ENNReal.ofReal c) := by
      ext x
      simp only [mem_ofPred_eq, mem_preimage, mem_Ici, measureReal_def]
      rw [← ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
    rw [this]
    exact (upperSemicontinuous_measure_closedBall μ ρ).isClosed_preimage _

theorem eventually_le_measureReal_closedBall {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] {x : X} {D a b : ℝ} (hD : 0 < D)
    (ha : 0 < a) (hb : 0 ≤ b) {N : ℕ}
    (h : ∀ n : ℕ, N ≤ n →
      Real.exp (-(n * b)) ≤ μ.real (closedBall x (D * Real.exp (-(n * a))))) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      Real.exp (-b) * D ^ (-(b / a)) * r ^ (b / a) ≤ μ.real (closedBall x r) := by
  have hpos : 0 < D * Real.exp (-(N * a)) := mul_pos hD (Real.exp_pos _)
  filter_upwards [Ioo_mem_nhdsGT hpos] with r hr
  obtain ⟨hr0, hr1⟩ := hr
  set t : ℝ := Real.log (D / r) / a with ht
  have hDr : 0 < D / r := div_pos hD hr0
  have hNt : (N : ℝ) ≤ t := by
    rw [ht, le_div_iff₀ ha]
    have h1 : Real.exp (N * a) < D / r := by
      rw [lt_div_iff₀ hr0]
      calc Real.exp (N * a) * r < Real.exp (N * a) * (D * Real.exp (-(N * a))) :=
            mul_lt_mul_of_pos_left hr1 (Real.exp_pos _)
        _ = D := by rw [mul_left_comm, ← Real.exp_add]; simp
    have := (Real.lt_log_iff_exp_lt hDr).2 h1
    linarith
  have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg _) hNt
  set n : ℕ := ⌊t⌋₊ with hn
  have hnN : N ≤ n := Nat.le_floor hNt
  have hnt : (n : ℝ) ≤ t := Nat.floor_le ht0
  have htn : t < n + 1 := Nat.lt_floor_add_one t

  have hrad : D * Real.exp (-((n + 1 : ℕ) * a)) ≤ r := by
    have h1 : Real.log (D / r) < (n + 1) * a := by
      rw [ht, div_lt_iff₀ ha] at htn
      linarith
    have h2 : D / r < Real.exp ((n + 1) * a) := (Real.log_lt_iff_lt_exp hDr).1 h1
    rw [div_lt_iff₀ hr0] at h2
    have h3 : D * Real.exp (-((n + 1 : ℕ) * a)) = D / Real.exp ((n + 1) * a) := by
      rw [Real.exp_neg]
      push_cast
      ring
    rw [h3, div_le_iff₀ (Real.exp_pos _)]
    linarith
  have hmass := h (n + 1) (by omega)
  have hmono : μ.real (closedBall x (D * Real.exp (-((n + 1 : ℕ) * a))))
      ≤ μ.real (closedBall x r) :=
    measureReal_mono (closedBall_subset_closedBall hrad)

  have hkey : Real.exp (-b) * D ^ (-(b / a)) * r ^ (b / a) = Real.exp (-b) * Real.exp (-(t * b))
      := by
    rw [mul_assoc]
    congr 1
    have e1 : Real.exp (-(t * b)) = (D / r) ^ (-(b / a)) := by
      rw [Real.rpow_def_of_pos hDr, ht]
      congr 1
      field_simp
    rw [e1, Real.div_rpow hD.le hr0.le, Real.rpow_neg hr0.le, div_inv_eq_mul]
  rw [hkey]
  refine le_trans ?_ (hmass.trans hmono)
  rw [← Real.exp_add, Real.exp_le_exp]
  push_cast
  nlinarith

namespace LineIFS

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem ae_eventually_log_div_log_le_entropy (S : LineIFS ι) (ν : Measure (ℤ → ι))
    [IsProbabilityMeasure ν] (herg : Ergodic (shift 1) ν) {θ : ℝ} (hθ : 0 < θ) :
    ∀ᵐ x ∂(ν.map S.code), ∀ᶠ r : ℝ in 𝓝[>] 0,
      Real.log ((ν.map S.code).real (closedBall x r)) / Real.log r ≤
        -entropy ν / S.lyapunov ν + θ := by
  set h := entropy ν with hh
  set a0 := -S.lyapunov ν with ha0
  have ha0pos : 0 < a0 := by rw [ha0]; linarith [S.lyapunov_neg ν]
  have hh0 : 0 ≤ h := entropy_nonneg herg.toMeasurePreserving

  set ε := min (a0 / 2) (θ * a0 ^ 2 / (4 * (a0 + h))) with hε
  have hεpos : 0 < ε := lt_min (by linarith) (by positivity)
  have hεa : ε ≤ a0 / 2 := min_le_left _ _
  have hεθ : ε ≤ θ * a0 ^ 2 / (4 * (a0 + h)) := min_le_right _ _
  set a := a0 - ε with ha
  set b := h + ε with hb
  have hapos : 0 < a := by linarith
  have hbnn : 0 ≤ b := by linarith
  have hratio : b / a ≤ h / a0 + θ / 2 := by
    rw [div_le_iff₀ hapos]
    have h1 : h / a0 * a = h - h * ε / a0 := by
      rw [ha]; field_simp
    have h2 : θ / 2 * a ≥ θ / 2 * (a0 / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    have h3 : ε * (a0 + h) ≤ θ * a0 ^ 2 / 4 := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 4 * (a0 + h))] at hεθ
      nlinarith
    have h4 : h * ε / a0 ≥ 0 := by positivity
    rw [add_mul, h1]
    have h5 : ε * a0 + h * ε ≤ θ * a0 ^ 2 / 4 := by nlinarith
    have h6 : ε + h * ε / a0 ≤ θ * a0 / 4 := by
      have : (ε + h * ε / a0) * a0 = ε * a0 + h * ε := by field_simp
      rw [← mul_le_mul_iff_of_pos_right ha0pos, this]
      nlinarith
    rw [hb]
    nlinarith

  obtain ⟨r₀, M, hS⟩ := S.exists_bounds
  obtain ⟨y₀⟩ := nonempty_of_isProbabilityMeasure ν
  have hM : 0 ≤ M := (abs_nonneg _).trans (hS.abs_trans_le (y₀ 0))
  set D := 2 * M / (1 - r₀) + 1 with hD
  have hDpos : 0 < D := by
    have : 0 ≤ 2 * M / (1 - r₀) := div_nonneg (by linarith) (by linarith [hS.r_lt_one])
    linarith
  set μ := ν.map S.code with hμ
  have hmeas : Measurable S.code := hS.measurable_code
  set A : ℕ → Set ℝ := fun N => {x | ∀ n : ℕ, N ≤ n →
    Real.exp (-(n * b)) ≤ μ.real (closedBall x (D * Real.exp (-(n * a))))} with hA
  have hAclosed : ∀ N, IsClosed (A N) := by
    intro N
    have : A N = ⋂ n : ℕ, ⋂ (_ : N ≤ n), {x | Real.exp (-(n * b)) ≤
        μ.real (closedBall x (D * Real.exp (-(n * a))))} := by
      ext x; simp [hA]
    rw [this]
    exact isClosed_iInter fun n => isClosed_iInter fun _ =>
      isClosed_setOf_le_measureReal_closedBall μ _ _
  have hAmeas : MeasurableSet (⋃ N, A N) :=
    MeasurableSet.iUnion fun N => (hAclosed N).measurableSet

  have hy : ∀ᵐ y ∂ν, S.code y ∈ ⋃ N, A N := by
    filter_upwards [ae_eventually_block_mem_typicalWords herg hεpos,
      birkhoff_ergodic herg (S.integrable_log_abs_ratio ν)] with y hy hbk
    have hbk' : ∀ᶠ n : ℕ in atTop, birkhoffAverage ℝ (shift 1)
        (fun y : ℤ → ι => Real.log |S.ratio (y 0)|) n y < -a0 + ε := by
      refine hbk.eventually_lt_const ?_
      rw [ha0, neg_neg, lyapunov]
      linarith
    obtain ⟨N, hN⟩ := (hy.and (hbk'.and (eventually_gt_atTop 0))).exists_forall_of_atTop
    refine mem_iUnion.2 ⟨N, fun n hn => ?_⟩
    obtain ⟨hty, hbn, hn0⟩ := hN n hn
    rw [mem_typicalWords] at hty
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn0
    rw [birkhoffAverage, birkhoffSum_log_abs_ratio, smul_eq_mul, inv_mul_lt_iff₀ hnpos] at hbn
    have hder : |S.gDeriv (futureWord y n)| ≤ Real.exp (-(n * a)) := by
      have hpos : 0 < |S.gDeriv (futureWord y n)| := abs_pos.2 (S.gDeriv_ne_zero _)
      rw [← Real.exp_log hpos, Real.exp_le_exp]
      rw [ha]
      linarith
    have hsub : cylinder (block n y) ⊆ S.code ⁻¹' closedBall (S.code y)
        (D * Real.exp (-(n * a))) := by
      intro y' hy'
      rw [mem_cylinder] at hy'
      have hagree : ∀ k : ℕ, k < n → y k = y' k := fun k hk => (hy' ⟨k, hk⟩).symm
      have hd := hS.abs_code_sub_le hagree
      rw [mem_preimage, mem_closedBall, Real.dist_eq, abs_sub_comm]
      calc |S.code y - S.code y'| ≤ |S.gDeriv (futureWord y n)| * (2 * M / (1 - r₀)) := hd
        _ ≤ Real.exp (-(n * a)) * D := by
          apply mul_le_mul hder (by rw [hD]; linarith) (div_nonneg (by linarith)
            (by linarith [hS.r_lt_one])) (Real.exp_pos _).le
        _ = D * Real.exp (-(n * a)) := mul_comm _ _
    calc Real.exp (-(n * b)) ≤ ν.real (cylinder (block n y)) := hty.1
      _ ≤ ν.real (S.code ⁻¹' closedBall (S.code y) (D * Real.exp (-(n * a)))) :=
          measureReal_mono hsub
      _ = μ.real (closedBall (S.code y) (D * Real.exp (-(n * a)))) := by
          rw [hμ, map_measureReal_apply hmeas measurableSet_closedBall]
  have hx : ∀ᵐ x ∂μ, x ∈ ⋃ N, A N := by
    rw [hμ]
    exact (ae_map_iff hmeas.aemeasurable (p := fun x => x ∈ ⋃ N, A N) hAmeas).2 hy
  filter_upwards [hx] with x hxA
  obtain ⟨N, hxN⟩ := mem_iUnion.1 hxA
  have hc := eventually_le_measureReal_closedBall hDpos hapos hbnn hxN
  have hcpos : 0 < Real.exp (-b) * D ^ (-(b / a)) :=
    mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hDpos _)
  filter_upwards [eventually_log_div_log_le hcpos hc (half_pos hθ)] with r hr
  have e : -entropy ν / S.lyapunov ν = h / a0 := by rw [ha0, hh, div_neg, neg_div]
  rw [e]
  linarith

end LineIFS

theorem ae_eventually_log_div_log_le_one (μ : Measure ℝ) [IsFiniteMeasure μ] {θ : ℝ}
    (hθ : 0 < θ) :
    ∀ᵐ x ∂μ, ∀ᶠ r : ℝ in 𝓝[>] 0,
      Real.log (μ.real (closedBall x r)) / Real.log r ≤ 1 + θ := by
  filter_upwards [ae_exists_mul_pow_le_measureReal_closedBall (μ := μ)] with x ⟨c, hc, h⟩
  have h' : ∀ᶠ r : ℝ in 𝓝[>] 0, c * r ^ (1 : ℝ) ≤ μ.real (closedBall x r) := by
    simpa using h
  exact eventually_log_div_log_le hc h' hθ

theorem ae_eventually_le_log_div_log_of_le {ν ν' : Measure ℝ} [IsFiniteMeasure ν]
    (hle : ν' ≤ ν) {s θ : ℝ} (hθ : 0 < θ)
    (hfr : ∀ x : ℝ, ∀ᶠ r : ℝ in 𝓝[>] 0, ν'.real (closedBall x r) ≤ r ^ s) :
    ∀ᵐ x ∂ν', ∀ᶠ r : ℝ in 𝓝[>] 0,
      s - θ ≤ Real.log (ν.real (closedBall x r)) / Real.log r := by
  have : IsFiniteMeasure ν' := isFiniteMeasure_of_le ν hle
  filter_upwards [ae_tendsto_log_div_log_sub_of_le hle, ae_forall_measure_closedBall_pos ν']
    with x hdiff hpos
  have h2 : ∀ᶠ r : ℝ in 𝓝[>] 0, Real.log r < 0 :=
    Real.tendsto_log_nhdsGT_zero.eventually_lt_atBot 0
  filter_upwards [hfr x, hdiff.eventually (Ioo_mem_nhds (neg_lt_zero.2 hθ) hθ), h2,
    self_mem_nhdsWithin] with r hr hd hlog hr0
  have hr0 : (0 : ℝ) < r := hr0
  have hp : 0 < ν'.real (closedBall x r) :=
    ENNReal.toReal_pos (hpos r hr0).ne' (measure_ne_top _ _)
  have h1 : s ≤ Real.log (ν'.real (closedBall x r)) / Real.log r := by
    rw [le_div_iff_of_neg hlog]
    calc Real.log (ν'.real (closedBall x r)) ≤ Real.log (r ^ s) := Real.log_le_log hp hr
      _ = s * Real.log r := Real.log_rpow hr0 s
  have := hd.1
  linarith

namespace LineIFS

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem ae_eventually_le_log_div_log_of_frostman (S : LineIFS ι) (ν : Measure (ℤ → ι))
    [IsProbabilityMeasure ν] {s θ : ℝ} (hθ : 0 < θ)
    (hfr : ∀ k : ℕ, ∃ Ω : Set (ℤ → ι), MeasurableSet Ω ∧ ν.real Ωᶜ ≤ 1 / (k + 1) ∧
      ∀ x : ℝ, ∀ᶠ r : ℝ in 𝓝[>] 0, ((ν.restrict Ω).map S.code).real (closedBall x r) ≤
        r ^ s) :
    ∀ᵐ x ∂(ν.map S.code), ∀ᶠ r : ℝ in 𝓝[>] 0,
      s - θ ≤ Real.log ((ν.map S.code).real (closedBall x r)) / Real.log r := by
  choose Ω hΩm hΩc hΩf using hfr
  obtain ⟨r₀, M, hS⟩ := S.exists_bounds
  have hmeas : Measurable S.code := hS.measurable_code
  set μ := ν.map S.code with hμ
  set μk : ℕ → Measure ℝ := fun k => (ν.restrict (Ω k)).map S.code with hμk
  have hle : ∀ k, μk k ≤ μ := fun k => Measure.map_mono Measure.restrict_le_self hmeas
  have hk : ∀ k, ∀ᵐ x ∂(μk k), ∀ᶠ r : ℝ in 𝓝[>] 0,
      s - θ ≤ Real.log (μ.real (closedBall x r)) / Real.log r :=
    fun k => ae_eventually_le_log_div_log_of_le (hle k) hθ (hΩf k)
  have hsum : ∀ᵐ x ∂(Measure.sum μk), ∀ᶠ r : ℝ in 𝓝[>] 0,
      s - θ ≤ Real.log (μ.real (closedBall x r)) / Real.log r := Measure.ae_sum_iff.2 hk
  refine Measure.AbsolutelyContinuous.ae_le ?_ hsum
  refine Measure.AbsolutelyContinuous.mk fun A hA h0 => ?_
  rw [Measure.sum_apply _ hA, ENNReal.tsum_eq_zero] at h0
  rw [hμ, Measure.map_apply hmeas hA]
  have hbound : ∀ k : ℕ, ν.real (S.code ⁻¹' A) ≤ 1 / (k + 1) := by
    intro k
    have h1 : (ν.restrict (Ω k)) (S.code ⁻¹' A) = 0 := by
      have := h0 k
      rwa [hμk, Measure.map_apply hmeas hA] at this
    rw [Measure.restrict_apply (hmeas hA)] at h1
    have h2 : ν (S.code ⁻¹' A) ≤ ν (Ω k)ᶜ := by
      calc ν (S.code ⁻¹' A) ≤ ν ((S.code ⁻¹' A ∩ Ω k) ∪ (Ω k)ᶜ) :=
            measure_mono fun z hz => by
              by_cases hzk : z ∈ Ω k
              · exact Or.inl ⟨hz, hzk⟩
              · exact Or.inr hzk
        _ ≤ ν (S.code ⁻¹' A ∩ Ω k) + ν (Ω k)ᶜ := measure_union_le _ _
        _ = ν (Ω k)ᶜ := by rw [h1, zero_add]
    exact (ENNReal.toReal_mono (measure_ne_top _ _) h2).trans (hΩc k)
  have hzero : ν.real (S.code ⁻¹' A) ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    linarith [hbound k]
  have h3 : ν.real (S.code ⁻¹' A) = 0 := le_antisymm hzero measureReal_nonneg
  rwa [measureReal_eq_zero_iff (measure_ne_top _ _)] at h3

end LineIFS

theorem jordanRapaportDimension_of_frostman (hfr : JordanRapaportFrostman.{u}) :
    JordanRapaportDimension.{u} := by
  intro ι _ _ _ S hsep ν _ herg
  set β := min 1 (-entropy ν / S.lyapunov ν) with hβ
  set μ := ν.map S.code with hμ
  obtain ⟨r₀, M, hS⟩ := S.exists_bounds
  have : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have hlow : ∀ k : ℕ, ∀ᵐ x ∂μ, ∀ᶠ r : ℝ in 𝓝[>] 0,
      β - 1 / (k + 1) ≤ Real.log (μ.real (closedBall x r)) / Real.log r := by
    intro k
    have hθ : (0 : ℝ) < 1 / (k + 1) / 2 := by positivity
    have h := S.ae_eventually_le_log_div_log_of_frostman ν (s := β - 1 / (k + 1) / 2) hθ
      fun j => hfr S hsep ν herg _ hθ _ (by positivity : (0 : ℝ) < 1 / (j + 1))
    filter_upwards [h] with x hx
    filter_upwards [hx] with r hr
    linarith
  have hup : ∀ k : ℕ, ∀ᵐ x ∂μ, ∀ᶠ r : ℝ in 𝓝[>] 0,
      Real.log (μ.real (closedBall x r)) / Real.log r ≤ β + 1 / (k + 1) := by
    intro k
    have hθ : (0 : ℝ) < 1 / (k + 1) := by positivity
    filter_upwards [ae_eventually_log_div_log_le_one μ hθ,
      S.ae_eventually_log_div_log_le_entropy ν herg hθ] with x h1 h2
    filter_upwards [h1, h2] with r hr1 hr2
    rw [hβ, ← min_add_add_right]
    exact le_min hr1 hr2
  rw [IsExactDim]
  filter_upwards [ae_all_iff.2 hlow, ae_all_iff.2 hup] with x hl hu
  rw [HasLocalDim]
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 ha)
    filter_upwards [hl k] with r hr
    linarith
  · obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 ha)
    filter_upwards [hu k] with r hr
    linarith

theorem jordanRapaportDimension_of_shmerkin (hsh : ShmerkinLqDimension.{u}) :
    JordanRapaportDimension.{u} :=
  jordanRapaportDimension_of_frostman (jordanRapaportFrostman_of_shmerkin hsh)

theorem jordanRapaportDimension_holds : JordanRapaportDimension.{u} :=
  jordanRapaportDimension_of_shmerkin shmerkinLqDimension_holds

end FractalGeometry
