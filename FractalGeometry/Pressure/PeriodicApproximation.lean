import Mathlib
import FractalGeometry.LinearCocycles.LowerBounds
import FractalGeometry.LinearCocycles.Products
import FractalGeometry.Pressure.NormPotential
import FractalGeometry.Pressure.PartitionSums
import FractalGeometry.Symbolic.BlockEntropyBounds
import FractalGeometry.Symbolic.Concatenation
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.PeriodicWords
import FractalGeometry.Symbolic.Shift

namespace FractalGeometry

open MeasureTheory Filter Topology Set

open scoped Matrix.Norms.L2Operator

namespace MatrixTuple

variable {ι : Type*} [Fintype ι] {A : ι → Matrix (Fin 2) (Fin 2) ℝ} {q : ℝ}

omit [Fintype ι] in

theorem shift_one_shift_periodicExtension {p : ℕ} (w : Fin (p + 1) → ι) (k : Fin (p + 1)) :
    shift 1 (shift ((k : ℕ) : ℤ) (periodicExtension w)) =
      shift (((k + 1 : Fin (p + 1)) : ℕ) : ℤ) (periodicExtension w) := by
  rw [shift_shift, Fin.val_add_one]
  split_ifs with hk
  · subst hk
    rw [Fin.val_last, Nat.cast_zero, shift_zero]
    exact_mod_cast shift_periodicExtension w
  · push_cast
    rfl

omit [Fintype ι] in

theorem shift_periodicExtension_mem_cylinder_iff {p k n : ℕ} (hk : k + n ≤ p + 1)
    (w : Fin (p + 1) → ι) (u : Fin n → ι) :
    shift (k : ℤ) (periodicExtension w) ∈ cylinder u ↔
      ((List.ofFn w).drop k).take n = List.ofFn u := by
  have hL : ((List.ofFn w).drop k).take n = List.ofFn fun i : Fin n => w ⟨k + i, by omega⟩ := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, List.length_ofFn]
      omega
    · intro i _ _
      simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
  rw [hL, List.ofFn_inj, funext_iff, mem_cylinder]
  refine forall_congr' fun i => ?_
  rw [shift_apply]
  have e := periodicExtension_natCast w ⟨k + i, by omega⟩
  push_cast at e
  rw [e]

theorem sum_ofFn_triple {M : Type*} [AddCommMonoid M] (k n l : ℕ) (G : List ι → M) :
    ∑ w : Fin (k + n + l) → ι, G (List.ofFn w) = ∑ x : Fin k → ι, ∑ v : Fin n → ι,
      ∑ y : Fin l → ι, G (List.ofFn x ++ List.ofFn v ++ List.ofFn y) :=
  (sum_ofFn_add (k + n) l G).trans
    (sum_ofFn_add k n fun L => ∑ y : Fin l → ι, G (L ++ List.ofFn y))

variable (A q) in

noncomputable def periodicWeight (p : ℕ) (w : Fin (p + 1) → ι) : ℝ :=
  ‖word A (List.ofFn w)‖ ^ q / ((p + 1 : ℕ) * normSum A q (p + 1))

theorem periodicWeight_nonneg {p : ℕ} (w : Fin (p + 1) → ι) : 0 ≤ periodicWeight A q p w :=
  div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (mul_nonneg (Nat.cast_nonneg _)
    (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _))

theorem sum_periodicWeight [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) (p : ℕ) :
    ∑ w : Fin (p + 1) → ι, periodicWeight A q p w = ((p + 1 : ℕ) : ℝ)⁻¹ := by
  unfold periodicWeight
  rw [← Finset.sum_div]
  change normSum A q (p + 1) / _ = _
  have hZ := normSum_pos (q := q) hA (p + 1)
  have hN : (0 : ℝ) < ((p + 1 : ℕ) : ℝ) := by positivity
  field_simp

variable [MeasurableSpace ι]

variable (A q) in

noncomputable def normPeriodicMeasure (p : ℕ) : Measure (ℤ → ι) :=
  ∑ kw : Fin (p + 1) × (Fin (p + 1) → ι),
    ENNReal.ofReal (periodicWeight A q p kw.2) •
      Measure.dirac (shift ((kw.1 : ℕ) : ℤ) (periodicExtension kw.2))

variable [MeasurableSingletonClass ι]

theorem normPeriodicMeasure_apply (p : ℕ) (s : Set (ℤ → ι)) :
    normPeriodicMeasure A q p s = ∑ kw : Fin (p + 1) × (Fin (p + 1) → ι),
      ENNReal.ofReal (periodicWeight A q p kw.2) *
        s.indicator 1 (shift ((kw.1 : ℕ) : ℤ) (periodicExtension kw.2)) := by
  simp only [normPeriodicMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply, smul_eq_mul]

theorem measureReal_normPeriodicMeasure (p : ℕ) (s : Set (ℤ → ι)) :
    (normPeriodicMeasure A q p).real s = ∑ kw : Fin (p + 1) × (Fin (p + 1) → ι),
      periodicWeight A q p kw.2 *
        s.indicator 1 (shift ((kw.1 : ℕ) : ℤ) (periodicExtension kw.2)) := by
  have hc : ∀ kw : Fin (p + 1) × (Fin (p + 1) → ι), 0 ≤ periodicWeight A q p kw.2 *
      s.indicator 1 (shift ((kw.1 : ℕ) : ℤ) (periodicExtension kw.2)) := fun kw =>
    mul_nonneg (periodicWeight_nonneg _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have key : normPeriodicMeasure A q p s = ENNReal.ofReal (∑ kw : Fin (p + 1) × (Fin (p + 1) → ι),
      periodicWeight A q p kw.2 *
        s.indicator 1 (shift ((kw.1 : ℕ) : ℤ) (periodicExtension kw.2))) := by
    rw [normPeriodicMeasure_apply, ENNReal.ofReal_sum_of_nonneg fun kw _ => hc kw]
    refine Finset.sum_congr rfl fun kw _ => ?_
    by_cases hx : shift ((kw.1 : ℕ) : ℤ) (periodicExtension kw.2) ∈ s <;> simp [hx]
  rw [measureReal_def, key, ENNReal.toReal_ofReal (Finset.sum_nonneg fun kw _ => hc kw)]

theorem isProbabilityMeasure_normPeriodicMeasure [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0)
    (p : ℕ) : IsProbabilityMeasure (normPeriodicMeasure A q p) := by
  refine ⟨?_⟩
  rw [normPeriodicMeasure_apply]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun kw _ => periodicWeight_nonneg kw.2]
  simp only [Fintype.sum_prod_type, sum_periodicWeight hA, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one]

theorem measurePreserving_normPeriodicMeasure (p : ℕ) :
    MeasurePreserving (shift 1) (normPeriodicMeasure A q p) (normPeriodicMeasure A q p) := by
  refine ⟨measurable_shift 1, ?_⟩
  ext s hs
  rw [Measure.map_apply (measurable_shift 1) hs, normPeriodicMeasure_apply,
    normPeriodicMeasure_apply]
  refine Fintype.sum_equiv (Equiv.prodCongr (Equiv.addRight 1) (Equiv.refl _)) _ _ fun kw => ?_
  simp only [Equiv.prodCongr_apply, Equiv.coe_addRight, Equiv.coe_refl, Prod.map_fst,
    Prod.map_snd, id_eq]
  rw [← shift_one_shift_periodicExtension]
  rfl

variable (A q) in

noncomputable def cylSum (p k : ℕ) {n : ℕ} (u : Fin n → ι) : ℝ :=
  ∑ w : Fin (p + 1) → ι, ‖word A (List.ofFn w)‖ ^ q *
    (cylinder u).indicator 1 (shift (k : ℤ) (periodicExtension w))

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in

theorem cylSum_nonneg (p k : ℕ) {n : ℕ} (u : Fin n → ι) : 0 ≤ cylSum A q p k u :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
    (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in

theorem cylSum_le_normSum (p k : ℕ) {n : ℕ} (u : Fin n → ι) :
    cylSum A q p k u ≤ normSum A q (p + 1) := by
  refine Finset.sum_le_sum fun w _ => mul_le_of_le_one_right (Real.rpow_nonneg (norm_nonneg _) _)
    ?_
  by_cases hx : shift (k : ℤ) (periodicExtension w) ∈ cylinder u <;> simp [hx]

theorem measureReal_normPeriodicMeasure_cylinder (p : ℕ) {n : ℕ} (u : Fin n → ι) :
    (normPeriodicMeasure A q p).real (cylinder u) =
      (∑ k ∈ Finset.range (p + 1), cylSum A q p k u) /
        ((p + 1 : ℕ) * normSum A q (p + 1)) := by
  rw [measureReal_normPeriodicMeasure, Fintype.sum_prod_type, Finset.sum_div,
    ← Fin.sum_univ_eq_sum_range (fun k => cylSum A q p k u /
      ((p + 1 : ℕ) * normSum A q (p + 1))) (p + 1)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cylSum, Finset.sum_div]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [periodicWeight]
  ring

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in

theorem cylSum_eq {p k n l : ℕ} (h : k + n + l = p + 1) (u : Fin n → ι) :
    cylSum A q p k u = ∑ x : Fin k → ι, ∑ y : Fin l → ι,
      ‖word A (List.ofFn x ++ List.ofFn u ++ List.ofFn y)‖ ^ q := by
  classical
  set G : List ι → ℝ := fun L =>
    ‖word A L‖ ^ q * if (L.drop k).take n = List.ofFn u then 1 else 0 with hG
  have h1 : cylSum A q p k u = ∑ w : Fin (p + 1) → ι, G (List.ofFn w) := by
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [hG, Set.indicator_apply, Pi.one_apply,
      shift_periodicExtension_mem_cylinder_iff (by omega : k + n ≤ p + 1) w u]
  have h2 : ∀ N : ℕ, N = k + n + l → ∑ w : Fin N → ι, G (List.ofFn w) =
      ∑ x : Fin k → ι, ∑ y : Fin l → ι,
        ‖word A (List.ofFn x ++ List.ofFn u ++ List.ofFn y)‖ ^ q := by
    rintro N rfl
    rw [sum_ofFn_triple]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_eq_single u]
    · simp [hG]
    · intro v _ hv
      simp [hG, List.ofFn_inj, hv]
    · simp
  rw [h1, h2 (p + 1) h.symm]

theorem measureReal_normPeriodicMeasure_cylinder_le [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0)
    (hq : 0 ≤ q) {K : ℝ} (hK : ∀ j : ℕ, normSum A q j ≤ K * Real.exp (j * normPressure A q))
    (p : ℕ) {n : ℕ} (u : Fin n → ι) :
    (normPeriodicMeasure A q p).real (cylinder u) ≤
      K ^ 2 * (Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn u)‖ ^ q) +
        n / (p + 1 : ℕ) := by
  classical
  set P := normPressure A q with hPdef
  set Z := normSum A q (p + 1) with hZdef
  set a := K ^ 2 * (Real.exp (-(n * P)) * ‖word A (List.ofFn u)‖ ^ q) with hadef
  have hZ : 0 < Z := normSum_pos hA (p + 1)
  have hZe : Real.exp ((p + 1 : ℕ) * P) ≤ Z := exp_mul_normPressure_le_normSum hA hq (p + 1)
  have ha : 0 ≤ a := by positivity
  have hterm : ∀ k ∈ Finset.range (p + 1),
      cylSum A q p k u ≤ (a + if p + 1 < k + n then 1 else 0) * Z := by
    intro k _
    by_cases hk : p + 1 < k + n
    · simp only [hk, ↓reduceIte]
      exact (cylSum_le_normSum p k u).trans (le_mul_of_one_le_left hZ.le (by linarith))
    · simp only [hk, ↓reduceIte, add_zero]
      obtain ⟨l, hl⟩ : ∃ l, k + n + l = p + 1 := ⟨p + 1 - (k + n), by omega⟩
      have hK0 : 0 ≤ K := by
        have := (normSum_pos (q := q) hA 0).le.trans (hK 0)
        exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
      have hψ : 0 ≤ ‖word A (List.ofFn u)‖ ^ q := Real.rpow_nonneg (norm_nonneg _) _
      have he : Real.exp (k * P) * Real.exp (l * P) =
          Real.exp (-(n * P)) * Real.exp ((p + 1 : ℕ) * P) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        have : (k : ℝ) + n + l = ((p + 1 : ℕ) : ℝ) := by exact_mod_cast hl
        linear_combination P * this
      calc cylSum A q p k u
          ≤ normSum A q k * ‖word A (List.ofFn u)‖ ^ q * normSum A q l := by
            rw [cylSum_eq hl]
            exact sum_triple_le hq _ k l
        _ ≤ (K * Real.exp (k * P)) * ‖word A (List.ofFn u)‖ ^ q * (K * Real.exp (l * P)) :=
            mul_le_mul (mul_le_mul_of_nonneg_right (hK k) hψ) (hK l) (normSum_pos hA l).le
              (mul_nonneg (mul_nonneg hK0 (Real.exp_pos _).le) hψ)
        _ = a * Real.exp ((p + 1 : ℕ) * P) := by
            rw [hadef]
            linear_combination K ^ 2 * ‖word A (List.ofFn u)‖ ^ q * he
        _ ≤ a * Z := mul_le_mul_of_nonneg_left hZe ha
  have hcard : ∑ k ∈ Finset.range (p + 1), (if p + 1 < k + n then (1 : ℝ) else 0) ≤ n := by
    rw [Finset.sum_boole]
    have hsub : (Finset.range (p + 1)).filter (fun k => p + 1 < k + n) ⊆
        Finset.Ico (p + 1 - n) (p + 1) := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      rw [Finset.mem_Ico]
      omega
    have := (Finset.card_le_card hsub).trans_eq (Nat.card_Ico _ _)
    exact_mod_cast this.trans (by omega)
  have hsum : ∑ k ∈ Finset.range (p + 1), cylSum A q p k u ≤ ((p + 1 : ℕ) * a + n) * Z := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by linarith) hZ.le
  have hN : (0 : ℝ) < ((p + 1 : ℕ) : ℝ) := by positivity
  rw [measureReal_normPeriodicMeasure_cylinder, div_le_iff₀ (mul_pos hN hZ)]
  calc ∑ k ∈ Finset.range (p + 1), cylSum A q p k u ≤ ((p + 1 : ℕ) * a + n) * Z := hsum
    _ = (a + n / (p + 1 : ℕ)) * ((p + 1 : ℕ) * Z) := by
        field_simp

theorem NormQMConstants.le_measureReal_normPeriodicMeasure_cylinder [Nonempty ι]
    (hA : ∀ i, (A i).det ≠ 0) (hq : 0 ≤ q) {m : ℕ} {c : ℝ} (h : NormQMConstants A q m c)
    {K : ℝ} (hK1 : 1 ≤ K) (hK : ∀ j : ℕ, normSum A q j ≤ K * Real.exp (j * normPressure A q))
    {p n : ℕ} (hn : 0 < n) (hp : n + 2 * m ≤ p + 1) (u : Fin n → ι) :
    ((p + 1 - n - 2 * m + 1 : ℕ) : ℝ) / (p + 1 : ℕ) *
        (padConst A q m c ^ 2 * K⁻¹ * Real.exp (-(2 * m * normPressure A q))) *
          (Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn u)‖ ^ q) ≤
      (normPeriodicMeasure A q p).real (cylinder u) := by
  set P := normPressure A q with hPdef
  set Z := normSum A q (p + 1) with hZdef
  set L := p + 1 - n - 2 * m with hLdef
  set κ := padConst A q m c with hκdef
  set ψ := ‖word A (List.ofFn u)‖ ^ q with hψdef
  have hZ : 0 < Z := normSum_pos hA (p + 1)
  have hK0 : 0 < K := by linarith
  have hψ : 0 ≤ ψ := Real.rpow_nonneg (norm_nonneg _) _
  have hκ : 0 < κ := padConst_pos h.1
  have hterm : ∀ a ∈ Finset.range (L + 1),
      κ ^ 2 * Real.exp (L * P) * ψ ≤ cylSum A q p (m + a) u := by
    intro a ha
    rw [Finset.mem_range] at ha
    have hl : m + a + n + (m + (L - a)) = p + 1 := by omega
    rw [cylSum_eq hl]
    refine le_trans ?_ (h.le_sum_triple hA hq (List.ofFn u) a (L - a))
    have h1 := exp_mul_normPressure_le_normSum (q := q) hA hq a
    have h2 := exp_mul_normPressure_le_normSum (q := q) hA hq (L - a)
    have hab : (a : ℝ) + ((L - a : ℕ) : ℝ) = L := by
      have : a + (L - a) = L := by omega
      exact_mod_cast this
    have he : Real.exp (L * P) = Real.exp (a * P) * Real.exp ((L - a : ℕ) * P) := by
      rw [← Real.exp_add, ← hab]
      ring_nf
    rw [he]
    calc κ ^ 2 * (Real.exp (a * P) * Real.exp ((L - a : ℕ) * P)) * ψ
        = κ ^ 2 * Real.exp (a * P) * ψ * Real.exp ((L - a : ℕ) * P) := by ring
      _ ≤ κ ^ 2 * normSum A q a * ψ * normSum A q (L - a) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity))
            hψ) h2 (Real.exp_pos _).le
            (mul_nonneg (mul_nonneg (by positivity) (normSum_pos hA a).le) hψ)
  have hsum : ((L + 1 : ℕ) : ℝ) * (κ ^ 2 * Real.exp (L * P) * ψ) ≤
      ∑ k ∈ Finset.range (p + 1), cylSum A q p k u := by
    have hsub : Finset.Ico m (m + (L + 1)) ⊆ Finset.range (p + 1) := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      rw [Finset.mem_range]
      omega
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun k _ _ => cylSum_nonneg p k u)
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    calc ((L + 1 : ℕ) : ℝ) * (κ ^ 2 * Real.exp (L * P) * ψ)
        = ∑ _a ∈ Finset.range (L + 1), κ ^ 2 * Real.exp (L * P) * ψ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ a ∈ Finset.range (L + 1), cylSum A q p (m + a) u := Finset.sum_le_sum hterm
  have hZK : Z ≤ K * Real.exp ((p + 1 : ℕ) * P) := hK (p + 1)
  have he : Real.exp (-(2 * m * P)) * Real.exp (-(n * P)) * Real.exp ((p + 1 : ℕ) * P) =
      Real.exp (L * P) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    have : (L : ℝ) + n + 2 * m = ((p + 1 : ℕ) : ℝ) := by
      have : L + n + 2 * m = p + 1 := by omega
      exact_mod_cast this
    linear_combination (-P) * this
  have hN : (0 : ℝ) < ((p + 1 : ℕ) : ℝ) := by positivity
  rw [measureReal_normPeriodicMeasure_cylinder, le_div_iff₀ (mul_pos hN hZ)]
  refine le_trans ?_ hsum
  calc ((p + 1 - n - 2 * m + 1 : ℕ) : ℝ) / (p + 1 : ℕ) *
        (κ ^ 2 * K⁻¹ * Real.exp (-(2 * m * P))) * (Real.exp (-(n * P)) * ψ) *
          ((p + 1 : ℕ) * Z)
      = ((L + 1 : ℕ) : ℝ) * (κ ^ 2 * ψ * K⁻¹ * Real.exp (-(2 * m * P)) *
          Real.exp (-(n * P))) * Z := by
        rw [hLdef]
        field_simp
    _ ≤ ((L + 1 : ℕ) : ℝ) * (κ ^ 2 * ψ * K⁻¹ * Real.exp (-(2 * m * P)) *
          Real.exp (-(n * P))) * (K * Real.exp ((p + 1 : ℕ) * P)) := by gcongr
    _ = ((L + 1 : ℕ) : ℝ) * (κ ^ 2 * Real.exp (L * P) * ψ) := by
        rw [← he]
        field_simp

theorem NormQMConstants.exists_eventually_gibbs [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0)
    (hq : 0 ≤ q) {m : ℕ} {c : ℝ} (h : NormQMConstants A q m c) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ u : Fin n → ι, ∀ᶠ p in atTop,
      C⁻¹ * (Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn u)‖ ^ q) ≤
          (normPeriodicMeasure A q p).real (cylinder u) ∧
        (normPeriodicMeasure A q p).real (cylinder u) ≤
          C * (Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn u)‖ ^ q) := by
  obtain ⟨K, hK1, hK⟩ := h.exists_normSum_le hA hq
  set P := normPressure A q with hPdef
  set c₁ := padConst A q m c ^ 2 * K⁻¹ * Real.exp (-(2 * m * P)) / 2 with hc₁def
  have hκ := padConst_pos (A := A) (q := q) (m := m) h.1
  have hK0 : 0 < K := by linarith
  have hc₁ : 0 < c₁ := by positivity
  refine ⟨max (2 * K ^ 2) c₁⁻¹, lt_max_of_lt_left (by positivity), fun n hn u => ?_⟩
  set g := Real.exp (-(n * P)) * ‖word A (List.ofFn u)‖ ^ q with hgdef
  have hg : 0 < g := mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (norm_word_pos hA _) _)
  have hC1 : (max (2 * K ^ 2) c₁⁻¹)⁻¹ ≤ c₁ := by
    rw [inv_le_comm₀ (lt_max_of_lt_left (by positivity)) hc₁]
    exact le_max_right _ _
  have hlim : Tendsto (fun p : ℕ => (n : ℝ) / (p + 1 : ℕ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (n : ℝ)).comp (tendsto_add_atTop_nat 1)
  have hev := hlim.eventually (gt_mem_nhds (mul_pos (pow_pos hK0 2) hg))
  filter_upwards [hev, eventually_ge_atTop (2 * (n + 2 * m))] with p hp1 hp2
  constructor
  · have hlow := h.le_measureReal_normPeriodicMeasure_cylinder hA hq hK1 hK hn
      (by omega : n + 2 * m ≤ p + 1) u
    refine le_trans ?_ hlow
    have hfrac : (1 : ℝ) / 2 ≤ ((p + 1 - n - 2 * m + 1 : ℕ) : ℝ) / (p + 1 : ℕ) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      have : p + 1 ≤ 2 * (p + 1 - n - 2 * m + 1) := by omega
      have : ((p + 1 : ℕ) : ℝ) ≤ ((2 * (p + 1 - n - 2 * m + 1) : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this ⊢
      linarith
    calc (max (2 * K ^ 2) c₁⁻¹)⁻¹ * g ≤ c₁ * g := mul_le_mul_of_nonneg_right hC1 hg.le
      _ = 1 / 2 * (padConst A q m c ^ 2 * K⁻¹ * Real.exp (-(2 * m * P))) * g := by
          rw [hc₁def]
          ring
      _ ≤ ((p + 1 - n - 2 * m + 1 : ℕ) : ℝ) / (p + 1 : ℕ) *
            (padConst A q m c ^ 2 * K⁻¹ * Real.exp (-(2 * m * P))) * g := by
          gcongr
  · have hup := measureReal_normPeriodicMeasure_cylinder_le hA hq hK p u
    calc (normPeriodicMeasure A q p).real (cylinder u) ≤ K ^ 2 * g + n / (p + 1 : ℕ) := hup
      _ ≤ 2 * K ^ 2 * g := by linarith
      _ ≤ max (2 * K ^ 2) c₁⁻¹ * g := mul_le_mul_of_nonneg_right (le_max_left _ _) hg.le

end MatrixTuple

end FractalGeometry
