import Mathlib
import FractalGeometry.LinearCocycles.Products
import FractalGeometry.Pressure.GibbsUniqueness
import FractalGeometry.Pressure.NormPotential
import FractalGeometry.Pressure.PartitionSums
import FractalGeometry.Pressure.QuasiMultiplicative
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.Shift

namespace FractalGeometry

open MeasureTheory Filter Topology Set

open scoped ENNReal symmDiff Matrix.Norms.L2Operator

namespace MatrixTuple

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {A : ι → Matrix (Fin 2) (Fin 2) ℝ} {q : ℝ} {μ : Measure (ℤ → ι)} {C : ℝ} {m : ℕ} {c : ℝ}

variable (A q μ C) in

def NormGibbsBounds : Prop :=
  1 ≤ C ∧ ∀ (n : ℕ) (w : Fin n → ι),
    C⁻¹ * (Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn w)‖ ^ q) ≤
        μ.real (cylinder w) ∧
      μ.real (cylinder w) ≤ C * (Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn w)‖ ^ q)

omit [MeasurableSingletonClass ι] in

theorem HasNormGibbs.exists_normGibbsBounds [IsProbabilityMeasure μ] (h : HasNormGibbs A q μ) :
    ∃ C : ℝ, NormGibbsBounds A q μ C := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨max C 1, le_max_right _ _, fun n w => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hcyl : cylinder w = univ := eq_univ_of_forall fun x k => k.elim0
    have hg : Real.exp (-((0 : ℕ) * normPressure A q)) * ‖word A (List.ofFn w)‖ ^ q = 1 := by
      simp
    rw [hcyl, probReal_univ, hg, mul_one, mul_one]
    exact ⟨inv_le_one_of_one_le₀ (le_max_right _ _), le_max_right _ _⟩
  · have hg : 0 ≤ Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn w)‖ ^ q :=
      mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (norm_nonneg _) _)
    refine ⟨le_trans ?_ (h n hn w).1, (h n hn w).2.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right (inv_anti₀ hC (le_max_left _ _)) hg
    · exact mul_le_mul_of_nonneg_right (le_max_left _ _) hg

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in

variable (A q C m c) in

noncomputable def qbConst : ℝ := (C ^ 3)⁻¹ * c * Real.exp (-(m * |normPressure A q|))

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in

theorem qbConst_pos (hC : 1 ≤ C) (hc : 0 < c) : 0 < qbConst A q C m c := by
  have : 0 < C := by linarith
  unfold qbConst
  positivity

omit [MeasurableSingletonClass ι] in

theorem NormGibbsBounds.quasiBernoulli_cylinder [IsFiniteMeasure μ] (hg : NormGibbsBounds A q μ C)
    (h : NormQMConstants A q m c) {n L : ℕ} (u : Fin n → ι) (v : Fin L → ι) :
    qbConst A q C m c * μ.real (cylinder u) * μ.real (cylinder v) ≤
      ∑ j ∈ Finset.range (m + 1),
        μ.real (cylinder u ∩ shift ((n + j : ℕ) : ℤ) ⁻¹' cylinder v) := by
  obtain ⟨k, hk, hle⟩ := h.2 (List.ofFn u) (List.ofFn v)
  set j := k.length with hjdef
  set P := normPressure A q with hPdef
  set kf : Fin j → ι := fun i => k[(i : ℕ)] with hkf
  have hkf' : List.ofFn kf = k := List.ofFn_getElem
  set w : Fin (n + j + L) → ι := Fin.append (Fin.append u kf) v with hw
  have hwl : List.ofFn w = List.ofFn u ++ k ++ List.ofFn v := by
    rw [hw, List.ofFn_fin_append, List.ofFn_fin_append, hkf']
  have hsub : cylinder w ⊆ cylinder u ∩ shift ((n + j : ℕ) : ℤ) ⁻¹' cylinder v := by
    rw [hw, cylinder_append, cylinder_append]
    exact fun x hx => ⟨hx.1.1, hx.2⟩
  have hC : 0 < C := by linarith [hg.1]
  have hc := h.1
  have hψu : 0 ≤ ‖word A (List.ofFn u)‖ ^ q := Real.rpow_nonneg (norm_nonneg _) _
  have hψv : 0 ≤ ‖word A (List.ofFn v)‖ ^ q := Real.rpow_nonneg (norm_nonneg _) _
  have hu := (hg.2 n u).2
  have hv := (hg.2 L v).2
  have hlow := (hg.2 (n + j + L) w).1
  rw [hwl] at hlow
  have hjP : -(m * |P|) ≤ -(j * P) := by
    have h1 : (j : ℝ) * P ≤ j * |P| := mul_le_mul_of_nonneg_left (le_abs_self P) (Nat.cast_nonneg _)
    have h2 : (j : ℝ) * |P| ≤ m * |P| :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (abs_nonneg P)
    linarith
  have hexp : Real.exp (-(m * |P|)) * (Real.exp (-(n * P)) * Real.exp (-(L * P))) ≤
      Real.exp (-(((n + j + L : ℕ) : ℝ) * P)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    push_cast
    linarith
  have hj : j ∈ Finset.range (m + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hk)
  refine le_trans ?_ (Finset.single_le_sum (f := fun j' => μ.real (cylinder u ∩
    shift ((n + j' : ℕ) : ℤ) ⁻¹' cylinder v)) (fun _ _ => measureReal_nonneg) hj)
  refine le_trans ?_ (measureReal_mono hsub)
  refine le_trans ?_ hlow
  calc qbConst A q C m c * μ.real (cylinder u) * μ.real (cylinder v)
      ≤ qbConst A q C m c * (C * (Real.exp (-(n * P)) * ‖word A (List.ofFn u)‖ ^ q)) *
          (C * (Real.exp (-(L * P)) * ‖word A (List.ofFn v)‖ ^ q)) := by
        have := qbConst_pos (A := A) (q := q) (m := m) hg.1 hc
        gcongr
    _ = C⁻¹ * (Real.exp (-(m * |P|)) * (Real.exp (-(n * P)) * Real.exp (-(L * P)))) *
          (c * (‖word A (List.ofFn u)‖ ^ q * ‖word A (List.ofFn v)‖ ^ q)) := by
        rw [qbConst, ← hPdef]
        field_simp
    _ ≤ C⁻¹ * Real.exp (-(((n + j + L : ℕ) : ℝ) * P)) *
          ‖word A (List.ofFn u ++ k ++ List.ofFn v)‖ ^ q :=
        mul_le_mul (mul_le_mul_of_nonneg_left hexp (inv_nonneg.2 hC.le)) hle
          (mul_nonneg hc.le (mul_nonneg hψu hψv))
          (mul_nonneg (inv_nonneg.2 hC.le) (Real.exp_pos _).le)
    _ = C⁻¹ * (Real.exp (-(((n + j + L : ℕ) : ℝ) * P)) *
          ‖word A (List.ofFn u ++ k ++ List.ofFn v)‖ ^ q) := by ring

open Classical in

theorem measureReal_inter_shift_window_preimage [IsFiniteMeasure μ]
    (B : Set (ℤ → ι)) (t : ℤ) (M : ℕ) (F : Set (Fin (2 * M + 1) → ι)) :
    μ.real (B ∩ shift (t + M) ⁻¹' (window M ⁻¹' F)) =
      ∑ w ∈ F.toFinset, μ.real (B ∩ shift t ⁻¹' cylinder w) := by
  set g : (ℤ → ι) → Fin (2 * M + 1) → ι := fun x => block (2 * M + 1) (shift t x) with hgdef
  have hgm : Measurable g := (measurable_block _).comp (measurable_shift _)
  have hpre : shift (t + M) ⁻¹' (window M ⁻¹' F) =
      g ⁻¹' ((F.toFinset : Finset _) : Set (Fin (2 * M + 1) → ι)) := by
    rw [Set.coe_toFinset]
    ext x
    simp only [mem_preimage, hgdef]
    have : window M (shift (t + M) x) = block (2 * M + 1) (shift t x) := by
      funext k
      simp only [window, block_apply, shift_apply]
      congr 1
      ring
    rw [this]
  have hfib : ∀ w, g ⁻¹' {w} = shift t ⁻¹' cylinder w := by
    intro w
    rw [cylinder_eq_preimage]
    rfl
  rw [hpre, inter_comm, ← measureReal_restrict_apply (hgm (Finset.measurableSet _)),
    ← sum_measureReal_preimage_singleton _ fun w _ => hgm (measurableSet_singleton w)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [measureReal_restrict_apply (hgm (measurableSet_singleton w)), hfib, inter_comm]

theorem NormGibbsBounds.quasiBernoulli_window [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (hg : NormGibbsBounds A q μ C)
    (h : NormQMConstants A q m c) {n : ℕ} (u : Fin n → ι) (M : ℕ)
    (F : Set (Fin (2 * M + 1) → ι)) :
    qbConst A q C m c * μ.real (cylinder u) * μ.real (window M ⁻¹' F) ≤
      ∑ j ∈ Finset.range (m + 1),
        μ.real (cylinder u ∩ shift (((n + j : ℕ) : ℤ) + M) ⁻¹' (window M ⁻¹' F)) := by
  classical
  have hwin : μ.real (window M ⁻¹' F) = ∑ w ∈ F.toFinset, μ.real (cylinder w) := by
    have := measure_window_preimage hinv M F.toFinset
    rw [Set.coe_toFinset] at this
    rw [measureReal_def, this, ENNReal.toReal_sum fun _ _ => measure_ne_top _ _]
    rfl
  simp only [measureReal_inter_shift_window_preimage]
  rw [hwin, Finset.mul_sum, Finset.sum_comm]
  exact Finset.sum_le_sum fun w _ => hg.quasiBernoulli_cylinder h u w

theorem NormGibbsBounds.quasiBernoulli_invariant [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (hg : NormGibbsBounds A q μ C)
    (h : NormQMConstants A q m c) {E : Set (ℤ → ι)} (hE : MeasurableSet E)
    (hEinv : shift 1 ⁻¹' E = E) {n : ℕ} (u : Fin n → ι) :
    qbConst A q C m c * μ.real (cylinder u) * μ.real E ≤ (m + 1) * μ.real (cylinder u ∩ E) := by
  set κ := qbConst A q C m c with hκdef
  have hκ : 0 < κ := qbConst_pos hg.1 h.1
  have hdense := Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite μ
    isSetAlgebra_windowSets generateFrom_windowSets.symm
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hm : (0 : ℝ) < m + 1 + κ := by positivity
  have hδ : (0 : ℝ) < ε / (m + 1 + κ) := div_pos hε hm
  obtain ⟨S, ⟨M, F, rfl⟩, hES⟩ := hdense.approx E hE (measure_ne_top _ _) (ε / (m + 1 + κ)) hδ
  have hES' : μ.real (E ∆ (window M ⁻¹' F)) < ε / (m + 1 + κ) :=
    ENNReal.toReal_lt_of_lt_ofReal hES
  set S := window M ⁻¹' F with hSdef
  have hS : MeasurableSet S := measurable_window M (Set.to_countable F).measurableSet
  have hqb := hg.quasiBernoulli_window hinv h u M F
  rw [← hSdef] at hqb
  have hsymm1 : μ.real (S \ E) ≤ μ.real (E ∆ S) :=
    measureReal_mono (subset_union_right (s := E \ S))
  have hsymm2 : μ.real (E \ S) ≤ μ.real (E ∆ S) :=
    measureReal_mono (subset_union_left (t := S \ E))
  have hA : ∀ j : ℕ, μ.real (cylinder u ∩ shift (((n + j : ℕ) : ℤ) + M) ⁻¹' S) ≤
      μ.real (cylinder u ∩ E) + μ.real (E ∆ S) := by
    intro j
    set k : ℕ := n + j + M with hkdef
    have hk : ((k : ℕ) : ℤ) = ((n + j : ℕ) : ℤ) + M := by rw [hkdef]; push_cast; ring
    rw [← hk]
    have hEk : shift (k : ℤ) ⁻¹' E = E := by
      rw [← iterate_shift_one]
      exact Function.IsFixedPt.preimage_iterate hEinv k
    calc μ.real (cylinder u ∩ shift (k : ℤ) ⁻¹' S)
        ≤ μ.real ((cylinder u ∩ E) ∪ shift (k : ℤ) ⁻¹' (S \ E)) := by
          refine measureReal_mono fun x hx => ?_
          by_cases hxE : x ∈ E
          · exact Or.inl ⟨hx.1, hxE⟩
          · refine Or.inr ⟨hx.2, fun hxE' => hxE ?_⟩
            rw [← hEk]
            exact hxE'
      _ ≤ μ.real (cylinder u ∩ E) + μ.real (shift (k : ℤ) ⁻¹' (S \ E)) :=
          measureReal_union_le _ _
      _ = μ.real (cylinder u ∩ E) + μ.real (S \ E) := by
          rw [(measurePreserving_shift_natCast hinv k).measureReal_preimage
            (hS.diff hE).nullMeasurableSet]
      _ ≤ μ.real (cylinder u ∩ E) + μ.real (E ∆ S) := by linarith
  have hB : μ.real E ≤ μ.real S + μ.real (E ∆ S) := by
    calc μ.real E ≤ μ.real (S ∪ (E \ S)) := measureReal_mono fun x hx => by
          by_cases hxS : x ∈ S
          · exact Or.inl hxS
          · exact Or.inr ⟨hx, hxS⟩
      _ ≤ μ.real S + μ.real (E \ S) := measureReal_union_le _ _
      _ ≤ μ.real S + μ.real (E ∆ S) := by linarith
  have hsum : ∑ j ∈ Finset.range (m + 1),
      μ.real (cylinder u ∩ shift (((n + j : ℕ) : ℤ) + M) ⁻¹' S) ≤
        (m + 1) * (μ.real (cylinder u ∩ E) + μ.real (E ∆ S)) := by
    refine (Finset.sum_le_sum fun j _ => hA j).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    exact le_rfl
  have hv0 : 0 ≤ μ.real (cylinder u) := measureReal_nonneg
  have hv1 : μ.real (cylinder u) ≤ 1 := measureReal_le_one
  have hd0 : 0 ≤ μ.real (E ∆ S) := measureReal_nonneg
  have hcv : 0 ≤ κ * μ.real (cylinder u) := mul_nonneg hκ.le hv0
  have hsmall : (m + 1 + κ) * μ.real (E ∆ S) ≤ ε := by
    rw [lt_div_iff₀ hm] at hES'
    linarith
  calc κ * μ.real (cylinder u) * μ.real E
      ≤ κ * μ.real (cylinder u) * (μ.real S + μ.real (E ∆ S)) :=
        mul_le_mul_of_nonneg_left hB hcv
    _ = κ * μ.real (cylinder u) * μ.real S + κ * μ.real (cylinder u) * μ.real (E ∆ S) := by
        ring
    _ ≤ (m + 1) * (μ.real (cylinder u ∩ E) + μ.real (E ∆ S)) + κ * μ.real (E ∆ S) :=
        add_le_add (hqb.trans hsum)
          (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hκ.le hv1) hd0)
    _ ≤ (m + 1) * μ.real (cylinder u ∩ E) + ε := by nlinarith

theorem NormGibbsBounds.ergodic [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (hg : NormGibbsBounds A q μ C)
    (h : NormQMConstants A q m c) : Ergodic (shift 1) μ := by
  refine ⟨hinv, ⟨fun E hE hEinv => ?_⟩⟩
  rw [eventuallyEmptyOrUniv_iff', ae_eq_empty, ae_eq_univ]
  by_cases hE0 : μ E = 0
  · exact Or.inl hE0
  right
  set κ := qbConst A q C m c with hκdef
  have hκ : 0 < κ := qbConst_pos hg.1 h.1
  have hEpos : 0 < μ.real E := ENNReal.toReal_pos hE0 (measure_ne_top _ _)
  have hcE : 0 < κ * μ.real E := mul_pos hκ hEpos
  have hrestr : MeasurePreserving (shift 1) (μ.restrict E) (μ.restrict E) := by
    have := hinv.restrict_preimage hE
    rwa [hEinv] at this
  have hcyl : ∀ (n : ℕ) (w : Fin n → ι), μ (cylinder w) ≤
      ENNReal.ofReal ((m + 1) * (κ * μ.real E)⁻¹) * μ.restrict E (cylinder w) := by
    intro n w
    have hq := hg.quasiBernoulli_invariant hinv h hE hEinv w
    rw [Measure.restrict_apply (measurableSet_cylinder w), ← ofReal_measureReal,
      ← ofReal_measureReal, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc μ.real (cylinder w) = (κ * μ.real E)⁻¹ * (κ * μ.real (cylinder w) * μ.real E) := by
          field_simp
      _ ≤ (κ * μ.real E)⁻¹ * ((m + 1) * μ.real (cylinder w ∩ E)) := by gcongr
      _ = (m + 1) * (κ * μ.real E)⁻¹ * μ.real (cylinder w ∩ E) := by ring
  have hle := le_of_cylinder_le hrestr hinv ENNReal.ofReal_ne_top hcyl hE.compl
  rw [Measure.restrict_apply hE.compl, compl_inter_self, measure_empty, mul_zero] at hle
  exact le_antisymm hle zero_le

theorem HasNormGibbs.ergodic [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (hμ : HasNormGibbs A q μ)
    (hA : NormQuasiMultiplicative A) (hq : 0 ≤ q) : Ergodic (shift 1) μ := by
  obtain ⟨C, hC⟩ := hμ.exists_normGibbsBounds
  obtain ⟨m, c, h⟩ := hA.exists_normQMConstants hq
  exact hC.ergodic hinv h

end MatrixTuple

end FractalGeometry
