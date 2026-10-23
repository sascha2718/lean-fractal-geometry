import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Pressure.GibbsUniqueness
import FractalGeometry.Pressure.ParityShift.HolderPotential
import FractalGeometry.Pressure.ParityShift.SymbolicMetric
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.ParityShift
import FractalGeometry.Symbolic.ParityShiftMixing
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology Set

open scoped ENNReal symmDiff

noncomputable def quasiBernoulliConst (P C B D : ℝ) : ℝ :=
  (C ^ 3)⁻¹ * Real.exp (-(P + B + 2 * D))

theorem quasiBernoulliConst_pos {P C B D : ℝ} (hC : 0 < C) : 0 < quasiBernoulliConst P C B D := by
  unfold quasiBernoulliConst
  positivity

section QuasiBernoulli

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {o : ι → ZMod 2} {f : (ℤ → ι × ZMod 2) → ℝ} {ν : Measure (ℤ → ι × ZMod 2)} {B D P C : ℝ}

omit [Fintype ι] [MeasurableSingletonClass ι] in

theorem IsGibbsPotential.measureReal_cylinder_le_exp [IsProbabilityMeasure ν]
    (hg : IsGibbsPotential o f ν P C) {y : ℤ → ι × ZMod 2} (hy : y ∈ subshift o) (n : ℕ) :
    ν.real (cylinder fun k : Fin n => y k) ≤
      C * Real.exp (-(n * P) + birkhoffSum (shift 1) f n y) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [CharP.cast_eq_zero, zero_mul, neg_zero, birkhoffSum_zero, Pi.zero_apply, add_zero,
      Real.exp_zero, mul_one]
    exact measureReal_le_one.trans (hg.one_le hy)
  · exact (hg.2 y hy n hn).2

omit [Fintype ι] [MeasurableSingletonClass ι] in

theorem IsGibbsPotential.quasiBernoulli_cylinder [IsProbabilityMeasure ν]
    (hν : ν (subshift o)ᶜ = 0) (hg : IsGibbsPotential o f ν P C)
    (h : HasBoundedDistortion o f B D) (h0 : ∃ i, o i = 0) (h1 : ∃ i, o i = 1) {n L : ℕ}
    (v : Fin n → ι × ZMod 2) (w : Fin L → ι × ZMod 2) :
    quasiBernoulliConst P C B D * ν.real (cylinder v) * ν.real (cylinder w) ≤
      ν.real (cylinder v ∩ shift ((n : ℤ) + 1) ⁻¹' cylinder w) := by
  have hc := quasiBernoulliConst_pos (P := P) (B := B) (D := D) hg.1
  by_cases hv : ν (cylinder v) = 0
  · have : ν.real (cylinder v) = 0 := by rw [measureReal_def, hv, ENNReal.toReal_zero]
    rw [this, mul_zero, zero_mul]
    exact measureReal_nonneg
  by_cases hw : ν (cylinder w) = 0
  · have : ν.real (cylinder w) = 0 := by rw [measureReal_def, hw, ENNReal.toReal_zero]
    rw [this, mul_zero]
    exact measureReal_nonneg
  obtain ⟨y, hyv, hy⟩ := nonempty_of_measure_ne_zero
    (by rwa [measure_inter_conull hν] : ν (cylinder v ∩ subshift o) ≠ 0)
  obtain ⟨z, hzw, hz⟩ := nonempty_of_measure_ne_zero
    (by rwa [measure_inter_conull hν] : ν (cylinder w ∩ subshift o) ≠ 0)
  set b : ℤ := (n : ℤ) + 1 with hb
  set z' : ℤ → ι × ZMod 2 := shift (-b) z with hz'def
  have hz' : z' ∈ subshift o := shift_mem_subshift o hz _
  obtain ⟨r, hr1, hr2⟩ := exists_trans_trans o h0 h1 (y (b - 2)) (z' b)
  set x : ℤ → ι × ZMod 2 := glue y z' b r with hxdef
  have hx : x ∈ subshift o := glue_mem_subshift hy hz' hr1 hr2
  have hxy : ∀ k : ℕ, k < n → x k = y k := fun k hk => glue_of_le (by omega)
  have hxz : ∀ k : ℕ, k < L → shift b x k = z k := by
    intro k _
    rw [shift_apply, hxdef, glue_of_ge (by omega), hz'def, shift_apply]
    congr 1
    ring
  have hsub : (cylinder fun k : Fin (n + (L + 1)) => x k) ⊆
      cylinder v ∩ shift b ⁻¹' cylinder w := by
    intro q hq
    refine ⟨fun k => ?_, fun k => ?_⟩
    · have hqk : q (k : ℕ) = x (k : ℕ) := hq ⟨k, by omega⟩
      rw [hqk, hxy k k.2]
      exact hyv k
    · rw [shift_apply]
      have hqk : q ((n + 1 + k : ℕ) : ℤ) = x ((n + 1 + k : ℕ) : ℤ) := hq ⟨n + 1 + k, by omega⟩
      have hcast : ((n + 1 + k : ℕ) : ℤ) = b + k := by push_cast; ring
      rw [hcast] at hqk
      have hxk := hxz k k.2
      rw [shift_apply] at hxk
      rw [hqk, hxk]
      exact hzw k
  have hlow := (hg.2 x hx (n + (L + 1)) (by omega)).1
  have hS : birkhoffSum (shift 1) f (n + (L + 1)) x = birkhoffSum (shift 1) f n x +
      (f (shift n x) + birkhoffSum (shift 1) f L (shift b x)) := by
    rw [birkhoffSum_add_right_apply, birkhoffSum_succ_apply', iterate_shift_one, shift_shift]
  have d1 := abs_le.1 (h.distortion n x hx y hy hxy)
  have d2 := abs_le.1 (h.distortion L (shift b x) (shift_mem_subshift o hx b) z hz hxz)
  have d3 := abs_le.1 (h.abs_le_bound (shift n x) (shift_mem_subshift o hx n))
  have u1 := hg.measureReal_cylinder_le_exp hy n
  have u2 := hg.measureReal_cylinder_le_exp hz L
  rw [show (fun k : Fin n => y k) = v from funext hyv] at u1
  rw [show (fun k : Fin L => z k) = w from funext hzw] at u2
  have hexp : Real.exp (-(P + B + 2 * D)) *
      Real.exp (-(n * P) + birkhoffSum (shift 1) f n y) *
        Real.exp (-(L * P) + birkhoffSum (shift 1) f L z) ≤
      Real.exp (-(((n + (L + 1) : ℕ) : ℝ) * P) + birkhoffSum (shift 1) f (n + (L + 1)) x) := by
    rw [← Real.exp_add, ← Real.exp_add, hS]
    refine Real.exp_le_exp.2 ?_
    push_cast
    linarith [d1.1, d2.1, d3.1]
  have hC := hg.1
  calc quasiBernoulliConst P C B D * ν.real (cylinder v) * ν.real (cylinder w)
      ≤ quasiBernoulliConst P C B D *
          (C * Real.exp (-(n * P) + birkhoffSum (shift 1) f n y)) *
            (C * Real.exp (-(L * P) + birkhoffSum (shift 1) f L z)) := by
        gcongr
    _ = C⁻¹ * (Real.exp (-(P + B + 2 * D)) *
          Real.exp (-(n * P) + birkhoffSum (shift 1) f n y) *
            Real.exp (-(L * P) + birkhoffSum (shift 1) f L z)) := by
        unfold quasiBernoulliConst
        field_simp
    _ ≤ C⁻¹ * Real.exp (-(((n + (L + 1) : ℕ) : ℝ) * P) +
          birkhoffSum (shift 1) f (n + (L + 1)) x) := by gcongr
    _ ≤ ν.real (cylinder fun k : Fin (n + (L + 1)) => x k) := hlow
    _ ≤ ν.real (cylinder v ∩ shift b ⁻¹' cylinder w) := measureReal_mono hsub

theorem IsGibbsPotential.quasiBernoulli_window [IsProbabilityMeasure ν]
    (hinv : MeasurePreserving (shift 1) ν ν) (hν : ν (subshift o)ᶜ = 0)
    (hg : IsGibbsPotential o f ν P C) (h : HasBoundedDistortion o f B D) (h0 : ∃ i, o i = 0)
    (h1 : ∃ i, o i = 1) {n : ℕ} (v : Fin n → ι × ZMod 2) (M : ℕ)
    (F : Set (Fin (2 * M + 1) → ι × ZMod 2)) :
    quasiBernoulliConst P C B D * ν.real (cylinder v) * ν.real (window M ⁻¹' F) ≤
      ν.real (cylinder v ∩ shift ((n : ℤ) + 1 + M) ⁻¹' (window M ⁻¹' F)) := by
  classical
  set g : (ℤ → ι × ZMod 2) → Fin (2 * M + 1) → ι × ZMod 2 :=
    fun x => block (2 * M + 1) (shift ((n : ℤ) + 1) x) with hgdef
  have hgm : Measurable g := (measurable_block _).comp (measurable_shift _)
  have hpre : shift ((n : ℤ) + 1 + M) ⁻¹' (window M ⁻¹' F) =
      g ⁻¹' ((F.toFinset : Finset _) : Set (Fin (2 * M + 1) → ι × ZMod 2)) := by
    rw [Set.coe_toFinset]
    ext x
    simp only [mem_preimage, hgdef]
    have : window M (shift ((n : ℤ) + 1 + M) x) = block (2 * M + 1) (shift ((n : ℤ) + 1) x) := by
      funext k
      simp only [window, block_apply, shift_apply]
      congr 1
      ring
    rw [this]
  have hfib : ∀ w, g ⁻¹' {w} = shift ((n : ℤ) + 1) ⁻¹' cylinder w := by
    intro w
    rw [cylinder_eq_preimage]
    rfl
  have hwin : ν.real (window M ⁻¹' F) = ∑ w ∈ F.toFinset, ν.real (cylinder w) := by
    have := measure_window_preimage hinv M F.toFinset
    rw [Set.coe_toFinset] at this
    rw [measureReal_def, this, ENNReal.toReal_sum fun _ _ => measure_ne_top _ _]
    rfl
  have hsum : ν.real (cylinder v ∩ shift ((n : ℤ) + 1 + M) ⁻¹' (window M ⁻¹' F)) =
      ∑ w ∈ F.toFinset, ν.real (cylinder v ∩ shift ((n : ℤ) + 1) ⁻¹' cylinder w) := by
    rw [hpre, inter_comm, ← measureReal_restrict_apply (hgm (Finset.measurableSet _)),
      ← sum_measureReal_preimage_singleton _ fun w _ => hgm (measurableSet_singleton w)]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [measureReal_restrict_apply (hgm (measurableSet_singleton w)), hfib, inter_comm]
  rw [hsum, hwin, Finset.mul_sum]
  exact Finset.sum_le_sum fun w _ => hg.quasiBernoulli_cylinder hν h h0 h1 v w

theorem IsGibbsPotential.quasiBernoulli_invariant [IsProbabilityMeasure ν]
    (hinv : MeasurePreserving (shift 1) ν ν) (hν : ν (subshift o)ᶜ = 0)
    (hg : IsGibbsPotential o f ν P C) (h : HasBoundedDistortion o f B D) (h0 : ∃ i, o i = 0)
    (h1 : ∃ i, o i = 1) {E : Set (ℤ → ι × ZMod 2)} (hE : MeasurableSet E)
    (hEinv : shift 1 ⁻¹' E = E) {n : ℕ} (v : Fin n → ι × ZMod 2) :
    quasiBernoulliConst P C B D * ν.real (cylinder v) * ν.real E ≤ ν.real (cylinder v ∩ E) := by
  set c := quasiBernoulliConst P C B D with hcdef
  have hc : 0 < c := quasiBernoulliConst_pos hg.1
  have hdense := Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite ν
    isSetAlgebra_windowSets generateFrom_windowSets.symm
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hδ : (0 : ℝ) < ε / (1 + c) := div_pos hε (by linarith)
  obtain ⟨S, ⟨M, F, rfl⟩, hES⟩ := hdense.approx E hE (measure_ne_top _ _) (ε / (1 + c)) hδ
  have hES' : ν.real (E ∆ (window M ⁻¹' F)) < ε / (1 + c) := ENNReal.toReal_lt_of_lt_ofReal hES
  set S := window M ⁻¹' F with hSdef
  have hS : MeasurableSet S := measurable_window M (Set.to_countable F).measurableSet
  set k : ℕ := n + 1 + M with hkdef
  have hk : ((k : ℕ) : ℤ) = (n : ℤ) + 1 + M := by rw [hkdef]; push_cast; ring
  have hEk : shift (k : ℤ) ⁻¹' E = E := by
    rw [← iterate_shift_one]
    exact Function.IsFixedPt.preimage_iterate hEinv k
  have hqb := hg.quasiBernoulli_window hinv hν h h0 h1 v M F
  rw [← hSdef, ← hk] at hqb
  have hsymm1 : ν.real (S \ E) ≤ ν.real (E ∆ S) :=
    measureReal_mono (subset_union_right (s := E \ S))
  have hsymm2 : ν.real (E \ S) ≤ ν.real (E ∆ S) :=
    measureReal_mono (subset_union_left (t := S \ E))
  have hA : ν.real (cylinder v ∩ shift (k : ℤ) ⁻¹' S) ≤
      ν.real (cylinder v ∩ E) + ν.real (E ∆ S) := by
    calc ν.real (cylinder v ∩ shift (k : ℤ) ⁻¹' S)
        ≤ ν.real ((cylinder v ∩ E) ∪ shift (k : ℤ) ⁻¹' (S \ E)) := by
          refine measureReal_mono fun x hx => ?_
          by_cases hxE : x ∈ E
          · exact Or.inl ⟨hx.1, hxE⟩
          · refine Or.inr ⟨hx.2, fun hxE' => hxE ?_⟩
            rw [← hEk]
            exact hxE'
      _ ≤ ν.real (cylinder v ∩ E) + ν.real (shift (k : ℤ) ⁻¹' (S \ E)) :=
          measureReal_union_le _ _
      _ = ν.real (cylinder v ∩ E) + ν.real (S \ E) := by
          rw [(measurePreserving_shift_natCast hinv k).measureReal_preimage
            (hS.diff hE).nullMeasurableSet]
      _ ≤ ν.real (cylinder v ∩ E) + ν.real (E ∆ S) := by linarith
  have hB : ν.real E ≤ ν.real S + ν.real (E ∆ S) := by
    calc ν.real E ≤ ν.real (S ∪ (E \ S)) := measureReal_mono fun x hx => by
          by_cases hxS : x ∈ S
          · exact Or.inl hxS
          · exact Or.inr ⟨hx, hxS⟩
      _ ≤ ν.real S + ν.real (E \ S) := measureReal_union_le _ _
      _ ≤ ν.real S + ν.real (E ∆ S) := by linarith
  have hv0 : 0 ≤ ν.real (cylinder v) := measureReal_nonneg
  have hv1 : ν.real (cylinder v) ≤ 1 := measureReal_le_one
  have hd0 : 0 ≤ ν.real (E ∆ S) := measureReal_nonneg
  have hcv : 0 ≤ c * ν.real (cylinder v) := mul_nonneg hc.le hv0
  have hsmall : (1 + c) * ν.real (E ∆ S) ≤ ε := by
    rw [lt_div_iff₀ (by linarith)] at hES'
    linarith
  calc c * ν.real (cylinder v) * ν.real E
      ≤ c * ν.real (cylinder v) * (ν.real S + ν.real (E ∆ S)) :=
        mul_le_mul_of_nonneg_left hB hcv
    _ = c * ν.real (cylinder v) * ν.real S + c * ν.real (cylinder v) * ν.real (E ∆ S) := by
        ring
    _ ≤ ν.real (cylinder v ∩ shift (k : ℤ) ⁻¹' S) + c * ν.real (E ∆ S) := by
        gcongr
        nlinarith
    _ ≤ ν.real (cylinder v ∩ E) + ε := by nlinarith

theorem IsGibbsPotential.ergodic [IsProbabilityMeasure ν]
    (hinv : MeasurePreserving (shift 1) ν ν) (hν : ν (subshift o)ᶜ = 0)
    (hg : IsGibbsPotential o f ν P C) (h : HasBoundedDistortion o f B D) (h0 : ∃ i, o i = 0)
    (h1 : ∃ i, o i = 1) : Ergodic (shift 1) ν := by
  refine ⟨hinv, ⟨fun E hE hEinv => ?_⟩⟩
  rw [eventuallyEmptyOrUniv_iff', ae_eq_empty, ae_eq_univ]
  by_cases hE0 : ν E = 0
  · exact Or.inl hE0
  right
  set c := quasiBernoulliConst P C B D with hcdef
  have hc : 0 < c := quasiBernoulliConst_pos hg.1
  have hEpos : 0 < ν.real E := ENNReal.toReal_pos hE0 (measure_ne_top _ _)
  have hcE : 0 < c * ν.real E := mul_pos hc hEpos
  have hrestr : MeasurePreserving (shift 1) (ν.restrict E) (ν.restrict E) := by
    have := hinv.restrict_preimage hE
    rwa [hEinv] at this
  have hcyl : ∀ (n : ℕ) (w : Fin n → ι × ZMod 2),
      ν (cylinder w) ≤ ENNReal.ofReal (c * ν.real E)⁻¹ * ν.restrict E (cylinder w) := by
    intro n w
    have hq := hg.quasiBernoulli_invariant hinv hν h h0 h1 hE hEinv w
    rw [Measure.restrict_apply (measurableSet_cylinder w), ← ofReal_measureReal,
      ← ofReal_measureReal, ← ENNReal.ofReal_mul (inv_nonneg.2 hcE.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [inv_mul_eq_div, le_div_iff₀ hcE]
    linarith
  have hle := le_of_cylinder_le hrestr hinv ENNReal.ofReal_ne_top hcyl hE.compl
  rw [Measure.restrict_apply hE.compl, compl_inter_self, measure_empty, mul_zero] at hle
  exact le_antisymm hle zero_le

theorem IsGibbsPotential.ergodic_of_isHolder [IsProbabilityMeasure ν]
    (hinv : MeasurePreserving (shift 1) ν ν) (hν : ν (subshift o)ᶜ = 0)
    (hg : IsGibbsPotential o f ν P C) (hf : IsHolderPotential o f) (h0 : ∃ i, o i = 0)
    (h1 : ∃ i, o i = 1) : Ergodic (shift 1) ν := by
  have : Nonempty ι := ⟨h0.choose⟩
  obtain ⟨B, D, -, -, h⟩ := hf.exists_hasBoundedDistortion
  exact hg.ergodic hinv hν h h0 h1

end QuasiBernoulli

end FractalGeometry
