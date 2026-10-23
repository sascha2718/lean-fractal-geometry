import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory ProbabilityTheory Filter

variable {Omega : Type*} [MeasurableSpace Omega]

theorem integral_sq_sum_le {P : Measure Omega} [IsProbabilityMeasure P]
    {y : Nat} {xi : Fin y -> Omega -> Real} {K mu : Real}
    (hxi_indep : iIndepFun xi P) (hxi_meas : forall c, Measurable (xi c))
    (hxi_nonneg : forall c omega, 0 <= xi c omega)
    (hxi_bound : forall c omega, xi c omega <= K)
    (hxi_mean : forall c, integral P (xi c) <= mu)
    (hmu : 0 <= mu) (hK : 0 <= K) :
    integral P (fun omega => (∑ c : Fin y, xi c omega) ^ 2) <=
      mu ^ 2 * y ^ 2 + K * mu * y := by
  classical
  have hxi_int (c : Fin y) : Integrable (xi c) P :=
    Integrable.of_bound (hxi_meas c).aestronglyMeasurable K <|
      ae_of_all P fun omega => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hxi_nonneg c omega)]
        exact hxi_bound c omega
  have hprod_int (c d : Fin y) : Integrable (fun omega => xi c omega * xi d omega) P :=
    Integrable.of_bound ((hxi_meas c).mul (hxi_meas d)).aestronglyMeasurable (K * K) <|
      ae_of_all P fun omega => by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (hxi_nonneg c omega) (hxi_nonneg d omega))]
        exact mul_le_mul (hxi_bound c omega) (hxi_bound d omega)
          (hxi_nonneg d omega) hK
  have hterm (c d : Fin y) :
      integral P (fun omega => xi c omega * xi d omega) <=
        mu ^ 2 + if c = d then K * mu else 0 := by
    by_cases hcd : c = d
    · subst d
      rw [ite_eq_left rfl]
      calc
        integral P (fun omega => xi c omega * xi c omega) <=
            integral P (fun omega => K * xi c omega) := by
          apply integral_mono (hprod_int c c) ((hxi_int c).const_mul K)
          intro omega
          exact mul_le_mul_of_nonneg_right (hxi_bound c omega) (hxi_nonneg c omega)
        _ = K * integral P (xi c) := by rw [integral_const_mul]
        _ <= K * mu := mul_le_mul_of_nonneg_left (hxi_mean c) hK
        _ <= mu ^ 2 + K * mu := by nlinarith [sq_nonneg mu]
    · rw [ite_eq_right hcd]
      have hind : IndepFun (xi c) (xi d) P := hxi_indep.indepFun hcd
      have hfactor := hind.integral_mul_eq_mul_integral
        (hxi_meas c).aestronglyMeasurable (hxi_meas d).aestronglyMeasurable
      change integral P (fun omega => xi c omega * xi d omega) =
        integral P (xi c) * integral P (xi d) at hfactor
      rw [hfactor]
      simpa [pow_two] using mul_le_mul (hxi_mean c) (hxi_mean d)
        (integral_nonneg fun omega => hxi_nonneg d omega) hmu
  have hsq (omega : Omega) : (∑ c : Fin y, xi c omega) ^ 2 =
      ∑ c : Fin y, ∑ d : Fin y, xi c omega * xi d omega := by
    simp only [sq, Finset.sum_mul_sum]
  calc
    integral P (fun omega => (∑ c : Fin y, xi c omega) ^ 2) =
        ∑ c : Fin y, ∑ d : Fin y,
          integral P (fun omega => xi c omega * xi d omega) := by
      simp_rw [hsq]
      rw [integral_finsetSum]
      · exact Finset.sum_congr rfl fun c _ => integral_finsetSum _ fun d _ => hprod_int c d
      · exact fun c _ => integrable_finsetSum _ fun d _ => hprod_int c d
    _ <= ∑ c : Fin y, ∑ d : Fin y,
        (mu ^ 2 + if c = d then K * mu else 0) :=
      Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun d _ => hterm c d
    _ = mu ^ 2 * y ^ 2 + K * mu * y := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      simp
      ring

theorem one_fourth_mul_sq_integral_div_le_measure_ge_half
    {P : Measure Omega} [IsProbabilityMeasure P] {Z : Omega -> Real} {B : Real}
    (hZmeas : Measurable Z) (hZnonneg : forall omega, 0 <= Z omega)
    (hZbound : exists C : Real, forall omega, Z omega <= C)
    (hB : integral P (fun omega => Z omega ^ 2) <= B)
    (hBpos : 0 < B) :
    (integral P Z) ^ 2 / (4 * B) <=
      (P {omega | integral P Z / 2 <= Z omega}).toReal := by
  let a : Real := integral P Z
  let S : Set Omega := {omega | a / 2 <= Z omega}
  let I : Omega -> Real := S.indicator fun _ => 1
  obtain ⟨C, hC⟩ := hZbound
  have hZint : Integrable Z P := Integrable.of_bound hZmeas.aestronglyMeasurable C <|
    ae_of_all P fun omega => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hZnonneg omega)]
      exact hC omega
  have hZ2int : Integrable (fun omega => Z omega ^ 2) P :=
    Integrable.of_bound (hZmeas.pow_const 2).aestronglyMeasurable (C ^ 2) <|
      ae_of_all P fun omega => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (hZnonneg omega) (hC omega) 2
  have hS : MeasurableSet S := by
    exact measurableSet_le measurable_const hZmeas
  have hImeas : Measurable I := measurable_const.indicator hS
  have hI0 (omega : Omega) : 0 <= I omega :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) omega
  have hI1 (omega : Omega) : I omega <= 1 := by
    by_cases h : omega ∈ S <;> simp [I, h]
  have hIint : Integrable I P := Integrable.of_bound hImeas.aestronglyMeasurable 1 <|
    ae_of_all P fun omega => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hI0 omega)]
      exact hI1 omega
  have hZIint : Integrable (fun omega => Z omega * I omega) P :=
    Integrable.of_bound (hZmeas.mul hImeas).aestronglyMeasurable C <|
      ae_of_all P fun omega => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hZnonneg omega) (hI0 omega))]
        exact (mul_le_of_le_one_right (hZnonneg omega) (hI1 omega)).trans (hC omega)
  have ha0 : 0 <= a := integral_nonneg hZnonneg
  have hsplit : a / 2 <= integral P (fun omega => Z omega * I omega) := by
    have hpoint (omega : Omega) : Z omega <= Z omega * I omega + a / 2 := by
      by_cases h : omega ∈ S
      · rw [show I omega = 1 by simp [I, h]]
        linarith
      · have hn : Z omega < a / 2 := lt_of_not_ge h
        rw [show I omega = 0 by simp [I, h]]
        simpa using hn.le
    have hint := integral_mono hZint (hZIint.add (integrable_const _)) hpoint
    have hint' : a <= integral P (fun omega => Z omega * I omega) + a / 2 := by
      calc
        a = integral P Z := rfl
        _ <= integral P ((fun omega => Z omega * I omega) + fun _ => a / 2) := hint
        _ = integral P (fun omega => Z omega * I omega) + a / 2 := by
          change (∫ omega, Z omega * I omega + a / 2 ∂P) = _
          rw [integral_add hZIint (integrable_const _), integral_const, probReal_univ,
            one_smul]
    linarith
  have hZmem : MemLp Z 2 P :=
    (memLp_two_iff_integrable_sq hZmeas.aestronglyMeasurable).2 hZ2int
  have hImem : MemLp I 2 P :=
    (memLp_two_iff_integrable_sq hImeas.aestronglyMeasurable).2 <|
      Integrable.of_bound (hImeas.pow_const 2).aestronglyMeasurable 1 <|
        ae_of_all P fun omega => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          nlinarith [hI0 omega, hI1 omega]
  have hpq : (2 : Real).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hZmem' : MemLp Z (ENNReal.ofReal 2) P := by simpa using hZmem
  have hImem' : MemLp I (ENNReal.ofReal 2) P := by simpa using hImem
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (ae_of_all P hZnonneg) (ae_of_all P hI0) hZmem' hImem'
  have hI2 : integral P (fun omega => I omega ^ 2) = P.real S := by
    rw [← integral_indicator_one hS]
    congr 1
    funext omega
    by_cases h : omega ∈ S <;> simp [I, Set.indicator, h]
  simp_rw [Real.rpow_two] at hholder
  rw [hI2] at hholder
  norm_num at hholder
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hholder
  have hE20 : 0 <= integral P (fun omega => Z omega ^ 2) :=
    integral_nonneg fun omega => sq_nonneg _
  have hp0 : 0 <= P.real S := measureReal_nonneg
  have hx0 : 0 <= integral P (fun omega => Z omega * I omega) :=
    integral_nonneg fun omega => mul_nonneg (hZnonneg omega) (hI0 omega)
  have hsquare : (integral P (fun omega => Z omega * I omega)) ^ 2 <=
      integral P (fun omega => Z omega ^ 2) * P.real S := by
    calc
      (integral P (fun omega => Z omega * I omega)) ^ 2 <=
          (Real.sqrt (integral P (fun omega => Z omega ^ 2)) * Real.sqrt (P.real S)) ^ 2 :=
        pow_le_pow_left₀ hx0 hholder 2
      _ = integral P (fun omega => Z omega ^ 2) * P.real S := by
        rw [mul_pow, Real.sq_sqrt hE20, Real.sq_sqrt hp0]
  have halower : a ^ 2 / 4 <=
      (integral P (fun omega => Z omega * I omega)) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity : 0 <= a / 2) hsplit 2
    nlinarith
  have hmain : a ^ 2 / 4 <= B * P.real S :=
    halower.trans (hsquare.trans <| mul_le_mul_of_nonneg_right hB hp0)
  change a ^ 2 / (4 * B) <= P.real S
  rw [div_le_iff₀ (mul_pos (by norm_num) hBpos)]
  nlinarith

theorem integral_coupled_le_of_indepFun_finite_states
    {alpha beta : Type*} [Fintype alpha] [MeasurableSpace alpha]
    [MeasurableSingletonClass alpha] [Finite beta] [MeasurableSpace beta]
    [MeasurableSingletonClass beta]
    {P : Measure Omega} [IsFiniteMeasure P]
    {U : Omega -> alpha} {V : Omega -> beta}
    (hind : IndepFun U V P) (hU : Measurable U) (hV : Measurable V)
    (g : alpha -> beta -> Real) (h : alpha -> Real)
    (hbound : forall u, integral P (fun omega => g u (V omega)) <= h u) :
    integral P (fun omega => g (U omega) (V omega)) <=
      integral P (fun omega => h (U omega)) := by
  classical
  let atom : alpha -> alpha -> Real := fun u x => if x = u then 1 else 0
  have hatom (u : alpha) : Measurable (atom u) := by
    apply Measurable.ite
    · simp [Set.ofPred_eq_eq_singleton]
    · exact measurable_const
    · exact measurable_const
  have hatom_int (u : alpha) : Integrable (fun omega => atom u (U omega)) P := by
    apply Integrable.of_bound ((hatom u).comp hU).aestronglyMeasurable 1
    filter_upwards [] with omega
    by_cases hu : U omega = u <;> simp [atom, hu]
  have hg_int (u : alpha) : Integrable (fun omega => g u (V omega)) P := by
    have hgu : Measurable (g u) := measurable_of_finite _
    obtain ⟨C, hC⟩ := (Set.finite_range fun x => ‖g u x‖).bddAbove
    apply Integrable.of_bound (hgu.comp hV).aestronglyMeasurable C
    filter_upwards [] with omega
    exact hC (Set.mem_range_self (V omega))
  have hprod_int (u : alpha) : Integrable
      (fun omega => atom u (U omega) * g u (V omega)) P :=
    (hind.comp (hatom u) (measurable_of_finite (g u))).integrable_mul
      (hatom_int u) (hg_int u)
  have hleft (omega : Omega) :
      g (U omega) (V omega) =
        ∑ u : alpha, atom u (U omega) * g u (V omega) := by
    rw [Fintype.sum_eq_single (U omega)]
    · simp [atom]
    · intro u hu
      simp [atom, Ne.symm hu]
  have hright (omega : Omega) :
      h (U omega) = ∑ u : alpha, atom u (U omega) * h u := by
    rw [Fintype.sum_eq_single (U omega)]
    · simp [atom]
    · intro u hu
      simp [atom, Ne.symm hu]
  rw [show (fun omega => g (U omega) (V omega)) =
      fun omega => ∑ u : alpha, atom u (U omega) * g u (V omega) by
        funext omega; exact hleft omega]
  rw [integral_finsetSum Finset.univ (fun u _ => hprod_int u)]
  calc
    (∑ u : alpha, ∫ omega, atom u (U omega) * g u (V omega) ∂P) =
        ∑ u : alpha, (∫ omega, atom u (U omega) ∂P) *
          integral P (fun omega => g u (V omega)) := by
      apply Finset.sum_congr rfl
      intro u _
      rw [hind.integral_fun_comp_mul_comp hU.aemeasurable hV.aemeasurable
        (hatom u).aestronglyMeasurable
        (measurable_of_finite (g u)).aestronglyMeasurable]
    _ <= ∑ u : alpha, (∫ omega, atom u (U omega) ∂P) * h u := by
      apply Finset.sum_le_sum
      intro u _
      exact mul_le_mul_of_nonneg_left (hbound u) <|
        integral_nonneg fun omega => by
          by_cases hu : U omega = u <;> simp [atom, hu]
    _ = integral P (fun omega => h (U omega)) := by
      rw [show (fun omega => h (U omega)) =
          fun omega => ∑ u : alpha, atom u (U omega) * h u by
            funext omega; exact hright omega]
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro u _
        rw [integral_mul_const]
      · intro u _
        exact (hatom_int u).mul_const _

theorem integral_coupled_eq_of_indepFun_finite_states
    {alpha beta : Type*} [Fintype alpha] [MeasurableSpace alpha]
    [MeasurableSingletonClass alpha] [Finite beta] [MeasurableSpace beta]
    [MeasurableSingletonClass beta]
    {P : Measure Omega} [IsFiniteMeasure P]
    {U : Omega -> alpha} {V : Omega -> beta}
    (hind : IndepFun U V P) (hU : Measurable U) (hV : Measurable V)
    (g : alpha -> beta -> Real) (h : alpha -> Real)
    (heq : forall u, integral P (fun omega => g u (V omega)) = h u) :
    integral P (fun omega => g (U omega) (V omega)) =
      integral P (fun omega => h (U omega)) := by
  apply le_antisymm
  · exact integral_coupled_le_of_indepFun_finite_states hind hU hV g h
      fun u => (heq u).le
  · have hneg := integral_coupled_le_of_indepFun_finite_states hind hU hV
        (fun u state => -g u state) (fun u => -h u) (fun u => by
          rw [integral_neg, heq u])
    rw [show (fun omega => -g (U omega) (V omega)) =
        fun omega => -(g (U omega) (V omega)) by rfl,
      integral_neg,
      show (fun omega => -h (U omega)) = fun omega => -(h (U omega)) by rfl,
      integral_neg] at hneg
    linarith

theorem secondMoment_le_mean_sq_mul_uniform {mu K : Real} (hmu : 1 < mu) (hK : 0 <= K)
    {a b : Nat -> Real}
    (ha : forall n, a n = mu ^ n)
    (hb0 : b 0 <= 1)
    (hb : forall n, b (n + 1) <= mu ^ 2 * b n + K * mu * a n) :
    forall n, b n <= mu ^ (2 * n) * (1 + K / (mu - 1)) := by
  have hden : 0 < mu - 1 := sub_pos.mpr hmu
  have hsharp : forall n, b n <=
      mu ^ (2 * n) + K * mu ^ n * (mu ^ n - 1) / (mu - 1) := by
    intro n
    induction n with
    | zero => simpa using hb0
    | succ n ih =>
        calc
          b (n + 1) <= mu ^ 2 * b n + K * mu * a n := hb n
          _ <= mu ^ 2 *
                (mu ^ (2 * n) + K * mu ^ n * (mu ^ n - 1) / (mu - 1)) +
              K * mu * mu ^ n := by
            rw [ha n]
            gcongr
          _ = mu ^ (2 * (n + 1)) +
              K * mu ^ (n + 1) * (mu ^ (n + 1) - 1) / (mu - 1) := by
            rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add, pow_succ]
            field_simp
            ring
  intro n
  calc
    b n <= mu ^ (2 * n) + K * mu ^ n * (mu ^ n - 1) / (mu - 1) := hsharp n
    _ <= mu ^ (2 * n) + K * mu ^ (2 * n) / (mu - 1) := by
      have hmun : 0 <= mu ^ n := pow_nonneg (zero_le_one.trans hmu.le) _
      have hnum : K * mu ^ n * (mu ^ n - 1) <= K * mu ^ (2 * n) := by
        calc
          K * mu ^ n * (mu ^ n - 1) <= K * mu ^ n * mu ^ n := by
            exact mul_le_mul_of_nonneg_left (sub_le_self _ zero_le_one)
              (mul_nonneg hK hmun)
          _ = K * mu ^ (2 * n) := by
            rw [show 2 * n = n + n by omega, pow_add]
            ring
      have hdiv := div_le_div_of_nonneg_right hnum hden.le
      linarith
    _ = mu ^ (2 * n) * (1 + K / (mu - 1)) := by ring

end FractalGeometry.Probability.GridPercolation
