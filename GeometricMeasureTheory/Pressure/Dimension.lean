/-
# Section 7.3: Dimension theory of cookie-cutters

The pressure of the geometric potential `-s log|f'|` is strictly decreasing in `s`, so it has a
unique zero, and that zero is the Hausdorff dimension of the repeller. At it the Hausdorff measure
of the repeller is positive and finite, and is itself a Gibbs measure.

| Notes | Lean declaration | Location |
|---|---|---|
| `P_s = P(-s log|f'|)` | `CookieCutter.pressureExp` | here |
| Lemma 7.9 (`thm:pressure-slope`) | `CookieCutter.pressure_slope` | here |
| Corollary 7.10 (`thm:pressure-zero`) | `CookieCutter.pressure_zero`, `CookieCutter.pressureExp_zero` | here |
| Theorem 7.11 (`thm:cookie-cutter-dimension`) | `CookieCutter.cookie_cutter_dimension` | here |
| The repeller is Ahlfors regular | `CookieCutter.isAhlforsRegularSet_attractor` | here |
| Exercise 7.13 (`ex:gibbs-ball-bound`) | `CookieCutter.measure_closedBall_le_of_measure_cylinder_le` | here |
-/
import GeometricMeasureTheory.Pressure.Gibbs
import GeometricMeasureTheory.CookieCutter.SelfSimilarity

open MeasureTheory Filter Topology Set Metric

open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

namespace CookieCutter

variable {ι : Type*} [Fintype ι] (C : CookieCutter ι)

/-- `P_s = P(-s log|f'|)`, the pressure of the geometric potential. -/
def pressureExp (C : CookieCutter ι) (s : ℝ) : ℝ := C.pressure (C.geometricPotential s)

omit [Fintype ι] in
/-- The geometric potential is Lipschitz, with the constant supplied by the system. -/
theorem lipschitzOnWith_geometricPotential (s : ℝ) (i : ι) :
    LipschitzOnWith (|s|.toNNReal * C.L) (C.geometricPotential s i) C.X := by
  have h : LipschitzOnWith C.L (fun x => Real.log |C.dF i x|) C.X :=
    C.lipschitzOnWith_log_abs_dF i
  rw [lipschitzOnWith_iff_dist_le_mul] at h ⊢
  intro x hx y hy
  have hxy := h x hx y hy
  have hcoe : ((|s|.toNNReal * C.L : ℝ≥0) : ℝ) = |s| * C.L := by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (abs_nonneg s)]
  have hd : dist (C.geometricPotential s i x) (C.geometricPotential s i y)
      = |s| * dist (Real.log |C.dF i x|) (Real.log |C.dF i y|) := by
    simp [geometricPotential, Real.dist_eq, ← mul_sub, abs_mul]
  rw [hcoe, hd, mul_assoc]
  exact mul_le_mul_of_nonneg_left hxy (abs_nonneg s)

omit [Fintype ι] in
/-- The left endpoint of the interval belongs to it. -/
private theorem a_mem_X : C.a ∈ C.X := left_mem_Icc.2 C.lt_ab.le

omit [Fintype ι] in
/-- The logarithm of the derivative of a branch map is squeezed between the logarithms of the
corresponding powers of the bounds. -/
private theorem log_abs_branchDeriv_mem (w : List ι) {x : ℝ} (hx : x ∈ C.X) :
    w.length * Real.log C.cmin ≤ Real.log |C.branchDeriv w x| ∧
      Real.log |C.branchDeriv w x| ≤ w.length * Real.log C.cmax := by
  have hmin : C.cmin ^ w.length ≤ |C.branchDeriv w x| := C.pow_le_abs_branchDeriv w hx
  have hmax : |C.branchDeriv w x| ≤ C.cmax ^ w.length := C.abs_branchDeriv_le_pow w hx
  have hpos : (0 : ℝ) < C.cmin ^ w.length := pow_pos C.cmin_pos _
  refine ⟨?_, ?_⟩
  · rw [← Real.log_pow]
    exact Real.log_le_log hpos hmin
  · rw [← Real.log_pow]
    exact Real.log_le_log (hpos.trans_le hmin) hmax

/-! ## Lemma 7.9 (`thm:pressure-slope`) -/

/-- Each term of the partition sum at exponent `s + δ` is the corresponding term at `s` times the
`δ`-th power of the derivative of the branch map, so the two partition sums differ by a factor
between `c_min^{δ k}` and `c_max^{δ k}`. -/
private theorem partitionSum_geometricPotential_le [Nonempty ι] (s : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (k : ℕ) :
    C.partitionSum (C.geometricPotential (s + δ)) (fun _ => C.a) k ≤
        Real.exp (δ * k * Real.log C.cmax) *
          C.partitionSum (C.geometricPotential s) (fun _ => C.a) k ∧
      Real.exp (δ * k * Real.log C.cmin) *
          C.partitionSum (C.geometricPotential s) (fun _ => C.a) k ≤
        C.partitionSum (C.geometricPotential (s + δ)) (fun _ => C.a) k := by
  have key : ∀ f : Fin k → ι,
      Real.exp (C.birkhoffSum (C.geometricPotential (s + δ)) (List.ofFn f) C.a) =
        Real.exp (δ * Real.log |C.branchDeriv (List.ofFn f) C.a|) *
          Real.exp (C.birkhoffSum (C.geometricPotential s) (List.ofFn f) C.a) := by
    intro f
    rw [← C.log_abs_branchDeriv _ _ C.a_mem_X, ← C.log_abs_branchDeriv _ _ C.a_mem_X,
      ← Real.exp_add]
    ring_nf
  have hlen : ∀ f : Fin k → ι, (List.ofFn f).length = k := fun _ => List.length_ofFn
  constructor
  · rw [partitionSum, partitionSum, Finset.mul_sum]
    refine Finset.sum_le_sum fun f _ => ?_
    rw [key f]
    have h := (C.log_abs_branchDeriv_mem (List.ofFn f) C.a_mem_X).2
    rw [hlen f] at h
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le
  · rw [partitionSum, partitionSum, Finset.mul_sum]
    refine Finset.sum_le_sum fun f _ => ?_
    rw [key f]
    have h := (C.log_abs_branchDeriv_mem (List.ofFn f) C.a_mem_X).1
    rw [hlen f] at h
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le

/-- Lemma 7.9 (`thm:pressure-slope`): increasing the exponent by `δ` decreases the pressure by
between `δ log(1/c_max)` and `δ log(1/c_min)`. -/
theorem pressure_slope [Nonempty ι] (s : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    δ * Real.log C.cmin ≤ C.pressureExp (s + δ) - C.pressureExp s ∧
      C.pressureExp (s + δ) - C.pressureExp s ≤ δ * Real.log C.cmax := by
  have htend : ∀ t : ℝ, Tendsto
      (fun k : ℕ => Real.log (C.partitionSum (C.geometricPotential t) (fun _ => C.a) k) / k)
      atTop (𝓝 (C.pressureExp t)) := fun t =>
    (C.pressure_gibbs fun i => C.lipschitzOnWith_geometricPotential t i).1 _ fun _ => C.a_mem_X
  have hpos : ∀ (t : ℝ) (k : ℕ), 0 < C.partitionSum (C.geometricPotential t) (fun _ => C.a) k :=
    fun t k => C.partitionSum_pos _ _ k
  constructor
  · have hle : (fun k : ℕ => δ * Real.log C.cmin +
        Real.log (C.partitionSum (C.geometricPotential s) (fun _ => C.a) k) / k) ≤ᶠ[atTop]
        fun k : ℕ =>
          Real.log (C.partitionSum (C.geometricPotential (s + δ)) (fun _ => C.a) k) / k := by
      filter_upwards [eventually_gt_atTop 0] with k hk
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      have h := (C.partitionSum_geometricPotential_le s hδ k).2
      have hlog := Real.log_le_log (mul_pos (Real.exp_pos _) (hpos s k)) h
      rw [Real.log_mul (Real.exp_ne_zero _) (hpos s k).ne', Real.log_exp] at hlog
      rw [le_div_iff₀ hk', add_mul, div_mul_cancel₀ _ hk'.ne']
      nlinarith [hlog]
    have := le_of_tendsto_of_tendsto (tendsto_const_nhds.add (htend s)) (htend (s + δ)) hle
    linarith
  · have hle : (fun k : ℕ =>
        Real.log (C.partitionSum (C.geometricPotential (s + δ)) (fun _ => C.a) k) / k) ≤ᶠ[atTop]
        fun k : ℕ => δ * Real.log C.cmax +
          Real.log (C.partitionSum (C.geometricPotential s) (fun _ => C.a) k) / k := by
      filter_upwards [eventually_gt_atTop 0] with k hk
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      have h := (C.partitionSum_geometricPotential_le s hδ k).1
      have hlog := Real.log_le_log (hpos (s + δ) k) h
      rw [Real.log_mul (Real.exp_ne_zero _) (hpos s k).ne', Real.log_exp] at hlog
      rw [div_le_iff₀ hk', add_mul, div_mul_cancel₀ _ hk'.ne']
      nlinarith [hlog]
    have := le_of_tendsto_of_tendsto (htend (s + δ)) (tendsto_const_nhds.add (htend s)) hle
    linarith

/-! ## Corollary 7.10 (`thm:pressure-zero`) -/

/-- The pressure at exponent zero counts the branches. -/
theorem pressureExp_zero [Nonempty ι] : C.pressureExp 0 = Real.log (Nat.card ι) := by
  have hps : ∀ k : ℕ, C.partitionSum (C.geometricPotential 0) (fun _ => C.a) k
      = (Fintype.card ι : ℝ) ^ k := by
    intro k
    have hb : ∀ w : List ι, C.birkhoffSum (C.geometricPotential 0) w C.a = 0 := by
      intro w
      rw [← C.log_abs_branchDeriv 0 w C.a_mem_X, zero_mul]
    simp [partitionSum, hb, Finset.card_univ]
  have hev : (fun k : ℕ =>
      Real.log (C.partitionSum (C.geometricPotential 0) (fun _ => C.a) k) / k)
        =ᶠ[atTop] fun _ => Real.log (Nat.card ι) := by
    filter_upwards [eventually_gt_atTop 0] with k hk
    rw [hps k, Real.log_pow, Nat.card_eq_fintype_card]
    field_simp
  exact Tendsto.limsup_eq (Tendsto.congr' hev.symm tendsto_const_nhds)

/-- The increment bound of Lemma 7.9, read for an arbitrary pair of exponents. -/
private theorem pressureExp_increment [Nonempty ι] {s t : ℝ} (hst : s ≤ t) :
    (t - s) * Real.log C.cmin ≤ C.pressureExp t - C.pressureExp s ∧
      C.pressureExp t - C.pressureExp s ≤ (t - s) * Real.log C.cmax := by
  rcases eq_or_lt_of_le hst with rfl | h
  · simp
  · have hs := C.pressure_slope s (sub_pos.2 h)
    have hts : s + (t - s) = t := by ring
    rwa [hts] at hs

/-- Corollary 7.10 (`thm:pressure-zero`): `P_s` is continuous and strictly decreasing, runs from
`∞` to `-∞`, and has a unique zero. -/
theorem pressure_zero [Nonempty ι] :
    StrictAnti C.pressureExp ∧ Continuous C.pressureExp ∧
      Tendsto C.pressureExp atTop atBot ∧ Tendsto C.pressureExp atBot atTop ∧
        ∃! s : ℝ, C.pressureExp s = 0 := by
  have hlogmax : Real.log C.cmax < 0 := Real.log_neg C.cmax_pos C.cmax_lt_one
  have hlogmin : Real.log C.cmin < 0 := Real.log_neg C.cmin_pos C.cmin_lt_one
  have hK0 : (0 : ℝ) ≤ -Real.log C.cmin := by linarith
  have hanti : StrictAnti C.pressureExp := by
    intro s t hst
    have h := (C.pressureExp_increment hst.le).2
    have hneg : (t - s) * Real.log C.cmax < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.2 hst) hlogmax
    linarith
  have habs : ∀ x y : ℝ, x ≤ y →
      |C.pressureExp x - C.pressureExp y| ≤ (-Real.log C.cmin) * |x - y| := by
    intro x y hxy
    obtain ⟨h1, h2⟩ := C.pressureExp_increment hxy
    have hxy' : (0 : ℝ) ≤ y - x := sub_nonneg.2 hxy
    have hle0 : C.pressureExp y - C.pressureExp x ≤ 0 := by nlinarith
    rw [abs_sub_comm, abs_of_nonpos hle0, abs_of_nonpos (sub_nonpos.2 hxy)]
    nlinarith
  have hcont : Continuous C.pressureExp := by
    refine LipschitzWith.continuous (K := (-Real.log C.cmin).toNNReal)
      (LipschitzWith.of_dist_le_mul fun x y => ?_)
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK0]
    rcases le_total x y with h | h
    · exact habs x y h
    · rw [abs_sub_comm, abs_sub_comm x y]
      exact habs y x h
  have hlin : Tendsto (fun t : ℝ => C.pressureExp 0 + t * Real.log C.cmax) atTop atBot :=
    tendsto_atBot_add_const_left _ _ ((tendsto_mul_const_atBot_of_neg hlogmax).2 tendsto_id)
  have hlin' : Tendsto (fun t : ℝ => C.pressureExp 0 + t * Real.log C.cmax) atBot atTop :=
    tendsto_atTop_add_const_left _ _ ((tendsto_mul_const_atTop_of_neg hlogmax).2 tendsto_id)
  have hto : Tendsto C.pressureExp atTop atBot := by
    refine tendsto_atBot_mono' atTop ?_ hlin
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have h := (C.pressureExp_increment ht).2
    rw [sub_zero] at h
    linarith
  have hfrom : Tendsto C.pressureExp atBot atTop := by
    refine tendsto_atTop_mono' atBot ?_ hlin'
    filter_upwards [eventually_le_atBot (0 : ℝ)] with t ht
    have h := (C.pressureExp_increment ht).2
    rw [zero_sub] at h
    nlinarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, C.pressureExp x < 0 :=
    (hto.eventually (eventually_lt_atBot (0 : ℝ))).exists
  obtain ⟨y, hy⟩ : ∃ y : ℝ, 0 < C.pressureExp y :=
    (hfrom.eventually (eventually_gt_atTop (0 : ℝ))).exists
  have hyx : y < x := (StrictAnti.lt_iff_gt hanti).1 (hx.trans hy)
  obtain ⟨z, -, hz⟩ :=
    intermediate_value_Icc' hyx.le hcont.continuousOn (⟨hx.le, hy.le⟩ : (0 : ℝ) ∈ Icc _ _)
  exact ⟨hanti, hcont, hto, hfrom, z, hz, fun w hw => hanti.injective (hw.trans hz.symm)⟩

/-- With at least two branches the zero of the pressure is positive. -/
theorem pos_of_pressureExp_eq_zero [Nontrivial ι] {s : ℝ} (hs : C.pressureExp s = 0) : 0 < s := by
  have hcard : (1 : ℝ) < (Nat.card ι : ℝ) := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.one_lt_card
  have h0 : 0 < C.pressureExp 0 := by
    rw [C.pressureExp_zero]
    exact Real.log_pos hcard
  exact (StrictAnti.lt_iff_gt C.pressure_zero.1).1 (by rw [hs]; exact h0)

/-! ## Theorem 7.11 (`thm:cookie-cutter-dimension`) -/

/-- Exercise 7.13 (`ex:gibbs-ball-bound`): a measure on the repeller whose cylinder masses obey the
power bound obeys the same bound on balls. -/
theorem measure_closedBall_le_of_measure_cylinder_le [Nonempty ι] {μ : Measure ℝ} {s : ℝ}
    (hs : 0 < s) {c : ℝ} (hc : 0 < c) (hμ : μ C.attractorᶜ = 0)
    (hcyl : ∀ w : List ι, μ (C.cylinder w) ≤ ENNReal.ofReal (c * diam (C.cylinder w) ^ s)) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ x ∈ C.attractor, ∀ r : ℝ, 0 < r → r ≤ diam C.X →
      μ (closedBall x r) ≤ ENNReal.ofReal (c' * r ^ s) := by
  obtain ⟨d, hd, hsub⟩ := C.exists_closedBall_subset_cylinder
  have hX : 0 < diam C.X := C.diam_X_pos
  have hρ : 0 < d * (C.cmin * diam C.X) / 2 :=
    div_pos (mul_pos hd (mul_pos C.cmin_pos hX)) two_pos
  have h2d : (0 : ℝ) < 2 / d := div_pos two_pos hd
  have hρs : (0 : ℝ) < (d * (C.cmin * diam C.X) / 2) ^ s := Real.rpow_pos_of_pos hρ s
  have hc₁ : 0 < c * (2 / d) ^ s := mul_pos hc (Real.rpow_pos_of_pos h2d s)
  have hc₂ : 0 < c * diam C.X ^ s / (d * (C.cmin * diam C.X) / 2) ^ s :=
    div_pos (mul_pos hc (Real.rpow_pos_of_pos hX s)) hρs
  refine ⟨max (c * (2 / d) ^ s) (c * diam C.X ^ s / (d * (C.cmin * diam C.X) / 2) ^ s),
    lt_max_of_lt_left hc₁, fun x hx r hr hrX => ?_⟩
  have hrs : (0 : ℝ) ≤ r ^ s := Real.rpow_nonneg hr.le s
  rcases le_or_gt r (d * (C.cmin * diam C.X) / 2) with hcase | hcase
  · obtain ⟨w, -, hw, hwd⟩ := hsub x hx (2 * r / d) (div_pos (by linarith) hd)
      (by rw [div_le_iff₀ hd]; nlinarith)
    have hdt : d * (2 * r / d) = 2 * r := by field_simp
    rw [hdt] at hw
    have hpow : (2 * r / d) ^ s = (2 / d) ^ s * r ^ s := by
      rw [show 2 * r / d = 2 / d * r by ring, Real.mul_rpow h2d.le hr.le]
    calc μ (closedBall x r) = μ (closedBall x r ∩ C.attractor) := (measure_inter_conull hμ).symm
      _ ≤ μ (C.cylinder w) :=
          measure_mono fun y hy => hw ⟨closedBall_subset_ball (by linarith) hy.1, hy.2⟩
      _ ≤ ENNReal.ofReal (c * diam (C.cylinder w) ^ s) := hcyl w
      _ ≤ ENNReal.ofReal (max (c * (2 / d) ^ s)
            (c * diam C.X ^ s / (d * (C.cmin * diam C.X) / 2) ^ s) * r ^ s) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hmono : diam (C.cylinder w) ^ s ≤ (2 * r / d) ^ s :=
            Real.rpow_le_rpow diam_nonneg hwd hs.le
          calc c * diam (C.cylinder w) ^ s ≤ c * ((2 / d) ^ s * r ^ s) := by
                rw [← hpow]; exact mul_le_mul_of_nonneg_left hmono hc.le
            _ = c * (2 / d) ^ s * r ^ s := by ring
            _ ≤ max (c * (2 / d) ^ s)
                  (c * diam C.X ^ s / (d * (C.cmin * diam C.X) / 2) ^ s) * r ^ s := by
                gcongr
                exact le_max_left _ _
  · have hle : μ (closedBall x r) ≤ ENNReal.ofReal (c * diam C.X ^ s) := by
      calc μ (closedBall x r) = μ (closedBall x r ∩ C.attractor) := (measure_inter_conull hμ).symm
        _ ≤ μ (C.cylinder ([] : List ι)) := by
            refine measure_mono fun y hy => ?_
            rw [C.cylinder_nil]
            exact C.attractor_subset_X hy.2
        _ ≤ ENNReal.ofReal (c * diam (C.cylinder ([] : List ι)) ^ s) := hcyl []
        _ = ENNReal.ofReal (c * diam C.X ^ s) := by rw [C.cylinder_nil]
    refine hle.trans (ENNReal.ofReal_le_ofReal ?_)
    have hmono : (d * (C.cmin * diam C.X) / 2) ^ s ≤ r ^ s :=
      Real.rpow_le_rpow hρ.le hcase.le hs.le
    calc c * diam C.X ^ s
        = c * diam C.X ^ s / (d * (C.cmin * diam C.X) / 2) ^ s *
            (d * (C.cmin * diam C.X) / 2) ^ s := by
          rw [div_mul_cancel₀ _ hρs.ne']
      _ ≤ max (c * (2 / d) ^ s) (c * diam C.X ^ s / (d * (C.cmin * diam C.X) / 2) ^ s) *
            r ^ s := by
          gcongr
          exact le_max_right _ _

/-- The repeller meets two disjoint cylinders, so it has at least two points. -/
private theorem nontrivial_attractor [Nontrivial ι] : C.attractor.Nontrivial := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  obtain ⟨y, hy, hy'⟩ := C.cylinder_inter_attractor_nonempty [i]
  obtain ⟨z, hz, hz'⟩ := C.cylinder_inter_attractor_nonempty [j]
  refine ⟨y, hy', z, hz', fun h => ?_⟩
  have hyj : y ∈ C.cylinder [j] := by rw [h]; exact hz
  exact Set.disjoint_left.1
    (C.disjoint_cylinder (v := [i]) (w := [j]) rfl fun h' => hij (by simpa using h')) hy hyj

/-- At the zero of the pressure the Gibbs measure of the geometric potential gives every cylinder
mass comparable to the corresponding power of its diameter, and is Ahlfors `s`-regular on the
repeller. -/
private theorem exists_isAhlforsRegular_gibbs [Nontrivial ι] {s : ℝ} (hs : C.pressureExp s = 0) :
    ∃ (μ : Measure ℝ) (K : ℝ≥0) (c : ℝ), 0 < c ∧ IsAhlforsRegular μ s C.attractor K ∧
      ∀ w : List ι, ENNReal.ofReal (c⁻¹ * diam (C.cylinder w) ^ s) ≤ μ (C.cylinder w) ∧
        μ (C.cylinder w) ≤ ENNReal.ofReal (c * diam (C.cylinder w) ^ s) := by
  have hs0 : 0 < s := C.pos_of_pressureExp_eq_zero hs
  have hp0 : C.pressure (C.geometricPotential s) = 0 := hs
  obtain ⟨-, μ, hprob, hcompl, a₀, ha₀, hgibbs⟩ :=
    C.pressure_gibbs fun i => C.lipschitzOnWith_geometricPotential s i
  obtain ⟨⟨b₀, hb₀, hbd⟩, -⟩ := C.bounded_distortion
  have hb₀0 : (0 : ℝ) < b₀ := zero_lt_one.trans_le hb₀
  have hc : 0 < a₀ * b₀ ^ s := mul_pos ha₀ (Real.rpow_pos_of_pos hb₀0 s)
  -- the cylinder masses
  have hcyl : ∀ w : List ι,
      ENNReal.ofReal ((a₀ * b₀ ^ s)⁻¹ * diam (C.cylinder w) ^ s) ≤ μ (C.cylinder w) ∧
        μ (C.cylinder w) ≤ ENNReal.ofReal (a₀ * b₀ ^ s * diam (C.cylinder w) ^ s) := by
    intro w
    have hD : 0 < diam (C.cylinder w) := C.diam_cylinder_pos w
    have hB : 0 < |C.branchDeriv w C.a| := abs_pos.2 (C.branchDeriv_ne_zero w C.a_mem_X)
    obtain ⟨h1, h2⟩ := hgibbs w C.a C.a_mem_X
    have hexp : Real.exp (C.birkhoffSum (C.geometricPotential s) w C.a
        - w.length * C.pressure (C.geometricPotential s)) = |C.branchDeriv w C.a| ^ s := by
      rw [hp0, mul_zero, sub_zero, ← C.log_abs_branchDeriv s w C.a_mem_X,
        Real.rpow_def_of_pos hB, mul_comm]
    rw [hexp] at h1 h2
    obtain ⟨hlo, hhi⟩ := hbd w C.a C.a_mem_X
    rw [le_div_iff₀ hB] at hlo
    rw [div_le_iff₀ hB] at hhi
    have hBD : |C.branchDeriv w C.a| ≤ b₀ * diam (C.cylinder w) := by
      have h := mul_le_mul_of_nonneg_left hlo hb₀0.le
      rwa [← mul_assoc, mul_inv_cancel₀ hb₀0.ne', one_mul] at h
    have hDB : b₀⁻¹ * diam (C.cylinder w) ≤ |C.branchDeriv w C.a| := by
      have h := mul_le_mul_of_nonneg_left hhi (inv_nonneg.2 hb₀0.le)
      rwa [← mul_assoc, inv_mul_cancel₀ hb₀0.ne', one_mul] at h
    constructor
    · refine le_trans (ENNReal.ofReal_le_ofReal ?_) h1
      have hmono : (b₀⁻¹ * diam (C.cylinder w)) ^ s ≤ |C.branchDeriv w C.a| ^ s :=
        Real.rpow_le_rpow (by positivity) hDB hs0.le
      rw [Real.mul_rpow (inv_nonneg.2 hb₀0.le) hD.le, Real.inv_rpow hb₀0.le] at hmono
      calc (a₀ * b₀ ^ s)⁻¹ * diam (C.cylinder w) ^ s
          = a₀⁻¹ * ((b₀ ^ s)⁻¹ * diam (C.cylinder w) ^ s) := by rw [mul_inv]; ring
        _ ≤ a₀⁻¹ * |C.branchDeriv w C.a| ^ s :=
            mul_le_mul_of_nonneg_left hmono (inv_nonneg.2 ha₀.le)
    · refine le_trans h2 (ENNReal.ofReal_le_ofReal ?_)
      have hmono : |C.branchDeriv w C.a| ^ s ≤ (b₀ * diam (C.cylinder w)) ^ s :=
        Real.rpow_le_rpow hB.le hBD hs0.le
      rw [Real.mul_rpow hb₀0.le hD.le] at hmono
      calc a₀ * |C.branchDeriv w C.a| ^ s
          ≤ a₀ * (b₀ ^ s * diam (C.cylinder w) ^ s) := mul_le_mul_of_nonneg_left hmono ha₀.le
        _ = a₀ * b₀ ^ s * diam (C.cylinder w) ^ s := by ring
  -- the two ball bounds
  obtain ⟨c', hc', hball⟩ :=
    C.measure_closedBall_le_of_measure_cylinder_le hs0 hc hcompl fun w => (hcyl w).2
  obtain ⟨e, he, hcylball⟩ := C.exists_cylinder_subset_closedBall
  have he2 : (0 : ℝ) < e / 2 := div_pos he two_pos
  have h2e : (0 : ℝ) < 2 / e := div_pos two_pos he
  set K : ℝ≥0 := 1 + c'.toNNReal + (a₀ * b₀ ^ s * (2 / e) ^ s).toNNReal with hKdef
  have hK1 : (1 : ℝ≥0) ≤ K := (self_le_add_right 1 _).trans (self_le_add_right _ _)
  have hKc' : c' ≤ (K : ℝ) := by
    have h := Real.le_coe_toNNReal c'
    have h0 : (0 : ℝ) ≤ ((a₀ * b₀ ^ s * (2 / e) ^ s).toNNReal : ℝ) := NNReal.coe_nonneg _
    rw [hKdef]
    push_cast
    linarith
  have hKlow : a₀ * b₀ ^ s * (2 / e) ^ s ≤ (K : ℝ) := by
    have h := Real.le_coe_toNNReal (a₀ * b₀ ^ s * (2 / e) ^ s)
    have h0 : (0 : ℝ) ≤ (c'.toNNReal : ℝ) := NNReal.coe_nonneg _
    rw [hKdef]
    push_cast
    linarith
  have hrX : ∀ r : ℝ, ENNReal.ofReal r ≤ ediam C.attractor → r ≤ diam C.X := by
    intro r hrE
    have hbdd : Bornology.IsBounded C.attractor := C.isCompact_attractor.isBounded
    have heq : ediam C.attractor = ENNReal.ofReal (diam C.attractor) :=
      (ENNReal.ofReal_toReal hbdd.ediam_ne_top).symm
    rw [heq, ENNReal.ofReal_le_ofReal_iff diam_nonneg] at hrE
    exact hrE.trans (diam_mono C.attractor_subset_X C.isCompact_X.isBounded)
  have hup : ∀ x ∈ C.attractor, ∀ r : ℝ, 0 < r → ENNReal.ofReal r ≤ ediam C.attractor →
      μ (ball x r) ≤ K * ENNReal.ofReal r ^ s := by
    intro x hx r hr hrE
    calc μ (ball x r) ≤ μ (closedBall x r) := measure_mono ball_subset_closedBall
      _ ≤ ENNReal.ofReal (c' * r ^ s) := hball x hx r hr (hrX r hrE)
      _ ≤ ENNReal.ofReal ((K : ℝ) * r ^ s) := by
          refine ENNReal.ofReal_le_ofReal ?_
          exact mul_le_mul_of_nonneg_right hKc' (Real.rpow_nonneg hr.le s)
      _ = K * ENNReal.ofReal r ^ s := by
          rw [ENNReal.ofReal_mul (NNReal.coe_nonneg K), ENNReal.ofReal_coe_nnreal,
            ENNReal.ofReal_rpow_of_pos hr]
  have hlow : ∀ x ∈ C.attractor, ∀ r : ℝ, 0 < r → ENNReal.ofReal r ≤ ediam C.attractor →
      ENNReal.ofReal r ^ s ≤ K * μ (ball x r) := by
    intro x hx r hr hrE
    obtain ⟨w, -, hwsub, hwd⟩ :=
      hcylball x hx (r / 2) (by linarith) (by linarith [hrX r hrE])
    have hsub : C.cylinder w ⊆ ball x r := hwsub.trans (closedBall_subset_ball (by linarith))
    have hee : (2 / e) ^ s * (e / 2) ^ s = 1 := by
      rw [← Real.mul_rpow h2e.le he2.le, show 2 / e * (e / 2) = 1 by field_simp, Real.one_rpow]
    have hkey : a₀ * b₀ ^ s * (2 / e) ^ s * ((a₀ * b₀ ^ s)⁻¹ * (e * (r / 2)) ^ s) = r ^ s := by
      rw [show e * (r / 2) = e / 2 * r by ring, Real.mul_rpow he2.le hr.le]
      calc a₀ * b₀ ^ s * (2 / e) ^ s * ((a₀ * b₀ ^ s)⁻¹ * ((e / 2) ^ s * r ^ s))
          = a₀ * b₀ ^ s * (a₀ * b₀ ^ s)⁻¹ * ((2 / e) ^ s * (e / 2) ^ s) * r ^ s := by ring
        _ = r ^ s := by rw [mul_inv_cancel₀ hc.ne', hee, one_mul, one_mul]
    have hcylw : ENNReal.ofReal ((a₀ * b₀ ^ s)⁻¹ * (e * (r / 2)) ^ s) ≤ μ (C.cylinder w) := by
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hcyl w).1
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hc.le)
      exact Real.rpow_le_rpow (by positivity) hwd hs0.le
    calc ENNReal.ofReal r ^ s = ENNReal.ofReal (r ^ s) := ENNReal.ofReal_rpow_of_pos hr
      _ ≤ ENNReal.ofReal ((K : ℝ) * ((a₀ * b₀ ^ s)⁻¹ * (e * (r / 2)) ^ s)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← hkey]
          refine mul_le_mul_of_nonneg_right hKlow ?_
          exact mul_nonneg (inv_nonneg.2 hc.le) (Real.rpow_nonneg (by positivity) s)
      _ = K * ENNReal.ofReal ((a₀ * b₀ ^ s)⁻¹ * (e * (r / 2)) ^ s) := by
          rw [ENNReal.ofReal_mul (NNReal.coe_nonneg K), ENNReal.ofReal_coe_nnreal]
      _ ≤ K * μ (C.cylinder w) := by gcongr
      _ ≤ K * μ (ball x r) := by gcongr
  -- the support of the Gibbs measure is the repeller
  have hclosed : IsClosed C.attractor := C.isCompact_attractor.isClosed
  have hnontriv : C.attractor.Nontrivial := C.nontrivial_attractor
  have hsupp : μ.support = C.attractor := by
    refine subset_antisymm (Measure.support_subset_of_isClosed hclosed (mem_ae_iff.2 hcompl))
      fun x hx => ?_
    rw [Measure.mem_support_iff_forall]
    intro U hU
    obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hU
    obtain ⟨r, hr, hrδ⟩ := ((eventually_pos_ofReal_le_ediam hnontriv).and
      (nhdsWithin_le_nhds (eventually_lt_nhds hδ))).exists
    refine (pos_iff_ne_zero.2 fun h0 => ?_).trans_le
      (measure_mono ((ball_subset_ball hrδ.le).trans hδU))
    have h := hlow x hx r hr.1 hr.2
    rw [h0, mul_zero] at h
    exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hr.1) ENNReal.ofReal_ne_top).not_ge h
  exact ⟨μ, K, a₀ * b₀ ^ s, hc,
    ⟨hclosed, hnontriv, hs0, inferInstance, hsupp, hK1, hlow, hup⟩, hcyl⟩

/-- Theorem 7.11 (`thm:cookie-cutter-dimension`): the zero of the pressure is the Hausdorff
dimension of the repeller, the Hausdorff measure there is positive and finite, and its restriction
to the repeller is a Gibbs measure. -/
theorem cookie_cutter_dimension [Nontrivial ι] {s : ℝ} (hs : C.pressureExp s = 0) :
    dimH C.attractor = ENNReal.ofReal s ∧ 0 < μH[s] C.attractor ∧ μH[s] C.attractor < ∞ ∧
      ∃ c : ℝ, 0 < c ∧ ∀ w : List ι,
        ENNReal.ofReal (c⁻¹ * diam (C.cylinder w) ^ s) ≤ μH[s] (C.attractor ∩ C.cylinder w) ∧
          μH[s] (C.attractor ∩ C.cylinder w) ≤
            ENNReal.ofReal (c * diam (C.cylinder w) ^ s) := by
  obtain ⟨μ, K, c, hc, hreg, hcylb⟩ := C.exists_isAhlforsRegular_gibbs hs
  obtain ⟨hcomp, hpos, hfin, hdim, -⟩ := ahlfors_hausdorff hreg C.isCompact_attractor
  have hK0 : (0 : ℝ) < (K : ℝ) := zero_lt_one.trans_le (by exact_mod_cast hreg.one_le)
  have h2s : (2 : ℝ≥0∞) ^ s = ENNReal.ofReal ((2 : ℝ) ^ s) := by
    rw [← ENNReal.ofReal_ofNat 2, ENNReal.ofReal_rpow_of_pos two_pos]
  refine ⟨hdim, hpos, hfin, max ((K : ℝ) * c) ((2 : ℝ) ^ s * (K : ℝ) * c),
    lt_max_of_lt_left (mul_pos hK0 hc), fun w => ?_⟩
  have hprod : (0 : ℝ) < (K : ℝ) * c := mul_pos hK0 hc
  have hmeas : μ (C.attractor ∩ C.cylinder w) = μ (C.cylinder w) := by
    rw [inter_comm]
    exact measure_inter_conull hreg.measure_compl
  obtain ⟨hlow, hup⟩ := hcomp (C.attractor ∩ C.cylinder w) inter_subset_left
  rw [hmeas] at hlow hup
  constructor
  · calc ENNReal.ofReal ((max ((K : ℝ) * c) ((2 : ℝ) ^ s * (K : ℝ) * c))⁻¹ *
          diam (C.cylinder w) ^ s)
        ≤ ENNReal.ofReal ((K : ℝ)⁻¹ * (c⁻¹ * diam (C.cylinder w) ^ s)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [show (K : ℝ)⁻¹ * (c⁻¹ * diam (C.cylinder w) ^ s)
              = ((K : ℝ) * c)⁻¹ * diam (C.cylinder w) ^ s by rw [mul_inv]; ring]
          gcongr
          exact le_max_left _ _
      _ = (K : ℝ≥0∞)⁻¹ * ENNReal.ofReal (c⁻¹ * diam (C.cylinder w) ^ s) := by
          rw [ENNReal.ofReal_mul (inv_nonneg.2 hK0.le), ENNReal.ofReal_inv_of_pos hK0,
            ENNReal.ofReal_coe_nnreal]
      _ ≤ (K : ℝ≥0∞)⁻¹ * μ (C.cylinder w) := by gcongr; exact (hcylb w).1
      _ = μ (C.cylinder w) / K := by rw [div_eq_mul_inv, mul_comm]
      _ ≤ μH[s] (C.attractor ∩ C.cylinder w) := hlow
  · calc μH[s] (C.attractor ∩ C.cylinder w) ≤ 2 ^ s * K * μ (C.cylinder w) := hup
      _ ≤ 2 ^ s * K * ENNReal.ofReal (c * diam (C.cylinder w) ^ s) := by
          gcongr
          exact (hcylb w).2
      _ = ENNReal.ofReal ((2 : ℝ) ^ s * (K : ℝ) * (c * diam (C.cylinder w) ^ s)) := by
          rw [h2s, ← ENNReal.ofReal_coe_nnreal,
            ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) s),
            ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ s * (K : ℝ))]
      _ ≤ ENNReal.ofReal (max ((K : ℝ) * c) ((2 : ℝ) ^ s * (K : ℝ) * c) *
            diam (C.cylinder w) ^ s) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [show (2 : ℝ) ^ s * (K : ℝ) * (c * diam (C.cylinder w) ^ s)
              = ((2 : ℝ) ^ s * (K : ℝ) * c) * diam (C.cylinder w) ^ s by ring]
          gcongr
          exact le_max_right _ _

/-- The repeller of a cookie cutter is Ahlfors regular at the zero of its pressure. -/
theorem isAhlforsRegularSet_attractor [Nontrivial ι] {s : ℝ} (hs : C.pressureExp s = 0) :
    IsAhlforsRegularSet s C.attractor := by
  obtain ⟨μ, K, -, -, hreg, -⟩ := C.exists_isAhlforsRegular_gibbs hs
  exact ⟨μ, K, hreg⟩

end CookieCutter

end GeometricMeasureTheory
