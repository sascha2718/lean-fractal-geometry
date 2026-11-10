module

/-
The two-lift comparison in the proof of `thm:entropy_eq_gibbs` in `sec:entropy_eq_state`: a
probability measure `ν` carried by the sub-shift `Σ_Z` and its image `q_*ν` under the factor map
`q = unCode : Σ_Z → Σ` that forgets the axis have the same Kolmogorov–Sinai entropy.

For a base block `w = i_0 ⋯ i_{n-1}` with `n ≥ 1`, the initial axis `c ∈ ZMod 2` determines the
lifted block `liftBlock o c w` by the transition rule of `Σ_Z`. The cylinders of all other
lifted blocks are `ν`-null, so every atom of `q^{-1}(𝒫_0^{n-1})` is, up to a null set, the
disjoint union of the two atoms `[liftBlock o 0 w]` and `[liftBlock o 1 w]` of
`\overline{𝒫}_0^{n-1}`.

* `negMulLog_add_le`, `negMulLog_add_negMulLog_le`: the scalar inequalities
  `η(a + b) ≤ η(a) + η(b) ≤ η(a + b) + (a + b) log 2` for `η(t) = -t log t` and `a, b ≥ 0`.
* `liftBlock`, `liftBlock_injective`, `mem_cylinder_liftBlock`: the lift of a base block along
  an initial axis, and the fact that a point of `Σ_Z` over `[w]` lies in the cylinder of a lift
  of `w`.
* `measurable_unCode`, `measurableSet_subshift`, `unCode_shift`,
  `measurePreserving_shift_map_unCode`: the factor map is measurable and commutes with the
  shift, `Σ_Z` is measurable, and `q_*ν` is invariant when `ν` is.
* `measure_cylinder_eq_zero`, `measureReal_preimage_unCode_cylinder`: inadmissible blocks are
  null, and `ν(q^{-1}[w]) = ν[liftBlock o 0 w] + ν[liftBlock o 1 w]`.
* `blockEntropy_map_unCode`:
  `0 ≤ H_ν(\overline{𝒫}_0^{n-1}) - H_{q_*ν}(𝒫_0^{n-1}) ≤ log 2` for every `n`.
* `entropy_map_unCode`: `thm:entropy_eq_gibbs` in measure-theoretic form, `h(q_*ν) = h(ν)`.
-/
public import BoxLike.Coding
public import BoxLike.Entropy
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

namespace BoxLike

open Filter Topology MeasureTheory

section Scalar

/-- The function `negMulLog` is sub-additive on the non-negative reals. -/
theorem negMulLog_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.negMulLog (a + b) ≤ Real.negMulLog a + Real.negMulLog b := by
  rcases ha.eq_or_lt with rfl | ha'
  · simp
  rcases hb.eq_or_lt with rfl | hb'
  · simp
  have h1 := mul_le_mul_of_nonneg_left (Real.log_le_log ha' (by linarith : a ≤ a + b)) ha
  have h2 := mul_le_mul_of_nonneg_left (Real.log_le_log hb' (by linarith : b ≤ a + b)) hb
  simp only [Real.negMulLog]
  linarith

/-- Splitting a mass `a + b` into two parts raises the entropy by at most `(a + b) log 2`. -/
theorem negMulLog_add_negMulLog_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.negMulLog a + Real.negMulLog b ≤ Real.negMulLog (a + b) + (a + b) * Real.log 2 := by
  rcases (add_nonneg ha hb).eq_or_lt with h | h
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0]
  · have hc := Real.concaveOn_negMulLog.2 (Set.mem_Ici.2 ha) (Set.mem_Ici.2 hb)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have e : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b = (a + b) / 2 := by
      simp only [smul_eq_mul]; ring
    rw [e] at hc
    simp only [smul_eq_mul, Real.negMulLog, Real.log_div h.ne' two_ne_zero] at hc ⊢
    linarith

/-- A sum over the two axes `0, 1 ∈ ZMod 2`. -/
theorem sum_zmod_two {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) : ∑ c, f c = f 0 + f 1 :=
  Fin.sum_univ_two f

end Scalar

section Lift

variable {ι : Type*} (o : ι → ZMod 2) {n : ℕ}

/-- The lift of the base block `w = i_0 ⋯ i_{n-1}` with initial axis `c`: the transition rule
of `Σ_Z` forces the axis `c + ∑_{j<k} o(i_j)` at time `k`. -/
def liftBlock (c : ZMod 2) (w : Fin n → ι) : Fin n → ι × ZMod 2 :=
  fun k => (w k, c + ∑ j ∈ Finset.Iio k, o (w j))

/-- The lifted block projects to the base block. -/
@[simp] theorem liftBlock_fst (c : ZMod 2) (w : Fin n → ι) (k : Fin n) :
    (liftBlock o c w k).1 = w k := rfl

/-- The lifted block starts on the axis `c`. -/
@[simp] theorem liftBlock_zero_snd (c : ZMod 2) (w : Fin (n + 1) → ι) :
    (liftBlock o c w 0).2 = c := by
  have h : Finset.Iio (0 : Fin (n + 1)) = ∅ := Finset.Iio_bot
  simp [liftBlock, h]

/-- A non-empty lifted block determines its base block and its initial axis. -/
theorem liftBlock_injective :
    Function.Injective fun p : (Fin (n + 1) → ι) × ZMod 2 => liftBlock o p.2 p.1 := by
  rintro ⟨w, c⟩ ⟨w', c'⟩ h
  have hw : w = w' := funext fun k => congrArg Prod.fst (congrFun h k)
  have hc : c = c' := by simpa using congrArg Prod.snd (congrFun h 0)
  rw [hw, hc]

variable {o}

/-- A point of `Σ_Z` over the base cylinder `[w]` lies in the cylinder of the lift of `w` along
its axis at time `0`. -/
theorem mem_cylinder_liftBlock {y : ℤ → ι × ZMod 2} (hy : y ∈ subshift o) {w : Fin n → ι}
    (hw : unCode y ∈ cylinder w) : y ∈ cylinder (liftBlock o (y 0).2 w) := by
  intro k
  refine Prod.ext (hw k) ?_
  have hsum : ∑ j ∈ Finset.Iio k, o (w j) = ∑ j ∈ Finset.range k, o (unCode y j) := by
    rw [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, Finset.sum_map]
    exact Finset.sum_congr rfl fun j _ => congrArg o (hw j).symm
  change (y k).2 = (y 0).2 + ∑ j ∈ Finset.Iio k, o (w j)
  rw [hsum, ← eps_natCast, ← snd_eq_of_mem_subshift hy]

end Lift

section Measure

variable {ι : Type*} (o : ι → ZMod 2) {n : ℕ}

/-- The factor map commutes with the shift. -/
theorem unCode_shift (n : ℤ) (y : ℤ → ι × ZMod 2) : unCode (shift n y) = shift n (unCode y) :=
  rfl

variable [MeasurableSpace ι]

/-- The factor map `q = unCode` that forgets the axis is measurable. -/
theorem measurable_unCode : Measurable (unCode : (ℤ → ι × ZMod 2) → ℤ → ι) :=
  Measurable.of_eval fun n => measurable_fst.comp (measurable_pi_apply n)

/-- The sub-shift `Σ_Z` is a measurable subset of the full shift over `ι × ZMod 2`. -/
theorem measurableSet_subshift [Fintype ι] [MeasurableSingletonClass ι] :
    MeasurableSet (subshift o) := by
  have h : subshift o = ⋂ n : ℤ, (fun y : ℤ → ι × ZMod 2 => (y n, y (n + 1))) ⁻¹'
      {pq | Trans o pq.1 pq.2} := by
    ext y
    simp [subshift]
  rw [h]
  exact MeasurableSet.iInter fun n =>
    ((measurable_pi_apply n).prodMk (measurable_pi_apply (n + 1)))
      (Set.to_countable _).measurableSet

variable {o} {ν : Measure (ℤ → ι × ZMod 2)}

/-- The image of an invariant measure under the factor map is invariant. -/
theorem measurePreserving_shift_map_unCode (hinv : MeasurePreserving (shift 1) ν ν) :
    MeasurePreserving (shift 1) (ν.map unCode) (ν.map unCode) := by
  refine ⟨measurable_shift 1, ?_⟩
  rw [Measure.map_map (measurable_shift 1) measurable_unCode]
  have h : (shift 1 : (ℤ → ι) → ℤ → ι) ∘ unCode = unCode ∘ shift 1 := rfl
  rw [h, ← Measure.map_map measurable_unCode (measurable_shift 1), hinv.map_eq]

/-- Inadmissible blocks are null for a measure carried by `Σ_Z`. -/
theorem measure_cylinder_eq_zero (hν : ν (subshift o)ᶜ = 0) {v : Fin (n + 1) → ι × ZMod 2}
    (hv : v ∉ Set.range fun p : (Fin (n + 1) → ι) × ZMod 2 => liftBlock o p.2 p.1) :
    ν (cylinder v) = 0 := by
  have hsub : cylinder v ⊆ (subshift o)ᶜ := fun y hy hys => by
    have h := mem_cylinder_liftBlock hys (w := fun k => (v k).1)
      fun k => congrArg Prod.fst (hy k)
    exact hv ⟨(fun k => (v k).1, (y 0).2), funext fun k => (h k).symm.trans (hy k)⟩
  exact measure_mono_null hsub hν

/-- The preimage of a base cylinder of positive length under the factor map is, up to a null
set, the disjoint union of the cylinders of its two lifts, so its measure is the sum of their
measures. -/
theorem measureReal_preimage_unCode_cylinder [IsFiniteMeasure ν] (hν : ν (subshift o)ᶜ = 0)
    (w : Fin (n + 1) → ι) :
    ν.real (unCode ⁻¹' cylinder w) = ∑ c : ZMod 2, ν.real (cylinder (liftBlock o c w)) := by
  have h := sum_measureReal_inter_preimage_singleton ν (f := fun y => (y 0).2)
    (fun c => (measurable_snd.comp (measurable_pi_apply 0)) (measurableSet_singleton c))
    (unCode ⁻¹' cylinder w)
  rw [← h]
  refine Finset.sum_congr rfl fun c _ => measureReal_congr ?_
  have hae : ∀ᵐ y ∂ν, y ∈ subshift o := mem_ae_iff.2 hν
  refine Filter.eventuallyEqSet_iff.2 (hae.mono fun y hy => ⟨?_, fun h => ⟨?_, ?_⟩⟩)
  · rintro ⟨hw, rfl⟩
    exact mem_cylinder_liftBlock hy hw
  · exact fun k => congrArg Prod.fst (h k)
  · have h0 := congrArg Prod.snd (h 0)
    simpa using h0

end Measure

section Entropy

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The block entropies of a measure carried by `Σ_Z` and of its image under the factor map
differ by at most `log 2`. -/
theorem blockEntropy_map_unCode (o : ι → ZMod 2) (ν : Measure (ℤ → ι × ZMod 2))
    [IsProbabilityMeasure ν] (hν : ν (subshift o)ᶜ = 0) (n : ℕ) :
    blockEntropy (ν.map unCode) n ≤ blockEntropy ν n ∧
      blockEntropy ν n ≤ blockEntropy (ν.map unCode) n + Real.log 2 := by
  rcases n with _ | n
  · simpa using Real.log_nonneg one_le_two
  have hbase : ∀ w : Fin (n + 1) → ι, (ν.map unCode).real (cylinder w)
      = ν.real (cylinder (liftBlock o 0 w)) + ν.real (cylinder (liftBlock o 1 w)) := by
    intro w
    rw [map_measureReal_apply measurable_unCode (measurableSet_cylinder w),
      measureReal_preimage_unCode_cylinder hν w, sum_zmod_two]
  have hlift : blockEntropy ν (n + 1) = ∑ w : Fin (n + 1) → ι,
      (Real.negMulLog (ν.real (cylinder (liftBlock o 0 w)))
        + Real.negMulLog (ν.real (cylinder (liftBlock o 1 w)))) := by
    rw [blockEntropy, ← Fintype.sum_of_injective _ (liftBlock_injective o)
      (fun p => Real.negMulLog (ν.real (cylinder (liftBlock o p.2 p.1)))) _
      (fun v hv => by rw [measureReal_def, measure_cylinder_eq_zero hν hv]; simp)
      (fun p => rfl), Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun w _ => sum_zmod_two _
  have hone : ∑ w : Fin (n + 1) → ι,
      (ν.real (cylinder (liftBlock o 0 w)) + ν.real (cylinder (liftBlock o 1 w))) = 1 := by
    simp_rw [← hbase]
    exact sum_measureReal_cylinder _ _
  constructor
  · rw [hlift, blockEntropy]
    refine Finset.sum_le_sum fun w _ => ?_
    rw [hbase]
    exact negMulLog_add_le measureReal_nonneg measureReal_nonneg
  · rw [hlift, blockEntropy]
    calc ∑ w : Fin (n + 1) → ι, (Real.negMulLog (ν.real (cylinder (liftBlock o 0 w)))
          + Real.negMulLog (ν.real (cylinder (liftBlock o 1 w))))
        ≤ ∑ w : Fin (n + 1) → ι, (Real.negMulLog ((ν.map unCode).real (cylinder w))
          + (ν.real (cylinder (liftBlock o 0 w)) + ν.real (cylinder (liftBlock o 1 w)))
            * Real.log 2) := by
          refine Finset.sum_le_sum fun w _ => ?_
          rw [hbase]
          exact negMulLog_add_negMulLog_le measureReal_nonneg measureReal_nonneg
      _ = ∑ w : Fin (n + 1) → ι, Real.negMulLog ((ν.map unCode).real (cylinder w))
          + Real.log 2 := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, hone, one_mul]

/-- `thm:entropy_eq_gibbs` in measure-theoretic form: an invariant measure carried by `Σ_Z` and
its image under the factor map that forgets the axis have the same Kolmogorov–Sinai entropy. -/
theorem entropy_map_unCode (o : ι → ZMod 2) (ν : Measure (ℤ → ι × ZMod 2))
    [IsProbabilityMeasure ν] (hinv : MeasurePreserving (shift 1) ν ν)
    (hν : ν (subshift o)ᶜ = 0) : entropy (ν.map unCode) = entropy ν := by
  refine entropy_eq_of_blockEntropy_close (C := Real.log 2) (tendsto_entropy hinv) fun n => ?_
  obtain ⟨h1, h2⟩ := blockEntropy_map_unCode o ν hν n
  rw [abs_le]
  constructor <;> linarith [Real.log_nonneg (one_le_two (α := ℝ))]

end Entropy

end BoxLike
