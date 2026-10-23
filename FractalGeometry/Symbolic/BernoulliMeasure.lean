import Mathlib
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.Shift

/-! Two-sided Bernoulli measures, cylinder probabilities and finite weight measures. -/

namespace FractalGeometry

open Filter Topology MeasureTheory ProbabilityTheory
open scoped symmDiff

section Bernoulli

variable {ι : Type*} [MeasurableSpace ι]

noncomputable def bernoulli (p : Measure ι) : Measure (ℤ → ι) :=
  Measure.infinitePi fun _ : ℤ => p

variable [MeasurableSingletonClass ι]

theorem bernoulli_cylinder (p : Measure ι) [IsProbabilityMeasure p] (k : ℤ) {n : ℕ}
    (w : Fin n → ι) : bernoulli p {x | ∀ j : Fin n, x (k + j) = w j} = ∏ j, p {w j} := by
  have hinj : Function.Injective fun j : Fin n => k + (j : ℤ) := fun i j h =>
    Fin.ext (by simpa using h)
  let t : ℤ → Set ι := Function.extend (fun j : Fin n => k + (j : ℤ)) (fun j => {w j})
    fun _ => Set.univ
  have ht : ∀ j : Fin n, t (k + j) = {w j} := fun j => hinj.extend_apply _ _ j
  have hset : {x : ℤ → ι | ∀ j : Fin n, x (k + j) = w j} =
      Set.pi (Finset.univ.map ⟨_, hinj⟩ : Finset ℤ) t := by
    ext x
    simp [ht]
  rw [hset, bernoulli, Measure.infinitePi_pi, Finset.prod_map]
  · simp [ht]
  · intro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 hi
    simp [ht]

theorem measureReal_bernoulli_cylinder (p : Measure ι) [IsProbabilityMeasure p] {n : ℕ}
    (w : Fin n → ι) : (bernoulli p).real (cylinder w) = ∏ j, p.real {w j} := by
  have h := bernoulli_cylinder p 0 w
  simp only [zero_add] at h
  rw [measureReal_def, cylinder, h, ENNReal.toReal_prod]
  rfl

variable [Fintype ι]

theorem measure_ext_of_cylinder {μ ν : Measure (ℤ → ι)} [IsFiniteMeasure μ]
    (h : ∀ (k : ℤ) (n : ℕ) (w : Fin n → ι),
      μ {x | ∀ j : Fin n, x (k + j) = w j} = ν {x | ∀ j : Fin n, x (k + j) = w j}) :
    μ = ν := by
  have hP : IsProjectiveLimit μ fun I : Finset ℤ => μ.map I.restrict := fun I => rfl
  refine hP.unique fun I => (Measure.ext_of_singleton fun f => ?_).symm
  rw [Measure.map_apply (Finset.measurable_restrict I) (measurableSet_singleton f),
    Measure.map_apply (Finset.measurable_restrict I) (measurableSet_singleton f)]
  obtain ⟨k, n, hkn⟩ : ∃ (k : ℤ) (n : ℕ), ∀ i ∈ I, ∃ j : Fin n, k + j = i := by
    refine ⟨-(I.sup Int.natAbs : ℕ), 2 * I.sup Int.natAbs + 1, fun i hi => ?_⟩
    have hle := Finset.le_sup (f := Int.natAbs) hi
    refine ⟨⟨(i + (I.sup Int.natAbs : ℕ)).toNat, by omega⟩, ?_⟩
    simp only
    omega
  have hg : ∀ w : Fin n → ι, MeasurableSet {x : ℤ → ι | ∀ j : Fin n, x (k + j) = w j} :=
    fun w => (measurable_shift k) (measurableSet_cylinder w)
  have hpre : ∀ w : Fin n → ι, (fun (x : ℤ → ι) (j : Fin n) => x (k + j)) ⁻¹' {w} =
      {x | ∀ j : Fin n, x (k + j) = w j} := fun w => by
    ext x
    simp [funext_iff]
  have key : ∀ ρ : Measure (ℤ → ι), ρ (I.restrict ⁻¹' {f}) =
      ∑ w : Fin n → ι, ρ ({x | ∀ j : Fin n, x (k + j) = w j} ∩ I.restrict ⁻¹' {f}) := by
    intro ρ
    have hsum := sum_measure_preimage_singleton (μ := ρ.restrict (I.restrict ⁻¹' {f}))
      Finset.univ (f := fun (x : ℤ → ι) (j : Fin n) => x (k + j))
      fun w _ => by rw [hpre]; exact hg w
    rw [Finset.coe_univ, Set.preimage_univ, Measure.restrict_apply_univ] at hsum
    rw [← hsum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hpre, Measure.restrict_apply (hg w)]
  rw [key μ, key ν]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hne :
      ({x : ℤ → ι | ∀ j : Fin n, x (k + j) = w j} ∩ I.restrict ⁻¹' {f}).Nonempty
  · obtain ⟨x, hxw, hxf⟩ := hne
    have hsub : {x : ℤ → ι | ∀ j : Fin n, x (k + j) = w j} ⊆
        (I.restrict ⁻¹' {f} : Set (ℤ → ι)) := by
      intro y hy
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hxf ⊢
      rw [← hxf]
      funext i
      obtain ⟨j, hj⟩ := hkn i i.2
      rw [Finset.restrict, Finset.restrict, ← hj, hy j, hxw j]
    rw [Set.inter_eq_left.2 hsub]
    exact h k n w
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, measure_empty, measure_empty]

theorem eq_bernoulli_of_cylinder (p : Measure ι) [IsProbabilityMeasure p] {μ : Measure (ℤ → ι)}
    (h : ∀ (k : ℤ) (n : ℕ) (w : Fin n → ι),
      μ {x | ∀ j : Fin n, x (k + j) = w j} = ∏ j, p {w j}) :
    μ = bernoulli p := by
  have : IsFiniteMeasure μ := ⟨by
    have h0 := h 0 0 Fin.elim0
    simp only [IsEmpty.forall_iff, Set.ofPred_true, Finset.univ_eq_empty,
      Finset.prod_empty] at h0
    rw [h0]
    exact ENNReal.one_lt_top⟩
  exact measure_ext_of_cylinder fun k n w => by rw [h k n w, bernoulli_cylinder]

theorem eq_bernoulli_of_measureReal_cylinder (p : Measure ι) [IsProbabilityMeasure p]
    {μ : Measure (ℤ → ι)} [IsFiniteMeasure μ]
    (h : ∀ (k : ℤ) (n : ℕ) (w : Fin n → ι),
      μ.real {x | ∀ j : Fin n, x (k + j) = w j} = ∏ j, p.real {w j}) :
    μ = bernoulli p := by
  refine eq_bernoulli_of_cylinder p fun k n w => ?_
  rw [← ofReal_measureReal, h k n w, ENNReal.ofReal_prod_of_nonneg fun _ _ => measureReal_nonneg]
  exact Finset.prod_congr rfl fun j _ => ofReal_measureReal

noncomputable def weightMeasure (p : ι → ℝ) : Measure ι :=
  ∑ i, ENNReal.ofReal (p i) • Measure.dirac i

theorem weightMeasure_singleton (p : ι → ℝ) (i : ι) :
    weightMeasure p {i} = ENNReal.ofReal (p i) := by
  classical
  simp [weightMeasure, Set.indicator_apply, eq_comm]

theorem measureReal_weightMeasure_singleton {p : ι → ℝ} {i : ι} (hp : 0 ≤ p i) :
    (weightMeasure p).real {i} = p i := by
  rw [measureReal_def, weightMeasure_singleton, ENNReal.toReal_ofReal hp]

omit [MeasurableSingletonClass ι] in

theorem isProbabilityMeasure_weightMeasure {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) : IsProbabilityMeasure (weightMeasure p) := by
  constructor
  have h : ∑ i, ENNReal.ofReal (p i) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hp i, hsum, ENNReal.ofReal_one]
  simpa [weightMeasure] using h

end Bernoulli

end FractalGeometry
