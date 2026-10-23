import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.BlockIndependence
import FractalGeometry.Probability.GridPercolation.Configuration
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.LawInvariance
import FractalGeometry.Probability.GridPercolation.Process

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {A : GridLaw} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

noncomputable def shallowInd (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (c : ℕ)
    (S : Set (ShallowCoord A c → Bool)) (ω : Ω) : ℝ :=
  S.indicator (fun _ => (1 : ℝ)) (shallowVector X c ω)

noncomputable def deepInd (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (root : Word A)
    (D : Set (Configuration A)) (ω : Ω) : ℝ :=
  D.indicator (fun _ => (1 : ℝ)) (deepVector X root ω)

lemma measurable_shallowVector (hX : IsPercolation P X) (c : ℕ) :
    Measurable (shallowVector X c) :=
  Measurable.of_eval fun _j => hX.measurable _ _

lemma measurable_deepVector (hX : IsPercolation P X) (root : Word A) :
    Measurable (deepVector X root) :=
  Measurable.of_eval fun _q => hX.measurable _ _

lemma measurable_blockVector (hX : IsPercolation P X) {ι : Type*} (roots : ι → Word A) (c : ℕ)
    (o : Option ι) : Measurable (fun ω => blockVector X roots c o ω) :=
  Measurable.of_eval fun _j => hX.measurable _ _

lemma measurable_shallowInd (hX : IsPercolation P X) (c : ℕ)
    {S : Set (ShallowCoord A c → Bool)} (hS : MeasurableSet S) :
    Measurable (shallowInd X c S) :=
  (measurable_const.indicator hS).comp (measurable_shallowVector hX c)

omit [MeasurableSpace Ω] in

lemma shallowInd_nonneg (c : ℕ) (S : Set (ShallowCoord A c → Bool)) (ω : Ω) :
    0 ≤ shallowInd X c S ω :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) _

omit [MeasurableSpace Ω] in

lemma shallowInd_le_one (c : ℕ) (S : Set (ShallowCoord A c → Bool)) (ω : Ω) :
    shallowInd X c S ω ≤ 1 :=
  Set.indicator_le_self' (fun _ _ => zero_le_one) _

omit [MeasurableSpace Ω] in

lemma shallowInd_mul_self (c : ℕ) (S : Set (ShallowCoord A c → Bool)) (ω : Ω) :
    shallowInd X c S ω * shallowInd X c S ω = shallowInd X c S ω := by
  unfold shallowInd Set.indicator
  split_ifs <;> simp

lemma integral_deepInd (hX : IsPercolation P X) (root : Word A)
    {D : Set (Configuration A)} (hD : MeasurableSet D) :
    ∫ ω, deepInd X root D ω ∂P = (P {ω | config X ω ∈ D}).toReal := by
  have h := hX.measure_config_functional_shift root (G := id) measurable_id hD
  simp only [id] at h
  have hset : (fun ω => deepInd X root D ω) =
      (deepVector X root ⁻¹' D).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    rfl
  rw [hset, integral_indicator_const _ ((measurable_deepVector hX root) hD), smul_eq_mul,
    mul_one, measureReal_def]
  simp only [Set.preimage, deepVector_eq_rebase]
  rw [h]

lemma integral_shallow_mul_deep (hX : IsPercolation P X) {ι : Type*} (roots : ι → Word A)
    {c : ℕ} (hlen : ∀ i, (roots i).length = c) (hinj : Function.Injective roots) (i : ι)
    (f₀ : (ShallowCoord A c → Bool) → ℝ) (f₁ : Configuration A → ℝ)
    (hf₀ : Measurable f₀) (hf₁ : Measurable f₁) :
    ∫ ω, f₀ (shallowVector X c ω) * f₁ (deepVector X (roots i) ω) ∂P =
      (∫ ω, f₀ (shallowVector X c ω) ∂P) * ∫ ω, f₁ (deepVector X (roots i) ω) ∂P := by
  let := hX.toIsProbabilityMeasure
  have hind := iIndepFun_shallow_deep hX roots hlen hinj
  have h := (hind.indepFun (show (none : Option ι) ≠ some i by simp)).comp hf₀ hf₁
  have h2 := h.integral_mul_eq_mul_integral
    (hf₀.comp (measurable_blockVector hX roots c none)).aestronglyMeasurable
    (hf₁.comp (measurable_blockVector hX roots c (some i))).aestronglyMeasurable
  simpa [Function.comp, Pi.mul_apply, blockVector_none, blockVector_some] using h2

lemma integral_shallow_mul_deep_mul_deep (hX : IsPercolation P X) {ι : Type*}
    (roots : ι → Word A) {c : ℕ} (hlen : ∀ i, (roots i).length = c)
    (hinj : Function.Injective roots) {i i' : ι} (hii' : i ≠ i')
    (f₀ : (ShallowCoord A c → Bool) → ℝ) (f₁ f₂ : Configuration A → ℝ)
    (hf₀ : Measurable f₀) (hf₁ : Measurable f₁) (hf₂ : Measurable f₂) :
    ∫ ω, f₀ (shallowVector X c ω) *
        (f₁ (deepVector X (roots i) ω) * f₂ (deepVector X (roots i') ω)) ∂P =
      (∫ ω, f₀ (shallowVector X c ω) ∂P) *
        ((∫ ω, f₁ (deepVector X (roots i) ω) ∂P) * ∫ ω, f₂ (deepVector X (roots i') ω) ∂P) := by
  classical
  let := hX.toIsProbabilityMeasure
  have hind := iIndepFun_shallow_deep hX roots hlen hinj
  have hmeas := measurable_blockVector hX roots c

  have hdisj : Disjoint ({none} : Finset (Option ι)) {some i, some i'} := by
    simp
  have h1 := hind.indepFun_finset {none} {some i, some i'} hdisj hmeas
  have hnone : (none : Option ι) ∈ ({none} : Finset (Option ι)) := by simp
  have hi : some i ∈ ({some i, some i'} : Finset (Option ι)) := by simp
  have hi' : some i' ∈ ({some i, some i'} : Finset (Option ι)) := by simp
  set φ : ((k : ↥({none} : Finset (Option ι))) → BlockIndex A c (k : Option ι) → Bool) → ℝ :=
    fun v => f₀ (v ⟨none, hnone⟩) with hφ
  set ψ : ((k : ↥({some i, some i'} : Finset (Option ι))) → BlockIndex A c (k : Option ι) → Bool)
      → ℝ := fun v => f₁ (v ⟨some i, hi⟩) * f₂ (v ⟨some i', hi'⟩) with hψ
  have hφm : Measurable φ := by
    show Measurable (fun v : ((k : ↥({none} : Finset (Option ι))) →
      BlockIndex A c (k : Option ι) → Bool) => f₀ (v ⟨none, hnone⟩))
    exact hf₀.comp (measurable_pi_apply _)
  have hψm : Measurable ψ := by
    show Measurable (fun v : ((k : ↥({some i, some i'} : Finset (Option ι))) →
      BlockIndex A c (k : Option ι) → Bool) => f₁ (v ⟨some i, hi⟩) * f₂ (v ⟨some i', hi'⟩))
    exact Measurable.mul (hf₁.comp (measurable_pi_apply _)) (hf₂.comp (measurable_pi_apply _))
  have h2 := (h1.comp hφm hψm).integral_mul_eq_mul_integral
    (hφm.comp (Measurable.of_eval fun k => hmeas k)).aestronglyMeasurable
    (hψm.comp (Measurable.of_eval fun k => hmeas k)).aestronglyMeasurable

  have h3 := ((hind.indepFun (show (some i : Option ι) ≠ some i' by simpa using hii')).comp
    hf₁ hf₂).integral_mul_eq_mul_integral
    (hf₁.comp (hmeas (some i))).aestronglyMeasurable
    (hf₂.comp (hmeas (some i'))).aestronglyMeasurable
  simp only [Function.comp, Pi.mul_apply, hφ, hψ, blockVector_none, blockVector_some] at h2 h3
  rw [h2, h3]

end FractalGeometry.Probability.GridPercolation
