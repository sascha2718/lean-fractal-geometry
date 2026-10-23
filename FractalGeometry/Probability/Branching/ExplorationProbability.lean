import Mathlib
import FractalGeometry.Probability.Branching.Configuration
import FractalGeometry.Probability.Branching.CoordinateBlocks
import FractalGeometry.Probability.Branching.Exploration
import FractalGeometry.Probability.Branching.FiniteLevels
import FractalGeometry.Probability.Branching.GenerationIndependence
import FractalGeometry.Probability.Branching.Hoeffding
import FractalGeometry.Probability.Branching.IdenticalLaws
import FractalGeometry.Probability.Branching.IndependentVectors
import FractalGeometry.Probability.Branching.Law
import FractalGeometry.Probability.Branching.Offspring
import FractalGeometry.Probability.Branching.Process
import FractalGeometry.Probability.Branching.RegionIndependence
import FractalGeometry.Probability.Branching.RetainedWords

namespace FractalGeometry.Probability.Branching

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal

variable {A : Law}

lemma measurableSet_of_shallow_congr (ℓ : ℕ) {S : Set (Configuration A)}
    (hS : ∀ x y : Configuration A,
      (∀ q : Word A × (Fin A.arity), q.1.length < ℓ → x q = y q) → x ∈ S → y ∈ S) :
    MeasurableSet S := by
  classical
  have : Finite {u : Word A // u.length < ℓ} := (List.finite_length_lt _ ℓ).to_subtype
  have hset : S = (fun x : Configuration A => fun j : ShallowCoord A ℓ => x (j.1.1, j.2)) ⁻¹'
      (shallowExtend ℓ ⁻¹' S) := by
    ext x
    simp only [Set.mem_preimage]
    constructor
    · refine hS x _ fun q hq => ?_
      simp [shallowExtend, hq]
    · refine hS _ x fun q hq => ?_
      simp [shallowExtend, hq]
  rw [hset]
  exact (Measurable.of_eval fun j => measurable_pi_apply _) (Set.to_countable _).measurableSet

lemma length_lt_of_mem_exploreRegion {x : Configuration A} {k₀ : ℕ} {c : ℕ → ℕ} {J : ℕ}
    {q : Word A × (Fin A.arity)} (hq : q ∈ exploreRegion x k₀ c J) :
    q.1.length < k₀ + J := by
  simp only [exploreRegion, exploreRegionOf, Set.mem_ofPred_eq] at hq
  rcases hq with h | ⟨j, hj, hmem⟩
  · omega
  · have := (mem_exploreG (Finset.mem_sdiff.mp hmem).1).1
    omega

lemma exploreG_congr_shallow {x y : Configuration A} {k₀ : ℕ} {c : ℕ → ℕ} {J : ℕ}
    (hxy : ∀ q : Word A × (Fin A.arity), q.1.length < k₀ + J → x q = y q) :
    ∀ j ≤ J, exploreG y k₀ c j = exploreG x k₀ c j :=
  exploreG_congr fun q hq => (hxy q (length_lt_of_mem_exploreRegion hq)).symm

lemma exploreRegion_eq_of_exploreG_eq {x y : Configuration A} {k₀ : ℕ} {c : ℕ → ℕ} {J : ℕ}
    (h : ∀ j ≤ J, exploreG y k₀ c j = exploreG x k₀ c j) :
    exploreRegion y k₀ c J = exploreRegion x k₀ c J := by
  ext q
  simp only [exploreRegion, exploreRegionOf, Set.mem_ofPred_eq]
  refine or_congr_right (exists_congr fun j => and_congr_right fun hj => ?_)
  rw [h j hj.le]

lemma offspringConfig_config {Ω : Type*}
    (X : Word A → (Fin A.arity) → Ω → Bool) (ω : Ω) (w : Word A) :
    offspringConfig (config X ω) w = totalOffspring X w ω := by
  classical
  unfold offspringConfig totalOffspring
  rw [Finset.card_filter]
  rfl

def exploreGood (k₀ : ℕ) (c : ℕ → ℕ) (M : ℕ → ℝ) (J : ℕ) : Set (Configuration A) :=
  {x | ∀ j ≤ J, M j ≤ (exploreG x k₀ c j).card}

lemma exploreGood_anti {k₀ : ℕ} {c : ℕ → ℕ} {M : ℕ → ℝ} {J J' : ℕ} (h : J ≤ J') :
    exploreGood (A := A) k₀ c M J' ⊆ exploreGood k₀ c M J :=
  fun _ hx j hj => hx j (hj.trans h)

lemma measurableSet_exploreGood (k₀ : ℕ) (c : ℕ → ℕ) (M : ℕ → ℝ) (J : ℕ) :
    MeasurableSet (exploreGood (A := A) k₀ c M J) :=
  measurableSet_of_shallow_congr (k₀ + J) fun x y hxy hx j hj => by
    rw [exploreG_congr_shallow hxy j hj]
    exact hx j hj

lemma measurableSet_exploreG_eq (k₀ : ℕ) (c : ℕ → ℕ) (J : ℕ) (s : Finset (Word A)) :
    MeasurableSet {x : Configuration A | exploreG x k₀ c J = s} :=
  measurableSet_of_shallow_congr (k₀ + J) fun x y hxy hx => by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [exploreG_congr_shallow hxy J le_rfl]
    exact hx

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Word A → (Fin A.arity) → Ω → Bool}

theorem measure_exploreGood_diff_le (hX : IsPercolation P X) {k₀ : ℕ} {c : ℕ → ℕ}
    {M : ℕ → ℝ} {J : ℕ} {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hcM : (c J : ℝ) ≤ M J)
    (hMsucc : M (J + 1) ≤ (1 - η) * A.m * (M J - c J)) :
    P (config X ⁻¹' exploreGood k₀ c M J \ config X ⁻¹' exploreGood k₀ c M (J + 1)) ≤
      ENNReal.ofReal (Real.exp (-(2 * η ^ 2 * A.m ^ 2 * (M J - c J) / ((A.arity : ℝ)) ^ 2))) *
        P (config X ⁻¹' exploreGood k₀ c M J) := by
  classical
  let := hX.toIsProbabilityMeasure
  set e := ENNReal.ofReal (Real.exp (-(2 * η ^ 2 * A.m ^ 2 * (M J - c J) /
    ((A.arity : ℝ)) ^ 2))) with he
  set good := config X ⁻¹' exploreGood k₀ c M J with hgood
  set bad := config X ⁻¹' exploreGood k₀ c M (J + 1) with hbad
  set slice : Finset (Word A) → Set Ω :=
    fun s => good ∩ config X ⁻¹' {x | exploreG x k₀ c J = s} with hslice
  have hslice_meas : ∀ s, MeasurableSet (slice s) := fun s =>
    (measurable_config hX (measurableSet_exploreGood k₀ c M J)).inter
      (measurable_config hX (measurableSet_exploreG_eq k₀ c J s))
  have hdisj : Pairwise (Function.onFun Disjoint slice) := by
    intro s t hst
    rw [Function.onFun, Set.disjoint_left]
    intro ω hs ht
    exact hst (hs.2.symm.trans ht.2)
  have hunion : ⋃ s, slice s = good := by
    ext ω
    simp only [hslice, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨_, h, rfl⟩⟩
  have hbound : ∀ s, P (slice s \ bad) ≤ e * P (slice s) := by
    intro s
    rcases (slice s \ bad).eq_empty_or_nonempty with hempty | ⟨ω₀, ⟨hω₀good, hω₀s⟩, -⟩
    · rw [hempty, measure_empty]
      exact zero_le
    have hs : exploreG (config X ω₀) k₀ c J = s := hω₀s
    have hs_len : ∀ w ∈ s, w.length = k₀ + J := fun w hw => by
      rw [← hs] at hw
      exact (mem_exploreG hw).1
    have hMs : M J ≤ s.card := by
      have := hω₀good J le_rfl
      rwa [hs] at this
    have hcs : c J ≤ s.card := by exact_mod_cast hcM.trans hMs
    set T := s \ chooseSubset s (c J) with hT
    have hTcard : (T.card : ℝ) = s.card - c J := by
      rw [hT, Finset.card_sdiff_of_subset (chooseSubset_subset s (c J)), chooseSubset_card hcs,
        Nat.cast_sub hcs]

    let f : ShallowCoord A (k₀ + J) → Word A × (Fin A.arity) := fun j => (j.1.1, j.2)
    let g : {w // w ∈ T} × (Fin A.arity) → Word A × (Fin A.arity) :=
      fun p => (p.1.1, p.2)
    have hf : Function.Injective f := by
      rintro ⟨⟨u, hu⟩, a⟩ ⟨⟨u', hu'⟩, a'⟩ h
      simp only [f, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    have hg : Function.Injective g := by
      rintro ⟨⟨w, hw⟩, a⟩ ⟨⟨w', hw'⟩, a'⟩ h
      simp only [g, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    have hfg : ∀ i j, f i ≠ g j := by
      rintro ⟨⟨u, hu⟩, a⟩ ⟨⟨w, hw⟩, b⟩ h
      simp only [f, g, Prod.mk.injEq] at h
      have hwlen := hs_len w (Finset.mem_sdiff.mp hw).1
      rw [← h.1] at hwlen
      omega
    have hind := iIndepFun.indepFun_coordinateBlocks (Z := fun q ω => X q.1 q.2 ω)
      (fun q => hX.measurable q.1 q.2) hX.indep f g hf hg hfg

    have : Finite {u : Word A // u.length < k₀ + J} :=
      (List.finite_length_lt _ (k₀ + J)).to_subtype
    set S₁ : Set (ShallowCoord A (k₀ + J) → Bool) :=
      {v | shallowExtend (k₀ + J) v ∈ exploreGood k₀ c M J ∧
        exploreG (shallowExtend (k₀ + J) v) k₀ c J = s} with hS₁
    have hslice_eq : slice s = (fun ω i => X (f i).1 (f i).2 ω) ⁻¹' S₁ := by
      ext ω
      have hagree : ∀ q : Word A × (Fin A.arity), q.1.length < k₀ + J →
          config X ω q = shallowExtend (k₀ + J) (fun i => X (f i).1 (f i).2 ω) q := by
        intro q hq
        simp [shallowExtend, hq, f, config]
      have hG := exploreG_congr_shallow (c := c) hagree
      simp only [hslice, hS₁, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, exploreGood]
      constructor
      · rintro ⟨hgoodω, hsω⟩
        exact ⟨fun j hj => by rw [hG j hj]; exact hgoodω j hj, by rw [hG J le_rfl]; exact hsω⟩
      · rintro ⟨hgoodω, hsω⟩
        exact ⟨fun j hj => by rw [← hG j hj]; exact hgoodω j hj, by rw [← hG J le_rfl]; exact hsω⟩

    set S₂ : Set ({w // w ∈ T} × (Fin A.arity) → Bool) :=
      {v | (∑ w : {w // w ∈ T},
        (((Finset.univ : Finset (Fin A.arity)).filter fun a => v (w, a) = true).card : ℝ))
          ≤ (1 - η) * A.m * T.card} with hS₂
    set hoeff := {ω | (∑ w ∈ T, (totalOffspring X w ω : ℝ)) ≤ (1 - η) * A.m * T.card}
      with hhoeff
    have hhoeff_eq : hoeff = (fun ω j => X (g j).1 (g j).2 ω) ⁻¹' S₂ := by
      ext ω
      simp only [hhoeff, hS₂, Set.mem_preimage, Set.mem_ofPred_eq, g]
      rw [← Finset.sum_coe_sort T]
      refine iff_of_eq (congrArg (· ≤ _) (Finset.sum_congr rfl fun w _ => ?_))
      rw [← offspringConfig_config X ω w]
      rfl

    have hsub : slice s \ bad ⊆ slice s ∩ hoeff := by
      rintro ω ⟨⟨hgoodω, hsω⟩, hbadω⟩
      refine ⟨⟨hgoodω, hsω⟩, ?_⟩
      have hsω' : exploreG (config X ω) k₀ c J = s := hsω
      have hfail : ¬ M (J + 1) ≤ (exploreG (config X ω) k₀ c (J + 1)).card := by
        intro hsucc
        refine hbadω fun j hj => ?_
        rcases Nat.lt_or_ge j (J + 1) with hlt | hge
        · exact hgoodω j (Nat.lt_succ_iff.mp hlt)
        · rw [show j = J + 1 by omega]
          exact hsucc
      have hchildren : (exploreG (config X ω) k₀ c (J + 1)).card =
          ∑ w ∈ T, totalOffspring X w ω := by
        rw [exploreG_succ, card_childrenConfig]
        simp only [exploreA, hsω', hT]
        exact Finset.sum_congr rfl fun w _ => offspringConfig_config X ω w
      rw [hchildren] at hfail
      push Not at hfail
      simp only [hhoeff, Set.mem_ofPred_eq]
      have hm0 : 0 ≤ (1 - η) * A.m := mul_nonneg (by linarith) A.m_nonneg
      calc (∑ w ∈ T, (totalOffspring X w ω : ℝ)) = ((∑ w ∈ T, totalOffspring X w ω : ℕ) : ℝ) := by
            push_cast; rfl
        _ ≤ M (J + 1) := hfail.le
        _ ≤ (1 - η) * A.m * (M J - c J) := hMsucc
        _ ≤ (1 - η) * A.m * T.card := by
            refine mul_le_mul_of_nonneg_left ?_ hm0
            rw [hTcard]
            linarith
    have hS₁meas : MeasurableSet S₁ := (Set.to_countable _).measurableSet
    have hS₂meas : MeasurableSet S₂ := (Set.to_countable _).measurableSet
    have hprod : P (slice s ∩ hoeff) = P (slice s) * P hoeff := by
      rw [hslice_eq, hhoeff_eq]
      exact hind.measure_inter_preimage_eq_mul _ _ hS₁meas hS₂meas
    have hhoeff_le : P hoeff ≤ e := by
      refine (measure_sum_totalOffspring_le hX T hη0).trans (ENNReal.ofReal_le_ofReal ?_)
      refine Real.exp_le_exp.mpr ?_
      have hMN : 0 < ((A.arity : ℝ)) ^ 2 := by
        have : (0 : ℝ) < A.arity := by exact_mod_cast A.arity_pos
        positivity
      rw [neg_le_neg_iff, div_le_div_iff_of_pos_right hMN]
      have hk : 0 ≤ 2 * η ^ 2 * A.m ^ 2 := by positivity
      refine mul_le_mul_of_nonneg_left ?_ hk
      rw [hTcard]
      linarith
    calc P (slice s \ bad) ≤ P (slice s ∩ hoeff) := measure_mono hsub
      _ = P (slice s) * P hoeff := hprod
      _ ≤ P (slice s) * e := by gcongr
      _ = e * P (slice s) := mul_comm _ _
  calc P (good \ bad) = P (⋃ s, (slice s \ bad)) := by
        rw [← Set.iUnion_sdiff, hunion]
    _ ≤ ∑' s, P (slice s \ bad) := measure_iUnion_le _
    _ ≤ ∑' s, e * P (slice s) := ENNReal.tsum_le_tsum hbound
    _ = e * ∑' s, P (slice s) := ENNReal.tsum_mul_left
    _ = e * P good := by rw [← measure_iUnion hdisj hslice_meas, hunion]

noncomputable def exploreHist (x : Configuration A) (k₀ : ℕ) (c : ℕ → ℕ) (J : ℕ) :
    Fin (J + 1) → Finset (Word A) :=
  fun j => exploreG x k₀ c j

lemma exploreHist_eq_iff {x y : Configuration A} {k₀ : ℕ} {c : ℕ → ℕ} {J : ℕ} :
    exploreHist y k₀ c J = exploreHist x k₀ c J ↔ ∀ j ≤ J, exploreG y k₀ c j = exploreG x k₀ c j := by
  constructor
  · intro h j hj
    exact congrFun h ⟨j, Nat.lt_succ_iff.mpr hj⟩
  · intro h
    funext j
    exact h j (Nat.lt_succ_iff.mp j.2)

noncomputable def regionExtend (R : Set (Word A × (Fin A.arity))) (r : R → Bool) :
    Configuration A := by
  classical
  exact fun q => if hq : q ∈ R then r ⟨q, hq⟩ else false

lemma measurable_regionExtend (R : Set (Word A × (Fin A.arity))) :
    Measurable (regionExtend R) := by
  classical
  refine Measurable.of_eval fun q => ?_
  by_cases hq : q ∈ R
  · simp only [regionExtend, dite_eq_left hq]
    exact measurable_pi_apply _
  · simp only [regionExtend, dite_eq_right hq]
    exact measurable_const

omit [MeasurableSpace Ω] in

lemma regionExtend_regionVector {R : Set (Word A × (Fin A.arity))} (ω : Ω)
    {q : Word A × (Fin A.arity)} (hq : q ∈ R) :
    regionExtend R (regionVector X R ω) q = config X ω q := by
  classical
  simp [regionExtend, hq, regionVector, config]

theorem measure_exploreGood_inter_miss_le (hX : IsPercolation P X) {k₀ : ℕ} {c : ℕ → ℕ}
    {M : ℕ → ℝ} (hcM : ∀ j, (c j : ℝ) ≤ M j) (E : ℕ → Set (Configuration A))
    (hE : ∀ n, MeasurableSet (E n)) (j₁ J : ℕ) :
    P (config X ⁻¹' exploreGood k₀ c M J ∩
        {ω | ∀ j, j₁ ≤ j → j < J → ∀ v ∈ exploreA (config X ω) k₀ c j,
          rebase v (config X ω) ∉ E (k₀ + j)}) ≤
      ∏ j ∈ Finset.Ico j₁ J, (1 - P (config X ⁻¹' E (k₀ + j))) ^ c j := by
  classical
  let := hX.toIsProbabilityMeasure
  set Q := ∏ j ∈ Finset.Ico j₁ J, (1 - P (config X ⁻¹' E (k₀ + j))) ^ c j with hQ
  set B := config X ⁻¹' exploreGood k₀ c M J ∩
    {ω | ∀ j, j₁ ≤ j → j < J → ∀ v ∈ exploreA (config X ω) k₀ c j,
      rebase v (config X ω) ∉ E (k₀ + j)} with hB
  set Ev : (Fin (J + 1) → Finset (Word A)) → Set Ω :=
    fun h => {ω | exploreHist (config X ω) k₀ c J = h} with hEv
  have hEv_meas : ∀ h, MeasurableSet (Ev h) := fun h => by
    show MeasurableSet (config X ⁻¹' {x : Configuration A | exploreHist x k₀ c J = h})
    exact measurable_config hX (measurableSet_of_shallow_congr (k₀ + J) fun x y hxy hx => by
      change exploreHist x k₀ c J = h at hx
      change exploreHist y k₀ c J = h
      rw [← hx]
      exact exploreHist_eq_iff.mpr fun j hj => exploreG_congr_shallow hxy j hj)
  have hdisj : Pairwise (Function.onFun Disjoint Ev) := by
    intro h h' hne
    rw [Function.onFun, Set.disjoint_left]
    intro ω hh hh'
    exact hne (hh.symm.trans hh')
  have hper : ∀ h, P (B ∩ Ev h) ≤ Q * P (Ev h) := by
    intro h
    rcases (B ∩ Ev h).eq_empty_or_nonempty with hempty | ⟨ω₀, ⟨hgood₀, -⟩, hω₀⟩
    · rw [hempty, measure_empty]
      exact zero_le
    set x₀ := config X ω₀ with hx₀
    set R := exploreRegion x₀ k₀ c J with hR
    set T := (Finset.Ico j₁ J).biUnion fun j => exploreA x₀ k₀ c j with hT
    have hTanti : ∀ v ∈ T, ∀ v' ∈ T, v <+: v' → v = v' := by
      intro v hv v' hv' hpre
      simp only [hT, Finset.mem_biUnion] at hv hv'
      obtain ⟨j, -, hvj⟩ := hv
      obtain ⟨j', -, hvj'⟩ := hv'
      exact exploreA_antichain hvj hvj' hpre
    have hRavoid : ∀ q ∈ R, ∀ v ∈ T, ¬ v <+: q.1 := by
      intro q hq v hv
      simp only [hT, Finset.mem_biUnion] at hv
      obtain ⟨j, -, hvj⟩ := hv
      exact not_prefix_of_mem_exploreRegion hq hvj
    set H : Set (R → Bool) :=
      regionExtend R ⁻¹' {x | ∀ j ≤ J, exploreG x k₀ c j = exploreG x₀ k₀ c j} with hH
    have hHmeas : MeasurableSet H := by
      refine measurable_regionExtend R (measurableSet_of_shallow_congr (k₀ + J) ?_)
      intro x y hxy hx j hj
      rw [exploreG_congr_shallow hxy j hj]
      exact hx j hj
    have hω₀' : ∀ j ≤ J, exploreG x₀ k₀ c j = exploreG (config X ω₀) k₀ c j := fun _ _ => rfl
    have hEv_eq : Ev h = {ω | regionVector X R ω ∈ H} := by
      ext ω
      simp only [hEv, hH, Set.mem_ofPred_eq, Set.mem_preimage]
      rw [← hω₀, exploreHist_eq_iff]
      constructor
      · intro hGω j hj
        have hreg : exploreRegion (config X ω) k₀ c J = R := exploreRegion_eq_of_exploreG_eq hGω
        have hagree : ∀ q ∈ exploreRegion (config X ω) k₀ c J,
            regionExtend R (regionVector X R ω) q = config X ω q := by
          intro q hq
          rw [hreg] at hq
          exact regionExtend_regionVector ω hq
        rw [exploreG_congr hagree j hj, hGω j hj]
      · intro hGy j hj
        have hreg : exploreRegion (regionExtend R (regionVector X R ω)) k₀ c J = R :=
          exploreRegion_eq_of_exploreG_eq hGy
        have hagree : ∀ q ∈ exploreRegion (regionExtend R (regionVector X R ω)) k₀ c J,
            config X ω q = regionExtend R (regionVector X R ω) q := by
          intro q hq
          rw [hreg] at hq
          exact (regionExtend_regionVector ω hq).symm
        rw [exploreG_congr hagree j hj, hGy j hj]
    have hsub : B ∩ Ev h ⊆ {ω | regionVector X R ω ∈ H} ∩
        ⋂ v ∈ T, {ω | deepVector X v ω ∈ (E v.length)ᶜ} := by
      rintro ω ⟨⟨-, hmiss⟩, hEvω⟩
      have hEvω' := hEvω
      rw [hEv_eq] at hEvω'
      refine ⟨hEvω', ?_⟩
      have hGω : ∀ j ≤ J, exploreG (config X ω) k₀ c j = exploreG x₀ k₀ c j := by
        have : exploreHist (config X ω) k₀ c J = exploreHist x₀ k₀ c J := hEvω.trans hω₀.symm
        exact exploreHist_eq_iff.mp this
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_compl_iff]
      intro v hv
      simp only [hT, Finset.mem_biUnion, Finset.mem_Ico] at hv
      obtain ⟨j, ⟨hj₁, hjJ⟩, hvj⟩ := hv
      have hvlen := (mem_exploreG (exploreA_subset x₀ k₀ c j hvj)).1
      have hA : exploreA (config X ω) k₀ c j = exploreA x₀ k₀ c j := by
        unfold exploreA
        rw [hGω j hjJ.le]
      rw [deepVector_eq_rebase, hvlen]
      exact hmiss j hj₁ hjJ v (hA ▸ hvj)
    have hformula := measure_region_inter_biInter_deep hX R T hTanti hRavoid hHmeas
      (fun v => (E v.length)ᶜ) (fun v _ => (hE _).compl)
    have hprodT : ∏ v ∈ T, P {ω | config X ω ∈ (E v.length)ᶜ} = Q := by
      rw [hT, Finset.prod_biUnion]
      · refine Finset.prod_congr rfl fun j hj => ?_
        have hcard : (exploreA x₀ k₀ c j).card = c j := by
          apply card_exploreA
          have := hgood₀ j (Finset.mem_Ico.mp hj).2.le
          exact_mod_cast (hcM j).trans this
        rw [← hcard, ← Finset.prod_const]
        refine Finset.prod_congr rfl fun v hv => ?_
        rw [(mem_exploreG (exploreA_subset x₀ k₀ c j hv)).1]
        change P (config X ⁻¹' (E (k₀ + j))ᶜ) = _
        rw [Set.preimage_compl, prob_compl_eq_one_sub (measurable_config hX (hE _))]
      · intro j _ j' _ hjj'
        rw [Function.onFun, Finset.disjoint_left]
        intro v hv hv'
        have h1 := (mem_exploreG (exploreA_subset x₀ k₀ c j hv)).1
        have h2 := (mem_exploreG (exploreA_subset x₀ k₀ c j' hv')).1
        exact hjj' (by omega)
    calc P (B ∩ Ev h) ≤ P ({ω | regionVector X R ω ∈ H} ∩
            ⋂ v ∈ T, {ω | deepVector X v ω ∈ (E v.length)ᶜ}) := measure_mono hsub
      _ = P {ω | regionVector X R ω ∈ H} * Q := by rw [hformula, hprodT]
      _ = Q * P (Ev h) := by rw [hEv_eq, mul_comm]
  calc P B ≤ ∑' h, P (B ∩ Ev h) := by
        refine (measure_mono ?_).trans (measure_iUnion_le _)
        intro ω hω
        exact Set.mem_iUnion.mpr ⟨exploreHist (config X ω) k₀ c J, hω, rfl⟩
    _ ≤ ∑' h, Q * P (Ev h) := ENNReal.tsum_le_tsum hper
    _ = Q * ∑' h, P (Ev h) := ENNReal.tsum_mul_left
    _ = Q * P (⋃ h, Ev h) := by rw [measure_iUnion hdisj hEv_meas]
    _ ≤ Q * 1 := by gcongr; exact prob_le_one
    _ = Q := mul_one Q

end FractalGeometry.Probability.Branching
