module

/-
The weak-star infrastructure behind the existence of an `s`-equilibrium state, tex lines 2105 to
2218, where the article cites Käenmäki, Ann. Acad. Sci. Fenn. Math. 29 (2004), Theorems 2.6 and
4.1, for the existence part of `thm:irred_eq_state`. The alphabet `ι` is finite, non-empty and
discrete, so `Σ = ℤ → ι` is a compact metrisable space whose product `σ`-algebra is the Borel
`σ`-algebra, the space of Borel probability measures on `Σ` is compact in the weak-star
topology, and the set `ℳ_σ(Σ)` of shift-invariant ones is a non-empty compact subset. Both
`h_0(μ)` and `Λ(𝖠, μ, s)` are infima of continuous functions of `μ` there, hence upper
semicontinuous, so `h_0(μ) + Λ(𝖠, μ, s)` attains its maximum on `ℳ_σ(Σ)`.

* `compactSpace_twoSided`, `metrizableSpace_twoSided`, `compactSpace_probabilityMeasure`: `Σ` is
  compact and metrisable, and the space of Borel probability measures on `Σ` is compact.
* `continuous_shift`, `continuous_block`: the shift and the block map `x ↦ x_0 ⋯ x_{n-1}` are
  continuous.
* `continuous_integral_comp_block`: `ν ↦ ∫ F(x_0 ⋯ x_{n-1}) dν` is weak-star continuous.
* `continuous_measureReal_cylinder`, `tendsto_measureReal_cylinder`: `ν ↦ ν([w])` is weak-star
  continuous, since a cylinder is clopen.
* `continuous_blockEntropy`, `System.continuous_integral_log_svf`,
  `System.continuous_energy_step`: `ν ↦ H_ν(𝒫_0^{n-1})` and `ν ↦ n⁻¹ ∫ log φ^s(A_{𝐢|_n}) dν` are
  weak-star continuous.
* `InvariantMeasures`, `mem_invariantMeasures_iff`, `isClosed_invariantMeasures`,
  `isCompact_invariantMeasures`, `invariantMeasures_nonempty`: the set `ℳ_σ(Σ)` is a non-empty
  compact subset of the space of Borel probability measures.
* `limUnder_eq_iInf_of_subadditive`: the limit of a bounded below sub-additive sequence `u_n / n`
  is the infimum of `u_n / n` over `n ≥ 1`.
* `subadditive_integral_futureWord`: the averages of a sub-additive function of words are
  sub-additive for an invariant measure.
* `entropy_eq_iInf`, `System.energyLim_eq_iInf`: `h_0(μ)` and `Λ(𝖠, μ, s)` as infima.
* `upperSemicontinuousOn_entropy`, `System.upperSemicontinuousOn_energyLim`: both are upper
  semicontinuous on `ℳ_σ(Σ)`.
* `System.exists_maximiser`, `System.exists_isGreatest_entropy_add_energyLim`,
  `System.exists_csSup_entropy_add_energyLim`: the supremum of `h_0(μ) + Λ(𝖠, μ, s)` over
  `ℳ_σ(Σ)` is attained.
-/
public import BoxLike.CodingTopology
public import BoxLike.Variational
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Topology.Semicontinuity.Basic

@[expose] public section

namespace BoxLike

open Filter MeasureTheory Topology
open scoped BoundedContinuousFunction

/-! ### The compact space of Borel probability measures on `Σ` -/

section Compact

variable (ι : Type*) [Fintype ι] [TopologicalSpace ι] [DiscreteTopology ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]

omit [DiscreteTopology ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The two-sided full shift `Σ = ℤ → ι` over a finite discrete alphabet is compact (tex line
800). -/
theorem compactSpace_twoSided : CompactSpace (ℤ → ι) := inferInstance

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The two-sided full shift `Σ = ℤ → ι` over a discrete alphabet is metrisable: it is a
countable product of metrisable spaces. -/
theorem metrizableSpace_twoSided : TopologicalSpace.MetrizableSpace (ℤ → ι) := inferInstance

/-- The space of Borel probability measures on `Σ` is compact in the weak-star topology, since
`Σ` is compact. This is the compactness of `ℳ(Σ)` behind the existence of an equilibrium state,
tex lines 2105 to 2106. -/
theorem compactSpace_probabilityMeasure : CompactSpace (ProbabilityMeasure (ℤ → ι)) :=
  inferInstance

end Compact

/-! ### Weak-star continuity of the functions of finitely many coordinates -/

section Continuity

variable {ι : Type*} [Fintype ι] [TopologicalSpace ι] [DiscreteTopology ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]

omit [Fintype ι] [DiscreteTopology ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Every iterate `σ^n`, `n ∈ ℤ`, of the shift is continuous. -/
theorem continuous_shift (n : ℤ) : Continuous (shift n : (ℤ → ι) → ℤ → ι) :=
  continuous_pi fun k => continuous_apply (n + k)

omit [Fintype ι] [DiscreteTopology ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The block map `x ↦ x_0 ⋯ x_{n-1}` is continuous. -/
theorem continuous_block (n : ℕ) : Continuous (block n : (ℤ → ι) → Fin n → ι) :=
  continuous_pi fun k => continuous_apply (k : ℤ)

/-- A function of the block `x_0 ⋯ x_{n-1}` is continuous and bounded, so its integral is a
weak-star continuous function of the measure. -/
theorem continuous_integral_comp_block {n : ℕ} (F : (Fin n → ι) → ℝ) :
    Continuous fun ν : ProbabilityMeasure (ℤ → ι) =>
      ∫ x, F (block n x) ∂(ν : Measure (ℤ → ι)) :=
  ProbabilityMeasure.continuous_integral_continuousMap
    (⟨fun x => F (block n x), continuous_of_discreteTopology.comp (continuous_block n)⟩ :
      C(ℤ → ι, ℝ))

/-- The measure of a cylinder is a weak-star continuous function of the measure: the cylinder is
clopen, so its indicator is a continuous function of the block `x_0 ⋯ x_{n-1}`. -/
theorem continuous_measureReal_cylinder {n : ℕ} (w : Fin n → ι) :
    Continuous fun ν : ProbabilityMeasure (ℤ → ι) => (ν : Measure (ℤ → ι)).real (cylinder w) := by
  classical
  refine (continuous_integral_comp_block fun v : Fin n → ι => if v = w then (1 : ℝ) else 0).congr
    fun ν => ?_
  exact (integral_comp_block_eq_sum (ν : Measure (ℤ → ι))
    fun v : Fin n → ι => if v = w then (1 : ℝ) else 0).trans (by simp)

/-- If `ν_k → ν` weakly, then `ν_k([w]) → ν([w])` for every word `w`. -/
theorem tendsto_measureReal_cylinder {γ : Type*} {F : Filter γ}
    {νs : γ → ProbabilityMeasure (ℤ → ι)} {ν : ProbabilityMeasure (ℤ → ι)}
    (h : Tendsto νs F (𝓝 ν)) {n : ℕ} (w : Fin n → ι) :
    Tendsto (fun k => (νs k : Measure (ℤ → ι)).real (cylinder w)) F
      (𝓝 ((ν : Measure (ℤ → ι)).real (cylinder w))) :=
  ((continuous_measureReal_cylinder w).tendsto ν).comp h

/-- The block entropy `H_ν(𝒫_0^{n-1})` is a weak-star continuous function of `ν`: it is a finite
sum of `negMulLog` of the measures of the cylinders of length `n`. -/
theorem continuous_blockEntropy (n : ℕ) :
    Continuous fun ν : ProbabilityMeasure (ℤ → ι) => blockEntropy (ν : Measure (ℤ → ι)) n :=
  continuous_finsetSum _ fun w _ =>
    Real.continuous_negMulLog.comp (continuous_measureReal_cylinder w)

namespace System

variable (S : System ι) (s : ℝ)

/-- The integral `∫ log φ^s(A_{𝐢|_n}) dν(𝐢)` is a weak-star continuous function of `ν`: the
integrand depends on the coordinates `i_0, …, i_{n-1}` only. -/
theorem continuous_integral_log_svf (n : ℕ) :
    Continuous fun ν : ProbabilityMeasure (ℤ → ι) =>
      ∫ x, Real.log (svf s (S.matWord (futureWord x n))) ∂(ν : Measure (ℤ → ι)) := by
  refine (continuous_integral_comp_block
    fun v : Fin n → ι => Real.log (svf s (S.matWord (List.ofFn v)))).congr fun ν => ?_
  simp only [futureWord_eq_ofFn_block]

/-- The average `n⁻¹ ∫ log φ^s(A_{𝐢|_n}) dν(𝐢)` is a weak-star continuous function of `ν`. -/
theorem continuous_energy_step (n : ℕ) :
    Continuous fun ν : ProbabilityMeasure (ℤ → ι) =>
      (∫ x, Real.log (svf s (S.matWord (futureWord x n))) ∂(ν : Measure (ℤ → ι))) / n :=
  (S.continuous_integral_log_svf s n).div_const _

end System

end Continuity

/-! ### The compact set of invariant measures -/

section Invariant

variable {ι : Type*} [Fintype ι] [TopologicalSpace ι] [DiscreteTopology ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]

variable (ι) in
/-- The set `ℳ_σ(Σ)` of `σ`-invariant Borel probability measures on `Σ`, tex line 745. -/
def InvariantMeasures : Set (ProbabilityMeasure (ℤ → ι)) :=
  {ν | MeasurePreserving (shift 1) (ν : Measure (ℤ → ι)) (ν : Measure (ℤ → ι))}

/-- A Borel probability measure on `Σ` is `σ`-invariant if and only if the integral of every
bounded continuous function does not change under `σ`. -/
theorem mem_invariantMeasures_iff {ν : ProbabilityMeasure (ℤ → ι)} :
    ν ∈ InvariantMeasures ι ↔ ∀ f : (ℤ → ι) →ᵇ ℝ,
      ∫ x, f (shift 1 x) ∂(ν : Measure (ℤ → ι)) = ∫ x, f x ∂(ν : Measure (ℤ → ι)) := by
  constructor
  · intro hν f
    have h := integral_comp_shift hν 1 (F := fun x => f x) f.continuous.measurable
    rwa [Nat.cast_one] at h
  · intro h
    refine ⟨measurable_shift 1, ?_⟩
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
    rw [integral_map (measurable_shift 1).aemeasurable
      f.continuous.measurable.aestronglyMeasurable]
    exact h f

/-- The set `ℳ_σ(Σ)` is closed in the weak-star topology: invariance is the vanishing of the
weak-star continuous functions `ν ↦ ∫ f ∘ σ dν - ∫ f dν`. -/
theorem isClosed_invariantMeasures : IsClosed (InvariantMeasures ι) := by
  have he : InvariantMeasures ι = ⋂ f : (ℤ → ι) →ᵇ ℝ,
      {ν : ProbabilityMeasure (ℤ → ι) |
        ∫ x, f (shift 1 x) ∂(ν : Measure (ℤ → ι)) = ∫ x, f x ∂(ν : Measure (ℤ → ι))} := by
    ext ν
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact mem_invariantMeasures_iff
  rw [he]
  refine isClosed_iInter fun f => isClosed_eq ?_ ?_
  · exact ProbabilityMeasure.continuous_integral_continuousMap
      (⟨fun x => f (shift 1 x), f.continuous.comp (continuous_shift 1)⟩ : C(ℤ → ι, ℝ))
  · exact ProbabilityMeasure.continuous_integral_continuousMap
      (⟨fun x => f x, f.continuous⟩ : C(ℤ → ι, ℝ))

/-- The set `ℳ_σ(Σ)` is compact: it is a closed subset of the compact space of Borel probability
measures on the compact space `Σ`. -/
theorem isCompact_invariantMeasures : IsCompact (InvariantMeasures ι) :=
  isClosed_invariantMeasures.isCompact

omit [Fintype ι] [TopologicalSpace ι] [DiscreteTopology ι] [MeasurableSingletonClass ι] in
/-- The set `ℳ_σ(Σ)` is non-empty: the Dirac mass at a fixed point of the shift is invariant. -/
theorem invariantMeasures_nonempty [Nonempty ι] : (InvariantMeasures ι).Nonempty := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine ⟨⟨Measure.dirac (fun _ : ℤ => i), inferInstance⟩, measurable_shift 1, ?_⟩
  show Measure.map (shift 1) (Measure.dirac (fun _ : ℤ => i)) = Measure.dirac fun _ : ℤ => i
  rw [Measure.map_dirac' (measurable_shift 1)]
  rfl

end Invariant

/-! ### The entropy and the energy as infima -/

/-- The limit of `u_n / n` for a sub-additive sequence `u` with `u_n / n` bounded below is the
infimum of `u_n / n` over `n ≥ 1`, by Fekete's lemma. -/
theorem limUnder_eq_iInf_of_subadditive {u : ℕ → ℝ} (h : Subadditive u)
    (hbdd : BddBelow (Set.range fun n : ℕ => u n / n)) :
    limUnder atTop (fun n : ℕ => u n / n) = ⨅ n : ℕ, u (n + 1) / (n + 1) := by
  have htend := h.tendsto_lim hbdd
  have hbdd' : BddBelow (Set.range fun n : ℕ => u (n + 1) / ((n : ℝ) + 1)) := by
    obtain ⟨c, hc⟩ := hbdd
    refine ⟨c, ?_⟩
    rintro _ ⟨n, rfl⟩
    have h' := hc (Set.mem_range_self (n + 1))
    push_cast at h'
    exact h'
  rw [htend.limUnder_eq]
  refine le_antisymm (le_ciInf fun n => ?_) (ge_of_tendsto htend ?_)
  · have h' := h.lim_le_div hbdd (n := n + 1) (Nat.succ_ne_zero n)
    push_cast at h'
    exact h'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h' := ciInf_le hbdd' m
    push_cast
    exact h'

section Infimum

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The Kolmogorov–Sinai entropy of an invariant measure is the infimum of the normalised block
entropies over `n ≥ 1`, since these are sub-additive. -/
theorem entropy_eq_iInf {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) :
    entropy μ = ⨅ n : ℕ, blockEntropy μ (n + 1) / (n + 1) :=
  limUnder_eq_iInf_of_subadditive (fun m n => blockEntropy_add_le hμ m n)
    ⟨0, by rintro _ ⟨n, rfl⟩; exact div_nonneg (blockEntropy_nonneg μ n) (Nat.cast_nonneg n)⟩

/-- The averages `∫ G(𝐢|_n) dμ(𝐢)` of a sub-additive function of words are sub-additive for an
invariant measure. -/
theorem subadditive_integral_futureWord {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) {G : List ι → ℝ}
    (hsub : ∀ w w', G (w ++ w') ≤ G w + G w') :
    Subadditive fun n : ℕ => ∫ x, G (futureWord x n) ∂μ := by
  intro m n
  have hint : Integrable (fun x => G (futureWord (shift m x) n)) μ :=
    (measurePreserving_shift_natCast hμ m).integrable_comp_of_integrable
      (integrable_comp_futureWord G n)
  calc ∫ x, G (futureWord x (m + n)) ∂μ
      ≤ ∫ x, (G (futureWord x m) + G (futureWord (shift m x) n)) ∂μ :=
        integral_mono (integrable_comp_futureWord G _)
          ((integrable_comp_futureWord G m).add hint) fun x => by
            rw [futureWord_add]; exact hsub _ _
    _ = ∫ x, G (futureWord x m) ∂μ + ∫ x, G (futureWord x n) ∂μ := by
        rw [integral_add (integrable_comp_futureWord G m) hint,
          integral_comp_shift hμ m (measurable_comp_futureWord G n)]

/-- The `s`-energy of an invariant measure is the infimum over `n ≥ 1` of the averages
`n⁻¹ ∫ log φ^s(A_{𝐢|_n}) dμ(𝐢)`, since `φ^s` is sub-multiplicative for `s ≥ 0`. -/
theorem System.energyLim_eq_iInf [Nonempty ι] (S : System ι) {μ : Measure (ℤ → ι)}
    [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ) {s : ℝ} (hs : 0 ≤ s) :
    S.energyLim s μ = ⨅ n : ℕ,
      (∫ x, Real.log (svf s (S.matWord (futureWord x (n + 1)))) ∂μ) / (n + 1) := by
  obtain ⟨δ, hδ⟩ := S.exists_ratioLowerBound
  refine limUnder_eq_iInf_of_subadditive (subadditive_integral_futureWord hμ
    (G := fun w => Real.log (svf s (S.matWord w))) (S.log_svf_matWord_append_le hs))
    ⟨min 0 (s * Real.log δ), ?_⟩
  rintro _ ⟨n, rfl⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (min_le_right _ _).trans (le_integral_futureWord_div (hδ.le_log_svf_matWord hs) hn)

end Infimum

/-! ### Upper semicontinuity and the maximum -/

section Maximum

variable {ι : Type*} [Fintype ι] [Nonempty ι] [TopologicalSpace ι] [DiscreteTopology ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Upper semicontinuity on a set depends only on the values of the function on that set. -/
theorem upperSemicontinuousOn_of_eqOn {α : Type*} [TopologicalSpace α] {f g : α → ℝ} {t : Set α}
    (hf : UpperSemicontinuousOn f t) (h : ∀ x ∈ t, f x = g x) : UpperSemicontinuousOn g t := by
  intro x hx y hy
  rw [← h x hx] at hy
  filter_upwards [hf x hx y hy, self_mem_nhdsWithin] with z hz hzt
  rwa [← h z hzt]

omit [Nonempty ι] in
/-- The Kolmogorov–Sinai entropy is upper semicontinuous on `ℳ_σ(Σ)`: it is the infimum of the
weak-star continuous functions `ν ↦ H_ν(𝒫_0^{n-1}) / n`, `n ≥ 1`. -/
theorem upperSemicontinuousOn_entropy :
    UpperSemicontinuousOn (fun ν : ProbabilityMeasure (ℤ → ι) => entropy (ν : Measure (ℤ → ι)))
      (InvariantMeasures ι) := by
  refine upperSemicontinuousOn_of_eqOn (f := fun ν : ProbabilityMeasure (ℤ → ι) =>
      ⨅ n : ℕ, blockEntropy (ν : Measure (ℤ → ι)) (n + 1) / ((n : ℝ) + 1)) ?_
    fun ν hν => (entropy_eq_iInf hν).symm
  refine upperSemicontinuousOn_ciInf (fun ν _ => ⟨0, ?_⟩) fun n =>
    ContinuousOn.upperSemicontinuousOn
      ((continuous_blockEntropy (n + 1)).div_const ((n : ℝ) + 1)).continuousOn
  rintro _ ⟨n, rfl⟩
  exact div_nonneg (blockEntropy_nonneg _ _) (by positivity)

/-- The `s`-energy is upper semicontinuous on `ℳ_σ(Σ)`: it is the infimum of the weak-star
continuous functions `ν ↦ n⁻¹ ∫ log φ^s(A_{𝐢|_n}) dν`, `n ≥ 1`. -/
theorem System.upperSemicontinuousOn_energyLim (S : System ι) {s : ℝ} (hs : 0 ≤ s) :
    UpperSemicontinuousOn
      (fun ν : ProbabilityMeasure (ℤ → ι) => S.energyLim s (ν : Measure (ℤ → ι)))
      (InvariantMeasures ι) := by
  obtain ⟨δ, hδ⟩ := S.exists_ratioLowerBound
  refine upperSemicontinuousOn_of_eqOn (f := fun ν : ProbabilityMeasure (ℤ → ι) => ⨅ n : ℕ,
      (∫ x, Real.log (svf s (S.matWord (futureWord x (n + 1)))) ∂(ν : Measure (ℤ → ι)))
        / ((n : ℝ) + 1)) ?_ fun ν hν => (S.energyLim_eq_iInf hν hs).symm
  refine upperSemicontinuousOn_ciInf (fun ν _ => ⟨s * Real.log δ, ?_⟩) fun n =>
    ContinuousOn.upperSemicontinuousOn
      ((S.continuous_integral_log_svf s (n + 1)).div_const ((n : ℝ) + 1)).continuousOn
  rintro _ ⟨n, rfl⟩
  have h := le_integral_futureWord_div (μ := (ν : Measure (ℤ → ι)))
    (hδ.le_log_svf_matWord hs) n.succ_pos
  push_cast at h
  exact h

/-- The supremum of `h_0(μ) + Λ(𝖠, μ, s)` over the invariant Borel probability measures on `Σ` is
attained, tex lines 2105 to 2106: both terms are upper semicontinuous on the non-empty compact
set `ℳ_σ(Σ)`. -/
theorem System.exists_maximiser (S : System ι) {s : ℝ} (hs : 0 ≤ s) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
      ∀ ν : Measure (ℤ → ι), MeasurePreserving (shift 1) ν ν → IsProbabilityMeasure ν →
        entropy ν + S.energyLim s ν ≤ entropy μ + S.energyLim s μ := by
  obtain ⟨μ, hμ, hmax⟩ := (upperSemicontinuousOn_entropy.add
    (S.upperSemicontinuousOn_energyLim hs)).exists_isMaxOn invariantMeasures_nonempty
    isCompact_invariantMeasures
  refine ⟨(μ : Measure (ℤ → ι)), inferInstance, hμ, fun ν hν hp => ?_⟩
  exact isMaxOn_iff.1 hmax (⟨ν, hp⟩ : ProbabilityMeasure (ℤ → ι)) hν

/-- The maximum of `h_0(μ) + Λ(𝖠, μ, s)` over `ℳ_σ(Σ)` is the greatest value of
`h_0 + Λ(𝖠, ·, s)` on `ℳ_σ(Σ)`. -/
theorem System.exists_isGreatest_entropy_add_energyLim (S : System ι) {s : ℝ} (hs : 0 ≤ s) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
      IsGreatest {c : ℝ | ∃ ν : Measure (ℤ → ι), IsProbabilityMeasure ν ∧
        MeasurePreserving (shift 1) ν ν ∧ c = entropy ν + S.energyLim s ν}
        (entropy μ + S.energyLim s μ) := by
  obtain ⟨μ, hp, hμ, hmax⟩ := S.exists_maximiser hs
  exact ⟨μ, hp, hμ, ⟨μ, hp, hμ, rfl⟩, by rintro _ ⟨ν, hpν, hν, rfl⟩; exact hmax ν hν hpν⟩

/-- The supremum of `h_0(μ) + Λ(𝖠, μ, s)` over `ℳ_σ(Σ)` is a maximum. -/
theorem System.exists_csSup_entropy_add_energyLim (S : System ι) {s : ℝ} (hs : 0 ≤ s) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
      sSup {c : ℝ | ∃ ν : Measure (ℤ → ι), IsProbabilityMeasure ν ∧
        MeasurePreserving (shift 1) ν ν ∧ c = entropy ν + S.energyLim s ν}
        = entropy μ + S.energyLim s μ := by
  obtain ⟨μ, hp, hμ, hgr⟩ := S.exists_isGreatest_entropy_add_energyLim hs
  exact ⟨μ, hp, hμ, hgr.csSup_eq⟩

end Maximum

end BoxLike
