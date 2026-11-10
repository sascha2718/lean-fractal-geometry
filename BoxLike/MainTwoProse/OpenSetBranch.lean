module

/-
The strong open set branch of the proof of `thm:main2` in `sec:dimension_result_proof`: the
words of the typical families are prefixed by a word `v` with `φ_v(X) ⊆ U` for a feasible open
set `U`: "The resulting attractor lies in `φ_v(X) ⊆ U`, so its first-level images lie in
pairwise disjoint level-`n` images of `U`. The subsystem therefore satisfies the strong
separation condition, which gives unique codings and hence `h_2(ν_n) = 0`." The conditional
entropy `h_2(ν_n)` is `q_n` in these docstrings.

* `System.subsystem_strongSeparation`: the subsystem of distinct words of equal length that all
  start with `v`, where `φ_v(X) ⊆ U`, satisfies the strong separation condition.
* `System.StrongSeparation.head_eq_of_proj_eq`, `System.StrongSeparation.future_eq_of_proj_eq`:
  strong separation gives unique coding, `π(𝐣) = π(𝐢) ⟹ 𝐣^+ = 𝐢^+`.
* `condEntropy_eq_zero_of_condMeas_eq_dirac`: Dirac conditional measures have zero conditional
  entropy.
* `System.IsHomDiag.xi_two_eq_singleton`,
  `System.IsHomDiag.dimEntropy_two_eq_zero_of_strongSeparation`: under unique coding the atom
  `ξ_2(𝐢)` is `{𝐢}`, the conditional measures are Dirac, and `h_2(ν_n) = 0`;
  `BoxLike/MainTwoProse/SubsystemEntropies.lean` has `q_n = 0` for the conditional entropy of
  the prose, which the endpoint uses.
-/
public import BoxLike.MainTwoProse.DiagonalSubsystem
public import BoxLike.Subsystem

@[expose] public section

namespace BoxLike

open MeasureTheory Set

namespace System

variable {ι κ : Type*}

/-! ### Strong separation of the selected subsystem -/

/-- The subsystem of the strong open set branch of the proof of `thm:main2` satisfies the strong
separation condition: its attractor lies in `φ_v(X) ⊆ U`, its first-level images lie in the
images `φ_{w_k}(U)` of the distinct words `w_k` of equal length, and these are pairwise disjoint
for a feasible open set `U`. -/
theorem subsystem_strongSeparation (S : System ι) [Finite ι] [Nonempty ι] [Finite κ]
    {U : Set (ℝ × ℝ)} (hsub : ∀ i, S.phi i '' U ⊆ U)
    (hdisj : Pairwise fun i j => Disjoint (S.phi i '' U) (S.phi j '' U)) {v : List ι}
    (hUv : S.phiWord v '' S.attractor ⊆ U) {w : κ → List ι} {hw : ∀ k, w k ≠ []}
    (hv : ∀ k, ∃ u, w k = v ++ u) (hlen : ∀ k k', (w k).length = (w k').length)
    (hinj : Function.Injective w) : (S.subsystem w hw).StrongSeparation := by
  have hatt : (S.subsystem w hw).attractor ⊆ U :=
    (S.subsystem_attractor_subset_image hv).trans hUv
  intro k k' hkk'
  rw [subsystem_phi, subsystem_phi]
  exact (S.pairwise_disjoint_image_phiWord hsub hdisj _ _ (hlen k k') (hinj.ne hkk')).mono
    (image_mono hatt) (image_mono hatt)

/-! ### Unique coding under strong separation -/

/-- Strong separation determines the first symbol: `π(𝐣) = π(𝐢)` forces `j_0 = i_0`, since
`π(𝐢) ∈ φ_{i_0}(X)` and the first-level images of `X` are pairwise disjoint. -/
theorem StrongSeparation.head_eq_of_proj_eq {T : System κ} [Finite κ] (hsep : T.StrongSeparation)
    {x y : ℤ → κ} (hxy : T.proj y = T.proj x) : y 0 = x 0 := by
  obtain ⟨r, M, hT⟩ := T.exists_bounds
  by_contra hne
  have hx : T.proj x ∈ T.phi (x 0) '' T.attractor :=
    ⟨T.proj (shift 1 x), ⟨_, rfl⟩, (hT.proj_eq x).symm⟩
  have hy : T.proj x ∈ T.phi (y 0) '' T.attractor :=
    hxy ▸ ⟨T.proj (shift 1 y), ⟨_, rfl⟩, (hT.proj_eq y).symm⟩
  exact Set.disjoint_left.1 (hsep hne) hy hx

/-- Strong separation gives unique coding (proof of `thm:main2`): `π(𝐣) = π(𝐢)` implies
`𝐣^+ = 𝐢^+`. The first symbols agree, `φ_{i_0}` is injective, and the shifted sequences have the
same projection. -/
theorem StrongSeparation.future_eq_of_proj_eq {T : System κ} [Finite κ]
    (hsep : T.StrongSeparation) {x y : ℤ → κ} (hxy : T.proj y = T.proj x) (k : ℕ) :
    y k = x k := by
  obtain ⟨r, M, hT⟩ := T.exists_bounds
  induction k generalizing x y with
  | zero => exact hsep.head_eq_of_proj_eq hxy
  | succ k ih =>
    have h0 := hsep.head_eq_of_proj_eq hxy
    have h1 : T.proj (shift 1 y) = T.proj (shift 1 x) := by
      apply T.injective_phi (x 0)
      rw [← hT.proj_eq x, ← h0, ← hT.proj_eq y, hxy]
    have h2 := ih h1
    have e : ((k + 1 : ℕ) : ℤ) = 1 + (k : ℤ) := by push_cast; ring
    simpa only [shift_apply, ← e] using h2

end System

/-! ### Zero conditional entropy -/

section Dirac

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- If the conditional measures of `ξ` are Dirac masses almost everywhere, then the conditional
entropy vanishes: `-log δ_𝐢([i_0]) = 0`. -/
theorem condEntropy_eq_zero_of_condMeas_eq_dirac (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    {ξ : (ℤ → α) → Set (ℤ → α)} (h : ∀ᵐ x ∂μ, condMeas μ ξ x = Measure.dirac x) :
    condEntropy μ ξ = 0 := by
  unfold condEntropy
  refine (integral_congr_ae ?_).trans (integral_zero _ _)
  filter_upwards [h] with x hx
  unfold condInfo
  rw [hx, measureReal_def, Measure.dirac_apply_of_mem (show x ∈ {y | y 0 = x 0} from rfl),
    ENNReal.toReal_one, Real.log_one, neg_zero]

end Dirac

namespace System.IsHomDiag

variable {κ : Type*} [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
  {T : System κ} {a b : ℝ} (hT : T.IsHomDiag a b)
include hT

/-- Under strong separation the atom `ξ_2(𝐢)` of a homogeneous diagonal system is `{𝐢}`: it fixes
the past, and unique coding fixes the future. -/
theorem xi_two_eq_singleton (hab : |b| ≤ |a|) {μ : Measure (ℤ → κ)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (hsep : T.StrongSeparation) (x : ℤ → κ) :
    T.xi μ 2 x = {x} := by
  rw [hT.xi_two_eq hab hinv]
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hp, hproj⟩
    funext k
    rcases lt_or_ge k 0 with hk | hk
    · exact hp k hk
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
      exact hsep.future_eq_of_proj_eq hproj m
  · rintro rfl
    exact ⟨fun _ _ => rfl, rfl⟩

/-- The open set branch of the proof of `thm:main2`: under strong separation of the subsystem
the conditional measures of `ξ_2` are Dirac, so `q_n = h_2(ν_n) = 0`. -/
theorem dimEntropy_two_eq_zero_of_strongSeparation [Nonempty κ] (hab : |b| ≤ |a|)
    (hsep : T.StrongSeparation) : T.dimEntropy (uniformBernoulli κ) 2 = 0 := by
  have hinv := measurePreserving_shift_uniformBernoulli (κ := κ) 1
  refine condEntropy_eq_zero_of_condMeas_eq_dirac _ ?_
  filter_upwards [condMeas_atom (uniformBernoulli κ)
    (T.isMeasurablePartition_xi (uniformBernoulli κ) 2)] with x hx
  rw [hT.xi_two_eq_singleton hab hinv hsep x] at hx
  exact eq_dirac_of_measure_singleton hx

end System.IsHomDiag

end BoxLike
