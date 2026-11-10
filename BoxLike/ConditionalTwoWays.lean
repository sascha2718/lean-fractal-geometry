module

/-
The conditional measures of the average Gibbs measure: `thm:conditional_two_ways` of
`sec:average_gibbs`. On each of the four sets `τ(Σ^τ)`, `ω(Σ^τ)`, `ω(Σ^ω)`, `τ(Σ^ω)` the
conditional measure of `\overline{μ} = (μ_1 + μ_2)/2` given `\overline{ξ}_1` is the conditional
measure of one Gibbs measure, and it is the image under the coding of a planar conditional
measure of the equilibrium state.

The core is a transport statement on standard Borel spaces. Let `T : X → Y` be a Borel map with a
Borel left inverse `g` on a Borel set `E` that is a union of atoms of `ξ`, let `T` carry the atoms
of `ξ` in `E` onto the atoms of `η`, and let `ν|_{T(E)}` be a multiple of `T_*(μ|_E)`. Then
`ν_y^η = T_*μ_{g(y)}^ξ` for `ν`-almost every `y ∈ T(E)`. The kernel that equals `T_*μ_{g(y)}^ξ`
on `T(E)` and `ν_y^η` off `T(E)` is `\widehat{η}`-measurable and satisfies the defining identity
for `ν`, so the uniqueness of the disintegration, `condMeas_unique`, gives the statement. The
image `T(E)` is Borel by the Lusin–Souslin theorem.

* `measurable_saturated_of_forall_eq`, `eq_of_measurable_saturated`, `condMeas_eq_of_mem`: a
  Borel map is `\widehat{ξ}`-measurable when it is constant on atoms, and the conditional measures
  are constant on atoms.
* `condMeas_smul`: conditional measures do not change when the measure is scaled.
* `condMeas_transport`: the transport of conditional measures along `T`.
* `System.image_image_unCode_xiBar`: `T(\overline{T}(\overline{ξ}_1(T(𝐢)))) =
  \overline{ξ}_1(T(𝐢))` for `T ∈ {τ, ω}`.
* `System.condMeas_xiBar_eq_map`: the transport for `\overline{ξ}_1` and a coding `T ∈ {τ, ω}`.
* `System.conditional_two_ways_aux`: one of the four cases of `thm:conditional_two_ways`.
* `System.conditional_two_ways`: `thm:conditional_two_ways`.
-/
public import BoxLike.ConditionalLemmas
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.GibbsOrientation
public import BoxLike.MeasurablePartitions
public import BoxLike.PartitionIdentities
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

@[expose] public section

namespace BoxLike

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

universe u

/-! ### Maps that are constant on atoms -/

section Saturated

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A Borel map that is constant on the atoms of `ξ` is measurable with respect to the
`σ`-algebra `\widehat{ξ}` of `sec:conditional` (tex line 1680). -/
theorem measurable_saturated_of_forall_eq {Z : Type*} [MeasurableSpace Z] {ξ : Ω → Set Ω}
    {f : Ω → Z} (hf : Measurable f) (hconst : ∀ x y, y ∈ ξ x → f x = f y) :
    Measurable[saturated ξ] f :=
  fun U hU => ⟨hf hU, fun x y hxy => by simp only [mem_preimage, hconst x y hxy]⟩

/-- A `\widehat{ξ}`-measurable map into a space with measurable singletons is constant on the
atoms of `ξ` (`sec:conditional`, tex line 1680). -/
theorem eq_of_measurable_saturated {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {ξ : Ω → Set Ω} {f : Ω → Z} (hf : Measurable[saturated ξ] f) {x y : Ω} (hxy : y ∈ ξ x) :
    f x = f y := by
  have h := (hf (measurableSet_singleton (f x))).2 x y hxy
  simp only [mem_preimage, mem_singleton_iff, true_iff] at h
  exact h.symm

end Saturated

/-! ### Transport of conditional measures -/

section Transport

variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y]
  [StandardBorelSpace Y]

/-- The conditional measures `μ_x^ξ` of `sec:conditional` are constant on the atoms of `ξ`,
because `x ↦ μ_x^ξ(A)` is `\widehat{ξ}`-measurable for every Borel set `A` (tex lines 1675 to
1753). -/
theorem condMeas_eq_of_mem (μ : Measure X) [IsFiniteMeasure μ] {ξ : X → Set X} {x y : X}
    (hxy : y ∈ ξ x) : condMeas μ ξ x = condMeas μ ξ y :=
  Measure.ext fun _ hA => eq_of_measurable_saturated (measurable_condMeas μ ξ hA) hxy

/-- Conditional measures do not change when the measure is multiplied by a constant: the kernel
`μ_x^ξ` satisfies the defining identity of `sec:conditional` (tex lines 1675 to 1679) for `c μ`.
This is the passage between the restrictions of `eq:orientation-restrictions` and the normalised
restrictions of `eq:normalised-orientation-restrictions`. It holds for every map `ξ`. -/
theorem condMeas_smul (μ : Measure X) [IsFiniteMeasure μ] (ξ : X → Set X) (c : ℝ≥0) :
    ∀ᵐ x ∂c • μ, condMeas (c • μ) ξ x = condMeas μ ξ x := by
  have h := condMeas_unique (c • μ) ξ (condMeas μ ξ) (fun A hA => measurable_condMeas μ ξ hA)
    fun A B hA hB => by
      rw [Measure.restrict_smul, lintegral_smul_measure, setLIntegral_condMeas μ ξ hA hB,
        Measure.smul_apply]
  filter_upwards [h] with x hx using hx.symm

/-- The transport of conditional measures in the proof of `thm:conditional_two_ways`. Let `T` be
a Borel map with a Borel left inverse `g` on a Borel set `E`, let `E` be a union of atoms of `ξ`,
let `T` map the atom `ξ(x)` onto the atom `η(T(x))` for every `x ∈ E`, and let
`ν|_{T(E)} = c T_*(μ|_E)`. Then `ν_y^η = T_*μ_{g(y)}^ξ` for `ν`-almost every `y ∈ T(E)`.

The article normalises the two restrictions, identifies the conditional measures of `ν_{T(E)}`
with the kernel `K_y = T_*(μ_E)_{g(y)}^ξ` by uniqueness of the disintegration, and removes the
normalisation with `thm:conditional_measures_of_a_conditional_measure`. Here the kernel equal to
`T_*μ_{g(y)}^ξ` on `T(E)` and to `ν_y^η` off `T(E)` satisfies the defining identity for `ν`
itself, so one application of `condMeas_unique` suffices; the constant `c` is arbitrary and
`μ(E) > 0` is not needed. The image `T(E)` is Borel by the Lusin–Souslin theorem.
Depends on: `condMeas_unique`, `setLIntegral_condMeas`,
`measurableSet_saturated_of_forall_subset`. -/
theorem condMeas_transport {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (μ : Measure X) [IsFiniteMeasure μ] (ν : Measure Y) [IsFiniteMeasure ν] {ξ : X → Set X}
    {η : Y → Set Y} (hξ : IsMeasurablePartition ξ) (hη : IsMeasurablePartition η) {T : X → Y}
    (hT : Measurable T) {g : Y → X} (hg : Measurable g) {E : Set X} (hE : MeasurableSet E)
    (hgT : ∀ x ∈ E, g (T x) = x) (hsat : ∀ x ∈ E, ξ x ⊆ E)
    (hatom : ∀ x ∈ E, η (T x) = T '' ξ x) (c : R)
    (hres : ν.restrict (T '' E) = c • (μ.restrict E).map T) :
    ∀ᵐ y ∂ν, y ∈ T '' E → condMeas ν η y = (condMeas μ ξ (g y)).map T := by
  classical
  have hmX := saturated_le (Ω := X) ξ
  have hmY := saturated_le (Ω := Y) η
  obtain ⟨fξ, -, hfξ⟩ := hξ
  have hsymm : ∀ x x', x' ∈ ξ x → x ∈ ξ x' := fun x x' h =>
    (hfξ x' x).2 ((hfξ x x').1 h).symm
  -- The image `F = T(E)` is Borel, by the Lusin–Souslin theorem, and a union of atoms of `η`.
  have hinj : InjOn T E := fun x hx x' hx' h => by rw [← hgT x hx, ← hgT x' hx', h]
  have hF : MeasurableSet (T '' E) := hE.image_of_measurable_injOn hT hinj
  have hFsub : ∀ y ∈ T '' E, η y ⊆ T '' E := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hatom x hx]
    exact image_mono (hsat x hx)
  have hFsat : MeasurableSet[saturated η] (T '' E) :=
    measurableSet_saturated_of_forall_subset hη hF hFsub
  -- The kernel `K` of the proof of `thm:conditional_two_ways`, equal to `ν_y^η` off `F`.
  set K : Y → Measure Y := fun y =>
    if y ∈ T '' E then (condMeas μ ξ (g y)).map T else condMeas ν η y
  have hKF : ∀ y ∈ T '' E, K y = (condMeas μ ξ (g y)).map T := fun y hy => ite_eq_left hy
  have hKF' : ∀ y ∉ T '' E, K y = condMeas ν η y := fun y hy => ite_eq_right hy
  -- `K` is constant on the atoms of `η`, since `T` identifies the atoms of `ξ` in `E` with
  -- those of `η` in `F`.
  have hKconst : ∀ y y', y' ∈ η y → K y = K y' := by
    intro y y' hyy'
    by_cases hy : y ∈ T '' E
    · have hy' : y' ∈ T '' E := hFsub y hy hyy'
      rw [hKF y hy, hKF y' hy']
      obtain ⟨x, hx, rfl⟩ := hy
      rw [hatom x hx] at hyy'
      obtain ⟨x', hx', rfl⟩ := hyy'
      rw [hgT x hx, hgT x' (hsat x hx hx'), condMeas_eq_of_mem μ hx']
    · have hy' : y' ∉ T '' E := fun h => hy ((hFsat.2 y y' hyy').2 h)
      rw [hKF' y hy, hKF' y' hy', condMeas_eq_of_mem ν hyy']
  have hKm : ∀ A, MeasurableSet A → Measurable[saturated η] fun y => K y A := by
    intro A hA
    refine measurable_saturated_of_forall_eq ?_ fun y y' h => by rw [hKconst y y' h]
    have h1 : Measurable fun y => (condMeas μ ξ (g y)).map T A := by
      simp_rw [Measure.map_apply hT hA]
      exact ((measurable_condMeas μ ξ (hT hA)).mono hmX le_rfl).comp hg
    have h2 : Measurable fun y => condMeas ν η y A :=
      (measurable_condMeas ν η hA).mono hmY le_rfl
    have h3 : (fun y => K y A) = fun y =>
        if y ∈ T '' E then (condMeas μ ξ (g y)).map T A else condMeas ν η y A := by
      funext y
      by_cases hy : y ∈ T '' E
      · rw [hKF y hy, ite_eq_left hy]
      · rw [hKF' y hy, ite_eq_right hy]
    rw [h3]
    exact Measurable.ite hF h1 h2
  -- The defining identity `∫_B K_y(A) dν(y) = ν(A ∩ B)`, split along `F`.
  have hint : ∀ A B, MeasurableSet A → MeasurableSet[saturated η] B →
      ∫⁻ y in B, K y A ∂ν = ν (A ∩ B) := by
    intro A B hA hB
    have hBm : MeasurableSet B := hmY _ hB
    -- The set `T⁻¹(B) ∩ E` is a Borel union of atoms of `ξ`.
    have hBE : MeasurableSet[saturated ξ] (T ⁻¹' B ∩ E) := by
      refine ⟨(hT hBm).inter hE, ?_⟩
      have key : ∀ x x', x' ∈ ξ x → x ∈ T ⁻¹' B ∩ E → x' ∈ T ⁻¹' B ∩ E := by
        rintro x x' hxx' ⟨hxB, hxE⟩
        refine ⟨?_, hsat x hxE hxx'⟩
        have hmem : T x' ∈ η (T x) := by
          rw [hatom x hxE]
          exact mem_image_of_mem T hxx'
        exact (hB.2 (T x) (T x') hmem).1 hxB
      exact fun x x' hxx' => ⟨key x x' hxx', key x' x (hsymm x x' hxx')⟩
    have hφ : Measurable fun y => condMeas μ ξ (g y) (T ⁻¹' A) :=
      ((measurable_condMeas μ ξ (hT hA)).mono hmX le_rfl).comp hg
    have e1 : ∫⁻ y in B ∩ T '' E, K y A ∂ν = ν (A ∩ B ∩ T '' E) := by
      calc ∫⁻ y in B ∩ T '' E, K y A ∂ν
          = ∫⁻ y in B ∩ T '' E, condMeas μ ξ (g y) (T ⁻¹' A) ∂ν :=
            setLIntegral_congr_fun (hBm.inter hF) fun y hy => by
              simp only [hKF y hy.2, Measure.map_apply hT hA]
        _ = ∫⁻ y in B, condMeas μ ξ (g y) (T ⁻¹' A) ∂(ν.restrict (T '' E)) := by
            rw [Measure.restrict_restrict hBm]
        _ = c • ∫⁻ x in T ⁻¹' B ∩ E, condMeas μ ξ (g (T x)) (T ⁻¹' A) ∂μ := by
            rw [hres, Measure.restrict_smul, lintegral_smul_measure,
              setLIntegral_map hBm hφ hT, Measure.restrict_restrict (hT hBm)]
        _ = c • ∫⁻ x in T ⁻¹' B ∩ E, condMeas μ ξ x (T ⁻¹' A) ∂μ := by
            congr 1
            exact setLIntegral_congr_fun ((hT hBm).inter hE) fun x hx => by
              simp only [hgT x hx.2]
        _ = c • μ (T ⁻¹' A ∩ (T ⁻¹' B ∩ E)) := by
            rw [setLIntegral_condMeas μ ξ (hT hA) hBE]
        _ = ν (A ∩ B ∩ T '' E) := by
            rw [← Measure.restrict_apply (hA.inter hBm), hres, Measure.smul_apply,
              Measure.map_apply hT (hA.inter hBm), Measure.restrict_apply (hT (hA.inter hBm)),
              preimage_inter, inter_assoc]
    have e2 : ∫⁻ y in B \ T '' E, K y A ∂ν = ν ((A ∩ B) \ T '' E) := by
      have hBF : MeasurableSet[saturated η] (B \ T '' E) :=
        @MeasurableSet.diff _ (saturated η) _ _ hB hFsat
      have hcongr : ∫⁻ y in B \ T '' E, K y A ∂ν = ∫⁻ y in B \ T '' E, condMeas ν η y A ∂ν :=
        setLIntegral_congr_fun (hBm.diff hF) fun y hy => by simp only [hKF' y hy.2]
      rw [hcongr, setLIntegral_condMeas ν η hA hBF, inter_sdiff_assoc]
    rw [← lintegral_inter_add_sdiff _ B hF, e1, e2, measure_inter_add_sdiff _ hF]
  filter_upwards [condMeas_unique ν η K hKm hint] with y hy hyF
  rw [← hy, hKF y hyF]

end Transport

namespace System

/-! ### `thm:conditional_two_ways` -/

section AverageGibbs

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {s : ℝ}

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Proof of `thm:conditional_two_ways`: for a coding `T ∈ {τ, ω}` the atom
`\overline{ξ}_1(T(𝐢))` lies in `T(Σ)`, so `T` maps `\overline{T}(\overline{ξ}_1(T(𝐢)))` back onto
it. With `thm:partitions_xi1` this says that `T` identifies the planar partition on `E` with
`\overline{ξ}_1` on `T(E)`. -/
theorem image_image_unCode_xiBar {T : (ℤ → ι) → ℤ → ι × ZMod 2}
    (hT : T = tau S.o ∨ T = omega S.o) (x : ℤ → ι) :
    T '' (unCode '' S.xiBar 1 (T x)) = S.xiBar 1 (T x) := by
  have h : ∀ z ∈ S.xiBar 1 (T x), T (unCode z) = z := by
    rcases hT with rfl | rfl
    exacts [fun z hz => S.tau_unCode_of_mem_xiBar hz, fun z hz => S.omega_unCode_of_mem_xiBar hz]
  rw [image_image]
  exact (image_congr h).trans (image_id' _)

/-- Proof of `thm:conditional_two_ways`, the transport step for a coding `T ∈ {τ, ω}`: let `E` be
a Borel union of atoms of a measurable partition `ζ` of `Σ` with
`ζ(𝐢) = \overline{T}(\overline{ξ}_1(T(𝐢)))` for `𝐢 ∈ E`, as in `thm:partitions_xi1`, and let
`ν|_{T(E)} = c T_*(μ|_E)`. Then `ν_𝐣^{\overline{ξ}_1} = T_*μ_{\overline{T}(𝐣)}^ζ` for `ν`-almost
every `𝐣 ∈ T(E)`.
Depends on: `condMeas_transport`, `isMeasurablePartition_xiBar`. -/
theorem condMeas_xiBar_eq_map {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ] (ν : Measure (ℤ → ι × ZMod 2))
    [IsFiniteMeasure ν] {T : (ℤ → ι) → ℤ → ι × ZMod 2} (hT : T = tau S.o ∨ T = omega S.o)
    {E : Set (ℤ → ι)} (hE : MeasurableSet E) {ζ : (ℤ → ι) → Set (ℤ → ι)}
    (hζ : IsMeasurablePartition ζ) (hsat : ∀ x ∈ E, ζ x ⊆ E)
    (hatom : ∀ x ∈ E, ζ x = unCode '' S.xiBar 1 (T x)) (c : R)
    (hres : ν.restrict (T '' E) = c • (μ.restrict E).map T) :
    ∀ᵐ y ∂ν, y ∈ T '' E → condMeas ν (S.xiBar 1) y = (condMeas μ ζ (unCode y)).map T := by
  have hTm : Measurable T := by
    rcases hT with rfl | rfl
    exacts [measurable_tau S.o, measurable_omega S.o]
  have hun : ∀ x ∈ E, unCode (T x) = x := by
    rcases hT with rfl | rfl
    exacts [fun x _ => unCode_tau x, fun x _ => unCode_omega x]
  refine condMeas_transport μ ν hζ (S.isMeasurablePartition_xiBar 1) hTm measurable_unCode hE hun
    hsat (fun x hx => ?_) c hres
  rw [hatom x hx, S.image_image_unCode_xiBar hT]

/-- One of the four cases of `thm:conditional_two_ways`, for a coding `T ∈ {τ, ω}`, a Borel set
`E`, a planar partition `ζ` and the Gibbs measure `ν_k` of that case: if
`\overline{ν}|_{T(E)} = c T_*(μ|_E)` and `ν_k|_{T(E)} = T_*(μ|_E)`, then
`\overline{ν}_𝐣^{\overline{ξ}_1} = (ν_k)_𝐣^{\overline{ξ}_1} = T_*μ_{\overline{T}(𝐣)}^ζ` for
`\overline{ν}`-almost every `𝐣 ∈ T(E)`. The two restrictions are proportional, so they have the
same null sets in `T(E)`.
Depends on: `condMeas_xiBar_eq_map`. -/
theorem conditional_two_ways_aux {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ] (ν ν' : Measure (ℤ → ι × ZMod 2))
    [IsFiniteMeasure ν] [IsFiniteMeasure ν'] {T : (ℤ → ι) → ℤ → ι × ZMod 2}
    (hT : T = tau S.o ∨ T = omega S.o) {E : Set (ℤ → ι)} (hE : MeasurableSet E)
    {ζ : (ℤ → ι) → Set (ℤ → ι)} (hζ : IsMeasurablePartition ζ) (hsat : ∀ x ∈ E, ζ x ⊆ E)
    (hatom : ∀ x ∈ E, ζ x = unCode '' S.xiBar 1 (T x)) (c : R)
    (hν : ν.restrict (T '' E) = c • (μ.restrict E).map T)
    (hν' : ν'.restrict (T '' E) = (μ.restrict E).map T) :
    ∀ᵐ y ∂ν, y ∈ T '' E →
      condMeas ν (S.xiBar 1) y = condMeas ν' (S.xiBar 1) y ∧
      condMeas ν' (S.xiBar 1) y = (condMeas μ ζ (unCode y)).map T := by
  have hF : MeasurableSet (T '' E) := by
    rcases hT with rfl | rfl
    exacts [measurableSet_tau_image S.o hE, measurableSet_omega_image S.o hE]
  have h1 := S.condMeas_xiBar_eq_map μ ν hT hE hζ hsat hatom c hν
  have h2 := S.condMeas_xiBar_eq_map μ ν' hT hE hζ hsat hatom (1 : ℝ≥0∞)
    (by rw [one_smul, hν'])
  have h3 : ∀ᵐ y ∂ν, y ∈ T '' E →
      condMeas ν' (S.xiBar 1) y = (condMeas μ ζ (unCode y)).map T := by
    rw [← ae_restrict_iff' hF, hν, ← hν']
    exact Measure.ae_smul_measure ((ae_restrict_iff' hF).2 h2) c
  filter_upwards [h1, h3] with y hy1 hy3 hyF
  exact ⟨(hy1 hyF).trans (hy3 hyF).symm, hy3 hyF⟩

variable {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)}

/-- `thm:conditional_two_ways`: for `\overline{μ}`-almost every `𝐣 ∈ Σ_Z`, the conditional
measure `\overline{μ}_𝐣^{\overline{ξ}_1}` equals `(μ_1)_𝐣^{\overline{ξ}_1} = τ_*μ^{ξ_1}` on
`τ(Σ^τ)`, `(μ_2)_𝐣^{\overline{ξ}_1} = ω_*μ^{ξ_1^⊥}` on `ω(Σ^τ)`,
`(μ_1)_𝐣^{\overline{ξ}_1} = ω_*μ^{ξ_1}` on `ω(Σ^ω)` and
`(μ_2)_𝐣^{\overline{ξ}_1} = τ_*μ^{ξ_1^⊥}` on `τ(Σ^ω)`, the planar conditional measures being taken
at `\overline{τ}(𝐣)`, respectively `\overline{ω}(𝐣)`, which is `unCode 𝐣`.
This proof transports the unnormalised restrictions with one application of `condMeas_unique`
and does not use `thm:conditional_measures_of_a_conditional_measure`; the proof of the prose,
which normalises on the positive pieces and removes the restrictions by that lemma, is
`System.conditional_two_ways_normalised` of `BoxLike/Aligned/ConditionalTwoWays.lean`, the form
the later results use.
Depends on: `eq:orientation-restrictions` (`orientation_restrictions`),
`thm:gibbs_tau_omega_positive`, `thm:partitions_xi1`, `conditional_two_ways_aux`
(`condMeas_transport`, `condMeas_unique`). -/
theorem conditional_two_ways (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u})
    (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal) (hs0 : 0 < s) (hs2 : s < 2)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (heq : S.IsEquilibriumState s μ) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (hdec : S.GibbsDecomposition s μ μ₁ μ₂) :
    ∀ᵐ y ∂avgMeasure μ₁ μ₂,
      (y ∈ tau S.o '' S.SigmaTau μ →
        condMeas (avgMeasure μ₁ μ₂) (S.xiBar 1) y = condMeas μ₁ (S.xiBar 1) y ∧
        condMeas μ₁ (S.xiBar 1) y = (condMeas μ (S.xi μ 1) (unCode y)).map (tau S.o)) ∧
      (y ∈ omega S.o '' S.SigmaTau μ →
        condMeas (avgMeasure μ₁ μ₂) (S.xiBar 1) y = condMeas μ₂ (S.xiBar 1) y ∧
        condMeas μ₂ (S.xiBar 1) y = (condMeas μ (S.xiPerp μ) (unCode y)).map (omega S.o)) ∧
      (y ∈ omega S.o '' S.SigmaOmega μ →
        condMeas (avgMeasure μ₁ μ₂) (S.xiBar 1) y = condMeas μ₁ (S.xiBar 1) y ∧
        condMeas μ₁ (S.xiBar 1) y = (condMeas μ (S.xi μ 1) (unCode y)).map (omega S.o)) ∧
      (y ∈ tau S.o '' S.SigmaOmega μ →
        condMeas (avgMeasure μ₁ μ₂) (S.xiBar 1) y = condMeas μ₂ (S.xiBar 1) y ∧
        condMeas μ₂ (S.xiBar 1) y = (condMeas μ (S.xiPerp μ) (unCode y)).map (tau S.o)) := by
  have hlt := S.simple_lyapunov hms hrot hdiag.proximal hs0 hs2 μ hinv heq
  have hmτ := S.measurableSet_SigmaTau μ
  have hmω := S.measurableSet_SigmaOmega μ
  obtain ⟨-, ⟨z1, z2, z3, z4⟩, -⟩ :=
    S.gibbs_tau_omega_positive hms hfk hrot hdiag hs0 hs2 μ hinv herg heq hdec
  -- `eq:orientation-restrictions` for `\overline{μ}`.
  have hor := fun {T : (ℤ → ι) → ℤ → ι × ZMod 2} (hT : T = tau S.o ∨ T = omega S.o)
      {E : Set (ℤ → ι)} (hE : E = S.SigmaTau μ ∨ E = S.SigmaOmega μ) =>
    (S.orientation_restrictions hfk hrot hs0 hs2 μ hinv herg heq hdec hT hE).1
  -- The restriction of the Gibbs measure that charges `T(E)`.
  have hk₁ : ∀ {F : Set (ℤ → ι × ZMod 2)}, μ₂ F = 0 →
      (μ₁ + μ₂).restrict F = μ₁.restrict F := fun h => by
    rw [Measure.restrict_add, Measure.restrict_eq_zero.2 h, add_zero]
  have hk₂ : ∀ {F : Set (ℤ → ι × ZMod 2)}, μ₁ F = 0 →
      (μ₁ + μ₂).restrict F = μ₂.restrict F := fun h => by
    rw [Measure.restrict_add, Measure.restrict_eq_zero.2 h, zero_add]
  have c1 := S.conditional_two_ways_aux μ (avgMeasure μ₁ μ₂) μ₁ (Or.inl rfl) hmτ
    (S.isMeasurablePartition_xi μ 1) (fun x hx => (S.xi_one_of_mem_SigmaTau μ hx).2)
    (fun x hx => (S.xi_one_of_mem_SigmaTau μ hx).1) _ (hor (Or.inl rfl) (Or.inl rfl))
    ((hk₁ z1).symm.trans (hdec.restrict_tau_image hmτ))
  have c2 := S.conditional_two_ways_aux μ (avgMeasure μ₁ μ₂) μ₂ (Or.inr rfl) hmτ
    (S.isMeasurablePartition_xiPerp μ) (fun x hx => (S.xiPerp_of_mem_SigmaTau μ hx).2)
    (fun x hx => (S.xiPerp_of_mem_SigmaTau μ hx).1) _ (hor (Or.inr rfl) (Or.inl rfl))
    ((hk₂ z3).symm.trans (hdec.restrict_omega_image hmτ))
  have c3 := S.conditional_two_ways_aux μ (avgMeasure μ₁ μ₂) μ₁ (Or.inr rfl) hmω
    (S.isMeasurablePartition_xi μ 1) (fun x hx => (S.xi_one_of_mem_SigmaOmega μ hlt hx).2)
    (fun x hx => (S.xi_one_of_mem_SigmaOmega μ hlt hx).1) _ (hor (Or.inr rfl) (Or.inr rfl))
    ((hk₁ z2).symm.trans (hdec.restrict_omega_image hmω))
  have c4 := S.conditional_two_ways_aux μ (avgMeasure μ₁ μ₂) μ₂ (Or.inl rfl) hmω
    (S.isMeasurablePartition_xiPerp μ) (fun x hx => (S.xiPerp_of_mem_SigmaOmega μ hlt hx).2)
    (fun x hx => (S.xiPerp_of_mem_SigmaOmega μ hlt hx).1) _ (hor (Or.inl rfl) (Or.inr rfl))
    ((hk₂ z4).symm.trans (hdec.restrict_tau_image hmω))
  filter_upwards [c1, c2, c3, c4] with y h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end AverageGibbs

end System

end BoxLike
