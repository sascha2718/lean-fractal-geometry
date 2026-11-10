module

/-
The strong open set condition and the vanishing of the `2`-dimensional entropy:
`thm:SOSC_h2_zero` of `sec:higher_dimensional_entropies`.

Let `U` be an open set of the strong open set condition. The self-affine set `X` lies in the
closure of `U`, and some cylinder `[w]` is coded into `U`. The cylinder has positive measure by
the Gibbs bounds, so almost every `𝐢` visits it infinitely often, by Poincaré recurrence and
ergodicity. For such `𝐢` every future tail `σ^k 𝐢` is coded into `U`, and the pairwise disjoint
open sets `φ_a(U)` then separate `π(𝐢)` from `π(𝐣)` for every `𝐣` with `𝐣^+ ≠ 𝐢^+`. Hence
`ξ_2(𝐢) = {𝐢}`, the conditional measure is the Dirac mass, and `thm:feng_entropy_zero` gives
`h_2(μ) = 0`.

* `System.phiInv`, `System.isOpen_image_phi`: `φ_i` is a homeomorphism of the plane, so it maps
  open sets to open sets.
* `System.Bounds.proj_eq_phiWord`: `π(𝐢) = φ_{𝐢|_n}(π(σ^n 𝐢))`.
* `System.attractor_subset_closure`: `X ⊆ \overline{U}` for a non-empty forward invariant `U`.
* `System.exists_cylinder_proj_mem`: a cylinder coded into `U`.
* `System.future_eq_of_proj_eq`: the geometric step, `π(𝐣) = π(𝐢)` implies `𝐣^+ = 𝐢^+` when
  every future tail of `𝐢` is coded into `U`.
* `System.HasGibbsBounds.measure_cylinder_pos_of_pos`: the Gibbs bounds give every cylinder of
  positive length positive measure.
* `ae_frequently_shift_mem`: an ergodic measure returns to a set of positive measure infinitely
  often from almost every point.
* `System.xi_two_subset_singleton`: `ξ_2(𝐢) = {𝐢}` on the set of the geometric step.
* `System.SOSC_h2_zero`: `thm:SOSC_h2_zero`.
-/
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.FengEntropy
public import BoxLike.General
public import BoxLike.SeparationConditions
public import BoxLike.SigmaMeasure
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set

universe u

namespace System

/-! ### The maps `φ_i` are open -/

section Geometry

variable {ι : Type u} (S : System ι)

/-- The inverse of the affine map `φ_i` of `sec:box_like_self_affine`. -/
noncomputable def phiInv (i : ι) (w : ℝ × ℝ) : ℝ × ℝ :=
  if S.o i = 0 then ((w.1 - (S.v i).1) / S.a i, (w.2 - (S.v i).2) / S.b i)
  else ((w.2 - (S.v i).2) / S.b i, (w.1 - (S.v i).1) / S.a i)

/-- `φ_i⁻¹ ∘ φ_i = id`. -/
theorem phiInv_phi (i : ι) (z : ℝ × ℝ) : S.phiInv i (S.phi i z) = z := by
  have ha := S.a_ne_zero i
  have hb := S.b_ne_zero i
  rcases zmod_two_cases (S.o i) with h | h
  · simp [phiInv, phi, h, ha, hb]
  · simp [phiInv, phi, h, ha, hb, show (1 : ZMod 2) + 1 = 0 from by decide]

/-- `φ_i ∘ φ_i⁻¹ = id`. -/
theorem phi_phiInv (i : ι) (w : ℝ × ℝ) : S.phi i (S.phiInv i w) = w := by
  have ha := S.a_ne_zero i
  have hb := S.b_ne_zero i
  rcases zmod_two_cases (S.o i) with h | h
  · simp [phiInv, phi, h, mul_div_cancel₀, ha, hb]
  · simp [phiInv, phi, h, mul_div_cancel₀, ha, hb, show (1 : ZMod 2) + 1 = 0 from by decide]

/-- The inverse of `φ_i` is continuous. -/
theorem continuous_phiInv (i : ι) : Continuous (S.phiInv i) := by
  unfold phiInv
  split_ifs <;> fun_prop

/-- `φ_i` maps open sets to open sets: it is an invertible affine map of the plane. This is used
in the proof of `thm:SOSC_h2_zero`, where `φ_{i_k}(U)` is open. -/
theorem isOpen_image_phi (i : ι) {U : Set (ℝ × ℝ)} (hU : IsOpen U) : IsOpen (S.phi i '' U) := by
  rw [image_eq_preimage_of_inverse (S.phiInv_phi i) (S.phi_phiInv i)]
  exact hU.preimage (S.continuous_phiInv i)

/-! ### Compositions along words -/

/-- The composition `φ_𝐢` is injective, as used in the proof of `thm:SOSC_h2_zero` to cancel a
common prefix. -/
theorem injective_phiWord (w : List ι) : Function.Injective (S.phiWord w) := by
  induction w with
  | nil => exact Function.injective_id
  | cons i w ih => exact (S.injective_phi i).comp ih

/-- Forward invariance along words: if `φ_i(U) ⊆ U` for all `i`, then `φ_𝐢(U) ⊆ U` for every
finite word `𝐢`. -/
theorem phiWord_mem {U : Set (ℝ × ℝ)} (hsub : ∀ i, S.phi i '' U ⊆ U) (w : List ι) {z : ℝ × ℝ}
    (hz : z ∈ U) : S.phiWord w z ∈ U := by
  induction w with
  | nil => exact hz
  | cons i w ih => exact hsub i ⟨_, ih, rfl⟩

/-- A point of the cylinder `[𝐢|_n]` has the prefix `𝐢|_n`. -/
theorem futureWord_eq_of_mem_cylinder {x y : ℤ → ι} {n : ℕ} (hy : y ∈ cylinder (block n x)) :
    futureWord y n = futureWord x n := by
  unfold futureWord
  refine List.map_congr_left fun k hk => ?_
  exact hy ⟨k, List.mem_range.1 hk⟩

variable {S} {r M : ℝ}

/-- Under uniform bounds `φ_𝐢` contracts distances by `r^{|𝐢|}`. -/
theorem Bounds.dist_phiWord_le (hS : S.Bounds r M) (w : List ι) (z z' : ℝ × ℝ) :
    dist (S.phiWord w z) (S.phiWord w z') ≤ r ^ w.length * dist z z' := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [phiWord_cons, Function.comp_apply, Function.comp_apply, List.length_cons, pow_succ',
      mul_assoc]
    exact (hS.dist_phi_le i _ _).trans (mul_le_mul_of_nonneg_left ih hS.r_nonneg)

/-- `π(𝐢) = φ_{𝐢|_n}(π(σ^n 𝐢))`, the iterated form of `π(𝐢) = φ_{i_0}(π(σ 𝐢))`. -/
theorem Bounds.proj_eq_phiWord (hS : S.Bounds r M) (x : ℤ → ι) (n : ℕ) :
    S.proj x = S.phiWord (futureWord x n) (S.proj (shift n x)) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [futureWord_succ', phiWord_cons, Function.comp_apply, hS.proj_eq x, ih (shift 1 x),
      shift_shift, Nat.cast_succ, add_comm]

/-- First step of the proof of `thm:SOSC_h2_zero`: `X ⊆ \overline{U}` for a non-empty set `U`
with `φ_i(U) ⊆ U` for all `i`. For `y ∈ U` the points `φ_{𝐣|_n}(y)` belong to `U` and converge
to `π(𝐣)`. -/
theorem Bounds.attractor_subset_closure (hS : S.Bounds r M) {U : Set (ℝ × ℝ)} (hne : U.Nonempty)
    (hsub : ∀ i, S.phi i '' U ⊆ U) : S.attractor ⊆ closure U := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hne
  have h0 : Tendsto (fun n => dist (S.phiWord (futureWord x n) 0) (S.phiWord (futureWord x n) y))
      atTop (𝓝 0) := by
    refine squeeze_zero (g := fun n => r ^ n * dist 0 y) (fun _ => dist_nonneg) (fun n => ?_) ?_
    · simpa using hS.dist_phiWord_le (futureWord x n) 0 y
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hS.r_nonneg hS.r_lt_one).mul_const
        (dist 0 y)
  exact mem_closure_of_tendsto ((hS.tendsto_phiWord x).congr_dist h0)
    (Eventually.of_forall fun n => S.phiWord_mem hsub _ hy)

variable (S)

/-- First step of the proof of `thm:SOSC_h2_zero`: `X ⊆ \overline{U}` for a non-empty set `U`
with `φ_i(U) ⊆ U` for all `i`. -/
theorem attractor_subset_closure [Finite ι] {U : Set (ℝ × ℝ)} (hne : U.Nonempty)
    (hsub : ∀ i, S.phi i '' U ⊆ U) : S.attractor ⊆ closure U := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  exact hS.attractor_subset_closure hne hsub

/-- Second step of the proof of `thm:SOSC_h2_zero`: if the open set `U` meets `X`, then some
cylinder `[w]` of positive length is coded into `U`, that is, `π([w]) = φ_w(X) ⊆ U`. The
cylinder images along an address of a point of `X ∩ U` contain the point and have diameters
tending to zero. -/
theorem exists_cylinder_proj_mem [Finite ι] {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hne : (U ∩ S.attractor).Nonempty) :
    ∃ (x : ℤ → ι) (n : ℕ), 0 < n ∧ ∀ y ∈ cylinder (block n x), S.proj y ∈ U := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  obtain ⟨_, hzU, x, rfl⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU _ hzU
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 S.isCompact_attractor.isBounded
  have hlim : Tendsto (fun n : ℕ => r ^ n * C) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hS.r_nonneg hS.r_lt_one).mul_const C
  obtain ⟨n, hn, hn0⟩ := ((hlim.eventually_lt_const hε).and (eventually_gt_atTop 0)).exists
  refine ⟨x, n, hn0, fun y hy => hball ?_⟩
  rw [Metric.mem_ball, hS.proj_eq_phiWord y n, hS.proj_eq_phiWord x n,
    futureWord_eq_of_mem_cylinder hy]
  refine lt_of_le_of_lt ((hS.dist_phiWord_le _ _ _).trans ?_) hn
  rw [length_futureWord]
  exact mul_le_mul_of_nonneg_left (hC ⟨_, rfl⟩ ⟨_, rfl⟩) (pow_nonneg hS.r_nonneg n)

/-! ### The geometric step -/

/-- If `π(σ^n 𝐢) ∈ U` for infinitely many `n ≥ 0` and `φ_i(U) ⊆ U` for all `i`, then every
future tail of `𝐢` is coded into `U`: `π(σ^k 𝐢) = φ_{i_k} ∘ ⋯ ∘ φ_{i_{n-1}}(π(σ^n 𝐢)) ∈ U` for
every `k ≥ 0`. -/
theorem proj_shift_mem_of_frequently [Finite ι] {U : Set (ℝ × ℝ)}
    (hsub : ∀ i, S.phi i '' U ⊆ U) {x : ℤ → ι}
    (h : ∃ᶠ n : ℕ in atTop, S.proj (shift n x) ∈ U) (k : ℕ) : S.proj (shift k x) ∈ U := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  obtain ⟨n, hn, hkn⟩ := (h.and_eventually (eventually_ge_atTop k)).exists
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkn
  rw [hS.proj_eq_phiWord (shift k x) m, shift_shift, ← Nat.cast_add]
  exact S.phiWord_mem hsub _ hn

/-- The separation step of the proof of `thm:SOSC_h2_zero`: if `π(σ 𝐢) ∈ U` and
`π(𝐣) = π(𝐢)`, then `j_0 = i_0`. Otherwise `π(𝐢)` lies in the open set `φ_{i_0}(U)` and in
`φ_{j_0}(X) ⊆ \overline{φ_{j_0}(U)}`, and these two sets are disjoint. -/
theorem head_eq_of_proj_eq [Finite ι] {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hne : U.Nonempty)
    (hsub : ∀ i, S.phi i '' U ⊆ U)
    (hdisj : Pairwise fun i j => Disjoint (S.phi i '' U) (S.phi j '' U)) {x y : ℤ → ι}
    (hx : S.proj (shift 1 x) ∈ U) (hxy : S.proj y = S.proj x) : y 0 = x 0 := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  by_contra hyx
  have h1 : S.proj x ∈ S.phi (x 0) '' U := ⟨_, hx, (hS.proj_eq x).symm⟩
  have h2 : S.proj x ∈ closure (S.phi (y 0) '' U) := by
    rw [← hxy, hS.proj_eq y]
    exact image_closure_subset_closure_image (S.continuous_phi (y 0))
      ⟨_, hS.attractor_subset_closure hne hsub ⟨_, rfl⟩, rfl⟩
  exact disjoint_left.1 ((hdisj (Ne.symm hyx)).closure_right (S.isOpen_image_phi _ hU)) h1 h2

/-- The geometric step of the proof of `thm:SOSC_h2_zero`, `(π^+)⁻¹({π(𝐢)}) = {𝐢^+}`: let `U` be
a non-empty open set with `φ_i(U) ⊆ U` for all `i` and pairwise disjoint images `φ_i(U)`. If
every future tail of `𝐢` is coded into `U` and `π(𝐣) = π(𝐢)`, then `𝐣^+ = 𝐢^+`. At the first
index `k` with `j_k ≠ i_k` the common prefix is cancelled by injectivity, and
`head_eq_of_proj_eq` applies to `σ^k 𝐢` and `σ^k 𝐣`. -/
theorem future_eq_of_proj_eq [Finite ι] {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hne : U.Nonempty)
    (hsub : ∀ i, S.phi i '' U ⊆ U)
    (hdisj : Pairwise fun i j => Disjoint (S.phi i '' U) (S.phi j '' U)) {x y : ℤ → ι}
    (hx : ∀ k : ℕ, S.proj (shift k x) ∈ U) (hxy : S.proj y = S.proj x) (k : ℕ) :
    y k = x k := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hw : futureWord y k = futureWord x k := by
      unfold futureWord
      exact List.map_congr_left fun m hm => ih m (List.mem_range.1 hm)
    have e : S.proj (shift k y) = S.proj (shift k x) := by
      apply S.injective_phiWord (futureWord x k)
      rw [← hS.proj_eq_phiWord x k, ← hw, ← hS.proj_eq_phiWord y k, hxy]
    have hx' : S.proj (shift 1 (shift k x)) ∈ U := by
      rw [shift_shift, ← Nat.cast_succ]
      exact hx (k + 1)
    simpa using S.head_eq_of_proj_eq hU hne hsub hdisj hx' e

end Geometry

end System

/-! ### Recurrence -/

/-- An ergodic map of a probability space returns to a set of positive measure infinitely often
from almost every point. By Poincaré recurrence almost every point of `s` returns to `s`
infinitely often, and the set of points that visit `s` infinitely often is invariant, so it has
full measure. The proof of `thm:SOSC_h2_zero` uses this recurrence for a word of positive
measure (tex lines 3336 to 3337), which it attributes to ergodicity. -/
theorem ae_frequently_iterate_mem {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {T : X → X} (hT : Ergodic T μ) {s : Set X} (hs : MeasurableSet s)
    (hpos : μ s ≠ 0) : ∀ᵐ x ∂μ, ∃ᶠ n in atTop, T^[n] x ∈ s := by
  have hAm : MeasurableSet {x | ∃ᶠ n in atTop, T^[n] x ∈ s} := by
    have e : {x | ∃ᶠ n in atTop, T^[n] x ∈ s} = limsup (fun n => T^[n] ⁻¹' s) atTop := by
      ext x
      simp [mem_limsup_iff_frequently_mem]
    rw [e]
    exact MeasurableSet.measurableSet_limsup fun n => (hT.measurable.iterate n) hs
  have hinv : T ⁻¹' {x | ∃ᶠ n in atTop, T^[n] x ∈ s} = {x | ∃ᶠ n in atTop, T^[n] x ∈ s} := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq]
    conv_rhs => rw [← map_add_atTop_eq_nat 1, frequently_map]
    simp only [Function.iterate_succ_apply]
  rcases hT.toPreErgodic.ae_mem_or_ae_notMem hAm hinv with h | h
  · exact h
  · refine (hpos (measure_eq_zero_iff_ae_notMem.2 ?_)).elim
    filter_upwards [h, hT.toMeasurePreserving.conservative.ae_mem_imp_frequently_image_mem
      hs.nullMeasurableSet] with x hx hx' hxs
    exact hx (hx' hxs)

/-- An ergodic measure on the two-sided shift space visits a set of positive measure along
`σ^n 𝐢`, `n ≥ 0`, infinitely often, for almost every `𝐢`. -/
theorem ae_frequently_shift_mem {α : Type*} [MeasurableSpace α] {μ : Measure (ℤ → α)}
    [IsProbabilityMeasure μ] (herg : Ergodic (shift 1) μ) {s : Set (ℤ → α)}
    (hs : MeasurableSet s) (hpos : μ s ≠ 0) :
    ∀ᵐ x ∂μ, ∃ᶠ n : ℕ in atTop, shift n x ∈ s := by
  filter_upwards [ae_frequently_iterate_mem herg hs hpos] with x hx
  simpa only [iterate_shift_one] using hx

/-- A probability measure that gives mass one to a point is the Dirac mass at that point. -/
theorem eq_dirac_of_measure_singleton {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] {ν : Measure Ω} [IsProbabilityMeasure ν] {x : Ω}
    (h : ν {x} = 1) : ν = Measure.dirac x := by
  have hnull : ν ({x} : Set Ω)ᶜ = 0 := (prob_compl_eq_zero_iff (measurableSet_singleton x)).2 h
  have hae : ∀ᵐ y ∂ν, y ∈ ({x} : Set Ω) :=
    (measure_eq_zero_iff_ae_notMem.1 hnull).mono fun y hy => not_not.1 hy
  rw [← Measure.restrict_eq_self_of_ae_mem hae, Measure.restrict_singleton, h, one_smul]

namespace System

/-! ### The atoms of `ξ_2` -/

section Atom

variable {ι : Type u} [MeasurableSpace ι] (S : System ι)

/-- The last step of the proof of `thm:SOSC_h2_zero`: if `𝐢 ∈ Σ'` and `π(𝐣) = π(𝐢)` implies
`𝐣^+ = 𝐢^+`, then `ξ_2(𝐢) = {𝐢}`, since `V_𝐢^2 = {0}` and the atom fixes the past. -/
theorem xi_two_subset_singleton (μ : Measure (ℤ → ι)) {x : ℤ → ι} (hx : x ∈ S.SigmaPrime μ)
    (hfut : ∀ y, S.proj y = S.proj x → ∀ k : ℕ, y k = x k) : S.xi μ 2 x ⊆ {x} := by
  unfold xi
  rw [atomsOn_of_mem hx]
  rintro y ⟨⟨hp, hv⟩, -⟩
  rw [mem_oseledets_iff] at hv
  have hxy : S.proj y = S.proj x := by
    rcases hv with h0 | ⟨h1, -⟩ | ⟨-, e⟩
    · omega
    · omega
    · exact e
  refine funext fun k => ?_
  rcases lt_or_ge k 0 with hk | hk
  · exact hp k hk
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    exact hfut y hxy m

end Atom

/-! ### `thm:SOSC_h2_zero` -/

section Entropy

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {s : ℝ}

omit [MeasurableSingletonClass ι] in
/-- A measure with the Gibbs bounds of `thm:irred_eq_state` charges every cylinder `[w]` of
positive length: it is fully supported. -/
theorem HasGibbsBounds.measure_cylinder_pos_of_pos {S : System ι} {μ : Measure (ℤ → ι)}
    (h : S.HasGibbsBounds s μ) {n : ℕ} (hn : 0 < n) (w : Fin n → ι) : 0 < μ (cylinder w) := by
  obtain ⟨C, hC, hb⟩ := h
  have hpos : 0 < μ.real (cylinder w) :=
    lt_of_lt_of_le (mul_pos (inv_pos.2 (lt_of_lt_of_le one_pos hC))
      (mul_pos (Real.exp_pos _) (S.svf_matWord_pos s _))) (hb n hn w).1
  rw [measureReal_def] at hpos
  exact (ENNReal.toReal_pos_iff.1 hpos).1

/-- `thm:SOSC_h2_zero`: under the strong open set condition, `h_2(μ) = 0` for the ergodic
`s`-equilibrium state, `0 < s < 2`, of a proximal box-like tuple with rotations. Neither
projective exponential separation nor a proximal diagonal generator is assumed.
Depends on: `thm:irred_eq_state` (ergodicity as `herg`; full support through the Gibbs bounds
of `EquilibriumGibbsStatement`), `eq:simple_lyapunov`, `measure_SigmaPrime_compl`,
`ae_frequently_shift_mem` (the recurrence that the article attributes to ergodicity),
`System.Bounds.proj_eq`, `condMeas_atom`, `thm:feng_entropy_zero`,
`eq:ergodic_entropy_constant`. -/
theorem SOSC_h2_zero (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfi : FengInfoSum.{u}) (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsosc : S.StrongOpenSet) (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (heq : S.IsEquilibriumState s μ) :
    S.dimEntropy μ 2 = 0 := by
  obtain ⟨U, hU, hne, hsub, hdisj⟩ := hsosc
  have hlt := S.simple_lyapunov hms hrot hprox hs0 hs2 μ hinv heq
  have hgibbs := hfk S hrot hs0 hs2 μ hinv heq
  -- A cylinder of positive measure coded into `U`, visited infinitely often.
  obtain ⟨x₀, n, hn, hcyl⟩ := S.exists_cylinder_proj_mem hU hne
  have hrec := ae_frequently_shift_mem herg (measurableSet_cylinder (block n x₀))
    (hgibbs.measure_cylinder_pos_of_pos hn (block n x₀)).ne'
  -- Hence `ξ_2(𝐢) = {𝐢}` and `μ_𝐢^{ξ_2} = δ_𝐢` almost everywhere.
  have hsing : ∀ᵐ x ∂μ, S.xi μ 2 x ⊆ {x} := by
    filter_upwards [hrec, measure_eq_zero_iff_ae_notMem.1 (S.measure_SigmaPrime_compl μ hinv herg)]
      with x hx hx'
    have htail : ∀ k : ℕ, S.proj (shift k x) ∈ U :=
      S.proj_shift_mem_of_frequently hsub (hx.mono fun m hm => hcyl _ hm)
    exact S.xi_two_subset_singleton μ (not_not.1 hx') fun y hxy =>
      S.future_eq_of_proj_eq hU (hne.mono inter_subset_left) hsub hdisj htail hxy
  have hdirac : ∀ᵐ x ∂μ, condMeas μ (S.xi μ 2) x = Measure.dirac x := by
    filter_upwards [condMeas_eq_one_of_atom_subset μ (S.isMeasurablePartition_xi μ 2) hsing]
      with x hx
    exact eq_dirac_of_measure_singleton hx
  -- `thm:feng_entropy_zero` and `eq:ergodic_entropy_constant`.
  have hzero : ∀ᵐ _ ∂μ, S.dimEntropy μ 2 = 0 := by
    filter_upwards [S.feng_entropy_zero hfi μ hinv herg hlt 2,
      localEntropy_ae_eq μ herg (S.xi μ 2), hdirac] with x h1 h2 h3
    exact h2.symm.trans (h1.2 h3)
  exact hzero.exists.elim fun _ h => h

end Entropy

end System

end BoxLike
