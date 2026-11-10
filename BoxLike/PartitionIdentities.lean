module

/-
The behaviour of `Σ^τ`, `Σ^ω` and `Σ'` under the shift (`sec:lyapunov_exponents`, tex lines 1521
to 1599, and `eq:sigma_tau_omega_positive_eq_measure1` in the proof of
`thm:sigma_tau_omega_positive_eq_measure` in `sec:normalisation`), and the identification of the
planar partitions `ξ_1`, `ξ_1^⊥` with the scalar partition `\overline{ξ}_1` through the codings
`τ`, `ω` at the end of `sec:entropies` (`thm:partitions_xi1`, `thm:partition_tau_conj`).

* `pastWord_shift_one`, `System.hasBackRate_shift_one`: appending one symbol to the past keeps
  the backward growth rate of `eq:lyapunov_exponent_gsystem`.
* `System.shift_mem_SigmaTau_iff`, `System.shift_mem_SigmaPrime_iff`:
  `eq:sigma_tau_omega_positive_eq_measure1` and `σ(Σ') = Σ'`.
* `samePast_tau`, `samePast_omega`, `tau_unCode_of_samePast`, `omega_unCode_of_samePast`: the
  lifted past determines the axis at time `0`, so `T ∈ {τ, ω}` maps the sequences with past
  `𝐢^-` onto the sequences of `Σ_Z` with past `T(𝐢)^-`.
* `System.image_unCode_xiBar_tau`, `System.image_unCode_xiBar_omega`: the sets
  `\overline{τ}(\overline{ξ}_1(τ(𝐢)))` and `\overline{ω}(\overline{ξ}_1(ω(𝐢)))` in planar terms.
* `System.xi_one_eq`, `System.xiPerp_eq`: the atoms `ξ_1(𝐢)`, `ξ_1^⊥(𝐢)` for `𝐢 ∈ Σ'` through
  one coordinate of `π`.
* `System.xi_one_of_mem_SigmaTau`, `System.xiPerp_of_mem_SigmaTau`,
  `System.xi_one_of_mem_SigmaOmega`, `System.xiPerp_of_mem_SigmaOmega`: the four cases of
  `thm:partitions_xi1` under the hypotheses their proofs use.
* `System.partitions_xi1`: `thm:partitions_xi1`.
* `tau_mem_cylinder_block_iff`, `omega_mem_cylinder_block_iff`: the identity
  `T⁻¹(\overline{𝒫}_0^{n-1}(T(𝐢)) ∩ T(Σ)) = 𝒫_0^{n-1}(𝐢)` of the proof of
  `thm:partition_tau_conj`.
* `System.partition_tau_conj`: `thm:partition_tau_conj`.
-/
public import BoxLike.DimPartitions
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set

/-! ### The backward rate under the shift -/

/-- The word `i_{-n} ⋯ i_{-1} i_0` of the past of `σ(𝐢)` is the word `i_{-n} ⋯ i_{-1}` of the
past of `𝐢` followed by `i_0`. In `sec:lyapunov_exponents`, tex lines 1521 to 1522, this is
"appending one matrix on the right". -/
theorem pastWord_shift_one {α : Type*} (y : ℤ → α) (n : ℕ) :
    pastWord (shift 1 y) (n + 1) = pastWord y n ++ [y 0] := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (1 : ℤ) + -(((n + 1 : ℕ) : ℤ) + 1) = -((n : ℤ) + 1) := by push_cast; ring
    rw [pastWord_succ, ih, pastWord_succ, shift_apply, List.cons_append, e]

/-- Adding a constant to the numerator and shifting the index by one do not change a limit of the
form `lim_n n⁻¹ f(n)`, as for the growth rates of `eq:lyapunov_exponent_gsystem`. -/
theorem tendsto_add_div_succ_iff (f : ℕ → ℝ) (c l : ℝ) :
    Tendsto (fun n : ℕ => (f n + c) / ((n : ℝ) + 1)) atTop (𝓝 l) ↔
      Tendsto (fun n : ℕ => f n / n) atTop (𝓝 l) := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) :=
    tendsto_natCast_div_add_atTop 1
  have h2 : Tendsto (fun n : ℕ => c / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul c
  have h3 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
    simpa using h1.inv₀ one_ne_zero
  have h4 : Tendsto (fun n : ℕ => c / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat c
  constructor
  · intro h
    have key := (h.mul h3).sub h4
    rw [mul_one, sub_zero] at key
    refine key.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    have hn'' : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  · intro h
    have key := (h.mul h1).add h2
    rw [mul_one, add_zero] at key
    refine key.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    have hn'' : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp

namespace System

section BackRate

variable {ι : Type*} (S : System ι)

/-- The backward growth rate of `eq:lyapunov_exponent_gsystem` along `σ(𝐣)` exists exactly when
it exists along `𝐣`, with the same value: the two products differ by the factor `g'_{j_0}`. This
holds for every sequence over `ι × ZMod 2`. -/
theorem hasBackRate_shift_one (y : ℤ → ι × ZMod 2) (l : ℝ) :
    S.HasBackRate (shift 1 y) l ↔ S.HasBackRate y l := by
  unfold HasBackRate
  rw [← tendsto_add_atTop_iff_nat 1,
    ← tendsto_add_div_succ_iff _ (Real.log |S.ratio (y 0)|) l]
  refine tendsto_congr fun n => ?_
  rw [pastWord_shift_one, gDeriv_append, gDeriv_cons, gDeriv_nil, mul_one, abs_mul,
    Real.log_mul (abs_ne_zero.2 (S.gDeriv_ne_zero _)) (abs_ne_zero.2 (S.ratio_ne_zero _))]
  push_cast
  rfl

end BackRate

section Shift

variable {ι : Type*} [MeasurableSpace ι] (S : System ι)

/-- `eq:sigma_tau_omega_positive_eq_measure1` and the shift-invariance of `Σ'`
(`sec:lyapunov_exponents`, tex lines 1521 to 1522): appending `A_{i_0}` on the right keeps the
two backward rates when `A_{i_0}` is diagonal and exchanges them when it is anti-diagonal.
Depends on: `eq:tau_omega_sigma_commutative1`, through `thm:tau_omega_sigma_commutative`. -/
theorem shift_mem_SigmaTau_iff (μ : Measure (ℤ → ι)) (x : ℤ → ι) :
    (shift 1 x ∈ S.SigmaTau μ ↔
      (S.o (x 0) = 0 ∧ x ∈ S.SigmaTau μ) ∨ (S.o (x 0) = 1 ∧ x ∈ S.SigmaOmega μ)) ∧
    (shift 1 x ∈ S.SigmaOmega μ ↔
      (S.o (x 0) = 0 ∧ x ∈ S.SigmaOmega μ) ∨ (S.o (x 0) = 1 ∧ x ∈ S.SigmaTau μ)) := by
  have he : eps S.o x 1 = S.o (x 0) := by
    have h := eps_add_one S.o x 0
    rwa [zero_add, eps_zero, zero_add] at h
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  rcases zmod_two_cases (S.o (x 0)) with h | h
  · rw [h] at he
    simp only [SigmaTau, SigmaOmega, mem_ofPred_eq, tau_shift_of_eps_eq_zero he,
      omega_shift_of_eps_eq_zero he, hasBackRate_shift_one, h, h01, true_and, false_and,
      or_false, and_self]
  · rw [h] at he
    simp only [SigmaTau, SigmaOmega, mem_ofPred_eq, tau_shift_of_eps_eq_one he,
      omega_shift_of_eps_eq_one he, hasBackRate_shift_one, h, h01.symm, true_and, false_and,
      false_or]
    exact ⟨and_comm, and_comm⟩

/-- `σ(Σ') = Σ'` (`sec:lyapunov_exponents`, tex lines 1521 to 1522): the set `Σ'` is
shift-invariant. -/
theorem shift_mem_SigmaPrime_iff (μ : Measure (ℤ → ι)) (x : ℤ → ι) :
    shift 1 x ∈ S.SigmaPrime μ ↔ x ∈ S.SigmaPrime μ := by
  obtain ⟨h1, h2⟩ := S.shift_mem_SigmaTau_iff μ x
  simp only [SigmaPrime, mem_union, h1, h2]
  rcases zmod_two_cases (S.o (x 0)) with h | h <;> simp [h, or_comm]

end Shift

end System

/-! ### The codings and the past -/

section Coding

variable {ι : Type*} {o : ι → ZMod 2}

/-- The cocycle `ε_n(𝐢)` of `eq:def_of_eps_mod2` at a time `n ≤ 0` depends only on the past
`𝐢^-`. -/
theorem eps_eq_of_samePast (o : ι → ZMod 2) {x y : ℤ → ι} (h : SamePast x y) {n : ℤ}
    (hn : n ≤ 0) : eps o x n = eps o y n := by
  rcases n with n | n
  · have hn' : (n : ℤ) ≤ 0 := hn
    have h0 : n = 0 := by omega
    subst h0
    rw [Int.ofNat_eq_natCast, Nat.cast_zero, eps_zero, eps_zero]
  · rw [eps_negSucc, eps_negSucc]
    exact Finset.sum_congr rfl fun j _ => by rw [h _ (by omega)]

/-- The coding `τ` of `eq:def_of_tau_omega` maps sequences with the same past to sequences with
the same past (proof of `thm:partitions_xi1`). -/
theorem samePast_tau (o : ι → ZMod 2) {x y : ℤ → ι} (h : SamePast x y) :
    SamePast (tau o x) (tau o y) := fun n hn => by
  rw [tau_apply, tau_apply, h n hn, eps_eq_of_samePast o h hn.le]

/-- The coding `ω` of `eq:def_of_tau_omega` maps sequences with the same past to sequences with
the same past (proof of `thm:partitions_xi1`). -/
theorem samePast_omega (o : ι → ZMod 2) {x y : ℤ → ι} (h : SamePast x y) :
    SamePast (omega o x) (omega o y) := fun n hn => by
  rw [omega_apply, omega_apply, h n hn, eps_eq_of_samePast o h hn.le]

/-- The inverse `\overline{τ}`, `\overline{ω}` of the codings of `eq:def_of_tau_omega` maps
sequences with the same past to sequences with the same past. -/
theorem samePast_unCode {z w : ℤ → ι × ZMod 2} (h : SamePast z w) :
    SamePast (unCode z) (unCode w) := fun n hn => congrArg Prod.fst (h n hn)

/-- Proof of `thm:partitions_xi1`: "the lifted past determines the orientation at coordinate
zero". A point of `Σ_Z` with the past of `τ(𝐢)` lies in `τ(Σ)`, by `eq:tau_omega_partition`. -/
theorem tau_unCode_of_samePast {x : ℤ → ι} {z : ℤ → ι × ZMod 2} (hz : z ∈ subshift o)
    (h : SamePast z (tau o x)) : tau o (unCode z) = z := by
  have h0 : (z 0).2 = 0 := by
    have h1 := hz (-1)
    have h2 := eps_add_one o x (-1)
    rw [show (-1 : ℤ) + 1 = 0 by norm_num] at h1 h2
    rw [Trans, h (-1) (by norm_num), tau_apply] at h1
    rw [h1, ← h2, eps_zero]
  have hr : z ∈ Set.range (tau o) := by
    rw [range_tau]
    exact ⟨hz, h0⟩
  obtain ⟨x', rfl⟩ := hr
  rw [unCode_tau]

/-- Proof of `thm:partitions_xi1`: a point of `Σ_Z` with the past of `ω(𝐢)` lies in `ω(Σ)`, by
`eq:tau_omega_partition`. -/
theorem omega_unCode_of_samePast {x : ℤ → ι} {z : ℤ → ι × ZMod 2} (hz : z ∈ subshift o)
    (h : SamePast z (omega o x)) : omega o (unCode z) = z := by
  have h0 : (z 0).2 = 1 := by
    have h1 := hz (-1)
    have h2 := eps_add_one o x (-1)
    rw [show (-1 : ℤ) + 1 = 0 by norm_num] at h1 h2
    rw [Trans, h (-1) (by norm_num), omega_apply] at h1
    rw [h1, add_right_comm, ← h2, eps_zero, zero_add]
  have hr : z ∈ Set.range (omega o) := by
    rw [range_omega]
    exact ⟨hz, h0⟩
  obtain ⟨x', rfl⟩ := hr
  rw [unCode_omega]

/-- Proof of `thm:partition_tau_conj`, for `T = τ`: by `eq:def_of_tau_omega`, `i_k = j_k` for
`0 ≤ k < n` exactly when `τ_k(𝐢) = τ_k(𝐣)` for `0 ≤ k < n`, that is,
`τ⁻¹(\overline{𝒫}_0^{n-1}(τ(𝐢))) = 𝒫_0^{n-1}(𝐢)`. -/
theorem tau_mem_cylinder_block_iff (o : ι → ZMod 2) (x y : ℤ → ι) (n : ℕ) :
    tau o y ∈ cylinder (block n (tau o x)) ↔ y ∈ cylinder (block n x) := by
  simp only [mem_cylinder, block_apply, tau_apply, Prod.mk.injEq]
  refine ⟨fun h k => (h k).1, fun h k => ⟨h k, ?_⟩⟩
  rw [eps_natCast, eps_natCast]
  refine Finset.sum_congr rfl fun j hj => ?_
  exact congrArg o (h ⟨j, (Finset.mem_range.1 hj).trans k.2⟩)

/-- Proof of `thm:partition_tau_conj`, for `T = ω`:
`ω⁻¹(\overline{𝒫}_0^{n-1}(ω(𝐢))) = 𝒫_0^{n-1}(𝐢)`, by `eq:def_of_tau_omega`. -/
theorem omega_mem_cylinder_block_iff (o : ι → ZMod 2) (x y : ℤ → ι) (n : ℕ) :
    omega o y ∈ cylinder (block n (omega o x)) ↔ y ∈ cylinder (block n x) := by
  simp only [mem_cylinder, block_apply, omega_apply, Prod.mk.injEq]
  refine ⟨fun h k => (h k).1, fun h k => ⟨h k, ?_⟩⟩
  rw [eps_natCast, eps_natCast]
  refine congrArg (· + 1) (Finset.sum_congr rfl fun j hj => ?_)
  exact congrArg o (h ⟨j, (Finset.mem_range.1 hj).trans k.2⟩)

end Coding

namespace System

/-! ### The atoms of `\overline{ξ}_1` pulled back by the codings -/

section Scalar

variable {ι : Type*} (S : System ι)

/-- Every point of the atom `\overline{ξ}_1(τ(𝐢))` lies in `τ(Σ)` (proof of
`thm:partitions_xi1`). -/
theorem tau_unCode_of_mem_xiBar {x : ℤ → ι} {z : ℤ → ι × ZMod 2}
    (hz : z ∈ S.xiBar 1 (tau S.o x)) : tau S.o (unCode z) = z := by
  simp only [xiBar, atomsOn_of_mem (tau_mem_subshift x)] at hz
  exact tau_unCode_of_samePast hz.2 hz.1.1

/-- Every point of the atom `\overline{ξ}_1(ω(𝐢))` lies in `ω(Σ)` (proof of
`thm:partitions_xi1`). -/
theorem omega_unCode_of_mem_xiBar {x : ℤ → ι} {z : ℤ → ι × ZMod 2}
    (hz : z ∈ S.xiBar 1 (omega S.o x)) : omega S.o (unCode z) = z := by
  simp only [xiBar, atomsOn_of_mem (omega_mem_subshift x)] at hz
  exact omega_unCode_of_samePast hz.2 hz.1.1

/-- Proof of `thm:partitions_xi1`: `\overline{τ}(\overline{ξ}_1(τ(𝐢)))` is the set of sequences
with the past of `𝐢` and the same first coordinate `\overline{π}(τ(·)) = proj_x(π(·))`
(`eq:commutative_diagram`). -/
theorem image_unCode_xiBar_tau (x : ℤ → ι) :
    unCode '' S.xiBar 1 (tau S.o x) =
      {y | SamePast y x ∧ S.projBar (tau S.o y) = S.projBar (tau S.o x)} := by
  ext y
  simp only [xiBar, atomsOn_of_mem (tau_mem_subshift x), mem_image, mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨z, ⟨⟨hp, hπ⟩, hz⟩, rfl⟩
    refine ⟨samePast_unCode hp, ?_⟩
    rw [tau_unCode_of_samePast hz hp]
    exact hπ
  · rintro ⟨hp, hπ⟩
    exact ⟨tau S.o y, ⟨⟨samePast_tau S.o hp, hπ⟩, tau_mem_subshift y⟩, unCode_tau y⟩

/-- Proof of `thm:partitions_xi1`: `\overline{ω}(\overline{ξ}_1(ω(𝐢)))` is the set of sequences
with the past of `𝐢` and the same second coordinate `\overline{π}(ω(·)) = proj_y(π(·))`
(`eq:commutative_diagram`). -/
theorem image_unCode_xiBar_omega (x : ℤ → ι) :
    unCode '' S.xiBar 1 (omega S.o x) =
      {y | SamePast y x ∧ S.projBar (omega S.o y) = S.projBar (omega S.o x)} := by
  ext y
  simp only [xiBar, atomsOn_of_mem (omega_mem_subshift x), mem_image, mem_inter_iff,
    mem_ofPred_eq]
  constructor
  · rintro ⟨z, ⟨⟨hp, hπ⟩, hz⟩, rfl⟩
    refine ⟨samePast_unCode hp, ?_⟩
    rw [omega_unCode_of_samePast hz hp]
    exact hπ
  · rintro ⟨hp, hπ⟩
    exact ⟨omega S.o y, ⟨⟨samePast_omega S.o hp, hπ⟩, omega_mem_subshift y⟩, unCode_omega y⟩

/-- Proof of `thm:partition_tau_conj`, for `T = τ`: intersecting the atom `\overline{ξ}_1(τ(𝐢))`
with `\overline{𝒫}_0^{n-1}(τ(𝐢))` and applying `\overline{τ}` intersects its image with
`𝒫_0^{n-1}(𝐢)`. -/
theorem image_unCode_xiBar_inter_cylinder_tau (x : ℤ → ι) (n : ℕ) :
    unCode '' (S.xiBar 1 (tau S.o x) ∩ cylinder (block n (tau S.o x))) =
      unCode '' S.xiBar 1 (tau S.o x) ∩ cylinder (block n x) := by
  rw [← image_inter_preimage]
  congr 1
  ext z
  simp only [mem_inter_iff, mem_preimage]
  refine and_congr_right fun hz => ?_
  rw [← tau_mem_cylinder_block_iff S.o, S.tau_unCode_of_mem_xiBar hz]

/-- Proof of `thm:partition_tau_conj`, for `T = ω`: intersecting the atom `\overline{ξ}_1(ω(𝐢))`
with `\overline{𝒫}_0^{n-1}(ω(𝐢))` and applying `\overline{ω}` intersects its image with
`𝒫_0^{n-1}(𝐢)`. -/
theorem image_unCode_xiBar_inter_cylinder_omega (x : ℤ → ι) (n : ℕ) :
    unCode '' (S.xiBar 1 (omega S.o x) ∩ cylinder (block n (omega S.o x))) =
      unCode '' S.xiBar 1 (omega S.o x) ∩ cylinder (block n x) := by
  rw [← image_inter_preimage]
  congr 1
  ext z
  simp only [mem_inter_iff, mem_preimage]
  refine and_congr_right fun hz => ?_
  rw [← omega_mem_cylinder_block_iff S.o, S.omega_unCode_of_mem_xiBar hz]

end Scalar

/-! ### The atoms of `ξ_1` and `ξ_1^⊥` -/

section Planar

variable {ι : Type*} [MeasurableSpace ι] (S : System ι)

/-- `Σ'` is saturated with respect to the past (`sec:lyapunov_exponents`, tex lines 1540 to
1618). -/
theorem mem_SigmaPrime_of_samePast (μ : Measure (ℤ → ι)) {x y : ℤ → ι} (h : SamePast x y)
    (hx : x ∈ S.SigmaPrime μ) : y ∈ S.SigmaPrime μ :=
  hx.imp (S.mem_SigmaTau_of_samePast μ h) (S.mem_SigmaOmega_of_samePast μ h)

/-- On `Σ^τ` the slow subspace `V_𝐢^1` is the `y`-axis (`eq:sigma_tau_omega`). -/
theorem slowAxis_of_mem_SigmaTau (μ : Measure (ℤ → ι)) {x : ℤ → ι} (hx : x ∈ S.SigmaTau μ) :
    S.slowAxis μ x = 1 := by
  simp [slowAxis, hx]

/-- On `Σ^ω` the slow subspace `V_𝐢^1` is the `x`-axis (`eq:sigma_tau_omega`), by
`eq:tau_omega_partition2`, when `λ_2(𝖠, μ) < λ_1(𝖠, μ)`. -/
theorem slowAxis_of_mem_SigmaOmega (μ : Measure (ℤ → ι)) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ)
    {x : ℤ → ι} (hx : x ∈ S.SigmaOmega μ) : S.slowAxis μ x = 0 := by
  have hx' : x ∉ S.SigmaTau μ := fun h =>
    Set.disjoint_left.1 (S.disjoint_SigmaTau_SigmaOmega μ hlt) h hx
  simp [slowAxis, hx']

/-- The atom `ξ_1(𝐢)` of `sec:entropies` for `𝐢 ∈ Σ'`: the sequences with the past of `𝐢` whose
image under `π` has the same coordinate transverse to `V_𝐢^1`. They lie in `Σ'` by
past-saturation. -/
theorem xi_one_eq (μ : Measure (ℤ → ι)) {x : ℤ → ι} (hx : x ∈ S.SigmaPrime μ) :
    S.xi μ 1 x = {y | SamePast y x ∧
      coord (S.slowAxis μ x + 1) (S.proj y) = coord (S.slowAxis μ x + 1) (S.proj x)} := by
  ext y
  simp only [xi, atomsOn_of_mem hx, mem_inter_iff, mem_ofPred_eq]
  rw [mem_oseledets_iff]
  constructor
  · rintro ⟨⟨hp, h0 | ⟨-, h1⟩ | ⟨h2, -⟩⟩, -⟩
    · exact absurd h0 one_ne_zero
    · exact ⟨hp, h1⟩
    · exact absurd h2 (by norm_num)
  · rintro ⟨hp, h1⟩
    exact ⟨⟨hp, Or.inr (Or.inl ⟨rfl, h1⟩)⟩, S.mem_SigmaPrime_of_samePast μ hp.symm hx⟩

/-- The atom `ξ_1^⊥(𝐢)` of `sec:entropies` for `𝐢 ∈ Σ'`: the sequences with the past of `𝐢`
whose image under `π` has the same coordinate along `V_𝐢^1`. -/
theorem xiPerp_eq (μ : Measure (ℤ → ι)) {x : ℤ → ι} (hx : x ∈ S.SigmaPrime μ) :
    S.xiPerp μ x = {y | SamePast y x ∧
      coord (S.slowAxis μ x) (S.proj y) = coord (S.slowAxis μ x) (S.proj x)} := by
  ext y
  simp only [xiPerp, atomsOn_of_mem hx, mem_inter_iff, mem_ofPred_eq, coord_sub, sub_eq_zero]
  exact ⟨fun h => h.1, fun h => ⟨h, S.mem_SigmaPrime_of_samePast μ h.1.symm hx⟩⟩

/-- `thm:partitions_xi1`, the first identity on `Σ^τ`: `V_𝐢^1` is the `y`-axis, so membership in
`ξ_1(𝐢)` is equality of the `x`-coordinates, that is, of the scalar codes under `τ`. -/
theorem xi_one_of_mem_SigmaTau (μ : Measure (ℤ → ι)) {x : ℤ → ι} (hx : x ∈ S.SigmaTau μ) :
    S.xi μ 1 x = unCode '' S.xiBar 1 (tau S.o x) ∧ S.xi μ 1 x ⊆ S.SigmaTau μ := by
  have e := S.xi_one_eq μ (Or.inl hx)
  simp only [S.slowAxis_of_mem_SigmaTau μ hx, show (1 : ZMod 2) + 1 = 0 by decide, coord_zero,
    fst_proj] at e
  refine ⟨by rw [e, S.image_unCode_xiBar_tau], fun y hy => ?_⟩
  rw [e] at hy
  exact S.mem_SigmaTau_of_samePast μ hy.1.symm hx

/-- `thm:partitions_xi1`, the second identity on `Σ^τ`: membership in `ξ_1^⊥(𝐢)` is equality of
the `y`-coordinates, that is, of the scalar codes under `ω`. -/
theorem xiPerp_of_mem_SigmaTau (μ : Measure (ℤ → ι)) {x : ℤ → ι} (hx : x ∈ S.SigmaTau μ) :
    S.xiPerp μ x = unCode '' S.xiBar 1 (omega S.o x) ∧ S.xiPerp μ x ⊆ S.SigmaTau μ := by
  have e := S.xiPerp_eq μ (Or.inl hx)
  simp only [S.slowAxis_of_mem_SigmaTau μ hx, coord_one, snd_proj] at e
  refine ⟨by rw [e, S.image_unCode_xiBar_omega], fun y hy => ?_⟩
  rw [e] at hy
  exact S.mem_SigmaTau_of_samePast μ hy.1.symm hx

/-- `thm:partitions_xi1`, the first identity on `Σ^ω`: `V_𝐢^1` is the `x`-axis, so membership in
`ξ_1(𝐢)` is equality of the `y`-coordinates, that is, of the scalar codes under `ω`. -/
theorem xi_one_of_mem_SigmaOmega (μ : Measure (ℤ → ι)) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ)
    {x : ℤ → ι} (hx : x ∈ S.SigmaOmega μ) :
    S.xi μ 1 x = unCode '' S.xiBar 1 (omega S.o x) ∧ S.xi μ 1 x ⊆ S.SigmaOmega μ := by
  have e := S.xi_one_eq μ (Or.inr hx)
  simp only [S.slowAxis_of_mem_SigmaOmega μ hlt hx, zero_add, coord_one, snd_proj] at e
  refine ⟨by rw [e, S.image_unCode_xiBar_omega], fun y hy => ?_⟩
  rw [e] at hy
  exact S.mem_SigmaOmega_of_samePast μ hy.1.symm hx

/-- `thm:partitions_xi1`, the second identity on `Σ^ω`: membership in `ξ_1^⊥(𝐢)` is equality of
the `x`-coordinates, that is, of the scalar codes under `τ`. -/
theorem xiPerp_of_mem_SigmaOmega (μ : Measure (ℤ → ι)) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ)
    {x : ℤ → ι} (hx : x ∈ S.SigmaOmega μ) :
    S.xiPerp μ x = unCode '' S.xiBar 1 (tau S.o x) ∧ S.xiPerp μ x ⊆ S.SigmaOmega μ := by
  have e := S.xiPerp_eq μ (Or.inr hx)
  simp only [S.slowAxis_of_mem_SigmaOmega μ hlt hx, coord_zero, fst_proj] at e
  refine ⟨by rw [e, S.image_unCode_xiBar_tau], fun y hy => ?_⟩
  rw [e] at hy
  exact S.mem_SigmaOmega_of_samePast μ hy.1.symm hx

/-- `thm:partitions_xi1`: for `𝐢 ∈ Σ^τ`, `ξ_1(𝐢) = \overline{τ}(\overline{ξ}_1(τ(𝐢))) ⊆
Σ^τ` and `ξ_1^⊥(𝐢) = \overline{ω}(\overline{ξ}_1(ω(𝐢))) ⊆ Σ^τ`; for `𝐢 ∈ Σ^ω` the roles of `τ`
and `ω` are exchanged. The atom `\overline{ξ}_1(τ(𝐢))` lies in `τ(Σ)`, so `\overline{τ}` of it is
its image under `unCode`. The hypotheses are those of the article; the proof uses
`λ_2(𝖠, μ) < λ_1(𝖠, μ)` only, and only on `Σ^ω`.
Depends on: `eq:commutative_diagram`, `eq:tau_omega_partition`, `mem_SigmaTau_of_samePast`,
`mem_SigmaOmega_of_samePast`, `disjoint_SigmaTau_SigmaOmega`. -/
theorem partitions_xi1 (_hrot : S.WithRotations) (_hprox : S.Proximal) (μ : Measure (ℤ → ι))
    (_hinv : MeasurePreserving (shift 1) μ μ)
    (_herg : Ergodic (shift 1) μ) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) (x : ℤ → ι) :
    (x ∈ S.SigmaTau μ →
      (S.xi μ 1 x = unCode '' S.xiBar 1 (tau S.o x) ∧ S.xi μ 1 x ⊆ S.SigmaTau μ) ∧
      (S.xiPerp μ x = unCode '' S.xiBar 1 (omega S.o x) ∧ S.xiPerp μ x ⊆ S.SigmaTau μ)) ∧
    (x ∈ S.SigmaOmega μ →
      (S.xi μ 1 x = unCode '' S.xiBar 1 (omega S.o x) ∧ S.xi μ 1 x ⊆ S.SigmaOmega μ) ∧
      (S.xiPerp μ x = unCode '' S.xiBar 1 (tau S.o x) ∧ S.xiPerp μ x ⊆ S.SigmaOmega μ)) :=
  ⟨fun hx => ⟨S.xi_one_of_mem_SigmaTau μ hx, S.xiPerp_of_mem_SigmaTau μ hx⟩,
    fun hx => ⟨S.xi_one_of_mem_SigmaOmega μ hlt hx, S.xiPerp_of_mem_SigmaOmega μ hlt hx⟩⟩

/-- `thm:partition_tau_conj`: for `𝐢 ∈ Σ^τ` and `n ≥ 1`,
`(ξ_1 ∨ 𝒫_0^{n-1})(𝐢) = \overline{τ}((\overline{ξ}_1 ∨ \overline{𝒫}_0^{n-1})(τ(𝐢)))`, and the
same with `ω` for `𝐢 ∈ Σ^ω`. The identity also holds for `n = 0`. The hypotheses are those of the
article; the proof uses `λ_2(𝖠, μ) < λ_1(𝖠, μ)` only, and only on `Σ^ω`.
Depends on: `thm:partitions_xi1`, `eq:def_of_tau_omega`. -/
theorem partition_tau_conj (hrot : S.WithRotations) (hprox : S.Proximal) (μ : Measure (ℤ → ι))
    (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) (x : ℤ → ι) (n : ℕ) :
    (x ∈ S.SigmaTau μ → S.xi μ 1 x ∩ cylinder (block n x) =
      unCode '' (S.xiBar 1 (tau S.o x) ∩ cylinder (block n (tau S.o x)))) ∧
    (x ∈ S.SigmaOmega μ → S.xi μ 1 x ∩ cylinder (block n x) =
      unCode '' (S.xiBar 1 (omega S.o x) ∩ cylinder (block n (omega S.o x)))) := by
  obtain ⟨hτ, hω⟩ := S.partitions_xi1 hrot hprox μ hinv herg hlt x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [S.image_unCode_xiBar_inter_cylinder_tau, (hτ hx).1.1]
  · rw [S.image_unCode_xiBar_inter_cylinder_omega, (hω hx).1.1]

end Planar

end System

end BoxLike
