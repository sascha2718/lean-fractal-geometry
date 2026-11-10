module

/-
The periodic-orbit measures of a Hölder potential on the mixing sub-shift `Σ_Z`, the finite-level
approximants in the proof of Bowen's theorem in `BoxLike/Bowen/`: the existence of an ergodic
Gibbs measure for a Hölder potential, which `sec:gibbs_measures` asserts at tex lines 2382 to
2503 with a citation of Sarig's notes. For a period `p ≥ 1` the measure
`ν_p = Z_p⁻¹ ∑_{𝐢 ∈ Σ_Z, σ^p 𝐢 = 𝐢} exp(S_p f(𝐢)) δ_𝐢` is a shift-invariant probability measure
carried by `Σ_Z`, since `σ` permutes the periodic points of period `p` and `S_p f` is constant
along a periodic orbit. By the bounds of `BoxLike/Bowen/PartitionBounds.lean`, `ν_{N+4}` satisfies
the Gibbs bounds for the cylinders of length at most `N`, with a constant independent of `N`.

* `periodicPartition_nonneg`, `periodicPartition_pos`: `Z_p > 0` for `p ≥ 1`.
* `periodicMeasure`: the measure `ν_p`.
* `periodicMeasure_apply`, `measureReal_periodicMeasure`, `periodicMeasure_ne_top`: the mass of a
  set is the normalised weight of the periodic points in it.
* `isProbabilityMeasure_periodicMeasure`, `periodicMeasure_compl_subshift`,
  `measurePreserving_periodicMeasure`: `ν_p` is a shift-invariant probability measure carried by
  `Σ_Z`.
* `birkhoffSum_shift_of_shift_eq`: `S_p f(σ 𝐢) = S_p f(𝐢)` for a point of period `p`.
* `exists_gibbsUpTo_periodic`: for every Hölder potential there is `C > 0` such that for every
  `N` some shift-invariant probability measure carried by `Σ_Z` satisfies the Gibbs bounds with
  constants `P_Z(f)` and `C` for the cylinders of length at most `N`.
-/
public import BoxLike.Bowen.Defs
public import BoxLike.Bowen.PartitionBounds

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set

universe u

section Measures

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {o : ι → ZMod 2} {f : (ℤ → ι × ZMod 2) → ℝ}

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The sum `Z_p` is non-negative. -/
theorem periodicPartition_nonneg (p : ℕ) : 0 ≤ periodicPartition o f p :=
  Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The Birkhoff sum `S_p f` is constant along a periodic orbit of period `p`:
`S_p f(σ 𝐢) - S_p f(𝐢) = f(σ^p 𝐢) - f(𝐢) = 0`. -/
theorem birkhoffSum_shift_of_shift_eq {p : ℕ} {x : ℤ → ι × ZMod 2} (hx : shift p x = x) :
    birkhoffSum (shift 1) f p (shift 1 x) = birkhoffSum (shift 1) f p x := by
  have h := birkhoffSum_apply_sub_birkhoffSum (shift 1) f p x
  rw [iterate_shift_one, hx, sub_self] at h
  exact sub_eq_zero.1 h

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Some generator diagonal, the constant point `(i, 0)(i, 0)⋯` is a periodic point of every
period, so `Z_p > 0` for `p ≥ 1`. -/
theorem periodicPartition_pos (h0 : ∃ i, o i = 0) {p : ℕ} (hp : 0 < p) :
    0 < periodicPartition o f p := by
  obtain ⟨i, hi⟩ := h0
  have hmem : (fun _ : ℤ => (i, (0 : ZMod 2))) ∈ periodicFinset o p := by
    refine (mem_periodicFinset hp).2 ⟨fun n => ?_, rfl⟩
    change (0 : ZMod 2) = 0 + o i
    rw [hi, add_zero]
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨_, hmem⟩

variable (o f) in
/-- The periodic-orbit measure `ν_p = Z_p⁻¹ ∑_{𝐢 ∈ Σ_Z, σ^p 𝐢 = 𝐢} exp(S_p f(𝐢)) δ_𝐢` of Bowen's
construction (tex lines 2382 to 2384). -/
noncomputable def periodicMeasure (p : ℕ) : Measure (ℤ → ι × ZMod 2) :=
  ∑ x ∈ periodicFinset o p,
    ENNReal.ofReal (Real.exp (birkhoffSum (shift 1) f p x) / periodicPartition o f p) •
      Measure.dirac x

omit [Fintype ι] in
variable (o f) in
/-- The mass of a set under `ν_p` is the normalised weight of the periodic points in it. -/
theorem periodicMeasure_apply (p : ℕ) (s : Set (ℤ → ι × ZMod 2)) :
    periodicMeasure o f p s = ∑ x ∈ periodicFinset o p,
      ENNReal.ofReal (Real.exp (birkhoffSum (shift 1) f p x) / periodicPartition o f p) *
        s.indicator 1 x := by
  simp only [periodicMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply, smul_eq_mul]

omit [Fintype ι] in
variable (o f) in
open Classical in
/-- The real mass of a set under `ν_p`. -/
theorem measureReal_periodicMeasure (p : ℕ) (s : Set (ℤ → ι × ZMod 2)) :
    (periodicMeasure o f p).real s = ∑ x ∈ (periodicFinset o p).filter (· ∈ s),
      Real.exp (birkhoffSum (shift 1) f p x) / periodicPartition o f p := by
  have hc : ∀ x, 0 ≤ Real.exp (birkhoffSum (shift 1) f p x) / periodicPartition o f p :=
    fun _ => div_nonneg (Real.exp_pos _).le (periodicPartition_nonneg p)
  have key : periodicMeasure o f p s = ENNReal.ofReal (∑ x ∈ (periodicFinset o p).filter (· ∈ s),
      Real.exp (birkhoffSum (shift 1) f p x) / periodicPartition o f p) := by
    rw [periodicMeasure_apply, ENNReal.ofReal_sum_of_nonneg fun x _ => hc x, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ s <;> simp [hx]
  rw [measureReal_def, key, ENNReal.toReal_ofReal (Finset.sum_nonneg fun x _ => hc x)]

omit [Fintype ι] in
/-- Every set has finite mass under `ν_p`. -/
theorem periodicMeasure_ne_top (p : ℕ) (s : Set (ℤ → ι × ZMod 2)) :
    periodicMeasure o f p s ≠ ⊤ := by
  rw [periodicMeasure_apply]
  refine ENNReal.sum_ne_top.2 fun x _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
  by_cases hx : x ∈ s <;> simp [hx]

/-- `ν_p` is a probability measure for `p ≥ 1`, when some generator is diagonal. -/
theorem isProbabilityMeasure_periodicMeasure (h0 : ∃ i, o i = 0) {p : ℕ} (hp : 0 < p) :
    IsProbabilityMeasure (periodicMeasure o f p) := by
  classical
  have hZ := periodicPartition_pos (f := f) h0 hp
  have h := measureReal_periodicMeasure o f p univ
  simp only [mem_univ, Finset.filter_true] at h
  rw [← Finset.sum_div, ← periodicPartition, div_self hZ.ne'] at h
  refine ⟨?_⟩
  rw [← ENNReal.ofReal_toReal (periodicMeasure_ne_top p univ), ← measureReal_def, h,
    ENNReal.ofReal_one]

/-- `ν_p` is carried by `Σ_Z`. -/
theorem periodicMeasure_compl_subshift (p : ℕ) : periodicMeasure o f p (subshift o)ᶜ = 0 := by
  rw [periodicMeasure_apply]
  refine Finset.sum_eq_zero fun x hx => ?_
  have : x ∉ (subshift o)ᶜ := not_not.2 (mem_subshift_of_mem_periodicFinset hx)
  rw [Set.indicator_of_notMem this, mul_zero]

/-- `ν_p` is shift-invariant for `p ≥ 1`: `σ` permutes the periodic points of period `p`, with
inverse `σ^{-1}`, and preserves their weights `exp(S_p f)`. -/
theorem measurePreserving_periodicMeasure {p : ℕ} (hp : 0 < p) :
    MeasurePreserving (shift 1) (periodicMeasure o f p) (periodicMeasure o f p) := by
  refine ⟨measurable_shift 1, ?_⟩
  ext s hs
  rw [Measure.map_apply (measurable_shift 1) hs, periodicMeasure_apply, periodicMeasure_apply]
  have hmaps : ∀ n : ℤ, ∀ x ∈ periodicFinset o p, shift n x ∈ periodicFinset o p := by
    intro n x hx
    obtain ⟨hx1, hx2⟩ := (mem_periodicFinset hp).1 hx
    refine (mem_periodicFinset hp).2 ⟨shift_mem_subshift o hx1 n, ?_⟩
    rw [shift_shift, add_comm, ← shift_shift, hx2]
  refine Finset.sum_nbij' (shift 1) (shift (-1)) (hmaps 1) (hmaps (-1))
    (fun x _ => by rw [shift_shift, add_neg_cancel, shift_zero])
    (fun x _ => by rw [shift_shift, neg_add_cancel, shift_zero]) fun x hx => ?_
  have hx2 := ((mem_periodicFinset hp).1 hx).2
  rw [birkhoffSum_shift_of_shift_eq hx2]
  rfl

end Measures

/-! ### The Gibbs bounds up to a given length -/

/-- The finite-level approximants of Bowen's theorem (tex lines 2382 to 2384): for a Hölder
potential `f` on the mixing sub-shift `Σ_Z` there is `C > 0` such that for every `N` some
shift-invariant probability measure carried by `Σ_Z`, the periodic-orbit measure `ν_{N+4}`,
satisfies the Gibbs bounds with constants `P_Z(f)` and `C` for the cylinders of length at most
`N`. -/
theorem exists_gibbsUpTo_periodic {ι : Type u} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {o : ι → ZMod 2} (h0 : ∃ i, o i = 0) (h1 : ∃ i, o i = 1)
    {f : (ℤ → ι × ZMod 2) → ℝ} (hf : IsHolderPotential o f) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ ν : Measure (ℤ → ι × ZMod 2), IsProbabilityMeasure ν ∧
      MeasurePreserving (shift 1) ν ν ∧ ν (subshift o)ᶜ = 0 ∧
        GibbsUpTo o f ν (pressureZPot o f) C N := by
  classical
  have : Nonempty ι := ⟨h0.choose⟩
  obtain ⟨B, D, -, -, h⟩ := hf.exists_hasBoundedDistortion
  obtain ⟨C, hC, hb⟩ := h.exists_periodic_cylinder_bounds h0 h1
  refine ⟨C, hC, fun N => ⟨periodicMeasure o f (N + 4),
    isProbabilityMeasure_periodicMeasure h0 (Nat.succ_pos _),
    measurePreserving_periodicMeasure (Nat.succ_pos _), periodicMeasure_compl_subshift _,
    hC, fun y hy n hn hnN => ?_⟩⟩
  have e : (periodicMeasure o f (N + 4)).real (cylinder fun k : Fin n => y k) =
      (∑ x ∈ (periodicFinset o (N + 4)).filter (· ∈ cylinder (block n y)),
        Real.exp (birkhoffSum (shift 1) f (N + 4) x)) / periodicPartition o f (N + 4) := by
    rw [measureReal_periodicMeasure, Finset.sum_div]
    rfl
  rw [e]
  exact hb N y hy n hn hnN

end BoxLike
