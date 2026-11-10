module

/-
The `s`-Gibbs measures of `sec:gibbs_measures` and the Gibbs bounds of their image on `Σ`: the
first two steps of the proof of `thm:eq_state_is_sum` (Fraser–Jordan–Jurga, J. Fractal Geom. 7
(2020), Lemma 1.3 and Corollaries 1.5 and 1.6). No literature premise is used.

Bowen's theorem (`bowenGibbsExistence`, `BoxLike/Bowen/Main.lean`) gives an ergodic Gibbs
probability measure `μ_1` carried by `Σ_Z` for the locally constant potential `f_{1,s}`. The
exchange of the axes carries it to the ergodic Gibbs measure `μ_2 = flip_*μ_1` for `f_{2,s}`. The
factor map `q = unCode : Σ_Z → Σ` that forgets the axis carries `μ_1` to an ergodic invariant
probability measure on `Σ`. Every word `𝐢|_n` of `Σ` has the two lifts `τ(𝐢)|_n` and `ω(𝐢)|_n`,
so that, by the Gibbs bounds of `μ_1`, `P(𝖠, s) = P_Z(f_{1,s})` and
`thm:matrix_products_g_derivatives` in the form of tex lines 2446 to 2451,
`q_*μ_1([𝐢|_n]) = μ_1([τ(𝐢)|_n]) + μ_1([ω(𝐢)|_n])
  ≍ e^{-nP(𝖠, s)} (e^{S_n f_{1,s}(τ(𝐢))} + e^{S_n f_{1,s}(ω(𝐢))}) ≍ e^{-nP(𝖠, s)} φ^s(A_{𝐢|_n})`:
the measure `q_*μ_1` has the Gibbs bounds of `thm:irred_eq_state`.

* `System.exists_isGibbs_potential₁`: the ergodic `s`-Gibbs measure `μ_1` exists.
* `preimage_flipAxis_subshift`, `preimage_flipAxis_cylinder`: the exchange of the axes preserves
  `Σ_Z` and maps cylinders to cylinders.
* `map_flipAxis_subshift_compl`, `ergodic_map_flipAxis`, `System.isGibbs_potential₂_map_flipAxis`:
  `μ_2 = flip_*μ_1` is an ergodic Gibbs measure carried by `Σ_Z` for `f_{2,s}`; it is a
  probability measure by the instance `IsProbabilityMeasure (ν.map f)` of Mathlib.
* `ergodic_map_unCode`: the image of an ergodic measure under the factor map is ergodic.
* `System.exists_isGibbsWith_pressure`: the Gibbs bounds of `μ_1` hold with the constant
  `P(𝖠, s)`.
* `System.measureReal_cylinder_liftBlock_bounds`: the Gibbs bounds of the cylinder of a lift.
* `System.hasGibbsBounds_map_unCode`: `q_*μ_1` has the Gibbs bounds of `thm:irred_eq_state`.
-/
public import BoxLike.Bowen.Main

@[expose] public section

namespace BoxLike

open MeasureTheory

/-! ### The first Gibbs measure -/

/-- `thm:eq_state_is_sum`, the Gibbs measure `μ_1` (tex lines 2382 to 2384 and 2572 to 2574): for
a box-like tuple with rotations and every `s`, there is an ergodic probability measure carried by
`Σ_Z` with the Gibbs property for the potential `f_{1,s}`. This is Bowen's theorem for the
locally constant, hence Hölder, potential `f_{1,s}`. -/
theorem System.exists_isGibbs_potential₁ {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (S : System ι) (hrot : S.WithRotations) (s : ℝ) :
    ∃ μ₁ : Measure (ℤ → ι × ZMod 2), IsProbabilityMeasure μ₁ ∧ μ₁ (subshift S.o)ᶜ = 0 ∧
      Ergodic (shift 1) μ₁ ∧ IsGibbs S.o (S.potential₁ s) μ₁ := by
  obtain ⟨ν, hp, hs, herg, P, C, hg⟩ := bowenGibbsExistence S.o hrot.1 hrot.2 _
    (isHolderPotential_apply_zero (o := S.o) (S.potential₁ s))
  exact ⟨ν, hp, hs, herg, isGibbs_iff.2 ⟨P, C, (isGibbsPotential_iff_isGibbsWith _).1 hg⟩⟩

/-! ### The second Gibbs measure -/

section Flip

variable {ι : Type*}

/-- `Σ_Z` is invariant under the exchange of the axes: the matrix `Z` of `sec:subshift` is. -/
theorem preimage_flipAxis_subshift (o : ι → ZMod 2) : flipAxis ⁻¹' subshift o = subshift o := by
  ext y
  change (∀ n, Trans o (flipSymbol (y n)) (flipSymbol (y (n + 1)))) ↔
    ∀ n, Trans o (y n) (y (n + 1))
  exact forall_congr' fun n => trans_flipSymbol_iff (y n) (y (n + 1))

/-- The preimage of the cylinder `[w]` under the exchange of the axes is the cylinder of the word
`w` with the axes exchanged. -/
theorem preimage_flipAxis_cylinder {n : ℕ} (w : Fin n → ι × ZMod 2) :
    flipAxis ⁻¹' cylinder w = cylinder fun k => flipSymbol (w k) := by
  ext y
  refine forall_congr' fun k => ?_
  change flipSymbol (y k) = w k ↔ y k = flipSymbol (w k)
  constructor
  · intro h
    rw [← h, flipSymbol_flipSymbol]
  · intro h
    rw [h, flipSymbol_flipSymbol]

variable [MeasurableSpace ι] {ν : Measure (ℤ → ι × ZMod 2)}

/-- The image `flip_*ν` of a measure carried by `Σ_Z` is carried by `Σ_Z`. -/
theorem map_flipAxis_subshift_compl [Fintype ι] [MeasurableSingletonClass ι]
    {o : ι → ZMod 2} (hν : ν (subshift o)ᶜ = 0) : ν.map flipAxis (subshift o)ᶜ = 0 := by
  rw [Measure.map_apply measurable_flipAxis (measurableSet_subshift o).compl, Set.preimage_compl,
    preimage_flipAxis_subshift, hν]

/-- The image `flip_*ν` of an ergodic measure is ergodic: the exchange of the axes commutes with
the shift. -/
theorem ergodic_map_flipAxis (h : Ergodic (shift 1) ν) : Ergodic (shift 1) (ν.map flipAxis) :=
  (⟨measurable_flipAxis, rfl⟩ : MeasurePreserving flipAxis ν (ν.map flipAxis))
    |>.ergodic_of_ergodic_semiconj h (measurable_shift 1) fun _ => rfl

/-- `thm:eq_state_is_sum`, the Gibbs measure `μ_2` (tex lines 2453 to 2455 and 2606 to 2607):
the image `flip_*ν` of a Gibbs measure for `f_{1,s}` is a Gibbs measure for `f_{2,s}`, with the
same constants, since `f_{2,s} = f_{1,s} ∘ flip`. -/
theorem System.isGibbs_potential₂_map_flipAxis [Fintype ι] [MeasurableSingletonClass ι]
    (S : System ι) {s : ℝ} (hg : IsGibbs S.o (S.potential₁ s) ν) :
    IsGibbs S.o (S.potential₂ s) (ν.map flipAxis) := by
  obtain ⟨P, C, hC, hb⟩ := hg
  refine ⟨P, C, hC, fun y hy n hn => ?_⟩
  have hy' : flipAxis y ∈ subshift S.o := by
    rw [← Set.mem_preimage, preimage_flipAxis_subshift]
    exact hy
  have hcyl : (ν.map flipAxis).real (cylinder fun k : Fin n => y k) =
      ν.real (cylinder fun k : Fin n => flipAxis y k) := by
    rw [map_measureReal_apply measurable_flipAxis (measurableSet_cylinder _),
      preimage_flipAxis_cylinder]
    rfl
  rw [hcyl]
  exact hb (flipAxis y) hy' n hn

end Flip

/-! ### The image of the first Gibbs measure on `Σ` -/

section Image

variable {ι : Type*} [MeasurableSpace ι] {ν : Measure (ℤ → ι × ZMod 2)}

/-- The image `q_*ν` of an ergodic measure under the factor map `q = unCode` that forgets the
axis is ergodic: `q` commutes with the shift. -/
theorem ergodic_map_unCode (h : Ergodic (shift 1) ν) : Ergodic (shift 1) (ν.map unCode) :=
  (⟨measurable_unCode, rfl⟩ : MeasurePreserving unCode ν (ν.map unCode))
    |>.ergodic_of_ergodic_semiconj h (measurable_shift 1) fun _ => rfl

variable [Fintype ι] [MeasurableSingletonClass ι] (S : System ι) {s : ℝ}

/-- `thm:eq_state_is_sum`, first line, for the Gibbs constant: a Gibbs probability measure carried
by `Σ_Z` for `f_{1,s}` has the Gibbs bounds with the constant `P(𝖠, s) = P_Z(f_{1,s})`, for
`0 < s < 2`. -/
theorem System.exists_isGibbsWith_pressure (hs0 : 0 < s) (hs2 : s < 2) [IsProbabilityMeasure ν]
    (hν : ν (subshift S.o)ᶜ = 0) (hg : IsGibbs S.o (S.potential₁ s) ν) :
    ∃ C, IsGibbsWith S.o (S.potential₁ s) ν (S.pressure s) C := by
  obtain ⟨P, C, hPC⟩ := isGibbs_iff.1 hg
  have hP : P = S.pressure s := IsGibbsAt.eq_pressure₁ (S := S) hν hs0 hs2 ⟨C, hPC⟩
  exact ⟨C, hP ▸ hPC⟩

omit [Fintype ι] [MeasurableSingletonClass ι] in
/-- The Gibbs bounds of the cylinder of the lift `liftBlock o c w` of a word `w` of length
`m + 1` along the axis `c`: it is the cylinder `[𝐣|_{m+1}]` of the point `𝐣 ∈ Σ_Z` over an
extension of `w` that starts on the axis `c`, and `S_{m+1} f_{1,s}(𝐣)` is the sum of `f_{1,s}`
over the lift. -/
theorem System.measureReal_cylinder_liftBlock_bounds {P C : ℝ}
    (hC : IsGibbsWith S.o (S.potential₁ s) ν P C) (m : ℕ) (w : Fin (m + 1) → ι) (c : ZMod 2) :
    C⁻¹ * (Real.exp (-((m + 1 : ℕ) * P)) *
        Real.exp (∑ k, S.potential₁ s (liftBlock S.o c w k))) ≤
        ν.real (cylinder (liftBlock S.o c w)) ∧
      ν.real (cylinder (liftBlock S.o c w)) ≤
        C * (Real.exp (-((m + 1 : ℕ) * P)) *
          Real.exp (∑ k, S.potential₁ s (liftBlock S.o c w k))) := by
  have hy := codeFrom_mem_subshift S.o c (extendWord w)
  have hblock := block_codeFrom_extendWord S.o c w
  have hsum : ∑ k ∈ Finset.range (m + 1), S.potential₁ s (codeFrom S.o c (extendWord w) k) =
      ∑ k, S.potential₁ s (liftBlock S.o c w k) := by
    rw [Finset.sum_range]
    exact Finset.sum_congr rfl fun k _ => congrArg (S.potential₁ s) (congrFun hblock k)
  have hcyl : (cylinder fun k : Fin (m + 1) => codeFrom S.o c (extendWord w) k) =
      cylinder (liftBlock S.o c w) := congrArg cylinder hblock
  have h := hC.2 _ hy (m + 1) m.succ_pos
  rw [hsum, Real.exp_add, hcyl] at h
  exact h

/-- `thm:eq_state_is_sum`, the Gibbs bounds of `q_*μ_1`: for `0 < s < 2` the image
`q_*ν` on `Σ` of a Gibbs probability measure `ν` carried by `Σ_Z` for `f_{1,s}` has the Gibbs
bounds of `thm:irred_eq_state`. For a word `w` of length `n ≥ 1`,
`q_*ν([w]) = ν([w, 0]) + ν([w, 1])` is the sum over the two lifts of `w`, each comparable to
`e^{-nP(𝖠, s)} e^{S_n f_{1,s}}` along the lift, and `φ^s(A_w)` is the larger of the two
exponentials (tex lines 2446 to 2451). With the Gibbs constant `C` of `ν` the constant of the
bounds is `2C`. -/
theorem System.hasGibbsBounds_map_unCode (hs0 : 0 < s) (hs2 : s < 2) [IsProbabilityMeasure ν]
    (hν : ν (subshift S.o)ᶜ = 0) (hg : IsGibbs S.o (S.potential₁ s) ν) :
    S.HasGibbsBounds s (ν.map unCode) := by
  obtain ⟨C, hC⟩ := S.exists_isGibbsWith_pressure hs0 hs2 hν hg
  obtain ⟨i⟩ : Nonempty ι := ⟨((nonempty_of_isProbabilityMeasure ν).some 0).1⟩
  have hC1 : 1 ≤ C := hC.one_le (tau_mem_subshift fun _ => i)
  have hC0 : 0 < C := by linarith
  refine ⟨2 * C, by linarith, fun n hn w => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsplit : (ν.map unCode).real (cylinder w) =
      ν.real (cylinder (liftBlock S.o 0 w)) + ν.real (cylinder (liftBlock S.o 1 w)) := by
    rw [map_measureReal_apply measurable_unCode (measurableSet_cylinder w),
      measureReal_preimage_unCode_cylinder hν w, sum_zmod_two]
  rw [hsplit, S.svf_matWord_ofFn w hs0 hs2]
  obtain ⟨l0, u0⟩ := S.measureReal_cylinder_liftBlock_bounds hC m w 0
  obtain ⟨l1, u1⟩ := S.measureReal_cylinder_liftBlock_bounds hC m w 1
  have hX := Real.exp_pos (-((m + 1 : ℕ) * S.pressure s))
  have hE0 := Real.exp_pos (∑ k, S.potential₁ s (liftBlock S.o 0 w k))
  have hE1 := Real.exp_pos (∑ k, S.potential₁ s (liftBlock S.o 1 w k))
  generalize Real.exp (-((m + 1 : ℕ) * S.pressure s)) = X at hX l0 u0 l1 u1 ⊢
  generalize Real.exp (∑ k, S.potential₁ s (liftBlock S.o 0 w k)) = E0 at hE0 l0 u0 ⊢
  generalize Real.exp (∑ k, S.potential₁ s (liftBlock S.o 1 w k)) = E1 at hE1 l1 u1 ⊢
  have hM : max E0 E1 ≤ E0 + E1 := max_le_add_of_nonneg hE0.le hE1.le
  have hM0 : E0 ≤ max E0 E1 := le_max_left E0 E1
  have hM1 : E1 ≤ max E0 E1 := le_max_right E0 E1
  constructor
  · calc (2 * C)⁻¹ * (X * max E0 E1) ≤ C⁻¹ * (X * (E0 + E1)) :=
          mul_le_mul (inv_anti₀ hC0 (by linarith)) (mul_le_mul_of_nonneg_left hM hX.le)
            (by positivity) (inv_nonneg.2 hC0.le)
      _ = C⁻¹ * (X * E0) + C⁻¹ * (X * E1) := by ring
      _ ≤ _ := add_le_add l0 l1
  · calc ν.real (cylinder (liftBlock S.o 0 w)) + ν.real (cylinder (liftBlock S.o 1 w))
        ≤ C * (X * E0) + C * (X * E1) := add_le_add u0 u1
      _ = C * (X * (E0 + E1)) := by ring
      _ ≤ C * (X * (2 * max E0 E1)) := by
          gcongr
          linarith
      _ = 2 * C * (X * max E0 E1) := by ring

end Image

end BoxLike
