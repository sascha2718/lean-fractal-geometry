module

/-
The orientation lift in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`, in
`sec:dimension_of_projections` (tex lines 2703 to 2713): for a Bernoulli measure `μ` on `Σ` the
measure `\widetilde μ = (τ_*μ + ω_*μ) / 2` on `Σ_Z` chooses the initial axis uniformly and then
each planar symbol independently. It is a stationary Markov measure, mixing when both matrix
types have positive probability, hence ergodic. Its entropy is `h_0(μ)`, and Birkhoff's theorem
along both lifts gives `λ_1(𝖠, μ) = λ_2(𝖠, μ) = \overline{λ}(𝖠, \widetilde μ)`.

* `ergodic_of_tendsto_measureReal_inter`: an invariant probability measure on `ℤ → α` that is
  mixing on the measurable cylinder sets is ergodic.
* `exists_block_preimage_of_mem_measurableCylinders`,
  `tendsto_measureReal_inter_of_cylinder`, `ergodic_of_tendsto_measureReal_cylinder_inter`:
  mixing on the cylinders `[w]` at time `0` gives mixing on all measurable cylinder sets, and
  hence ergodicity, for a finite alphabet.
* `appendSet`, `block_inter_shift_block`, `measureReal_preimage_eq_sum_ite`,
  `bernoulli_block_inter_shift_block`: under a Bernoulli measure an event of the first `a`
  symbols is independent of a shifted event of the next `b` symbols.
* `eps_natCast_eq_sum_block`, `eps_add`, `parSet`, `setOf_eps_eq`: the cocycle `ε` as a
  function of blocks, and its additivity along the shift.
* `bernoulli_parity_succ`, `bernoulli_parity_add`, `bernoulli_parity_sub`,
  `tendsto_bernoulli_parity`, `bernoulli_parity_one_pos`: the parity `ε_L` of the number of
  anti-diagonal symbols among `L` independent symbols has bias `r^L`, `|r| < 1`, and is
  asymptotically uniform when both types have positive probability.
* `orientLift`, `orientLift_zero`, `orientLift_one`, `unCode_orientLift`,
  `orientLift_mem_cylinder_iff`, `shift_orientLift`, `measurable_orientLift`: the lift
  `𝐢 ↦ (i_k, c + ε_k(𝐢))_k` of `𝐢` with initial axis `c`; it is `τ` for `c = 0` and `ω` for
  `c = 1`, and `thm:tau_omega_sigma_commutative` holds for it.
* `orientationLift`, `orientationLift_real_apply`, `orientationLift_subshift_compl`,
  `map_unCode_orientationLift`, `measurePreserving_shift_orientationLift`: the lift
  `(τ_*μ + ω_*μ) / 2`, its support in `Σ_Z`, its image `μ` under the factor map, and its
  stationarity.
* `orientationLift_real_cylinder_liftBlock`, `entropy_orientationLift`,
  `admissible_iff_eq_liftBlock`, `liftBlock_zero_ne_one`: each planar word has exactly two
  lifts, each carrying half of its mass, and `\overline{h}_0(\widetilde μ) = h_0(μ)`.
* `decidableTrans`, `liftBlock_succ_snd`, `eq_liftBlock_iff`, `orientationLift_real_cylinder`,
  `orientationLift_bernoulli_cylinder`: the admissible words of `Σ_Z`, and the Markov form
  `\widetilde μ([v]) = (p_{v_0} / 2) ∏_j Q(v_j, v_{j+1})` of the lift of a Bernoulli measure.
* `orientLift_preimage_cylinder_inter_shift`, `tendsto_orientationLift_bernoulli_cylinder_inter`,
  `ergodic_orientationLift_bernoulli`: the lift of a Bernoulli measure charging both types is
  mixing, hence ergodic.
* `System.lyapBar_orientationLift`:
  `\overline{λ}(𝖠, \widetilde μ) = (λ_1(𝖠, μ) + λ_2(𝖠, μ)) / 2 = (1/2) ∑_i μ([i]) log |det A_i|`.
* `System.lyapunov_eq_of_ergodic_orientationLift`: Birkhoff's theorem along both lifts and
  `thm:matrix_products_g_derivatives` give
  `λ_1(𝖠, μ) = λ_2(𝖠, μ) = \overline{λ}(𝖠, \widetilde μ)` when the lift is ergodic.
* `System.map_projBar_orientationLift`: `\overline{π}_* \widetilde μ = (ν_x + ν_y) / 2`, from
  `eq:commutative_diagram`.
-/
public import BoxLike.BernoulliEquilibrium
public import BoxLike.EntropyFactor
public import BoxLike.Main
public import BoxLike.SigmaMeasure

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set
open scoped symmDiff

/-! ### Mixing implies ergodicity -/

section Mixing

variable {α : Type*} [MeasurableSpace α]

/-- An invariant probability measure `ν` on `ℤ → α` with
`ν(B ∩ σ^{-m} B) → ν(B)^2` for every measurable cylinder set `B` is ergodic. An invariant set
`A` is approximated by a cylinder set `B`; then `σ^{-m} B` approximates `σ^{-m} A = A`
equally well, so `ν(A) = ν(A)^2`. This is the argument of `ergodic_shift_bernoulli` with
independence replaced by mixing. Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem ergodic_of_tendsto_measureReal_inter {ν : Measure (ℤ → α)} [IsProbabilityMeasure ν]
    (hinv : MeasurePreserving (shift 1) ν ν)
    (hmix : ∀ B ∈ measurableCylinders fun _ : ℤ => α,
      Tendsto (fun m : ℕ => ν.real (B ∩ shift (m : ℤ) ⁻¹' B)) atTop
        (𝓝 (ν.real B * ν.real B))) :
    Ergodic (shift 1) ν := by
  refine ⟨hinv, ⟨fun A hA hAinv => ?_⟩⟩
  have hinvm : ∀ m : ℕ, shift (m : ℤ) ⁻¹' A = A := fun m => by
    have h := Function.IsFixedPt.preimage_iterate (f := shift 1) hAinv m
    rwa [iterate_shift_one] at h
  have key : ∀ ε : ℝ, 0 < ε → |ν.real A - ν.real A * ν.real A| ≤ 5 * ε := by
    intro ε hε
    obtain ⟨B, hB, hBA⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
      (μ := ν) isSetRing_measurableCylinders
      ⟨{Set.univ}, Set.countable_singleton _,
        by simpa using univ_mem_measurableCylinders fun _ : ℤ => α, by simp⟩
      generateFrom_measurableCylinders.symm hA (ENNReal.ofReal_pos.2 hε)
    have hBm : MeasurableSet B := .of_mem_measurableCylinders hB
    obtain ⟨m, hm⟩ := ((hmix B hB).eventually (Metric.ball_mem_nhds _ hε)).exists
    have hmp := measurePreserving_shift_natCast hinv m
    have hB'm : MeasurableSet (shift (m : ℤ) ⁻¹' B) := hmp.measurable hBm
    have hd : ν.real (B ∆ A) < ε := ENNReal.toReal_lt_of_lt_ofReal hBA
    have hd' : ν.real ((shift (m : ℤ) ⁻¹' B) ∆ A) = ν.real (B ∆ A) := by
      conv_lhs => rw [← hinvm m, ← Set.preimage_symmDiff]
      exact hmp.measureReal_preimage (hBm.symmDiff hA).nullMeasurableSet
    have h1 := abs_measureReal_sub_le_measureReal_symmDiff (μ := ν)
      hBm.nullMeasurableSet hA.nullMeasurableSet
    have h2 := abs_measureReal_sub_le_measureReal_symmDiff (μ := ν)
      (hBm.inter hB'm).nullMeasurableSet hA.nullMeasurableSet
    have hsub : (B ∩ shift (m : ℤ) ⁻¹' B) ∆ A ⊆ B ∆ A ∪ (shift (m : ℤ) ⁻¹' B) ∆ A := by
      intro x
      simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_union]
      tauto
    have h3 := (measureReal_mono hsub).trans (measureReal_union_le _ _)
    rw [hd'] at h3
    have h4 : |ν.real (B ∩ shift (m : ℤ) ⁻¹' B) - ν.real B * ν.real B| < ε := by
      simpa [Metric.mem_ball, Real.dist_eq] using hm
    have ha0 : 0 ≤ ν.real A := measureReal_nonneg
    have ha1 : ν.real A ≤ 1 := measureReal_le_one
    have hb0 : 0 ≤ ν.real B := measureReal_nonneg
    have hb1 : ν.real B ≤ 1 := measureReal_le_one
    generalize ν.real A = a at *
    generalize ν.real B = b at *
    generalize ν.real (B ∆ A) = d at *
    generalize ν.real (B ∩ shift (m : ℤ) ⁻¹' B) = e at *
    have h5 : |b * b - a * a| ≤ 2 * d := by
      have e' : b * b - a * a = (b + a) * (b - a) := by ring
      rw [e', abs_mul]
      exact mul_le_mul (abs_le.2 ⟨by linarith, by linarith⟩) h1 (abs_nonneg _) (by norm_num)
    rw [abs_le] at h2 h5 ⊢
    rw [abs_lt] at h4
    constructor <;> nlinarith
  have h0 : ν.real A - ν.real A * ν.real A = 0 :=
    abs_eq_zero.1 <| le_antisymm (le_of_forall_pos_le_add fun ε hε => by
      have := key (ε / 5) (by positivity)
      linarith) (abs_nonneg _)
  rw [eventuallyEmptyOrUniv_iff', ae_eq_empty, ae_eq_univ, prob_compl_eq_zero_iff hA]
  have h01 : ν.real A = 0 ∨ ν.real A = 1 := by
    have : ν.real A * (1 - ν.real A) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases h01 with h | h
  · exact Or.inl ((measureReal_eq_zero_iff (by finiteness)).1 h)
  · refine Or.inr ?_
    rw [measureReal_def] at h
    exact (ENNReal.toReal_eq_one_iff _).1 h

/-- A measurable cylinder set depends on a window of coordinates: it is the preimage of a set
of words under `𝐢 ↦ i_k ⋯ i_{k+n-1}` for some `k ∈ ℤ` and `n ∈ ℕ`.
Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem exists_block_preimage_of_mem_measurableCylinders {B : Set (ℤ → α)}
    (hB : B ∈ measurableCylinders fun _ : ℤ => α) :
    ∃ (k : ℤ) (n : ℕ) (W : Set (Fin n → α)), B = (fun x => block n (shift k x)) ⁻¹' W := by
  obtain ⟨I, S, -, rfl⟩ := (mem_measurableCylinders B).1 hB
  obtain ⟨k, n, hkn⟩ : ∃ (k : ℤ) (n : ℕ), ∀ i ∈ I, ∃ j : Fin n, k + j = i := by
    refine ⟨-(I.sup Int.natAbs : ℕ), 2 * I.sup Int.natAbs + 1, fun i hi => ?_⟩
    have hle := Finset.le_sup (f := Int.natAbs) hi
    refine ⟨⟨(i + (I.sup Int.natAbs : ℕ)).toNat, by omega⟩, ?_⟩
    simp only
    omega
  refine ⟨k, n, (fun x => block n (shift k x)) '' (I.restrict ⁻¹' S),
    (Set.subset_preimage_image _ _).antisymm ?_⟩
  rintro y ⟨x, hx, hxy⟩
  rw [MeasureTheory.mem_cylinder] at hx
  rw [MeasureTheory.mem_cylinder]
  convert hx using 1
  funext i
  obtain ⟨j, hj⟩ := hkn i i.2
  have h := congrFun hxy j
  simp only [block_apply, shift_apply] at h
  simp only [Finset.restrict, ← hj, h]

variable [Fintype α] [MeasurableSingletonClass α]

/-- Mixing on the cylinders `[w]` at time `0` gives mixing on every measurable cylinder set,
for an invariant probability measure: such a set is a finite disjoint union of translates
`σ^{-k}[w]` of cylinders, and `ν(σ^{-k}[w] ∩ σ^{-m-k}[w']) = ν([w] ∩ σ^{-m}[w'])`.
Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem tendsto_measureReal_inter_of_cylinder {ν : Measure (ℤ → α)} [IsProbabilityMeasure ν]
    (hinv : MeasurePreserving (shift 1) ν ν)
    (hmix : ∀ (n : ℕ) (w w' : Fin n → α),
      Tendsto (fun m : ℕ => ν.real (cylinder w ∩ shift (m : ℤ) ⁻¹' cylinder w')) atTop
        (𝓝 (ν.real (cylinder w) * ν.real (cylinder w'))))
    {B : Set (ℤ → α)} (hB : B ∈ measurableCylinders fun _ : ℤ => α) :
    Tendsto (fun m : ℕ => ν.real (B ∩ shift (m : ℤ) ⁻¹' B)) atTop (𝓝 (ν.real B * ν.real B)) := by
  classical
  obtain ⟨k, n, W, rfl⟩ := exists_block_preimage_of_mem_measurableCylinders hB
  set f : (ℤ → α) → Fin n → α := fun x => block n (shift k x) with hf_def
  have hf : Measurable f := (measurable_block n).comp (measurable_shift k)
  have hfib : ∀ w, f ⁻¹' {w} = shift k ⁻¹' cylinder w := fun w => by
    rw [cylinder_eq_preimage]
    rfl
  have hW : f ⁻¹' W = f ⁻¹' ↑W.toFinset := by rw [Set.coe_toFinset]
  have hB1 : ν.real (f ⁻¹' W) = ∑ w ∈ W.toFinset, ν.real (cylinder w) := by
    rw [hW, ← sum_measureReal_preimage_singleton _ fun w _ => hf (measurableSet_singleton w)]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hfib, measureReal_preimage_shift hinv k (measurableSet_cylinder w)]
  have hB2 : ∀ m : ℕ, ν.real (f ⁻¹' W ∩ shift (m : ℤ) ⁻¹' (f ⁻¹' W)) =
      ∑ q ∈ W.toFinset ×ˢ W.toFinset,
        ν.real (cylinder q.1 ∩ shift (m : ℤ) ⁻¹' cylinder q.2) := by
    intro m
    set g : (ℤ → α) → (Fin n → α) × (Fin n → α) := fun x => (f x, f (shift m x))
    have hg : Measurable g := hf.prodMk (hf.comp (measurable_shift m))
    have hset : f ⁻¹' W ∩ shift (m : ℤ) ⁻¹' (f ⁻¹' W) = g ⁻¹' ↑(W.toFinset ×ˢ W.toFinset) := by
      ext x
      simp [g]
    rw [hset, ← sum_measureReal_preimage_singleton _ fun q _ => hg (measurableSet_singleton q)]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hq : g ⁻¹' {q} = shift k ⁻¹' (cylinder q.1 ∩ shift (m : ℤ) ⁻¹' cylinder q.2) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.ext_iff, g, Set.mem_inter_iff]
      rw [← Set.mem_singleton_iff (a := f x), ← Set.mem_singleton_iff (a := f (shift m x)),
        ← Set.mem_preimage, ← Set.mem_preimage (f := f), hfib, hfib]
      simp only [Set.mem_preimage, shift_shift, add_comm]
    rw [hq, measureReal_preimage_shift hinv k
      ((measurableSet_cylinder _).inter (measurable_shift _ (measurableSet_cylinder _)))]
  simp only [hB2, hB1, Finset.sum_mul_sum, ← Finset.sum_product']
  exact tendsto_finsetSum _ fun q _ => hmix n q.1 q.2

/-- An invariant probability measure on `ℤ → α`, `α` finite, that is mixing on the cylinders
`[w]`, that is `ν([w] ∩ σ^{-m}[w']) → ν([w]) ν([w'])`, is ergodic.
Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem ergodic_of_tendsto_measureReal_cylinder_inter {ν : Measure (ℤ → α)}
    [IsProbabilityMeasure ν] (hinv : MeasurePreserving (shift 1) ν ν)
    (hmix : ∀ (n : ℕ) (w w' : Fin n → α),
      Tendsto (fun m : ℕ => ν.real (cylinder w ∩ shift (m : ℤ) ⁻¹' cylinder w')) atTop
        (𝓝 (ν.real (cylinder w) * ν.real (cylinder w')))) :
    Ergodic (shift 1) ν :=
  ergodic_of_tendsto_measureReal_inter hinv fun _ hB =>
    tendsto_measureReal_inter_of_cylinder hinv hmix hB

end Mixing

/-! ### Independent blocks of a Bernoulli measure -/

section Blocks

variable {ι : Type*} {a b : ℕ}

/-- The words `z` of length `a + b` whose first `a` symbols form a word of `S` and whose last
`b` symbols form a word of `T`. Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
def appendSet (S : Set (Fin a → ι)) (T : Set (Fin b → ι)) : Set (Fin (a + b) → ι) :=
  {z | (fun j => z (Fin.castAdd b j)) ∈ S ∧ (fun j => z (Fin.natAdd a j)) ∈ T}

/-- An event of the first `a` symbols together with a shifted event of the next `b` symbols is
an event of the first `a + b` symbols. Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem block_inter_shift_block (S : Set (Fin a → ι)) (T : Set (Fin b → ι)) :
    block a ⁻¹' S ∩ shift a ⁻¹' (block b ⁻¹' T) = block (a + b) ⁻¹' appendSet S T := by
  ext x
  have e1 : (fun j => block (a + b) x (Fin.castAdd b j)) = block a x :=
    funext fun j => by simp [block]
  have e2 : (fun j => block (a + b) x (Fin.natAdd a j)) = block b (shift a x) :=
    funext fun j => by simp [block, shift]
  simp only [Set.mem_inter_iff, Set.mem_preimage, appendSet, Set.mem_ofPred_eq, e1, e2]

/-- `ε_L(𝐢) = ∑_{j < L} o(i_j)` as a function of the block `i_0 ⋯ i_{L-1}`.
Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem eps_natCast_eq_sum_block (o : ι → ZMod 2) (x : ℤ → ι) (L : ℕ) :
    eps o x L = ∑ j : Fin L, o (block L x j) := by
  rw [eps_natCast, ← Fin.sum_univ_eq_sum_range (fun j : ℕ => o (x j))]
  rfl

/-- The cocycle identity `ε_{m+k}(𝐢) = ε_m(𝐢) + ε_k(σ^m 𝐢)`, a form of
`eq:tau_omega_sigma_commutative1`. -/
theorem eps_add (o : ι → ZMod 2) (x : ℤ → ι) (m k : ℤ) :
    eps o x (m + k) = eps o x m + eps o (shift m x) k := by
  rw [eps_shift, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- The words `w` of length `L` with `∑_j o(w_j) = d`, an even or an odd number of
anti-diagonal symbols. Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
def parSet (o : ι → ZMod 2) (L : ℕ) (d : ZMod 2) : Set (Fin L → ι) := {w | ∑ j, o (w j) = d}

/-- The event `ε_L = d` depends on the block `i_0 ⋯ i_{L-1}`.
Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem setOf_eps_eq (o : ι → ZMod 2) (L : ℕ) (d : ZMod 2) :
    {x : ℤ → ι | eps o x L = d} = block L ⁻¹' parSet o L d := by
  ext x
  simp [parSet, eps_natCast_eq_sum_block]

variable [MeasurableSpace ι]

/-- The measure of a preimage `f^{-1}(S)` under a map into a finite type with measurable
fibres is `∑_c [c ∈ S] ν(f^{-1}{c})`. Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem measureReal_preimage_eq_sum_ite {X γ : Type*} [MeasurableSpace X] [Fintype γ]
    (ν : Measure X) [IsFiniteMeasure ν] {f : X → γ} (hf : ∀ c, MeasurableSet (f ⁻¹' {c}))
    (S : Set γ) [DecidablePred (· ∈ S)] :
    ν.real (f ⁻¹' S) = ∑ c, if c ∈ S then ν.real (f ⁻¹' {c}) else 0 := by
  rw [← sum_measureReal_inter_preimage_singleton ν hf (f ⁻¹' S)]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs with hc
  · congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hc, h⟩⟩
  · rw [show f ⁻¹' S ∩ f ⁻¹' {c} = ∅ from ?_, measureReal_empty]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, iff_false, not_and]
    rintro h rfl
    exact hc h

variable [Fintype ι] [MeasurableSingletonClass ι]

/-- Independence of disjoint blocks under a Bernoulli measure: an event `S` of the symbols
`i_0 ⋯ i_{a-1}` and an event `T` of the symbols `i_a ⋯ i_{a+b-1}` satisfy
`μ(S ∩ σ^{-a} T) = μ(S) μ(T)`, by `bernoulli_cylinder` for the concatenated words.
Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem bernoulli_block_inter_shift_block (p : Measure ι) [IsProbabilityMeasure p]
    (S : Set (Fin a → ι)) (T : Set (Fin b → ι)) :
    (bernoulli p).real (block a ⁻¹' S ∩ shift a ⁻¹' (block b ⁻¹' T)) =
      (bernoulli p).real (block a ⁻¹' S) * (bernoulli p).real (block b ⁻¹' T) := by
  classical
  set F : (ℤ → ι) → (Fin a → ι) × (Fin b → ι) := fun x => (block a x, block b (shift a x))
  have hF : Measurable F :=
    (measurable_block a).prodMk ((measurable_block b).comp (measurable_shift a))
  have hset : block a ⁻¹' S ∩ shift a ⁻¹' (block b ⁻¹' T) = F ⁻¹' (S ×ˢ T) := rfl
  have hfib : ∀ q : (Fin a → ι) × (Fin b → ι), (bernoulli p).real (F ⁻¹' {q}) =
      (bernoulli p).real (cylinder q.1) * (bernoulli p).real (cylinder q.2) := by
    rintro ⟨u, u'⟩
    have h : F ⁻¹' {(u, u')} = cylinder (Fin.append u u') := by
      rw [cylinder_append, cylinder_eq_preimage, cylinder_eq_preimage]
      ext x
      simp [F, Prod.ext_iff]
    rw [h, measureReal_bernoulli_cylinder, measureReal_bernoulli_cylinder,
      measureReal_bernoulli_cylinder, Fin.prod_univ_add]
    simp [Fin.append_left, Fin.append_right]
  rw [hset, measureReal_preimage_eq_sum_ite _ (fun q => hF (measurableSet_singleton q)),
    measureReal_preimage_eq_sum_ite _ (fun u => measurable_block a (measurableSet_singleton u)) S,
    measureReal_preimage_eq_sum_ite _ (fun u => measurable_block b (measurableSet_singleton u)) T,
    Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => ?_
  rw [hfib, ← cylinder_eq_preimage, ← cylinder_eq_preimage]
  simp only [Set.mem_prod]
  split_ifs <;> simp_all

/-- The recursion for the parity of the number of anti-diagonal symbols under a Bernoulli
measure: `μ(ε_{L+1} = d) = ∑_e μ(ε_L = e) μ(ε_1 = d - e)`.
Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem bernoulli_parity_succ (o : ι → ZMod 2) (p : Measure ι) [IsProbabilityMeasure p]
    (L : ℕ) (d : ZMod 2) :
    (bernoulli p).real {x | eps o x ((L + 1 : ℕ) : ℤ) = d} =
      ∑ e, (bernoulli p).real {x | eps o x L = e} *
        (bernoulli p).real {x | eps o x ((1 : ℕ) : ℤ) = d - e} := by
  have hf : ∀ e : ZMod 2, MeasurableSet ((fun x : ℤ → ι => eps o x L) ⁻¹' {e}) := fun e => by
    change MeasurableSet {x : ℤ → ι | eps o x L = e}
    rw [setOf_eps_eq]
    exact measurable_block L (Set.toFinite _).measurableSet
  rw [← sum_measureReal_inter_preimage_singleton _ hf]
  refine Finset.sum_congr rfl fun e _ => ?_
  have h : {x : ℤ → ι | eps o x ((L + 1 : ℕ) : ℤ) = d} ∩
      (fun x : ℤ → ι => eps o x L) ⁻¹' {e} =
      block L ⁻¹' parSet o L e ∩ shift L ⁻¹' (block 1 ⁻¹' parSet o 1 (d - e)) := by
    rw [← setOf_eps_eq, ← setOf_eps_eq]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    rw [Nat.cast_add, eps_add]
    constructor
    · rintro ⟨h1, h2⟩
      rw [h2] at h1
      exact ⟨h2, by rw [← h1]; ring⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [h1, h2]; ring, h1⟩
  rw [h, bernoulli_block_inter_shift_block, ← setOf_eps_eq, ← setOf_eps_eq]

/-- Under a Bernoulli measure the parities are complementary:
`μ(ε_L = 0) + μ(ε_L = 1) = 1`. Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem bernoulli_parity_add (o : ι → ZMod 2) (p : Measure ι) [IsProbabilityMeasure p]
    (L : ℕ) :
    (bernoulli p).real {x | eps o x L = 0} + (bernoulli p).real {x | eps o x L = 1} = 1 := by
  have hf : ∀ e : ZMod 2, MeasurableSet ((fun x : ℤ → ι => eps o x L) ⁻¹' {e}) := fun e => by
    change MeasurableSet {x : ℤ → ι | eps o x L = e}
    rw [setOf_eps_eq]
    exact measurable_block L (Set.toFinite _).measurableSet
  have h := sum_measureReal_inter_preimage_singleton (bernoulli p) hf Set.univ
  rw [sum_zmod_two, probReal_univ] at h
  simp only [Set.univ_inter] at h
  exact h

/-- The bias of the parity of `L` independent symbols is the `L`-th power of the bias of one
symbol: `μ(ε_L = 0) - μ(ε_L = 1) = (μ(ε_1 = 0) - μ(ε_1 = 1))^L`.
Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem bernoulli_parity_sub (o : ι → ZMod 2) (p : Measure ι) [IsProbabilityMeasure p]
    (L : ℕ) :
    (bernoulli p).real {x | eps o x L = 0} - (bernoulli p).real {x | eps o x L = 1} =
      ((bernoulli p).real {x | eps o x ((1 : ℕ) : ℤ) = 0} -
        (bernoulli p).real {x | eps o x ((1 : ℕ) : ℤ) = 1}) ^ L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [bernoulli_parity_succ, bernoulli_parity_succ, sum_zmod_two, sum_zmod_two, pow_succ,
      ← ih]
    have e1 : (0 : ZMod 2) - 1 = 1 := by decide
    have e2 : (1 : ZMod 2) - 1 = 0 := by decide
    simp only [sub_zero, e1, e2]
    ring

/-- The parity of the number of anti-diagonal symbols among `i_0, …, i_{L-1}` is
asymptotically uniform under a Bernoulli measure giving both types positive probability.
Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem tendsto_bernoulli_parity (o : ι → ZMod 2) (p : Measure ι) [IsProbabilityMeasure p]
    (h0 : 0 < (bernoulli p).real {x | eps o x ((1 : ℕ) : ℤ) = 0})
    (h1 : 0 < (bernoulli p).real {x | eps o x ((1 : ℕ) : ℤ) = 1}) (d : ZMod 2) :
    Tendsto (fun L : ℕ => (bernoulli p).real {x | eps o x L = d}) atTop (𝓝 (1 / 2)) := by
  have hsum := bernoulli_parity_add o p 1
  have hr : |(bernoulli p).real {x | eps o x ((1 : ℕ) : ℤ) = 0} -
      (bernoulli p).real {x | eps o x ((1 : ℕ) : ℤ) = 1}| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have hD := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr)
  have hval : ∀ L : ℕ, (bernoulli p).real {x | eps o x L = d} =
      (1 + (if d = 0 then 1 else -1) * ((bernoulli p).real {x | eps o x L = 0} -
        (bernoulli p).real {x | eps o x L = 1})) / 2 := by
    intro L
    have hs := bernoulli_parity_add o p L
    rcases zmod_two_cases d with rfl | rfl
    · simp only [ite_true]
      linarith
    · simp only [show (1 : ZMod 2) ≠ 0 by decide, ite_false]
      linarith
  have hfun : (fun L : ℕ => (bernoulli p).real {x | eps o x L = d}) = fun L : ℕ =>
      (1 + (if d = 0 then 1 else -1) * ((bernoulli p).real {x | eps o x ((1 : ℕ) : ℤ) = 0} -
        (bernoulli p).real {x | eps o x ((1 : ℕ) : ℤ) = 1}) ^ L) / 2 :=
    funext fun L => by rw [hval L, bernoulli_parity_sub]
  rw [hfun]
  have := ((hD.const_mul (if d = 0 then (1 : ℝ) else -1)).const_add 1).div_const 2
  simpa using this

omit [Fintype ι] in
/-- A Bernoulli measure charging a symbol `i` with `o(i) = c` gives the event `o(i_0) = c`
positive measure. Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem bernoulli_parity_one_pos (o : ι → ZMod 2) (p : Measure ι) [IsProbabilityMeasure p]
    {i : ι} (hi : 0 < p.real {i}) :
    0 < (bernoulli p).real {x | eps o x ((1 : ℕ) : ℤ) = o i} := by
  have hsub : cylinder ![i] ⊆ {x : ℤ → ι | eps o x ((1 : ℕ) : ℤ) = o i} := by
    intro x hx
    have h := hx 0
    simp only [Fin.val_zero, Nat.cast_zero, Matrix.cons_val_zero] at h
    change eps o x ((1 : ℕ) : ℤ) = o i
    rw [eps_natCast, Finset.sum_range_one, Nat.cast_zero, h]
  have hpos : 0 < (bernoulli p).real (cylinder ![i]) := by
    rw [measureReal_bernoulli_cylinder]
    simpa using hi
  exact hpos.trans_le (measureReal_mono hsub)

end Blocks

/-! ### The orientation lift -/

section Lift

variable {ι : Type*} (o : ι → ZMod 2)

/-- The lift of `𝐢 ∈ Σ` to `Σ_Z` with initial axis `c`: the symbol `(i_k, c + ε_k(𝐢))` at
time `k`. Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
def orientLift (c : ZMod 2) (x : ℤ → ι) : ℤ → ι × ZMod 2 := fun k => (x k, c + eps o x k)

/-- The lift with initial axis `0` is the coding `τ`.
Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem orientLift_zero : orientLift o 0 = tau o := by
  funext x k
  simp [orientLift]

/-- The lift with initial axis `1` is the coding `ω`.
Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem orientLift_one : orientLift o 1 = omega o := by
  funext x k
  simp [orientLift, add_comm]

/-- The lift of `𝐢` lies over `𝐢`. Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
@[simp] theorem unCode_orientLift (c : ZMod 2) (x : ℤ → ι) : unCode (orientLift o c x) = x :=
  rfl

/-- The lift of `𝐢` with initial axis `c` lies in the cylinder `[v]` of `Σ_Z` exactly when `v`
is the lift `liftBlock o c (i_0 ⋯ i_{n-1})` of the planar word.
Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem orientLift_mem_cylinder_iff {n : ℕ} (c : ZMod 2) (x : ℤ → ι)
    (v : Fin n → ι × ZMod 2) :
    orientLift o c x ∈ cylinder v ↔ liftBlock o c (block n x) = v := by
  rw [mem_cylinder, funext_iff]
  refine forall_congr' fun k => ?_
  suffices h : orientLift o c x k = liftBlock o c (block n x) k by rw [h]
  have hsum : ∑ j ∈ Finset.Iio k, o (block n x j) = ∑ j ∈ Finset.range k, o (x j) := by
    rw [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, Finset.sum_map]
    rfl
  change (x k, c + eps o x ((k : ℕ) : ℤ)) = (x k, c + ∑ j ∈ Finset.Iio k, o (block n x j))
  rw [hsum, eps_natCast]

/-- `thm:tau_omega_sigma_commutative` for the lifts: `σ^m` of the lift of `𝐢` with initial
axis `c` is the lift of `σ^m 𝐢` with initial axis `c + ε_m(𝐢)`. -/
theorem shift_orientLift (c : ZMod 2) (x : ℤ → ι) (m : ℤ) :
    shift m (orientLift o c x) = orientLift o (c + eps o x m) (shift m x) := by
  funext k
  simp only [shift_apply, orientLift, eps_add, add_assoc]

variable [MeasurableSpace ι]

/-- The orientation lift `\widetilde μ = (τ_*μ + ω_*μ) / 2` of a measure `μ` on `Σ`, in the
proof of `thm:eq_state_proj_dim` for `s ≥ 2`: the initial axis is chosen uniformly. -/
noncomputable def orientationLift (μ : Measure (ℤ → ι)) : Measure (ℤ → ι × ZMod 2) :=
  avgMeasure (μ.map (tau o)) (μ.map (omega o))

/-- The orientation lift of a probability measure is a probability measure.
Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
instance isProbabilityMeasure_orientationLift (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (orientationLift o μ) :=
  isProbabilityMeasure_avgMeasure _ _

variable [Fintype ι] [MeasurableSingletonClass ι]

/-- The lifts are measurable. Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem measurable_orientLift (c : ZMod 2) : Measurable (orientLift o c) :=
  measurable_pi_iff.2 fun n => (measurable_pi_apply n).prodMk ((measurable_eps o n).const_add c)

/-- `\widetilde μ(E) = (μ(τ^{-1} E) + μ(ω^{-1} E)) / 2`, written as the average over the two
initial axes. Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem orientationLift_real_apply (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ]
    {E : Set (ℤ → ι × ZMod 2)} (hE : MeasurableSet E) :
    (orientationLift o μ).real E = (∑ c, μ.real (orientLift o c ⁻¹' E)) / 2 := by
  rw [orientationLift, avgMeasure, measureReal_nnreal_smul_apply, measureReal_add_apply,
    map_measureReal_apply (measurable_tau o) hE, map_measureReal_apply (measurable_omega o) hE,
    sum_zmod_two, orientLift_zero, orientLift_one, NNReal.coe_inv, NNReal.coe_ofNat]
  ring

/-- The orientation lift is carried by `Σ_Z`.
Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem orientationLift_subshift_compl (μ : Measure (ℤ → ι)) :
    orientationLift o μ (subshift o)ᶜ = 0 := by
  have h : ∀ c : ZMod 2, orientLift o c ⁻¹' (subshift o)ᶜ = ∅ := fun c => by
    ext x
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false,
      not_not]
    rcases zmod_two_cases c with rfl | rfl
    · rw [orientLift_zero]
      exact tau_mem_subshift x
    · rw [orientLift_one]
      exact omega_mem_subshift x
  have hm : MeasurableSet (subshift o)ᶜ := (measurableSet_subshift o).compl
  rw [orientationLift, avgMeasure, Measure.smul_apply, Measure.add_apply,
    Measure.map_apply (measurable_tau o) hm, Measure.map_apply (measurable_omega o) hm,
    ← orientLift_zero, ← orientLift_one, h, h]
  simp

/-- The orientation lift lies over `μ`: its image under the factor map `q = unCode` is `μ`.
Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem map_unCode_orientationLift (μ : Measure (ℤ → ι)) :
    (orientationLift o μ).map unCode = μ := by
  rw [orientationLift, avgMeasure, Measure.map_smul _ measurable_unCode.aemeasurable,
    Measure.map_add _ _ measurable_unCode, Measure.map_map measurable_unCode (measurable_tau o),
    Measure.map_map measurable_unCode (measurable_omega o)]
  have h1 : unCode ∘ tau o = id := rfl
  have h2 : unCode ∘ omega o = id := rfl
  rw [h1, h2, Measure.map_id]
  ext s hs
  rw [Measure.smul_apply, Measure.add_apply, ENNReal.smul_def, smul_eq_mul, ← two_mul,
    ← mul_assoc]
  simp [ENNReal.inv_mul_cancel]

/-- The orientation lift of an invariant measure is invariant: `\widetilde μ` is stationary.
Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem measurePreserving_shift_orientationLift {μ : Measure (ℤ → ι)}
    (hinv : MeasurePreserving (shift 1) μ μ) :
    MeasurePreserving (shift 1) (orientationLift o μ) (orientationLift o μ) :=
  measurePreserving_shift_avgMeasure_coding o hinv

/-- Each lift `liftBlock o c w` of a planar word `w` of positive length carries half of the
mass `μ([w])`: `\widetilde μ([liftBlock o c w]) = μ([w]) / 2`. The two lifts of `w` are the only
admissible words over `w`. Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem orientationLift_real_cylinder_liftBlock (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ]
    {n : ℕ} (c : ZMod 2) (w : Fin (n + 1) → ι) :
    (orientationLift o μ).real (cylinder (liftBlock o c w)) = μ.real (cylinder w) / 2 := by
  classical
  rw [orientationLift_real_apply o μ (measurableSet_cylinder _)]
  congr 1
  have h : ∀ c' : ZMod 2, orientLift o c' ⁻¹' cylinder (liftBlock o c w) =
      if c' = c then cylinder w else ∅ := fun c' => by
    ext x
    rw [Set.mem_preimage, orientLift_mem_cylinder_iff, cylinder_eq_preimage]
    have hinj := @liftBlock_injective _ o n (block (n + 1) x, c') (w, c)
    split_ifs with hc
    · subst hc
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => (Prod.ext_iff.1 (hinj h)).1, fun h => by rw [h]⟩
    · simp only [Set.mem_empty_iff_false, iff_false]
      exact fun h => hc (Prod.ext_iff.1 (hinj h)).2
  simp only [h, apply_ite, measureReal_empty]
  rw [Finset.sum_ite_eq']
  simp

/-- `\overline{h}_0(\widetilde μ) = h_0(μ)`: the lift is carried by `Σ_Z`, lies over `μ`, and
each planar word has exactly two lifts, so the block entropies differ by at most `log 2`
(`entropy_map_unCode`). Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem entropy_orientationLift (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) : entropy (orientationLift o μ) = entropy μ := by
  have h := entropy_map_unCode o (orientationLift o μ)
    (measurePreserving_shift_orientationLift o hinv) (orientationLift_subshift_compl o μ)
  rw [map_unCode_orientationLift] at h
  exact h.symm

/-- The transition rule of `Σ_Z` is decidable.
Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
instance decidableTrans (p q : ι × ZMod 2) : Decidable (Trans o p q) :=
  inferInstanceAs (Decidable (q.2 = p.2 + o p.1))

omit [MeasurableSpace ι] [Fintype ι] [MeasurableSingletonClass ι] in
/-- The lifted word `liftBlock o c w` follows the transition rule of `Σ_Z`: the axis at time
`j + 1` is the axis at time `j` plus `o(w_j)`.
Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem liftBlock_succ_snd {n : ℕ} (c : ZMod 2) (w : Fin (n + 1) → ι) (j : Fin n) :
    (liftBlock o c w j.succ).2 = (liftBlock o c w j.castSucc).2 + o (w j.castSucc) := by
  simp only [liftBlock]
  rw [add_assoc]
  congr 1
  have h : Finset.Iio j.succ = insert j.castSucc (Finset.Iio j.castSucc) := by
    ext i
    simp only [Finset.mem_Iio, Finset.mem_insert, Fin.lt_def, Fin.ext_iff, Fin.val_succ,
      Fin.val_castSucc]
    omega
  rw [h, Finset.sum_insert (by simp), add_comm]

omit [MeasurableSpace ι] [Fintype ι] [MeasurableSingletonClass ι] in
/-- A word `v` of `n + 1` symbols of `ι × ZMod 2` is the lift of its planar word from its initial
axis exactly when consecutive symbols follow the transition rule of `Σ_Z`.
Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem eq_liftBlock_iff {n : ℕ} (v : Fin (n + 1) → ι × ZMod 2) :
    v = liftBlock o (v 0).2 (fun j => (v j).1) ↔
      ∀ j : Fin n, Trans o (v j.castSucc) (v j.succ) := by
  constructor
  · intro h j
    unfold Trans
    rw [h]
    simp only [liftBlock_fst]
    exact liftBlock_succ_snd o _ _ j
  · intro h
    funext k
    refine Prod.ext rfl ?_
    induction k using Fin.induction with
    | zero => rw [liftBlock_zero_snd]
    | succ j ih => rw [liftBlock_succ_snd, ← ih, h j]

omit [MeasurableSpace ι] [Fintype ι] [MeasurableSingletonClass ι] in
/-- Each planar word `w` of positive length has exactly two orientation lifts, as in the proof of
`thm:eq_state_proj_dim` (tex line 2703): an admissible word `v` of `Σ_Z` over `w` is
`liftBlock o 0 w` or `liftBlock o 1 w`, and these two lifts differ. -/
theorem admissible_iff_eq_liftBlock {n : ℕ} (v : Fin (n + 1) → ι × ZMod 2)
    (w : Fin (n + 1) → ι) :
    ((∀ j, (v j).1 = w j) ∧ ∀ j : Fin n, Trans o (v j.castSucc) (v j.succ)) ↔
      v = liftBlock o 0 w ∨ v = liftBlock o 1 w := by
  constructor
  · rintro ⟨hw, ht⟩
    have hv := (eq_liftBlock_iff o v).2 ht
    have hw' : (fun j => (v j).1) = w := funext hw
    rw [hw'] at hv
    rcases zmod_two_cases (v 0).2 with h | h
    · exact Or.inl (hv.trans (by rw [h]))
    · exact Or.inr (hv.trans (by rw [h]))
  · intro h
    have key : ∀ c : ZMod 2, v = liftBlock o c w →
        (∀ j, (v j).1 = w j) ∧ ∀ j : Fin n, Trans o (v j.castSucc) (v j.succ) := by
      rintro c rfl
      refine ⟨fun j => rfl, fun j => ?_⟩
      unfold Trans
      simp only [liftBlock_fst]
      exact liftBlock_succ_snd o c w j
    rcases h with h | h
    · exact key 0 h
    · exact key 1 h

omit [MeasurableSpace ι] [Fintype ι] [MeasurableSingletonClass ι] in
/-- The two orientation lifts of a planar word of positive length differ in their initial axis,
as in the proof of `thm:eq_state_proj_dim` (tex line 2703). -/
theorem liftBlock_zero_ne_one {n : ℕ} (w : Fin (n + 1) → ι) :
    liftBlock o 0 w ≠ liftBlock o 1 w := fun h => by
  have h0 := congrArg (fun v => (v 0).2) h
  simp only [liftBlock_zero_snd] at h0
  exact absurd h0 (by decide)

/-- The cylinder measures of the orientation lift: `\widetilde μ([v]) = μ([v_1]) / 2` when the
word `v` of `Σ_Z` is admissible, with planar word `v_1`, and `0` otherwise.
Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem orientationLift_real_cylinder (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ] {n : ℕ}
    (v : Fin (n + 1) → ι × ZMod 2) :
    (orientationLift o μ).real (cylinder v) =
      if ∀ j : Fin n, Trans o (v j.castSucc) (v j.succ) then
        μ.real (cylinder fun j => (v j).1) / 2 else 0 := by
  split_ifs with h
  · rw [(eq_liftBlock_iff o v).2 h]
    exact orientationLift_real_cylinder_liftBlock o μ _ _
  · rw [orientationLift_real_apply o μ (measurableSet_cylinder v)]
    have h0 : ∀ c : ZMod 2, orientLift o c ⁻¹' cylinder v = ∅ := fun c => by
      ext x
      rw [Set.mem_preimage, orientLift_mem_cylinder_iff]
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hv
      apply h
      subst hv
      intro j
      unfold Trans
      simp only [liftBlock_fst]
      exact liftBlock_succ_snd o c _ j
    simp [h0]

/-- The lift of a Bernoulli measure with weights `p` is the stationary Markov measure on `Σ_Z`
with initial distribution `π(i, c) = p_i / 2` and transition probabilities
`Q((i, c), (j, c')) = p_j` when `c' = c + o(i)` and `0` otherwise: diagonal symbols preserve the
axis and anti-diagonal symbols switch it.
Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem orientationLift_bernoulli_cylinder (p : Measure ι) [IsProbabilityMeasure p] {n : ℕ}
    (v : Fin (n + 1) → ι × ZMod 2) :
    (orientationLift o (bernoulli p)).real (cylinder v) =
      p.real {(v 0).1} / 2 *
        ∏ j : Fin n, if Trans o (v j.castSucc) (v j.succ) then p.real {(v j.succ).1} else 0 := by
  classical
  rw [orientationLift_real_cylinder, measureReal_bernoulli_cylinder]
  split_ifs with h
  · rw [Fin.prod_univ_succ]
    simp only [h, ite_true]
    ring
  · simp only [not_forall] at h
    obtain ⟨j, hj⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), mul_zero]

omit [MeasurableSpace ι] [Fintype ι] [MeasurableSingletonClass ι] in
/-- The set identity behind the mixing of the lift: the lift with initial axis `c` meets
`[v] ∩ σ^{-(n+L)}[v']`, with `ε_L(σ^n 𝐢) = d`, exactly when `i_0 ⋯ i_{n-1}` lifts to `v` from
`c`, the next `L` symbols have parity `d`, and the following `n` symbols lift to `v'` from the
axis `c + ∑_j o(v_j) + d`. Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem orientLift_preimage_cylinder_inter_shift (c : ZMod 2) {n : ℕ}
    (v v' : Fin n → ι × ZMod 2) (L : ℕ) (d : ZMod 2) :
    orientLift o c ⁻¹' (cylinder v ∩ shift ((L + n : ℕ) : ℤ) ⁻¹' cylinder v') ∩
        {x | eps o (shift n x) L = d} =
      block n ⁻¹' {u | liftBlock o c u = v} ∩ shift n ⁻¹' (block L ⁻¹' parSet o L d ∩
        shift L ⁻¹' (block n ⁻¹' {u | liftBlock o (c + ∑ j, o (v j).1 + d) u = v'})) := by
  ext x
  have hshift : shift (L : ℤ) (shift (n : ℤ) x) = shift ((L + n : ℕ) : ℤ) x := by
    rw [shift_shift]
    congr 1
    push_cast
    ring
  have heps : eps o x ((L + n : ℕ) : ℤ) = eps o x n + eps o (shift n x) L := by
    rw [← eps_add]
    congr 1
    push_cast
    ring
  have hsv : liftBlock o c (block n x) = v → eps o x n = ∑ j, o (v j).1 := fun h => by
    rw [eps_natCast_eq_sum_block, ← h]
    rfl
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
    orientLift_mem_cylinder_iff, shift_orientLift, hshift, heps, ← setOf_eps_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h3, ?_⟩
    rwa [hsv h1, h3, ← add_assoc] at h2
  · rintro ⟨h1, h3, h2⟩
    refine ⟨⟨h1, ?_⟩, h3⟩
    rwa [hsv h1, h3, ← add_assoc]

/-- The lift of a Bernoulli measure giving both matrix types positive probability is mixing:
`\widetilde μ([v] ∩ σ^{-m}[v']) → \widetilde μ([v]) \widetilde μ([v'])`. For `m = n + L` the
measure is a sum over the initial axis and the parity `d` of the `L` intermediate symbols of
the products of three independent block probabilities, and the parity is asymptotically
uniform. Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem tendsto_orientationLift_bernoulli_cylinder_inter (p : Measure ι) [IsProbabilityMeasure p]
    (h0 : 0 < (bernoulli p).real {x | eps o x ((1 : ℕ) : ℤ) = 0})
    (h1 : 0 < (bernoulli p).real {x | eps o x ((1 : ℕ) : ℤ) = 1})
    {n : ℕ} (v v' : Fin n → ι × ZMod 2) :
    Tendsto (fun m : ℕ => (orientationLift o (bernoulli p)).real
        (cylinder v ∩ shift (m : ℤ) ⁻¹' cylinder v')) atTop
      (𝓝 ((orientationLift o (bernoulli p)).real (cylinder v) *
        (orientationLift o (bernoulli p)).real (cylinder v'))) := by
  set μ := bernoulli p
  set M : ZMod 2 → ℝ := fun c => μ.real (block n ⁻¹' {u | liftBlock o c u = v})
  set M' : ZMod 2 → ℝ := fun e => μ.real (block n ⁻¹' {u | liftBlock o e u = v'})
  set sv := ∑ j, o (v j).1
  have hC : ∀ (w : Fin n → ι × ZMod 2) (c : ZMod 2),
      orientLift o c ⁻¹' cylinder w = block n ⁻¹' {u | liftBlock o c u = w} := fun w c => by
    ext x
    exact orientLift_mem_cylinder_iff o c x w
  have hν1 : (orientationLift o μ).real (cylinder v) = (∑ c, M c) / 2 := by
    rw [orientationLift_real_apply o μ (measurableSet_cylinder v)]
    simp only [hC, M]
  have hν2 : (orientationLift o μ).real (cylinder v') = (∑ e, M' e) / 2 := by
    rw [orientationLift_real_apply o μ (measurableSet_cylinder v')]
    simp only [hC, M']
  have hkey : ∀ L : ℕ, (orientationLift o μ).real
      (cylinder v ∩ shift ((L + n : ℕ) : ℤ) ⁻¹' cylinder v') =
      (∑ c, ∑ d, M c * (μ.real {x | eps o x L = d} * M' (c + sv + d))) / 2 := by
    intro L
    have hE : MeasurableSet (cylinder v ∩ shift ((L + n : ℕ) : ℤ) ⁻¹' cylinder v') :=
      (measurableSet_cylinder v).inter (measurable_shift _ (measurableSet_cylinder v'))
    rw [orientationLift_real_apply o μ hE]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    have hf : ∀ d : ZMod 2,
        MeasurableSet ((fun x : ℤ → ι => eps o (shift n x) L) ⁻¹' {d}) := fun d => by
      change MeasurableSet (shift (n : ℤ) ⁻¹' {x : ℤ → ι | eps o x L = d})
      rw [setOf_eps_eq]
      exact measurable_shift _ (measurable_block L (Set.toFinite _).measurableSet)
    rw [← sum_measureReal_inter_preimage_singleton _ hf]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hset := orientLift_preimage_cylinder_inter_shift o c v v' L d
    change μ.real (orientLift o c ⁻¹' (cylinder v ∩ shift ((L + n : ℕ) : ℤ) ⁻¹' cylinder v') ∩
      {x | eps o (shift n x) L = d}) = _
    rw [hset, block_inter_shift_block, bernoulli_block_inter_shift_block,
      ← block_inter_shift_block, bernoulli_block_inter_shift_block, ← setOf_eps_eq]
  rw [← tendsto_add_atTop_iff_nat n]
  simp only [hkey, hν1, hν2]
  have hlim : Tendsto (fun L : ℕ =>
      (∑ c, ∑ d, M c * (μ.real {x | eps o x L = d} * M' (c + sv + d))) / 2) atTop
      (𝓝 ((∑ c, ∑ d, M c * (1 / 2 * M' (c + sv + d))) / 2)) := by
    refine Tendsto.div_const (tendsto_finsetSum _ fun c _ =>
      tendsto_finsetSum _ fun d _ => ?_) 2
    exact ((tendsto_bernoulli_parity o p h0 h1 d).mul_const _).const_mul _
  convert hlim using 2
  have hsum : ∀ c, ∑ d, M' (c + sv + d) = ∑ e, M' e := fun c => by
    simpa [add_assoc] using Equiv.sum_comp (Equiv.addLeft (c + sv)) M'
  simp_rw [← Finset.mul_sum, hsum, ← Finset.sum_mul]
  ring

/-- The lift of a Bernoulli measure giving both matrix types positive probability is ergodic:
it is mixing (`tendsto_orientationLift_bernoulli_cylinder_inter`).
Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem ergodic_orientationLift_bernoulli (p : Measure ι) [IsProbabilityMeasure p] {i₀ i₁ : ι}
    (hi₀ : o i₀ = 0) (hp₀ : 0 < p.real {i₀}) (hi₁ : o i₁ = 1) (hp₁ : 0 < p.real {i₁}) :
    Ergodic (shift 1) (orientationLift o (bernoulli p)) := by
  have h0 := bernoulli_parity_one_pos o p hp₀
  have h1 := bernoulli_parity_one_pos o p hp₁
  rw [hi₀] at h0
  rw [hi₁] at h1
  exact ergodic_of_tendsto_measureReal_cylinder_inter
    (measurePreserving_shift_orientationLift o (measurePreserving_shift_bernoulli p 1))
    fun _ v v' => tendsto_orientationLift_bernoulli_cylinder_inter o p h0 h1 v v'

end Lift

/-! ### The Lyapunov exponents and the projection of the lift -/

universe u

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι)

/-- `\overline{λ}(𝖠, \widetilde μ) = (λ_1(𝖠, μ) + λ_2(𝖠, μ)) / 2` for the orientation lift of an
invariant measure: the lift follows each axis at time `0` with probability one half, so
`\overline{λ}(𝖠, \widetilde μ) = (1/2) ∑_i μ([i]) (log |a_i| + log |b_i|)
= (1/2) ∑_i μ([i]) log |det A_i|`. Used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem lyapBar_orientationLift {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) :
    S.lyapBar (orientationLift S.o μ) = (S.lyapunov₁ μ + S.lyapunov₂ μ) / 2 := by
  have hmeas : Measurable fun y : ℤ → ι × ZMod 2 => Real.log |S.ratio (y 0)| :=
    (Measurable.of_discrete (f := fun p : ι × ZMod 2 => Real.log |S.ratio p|)).comp
      (measurable_pi_apply 0)
  have hint : ∀ (ν : Measure (ℤ → ι × ZMod 2)) [IsFiniteMeasure ν],
      Integrable (fun y : ℤ → ι × ZMod 2 => Real.log |S.ratio (y 0)|) ν := fun ν _ =>
    (Integrable.of_finite (f := fun p : ι × ZMod 2 => Real.log |S.ratio p|)).comp_measurable
      (measurable_pi_apply 0)
  rw [S.lyapunov₁_add_lyapunov₂ hinv, lyapBar, orientationLift, avgMeasure,
    integral_smul_nnreal_measure, integral_add_measure (hint _) (hint _),
    integral_map (measurable_tau S.o).aemeasurable hmeas.aestronglyMeasurable,
    integral_map (measurable_omega S.o).aemeasurable hmeas.aestronglyMeasurable]
  have h1 : ∀ x : ℤ → ι, Real.log |S.ratio (tau S.o x 0)| = Real.log |S.a (x 0)| := fun x => by
    simp [ratio]
  have h2 : ∀ x : ℤ → ι, Real.log |S.ratio (omega S.o x 0)| = Real.log |S.b (x 0)| :=
    fun x => by simp [ratio]
  simp only [h1, h2]
  rw [integral_comp_apply_zero μ (fun i => Real.log |S.a i|),
    integral_comp_apply_zero μ (fun i => Real.log |S.b i|)]
  have hdet : ∀ i, Real.log |(S.mat i).det| = Real.log |S.a i| + Real.log |S.b i| := fun i => by
    rw [mat, abs_det_boxMat,
      Real.log_mul (abs_ne_zero.2 (S.a_ne_zero i)) (abs_ne_zero.2 (S.b_ne_zero i))]
  simp only [hdet, mul_add, Finset.sum_add_distrib, NNReal.smul_def, smul_eq_mul,
    NNReal.coe_inv, NNReal.coe_ofNat]
  ring

/-- If the orientation lift of an invariant measure `μ` is ergodic, then
`λ_1(𝖠, μ) = λ_2(𝖠, μ) = \overline{λ}(𝖠, \widetilde μ)`: Birkhoff's theorem for the lift
(`lyapunov_exponent_gsystem`) gives the backward rate `\overline{λ}(𝖠, \widetilde μ)` along
both lifts `τ(𝐢)` and `ω(𝐢)` for `μ`-almost every `𝐢`, and by
`thm:matrix_products_g_derivatives` the singular values of `A_{i_{-n}} ⋯ A_{i_{-1}}` are the
larger and the smaller of the two scalar contractions, so both exponents equal this rate. -/
theorem lyapunov_eq_of_ergodic_orientationLift {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) (orientationLift S.o μ)) :
    S.lyapunov₁ μ = S.lyapBar (orientationLift S.o μ) ∧
      S.lyapunov₂ μ = S.lyapBar (orientationLift S.o μ) := by
  have : Nonempty ι := nonempty_of_measure μ
  have hrate := S.lyapunov_exponent_gsystem (orientationLift S.o μ) herg
  generalize S.lyapBar (orientationLift S.o μ) = l at hrate ⊢
  obtain ⟨hτ, hω⟩ := ae_of_ae_avgMeasure (m₁ := μ.map (tau S.o)) (m₂ := μ.map (omega S.o))
    (p := fun y => S.HasBackRate y l) hrate
  have hτ' := ae_of_ae_map (measurable_tau S.o).aemeasurable hτ
  have hω' := ae_of_ae_map (measurable_omega S.o).aemeasurable hω
  obtain ⟨C, hC₁, hC₂⟩ := S.exists_abs_log_singularValue_le
  constructor
  · refine tendsto_nhds_unique (S.tendsto_lyapunov₁ hinv) ?_
    refine tendsto_integral_futureWord_div_of_ae_pastWord hinv hC₁ ?_
    filter_upwards [hτ', hω'] with x ha hb
    simpa using S.tendsto_log_norm_matWord_pastWord ha hb
  · refine tendsto_nhds_unique (S.tendsto_lyapunov₂ hinv) ?_
    refine tendsto_integral_futureWord_div_of_ae_pastWord hinv hC₂ ?_
    filter_upwards [hτ', hω'] with x ha hb
    simpa using S.tendsto_log_abs_det_div_norm_matWord_pastWord ha hb

/-- `\overline{π}_* \widetilde μ = (ν_x + ν_y) / 2`: by `eq:commutative_diagram`,
`\overline{π} ∘ τ = proj_x ∘ π` and `\overline{π} ∘ ω = proj_y ∘ π`. -/
theorem map_projBar_orientationLift (μ : Measure (ℤ → ι)) :
    (orientationLift S.o μ).map S.projBar = avgMeasure (S.marginal 0 μ) (S.marginal 1 μ) := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  rw [orientationLift, avgMeasure, avgMeasure,
    Measure.map_smul _ hS.measurable_projBar.aemeasurable,
    Measure.map_add _ _ hS.measurable_projBar,
    Measure.map_map hS.measurable_projBar (measurable_tau S.o),
    Measure.map_map hS.measurable_projBar (measurable_omega S.o),
    S.marginal_eq_map hS, S.marginal_eq_map hS]
  rfl

end System

end BoxLike
