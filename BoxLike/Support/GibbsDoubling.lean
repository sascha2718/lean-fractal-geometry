module

/-
Gibbs measures on the sub-shift `Σ_Z` for arbitrary bounded potentials, and the metric doubling
property of `sec:gibbs_measures` (tex lines 2374 to 2382): "the measure of any ball is at most a
constant times the measure of the corresponding ball with half the radius". The balls are those
of the standard metric `d(𝐢, 𝐣) = 2^{-min{|n| : i_n ≠ j_n}}` of the two-sided shift, which are
the cylinders `[i_{-m} ⋯ i_m]` extended both to the future and to the past.

* `symDist`, `symDist_comm`, `symDist_eq_zero_iff`, `symDist_le_max`: the standard metric of
  the two-sided shift; it is an ultrametric.
* `symCyl`, `symBall`, `symBall_eq_symCyl`, `symBall_eq_univ`: the cylinder
  `[i_{-m} ⋯ i_m]` around `𝐢` and the open ball; the ball of radius `r` with
  `2^{-(m+1)} < r ≤ 2^{-m}` is `[i_{-m} ⋯ i_m]`, and the ball of radius `r > 1` is everything.
* `IsGibbsPotential`, `isGibbsPotential_iff_isGibbsWith`: the Gibbs property of
  `sec:gibbs_measures` for a potential `f : Σ_Z → ℝ` with Birkhoff sums `S_n f`, and its
  agreement with `IsGibbsWith` for one-symbol potentials.
* `IsGibbsPotential.measureReal_cylinder_le_succ`,
  `IsGibbsPotential.measureReal_cylinder_succ_le_shift`: the displayed comparison
  `ν([𝐢|_n]) ≤ C² exp(P + ‖f‖_∞) ν([𝐢|_{n+1}])` and its extension to the past by invariance.
* `IsGibbsPotential.measureReal_symCyl_le_succ`: `ν([i_{-m} ⋯ i_m]) ≤ D ν([i_{-m-1} ⋯ i_{m+1}])`
  with `D = (C² exp(P + ‖f‖_∞))²`.
* `isOpen_symCyl`, `isOpen_symBall`, `isOpen_iff_forall_symBall`: the metric induces the product
  topology, so the cylinders `[i_{-m} ⋯ i_m]` are the balls of the shift.
* `IsGibbsPotential.doubling`, `IsGibbsPotential.doubling_subshift`, `IsGibbs.doubling_symBall`:
  the Gibbs measure is doubling, `ν(B(𝐢, r)) ≤ D ν(B(𝐢, r/2))` for every `𝐢 ∈ Σ_Z` and every
  `r > 0`, also for the balls of `Σ_Z` itself.
-/
public import BoxLike.GibbsProperties
public import BoxLike.Support.SubshiftMixing
public import Mathlib.Dynamics.BirkhoffSum.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

namespace BoxLike

open MeasureTheory Set

/-! ### The standard metric of the two-sided shift -/

section Metric

variable {α : Type*}

/-- `x` and `y` differ at some coordinate `k` with `|k| = n`. -/
def DiffersAt (x y : ℤ → α) (n : ℕ) : Prop := ∃ k : ℤ, k.natAbs = n ∧ x k ≠ y k

open Classical in
/-- The standard metric `d(𝐢, 𝐣) = 2^{-min{|n| : i_n ≠ j_n}}` of the two-sided shift, with
`d(𝐢, 𝐢) = 0`. -/
noncomputable def symDist (x y : ℤ → α) : ℝ :=
  if h : ∃ n, DiffersAt x y n then (1 / 2 : ℝ) ^ Nat.find h else 0

/-- The open ball `B(𝐢, r) = {𝐣 : d(𝐢, 𝐣) < r}`. -/
def symBall (x : ℤ → α) (r : ℝ) : Set (ℤ → α) := {y | symDist x y < r}

/-- The cylinder `[i_{-m} ⋯ i_m]` of the points that agree with `𝐢` at the coordinates
`|k| ≤ m`. -/
def symCyl (x : ℤ → α) (m : ℕ) : Set (ℤ → α) := {y | ∀ k : ℤ, k.natAbs ≤ m → y k = x k}

/-- Differing at level `n` is a symmetric relation. -/
theorem differsAt_comm {x y : ℤ → α} {n : ℕ} : DiffersAt x y n ↔ DiffersAt y x n :=
  exists_congr fun _ => and_congr_right fun _ => ne_comm

/-- The metric is symmetric. -/
theorem symDist_comm (x y : ℤ → α) : symDist x y = symDist y x := by
  classical
  have h : (∃ n, DiffersAt x y n) ↔ ∃ n, DiffersAt y x n := exists_congr fun _ => differsAt_comm
  unfold symDist
  by_cases hx : ∃ n, DiffersAt x y n
  · rw [dite_eq_left hx, dite_eq_left (h.1 hx)]
    congr 1
    exact (Nat.find_congr' fun {_} => differsAt_comm)
  · rw [dite_eq_right hx, dite_eq_right (fun h' => hx (h.2 h'))]

/-- The metric is non-negative. -/
theorem symDist_nonneg (x y : ℤ → α) : 0 ≤ symDist x y := by
  unfold symDist
  split_ifs <;> positivity

/-- The metric vanishes exactly on the diagonal. -/
theorem symDist_eq_zero_iff {x y : ℤ → α} : symDist x y = 0 ↔ x = y := by
  classical
  unfold symDist
  constructor
  · intro h
    by_contra hxy
    obtain ⟨k, hk⟩ : ∃ k, x k ≠ y k := by
      by_contra h'
      push Not at h'
      exact hxy (funext h')
    have hd : ∃ n, DiffersAt x y n := ⟨k.natAbs, k, rfl, hk⟩
    rw [dite_eq_left hd] at h
    exact absurd h (pow_ne_zero _ (by norm_num))
  · rintro rfl
    rw [dite_eq_right]
    rintro ⟨n, k, -, hk⟩
    exact hk rfl

/-- `d(𝐢, 𝐣) < 2^{-m}` exactly when `𝐢` and `𝐣` agree at the coordinates `|k| ≤ m`. -/
theorem symDist_lt_pow_iff {x y : ℤ → α} (m : ℕ) :
    symDist x y < (1 / 2 : ℝ) ^ m ↔ ∀ k : ℤ, k.natAbs ≤ m → y k = x k := by
  classical
  unfold symDist
  by_cases hd : ∃ n, DiffersAt x y n
  · rw [dite_eq_left hd, pow_lt_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num),
      Nat.lt_find_iff]
    constructor
    · intro h k hk
      by_contra hne
      exact h k.natAbs hk ⟨k, rfl, Ne.symm hne⟩
    · rintro h n hn ⟨k, rfl, hk⟩
      exact hk (h k hn).symm
  · rw [dite_eq_right hd]
    refine ⟨fun _ k _ => ?_, fun _ => by positivity⟩
    by_contra hne
    exact hd ⟨k.natAbs, k, rfl, Ne.symm hne⟩

/-- The metric is an ultrametric: `d(𝐢, 𝐤) ≤ max{d(𝐢, 𝐣), d(𝐣, 𝐤)}`. -/
theorem symDist_le_max (x y z : ℤ → α) :
    symDist x z ≤ max (symDist x y) (symDist y z) := by
  classical
  by_cases hxz : ∃ n, DiffersAt x z n
  · set N := Nat.find hxz
    have hN : symDist x z = (1 / 2 : ℝ) ^ N := by unfold symDist; rw [dite_eq_left hxz]
    by_contra hlt
    push Not at hlt
    rw [hN, max_lt_iff] at hlt
    have h1 := (symDist_lt_pow_iff N).1 hlt.1
    have h2 := (symDist_lt_pow_iff N).1 hlt.2
    obtain ⟨k, hk, hne⟩ := Nat.find_spec hxz
    exact hne ((h1 k hk.le).symm.trans (h2 k hk.le).symm)
  · have : symDist x z = 0 := by unfold symDist; rw [dite_eq_right hxz]
    rw [this]
    exact le_max_of_le_left (symDist_nonneg x y)

/-- The metric is at most `1`. -/
theorem symDist_le_one (x y : ℤ → α) : symDist x y ≤ 1 := by
  unfold symDist
  split_ifs
  · exact pow_le_one₀ (by norm_num) (by norm_num)
  · exact zero_le_one

/-- The ball of radius `r` with `2^{-(m+1)} < r ≤ 2^{-m}` is the cylinder `[i_{-m} ⋯ i_m]`. -/
theorem symBall_eq_symCyl (x : ℤ → α) {r : ℝ} {m : ℕ} (h1 : (1 / 2 : ℝ) ^ (m + 1) < r)
    (h2 : r ≤ (1 / 2 : ℝ) ^ m) : symBall x r = symCyl x m := by
  classical
  ext y
  simp only [symBall, symCyl, mem_ofPred_eq]
  rw [← symDist_lt_pow_iff]
  constructor
  · intro h
    exact h.trans_le h2
  · intro h
    by_cases hd : ∃ n, DiffersAt x y n
    · have hN : symDist x y = (1 / 2 : ℝ) ^ Nat.find hd := by unfold symDist; rw [dite_eq_left hd]
      rw [hN] at h ⊢
      rw [pow_lt_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)] at h
      exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) h).trans_lt h1
    · have : symDist x y = 0 := by unfold symDist; rw [dite_eq_right hd]
      rw [this]
      exact (pow_pos (by norm_num) _).trans h1

/-- The ball of radius `r > 1` is the whole space. -/
theorem symBall_eq_univ (x : ℤ → α) {r : ℝ} (hr : 1 < r) : symBall x r = univ :=
  eq_univ_of_forall fun y => (symDist_le_one x y).trans_lt hr

/-- Every radius `0 < r ≤ 1` lies in a unique dyadic range `2^{-(m+1)} < r ≤ 2^{-m}`. -/
theorem exists_pow_lt_le {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ m : ℕ, (1 / 2 : ℝ) ^ (m + 1) < r ∧ r ≤ (1 / 2 : ℝ) ^ m := by
  classical
  have hex : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < r := exists_pow_lt_of_lt_one hr (by norm_num)
  set n := Nat.find hex
  have hn : (1 / 2 : ℝ) ^ n < r := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, pow_zero] at hn
    exact absurd hr1 (not_le.2 hn)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hm' : (1 / 2 : ℝ) ^ (m + 1) < r := by
    rw [← Nat.succ_eq_add_one, ← hm]
    exact hn
  refine ⟨m, hm', ?_⟩
  have := Nat.find_min hex (show m < n by omega)
  exact not_lt.1 this

/-- `[i_{-m} ⋯ i_m]` is the preimage under `σ^{-m}` of the cylinder `[i_{-m} ⋯ i_m]` read from
time `0`. -/
theorem symCyl_eq_preimage (x : ℤ → α) (m : ℕ) :
    symCyl x m = shift (-(m : ℤ)) ⁻¹' cylinder (block (2 * m + 1) (shift (-(m : ℤ)) x)) := by
  ext y
  simp only [symCyl, mem_ofPred_eq, mem_preimage, mem_cylinder, block_apply, shift_apply]
  constructor
  · intro h k
    exact h _ (by omega)
  · intro h k hk
    have hk' : (0 : ℤ) ≤ m + k ∧ m + k < 2 * m + 1 := by omega
    have := h ⟨(m + k).toNat, by omega⟩
    simp only [Int.toNat_of_nonneg hk'.1] at this
    rwa [show -(m : ℤ) + (m + k) = k by ring] at this

/-- The cylinder `[i_{-m} ⋯ i_m]` read from time `0` is the preimage of `[i_{-m} ⋯ i_m]` under
`σ^m`. -/
theorem preimage_shift_symCyl (x : ℤ → α) (m : ℕ) :
    shift (m : ℤ) ⁻¹' symCyl x m = cylinder (block (2 * m + 1) (shift (-(m : ℤ)) x)) := by
  rw [symCyl_eq_preimage, ← preimage_comp]
  have : shift (-(m : ℤ)) ∘ shift (m : ℤ) = (id : (ℤ → α) → ℤ → α) := by
    funext y
    simp [shift_shift]
  rw [this, preimage_id]

end Metric

/-! ### The metric induces the product topology -/

section Topology

variable {α : Type*} [TopologicalSpace α] [DiscreteTopology α]

/-- The cylinder `[i_{-m} ⋯ i_m]` is open in the product topology. -/
theorem isOpen_symCyl (x : ℤ → α) (m : ℕ) : IsOpen (symCyl x m) := by
  have h : symCyl x m = ⋂ k ∈ Finset.Icc (-(m : ℤ)) m, (fun y : ℤ → α => y k) ⁻¹' {x k} := by
    ext y
    simp only [symCyl, mem_ofPred_eq, mem_iInter, Finset.mem_Icc, mem_preimage,
      mem_singleton_iff]
    constructor
    · intro hy k hk
      exact hy k (by omega)
    · intro hy k hk
      exact hy k (by omega)
  rw [h]
  exact isOpen_biInter_finset fun k _ => (isOpen_discrete _).preimage (continuous_apply k)

/-- Every ball of positive radius is open in the product topology. -/
theorem isOpen_symBall (x : ℤ → α) {r : ℝ} (hr : 0 < r) : IsOpen (symBall x r) := by
  rcases le_or_gt r 1 with hr1 | hr1
  · obtain ⟨m, h1, h2⟩ := exists_pow_lt_le hr hr1
    rw [symBall_eq_symCyl x h1 h2]
    exact isOpen_symCyl x m
  · rw [symBall_eq_univ x hr1]
    exact isOpen_univ

/-- The standard metric induces the product topology of the two-sided shift (tex lines 719 to
802 and 2497 to 2499): a set is open exactly when it contains a ball of positive radius around
each of its points. Hence the cylinders `[i_{-m} ⋯ i_m]` are the balls of the shift. -/
theorem isOpen_iff_forall_symBall {U : Set (ℤ → α)} :
    IsOpen U ↔ ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ symBall x r ⊆ U := by
  constructor
  · intro hU x hx
    obtain ⟨I, u, hu, hIU⟩ := isOpen_pi_iff.1 hU x hx
    set M : ℕ := I.sup Int.natAbs
    refine ⟨(1 / 2 : ℝ) ^ M, by positivity, fun y hy => hIU fun k hk => ?_⟩
    have hy' : y ∈ symCyl x M := by
      rw [← symBall_eq_symCyl x (r := (1 / 2 : ℝ) ^ M) (m := M)
        (pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (Nat.lt_succ_self M)) le_rfl]
      exact hy
    rw [hy' k (Finset.le_sup (f := Int.natAbs) hk)]
    exact (hu k hk).2
  · intro h
    refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
    obtain ⟨r, hr, hsub⟩ := h x hx
    refine ⟨symBall x r, hsub, isOpen_symBall x hr, ?_⟩
    change symDist x x < r
    rw [symDist_eq_zero_iff.2 rfl]
    exact hr

end Topology

/-! ### Gibbs measures for arbitrary potentials -/

section Gibbs

variable {ι : Type*} [MeasurableSpace ι] {o : ι → ZMod 2}
  {f : (ℤ → ι × ZMod 2) → ℝ} {ν : Measure (ℤ → ι × ZMod 2)} {P C : ℝ}

/-- The Gibbs property of `sec:gibbs_measures` for a potential `f : Σ_Z → ℝ` with constants `P`
and `C`: `C⁻¹ exp(-nP + S_n f(𝐢)) ≤ ν([𝐢|_n]) ≤ C exp(-nP + S_n f(𝐢))` for all `𝐢 ∈ Σ_Z` and
`n ≥ 1`, with `S_n f = ∑_{k<n} f ∘ σ^k`. -/
def IsGibbsPotential (o : ι → ZMod 2) (f : (ℤ → ι × ZMod 2) → ℝ) (ν : Measure (ℤ → ι × ZMod 2))
    (P C : ℝ) : Prop :=
  0 < C ∧ ∀ y ∈ subshift o, ∀ n : ℕ, 0 < n →
    C⁻¹ * Real.exp (-(n * P) + birkhoffSum (shift 1) f n y) ≤
        ν.real (cylinder fun k : Fin n => y k) ∧
      ν.real (cylinder fun k : Fin n => y k) ≤
        C * Real.exp (-(n * P) + birkhoffSum (shift 1) f n y)

omit [MeasurableSpace ι] in
/-- The Birkhoff sums of a one-symbol potential `f(𝐣) = φ(j_0)` are `∑_{k<n} φ(j_k)`. -/
theorem birkhoffSum_apply_zero (φ : ι × ZMod 2 → ℝ) (n : ℕ) (y : ℤ → ι × ZMod 2) :
    birkhoffSum (shift 1) (fun z => φ (z 0)) n y = ∑ k ∈ Finset.range n, φ (y k) := by
  unfold birkhoffSum
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iterate_shift_one]
  simp

/-- For a one-symbol potential the Gibbs property is `IsGibbsWith` of `BoxLike/GibbsProperties`. -/
theorem isGibbsPotential_iff_isGibbsWith (φ : ι × ZMod 2 → ℝ) :
    IsGibbsPotential o (fun z => φ (z 0)) ν P C ↔ IsGibbsWith o φ ν P C := by
  simp only [IsGibbsPotential, IsGibbsWith, birkhoffSum_apply_zero]

/-- The constant of a Gibbs measure is at least `1`. -/
theorem IsGibbsPotential.one_le (h : IsGibbsPotential o f ν P C) {y : ℤ → ι × ZMod 2}
    (hy : y ∈ subshift o) : 1 ≤ C := by
  obtain ⟨hC, hb⟩ := h
  have h1 : C⁻¹ ≤ C :=
    le_of_mul_le_mul_right ((hb y hy 1 one_pos).1.trans (hb y hy 1 one_pos).2) (Real.exp_pos _)
  by_contra hlt
  have h2 : 1 < C⁻¹ := (one_lt_inv₀ hC).2 (not_le.1 hlt)
  linarith

/-- The displayed comparison of tex lines 2375 to 2377, in its sharp form:
`ν([𝐢|_n]) ≤ C² exp(P - f(σ^n 𝐢)) ν([𝐢|_{n+1}])` for `𝐢 ∈ Σ_Z` and `n ≥ 1`. -/
theorem IsGibbsPotential.measureReal_cylinder_le_succ (h : IsGibbsPotential o f ν P C)
    {y : ℤ → ι × ZMod 2} (hy : y ∈ subshift o) {n : ℕ} (hn : 0 < n) :
    ν.real (cylinder fun k : Fin n => y k) ≤
      C ^ 2 * Real.exp (P - f ((shift 1)^[n] y)) *
        ν.real (cylinder fun k : Fin (n + 1) => y k) := by
  obtain ⟨hC, hb⟩ := h
  have h1 := (hb y hy n hn).2
  have h2 := (hb y hy (n + 1) n.succ_pos).1
  rw [inv_mul_le_iff₀ hC] at h2
  have hexp : Real.exp (-(n * P) + birkhoffSum (shift 1) f n y) =
      Real.exp (P - f ((shift 1)^[n] y)) *
        Real.exp (-(((n + 1 : ℕ) : ℝ) * P) + birkhoffSum (shift 1) f (n + 1) y) := by
    rw [← Real.exp_add, birkhoffSum_succ_apply]
    congr 1
    push_cast
    ring
  calc ν.real (cylinder fun k : Fin n => y k)
      ≤ C * (Real.exp (P - f ((shift 1)^[n] y)) *
          Real.exp (-(((n + 1 : ℕ) : ℝ) * P) + birkhoffSum (shift 1) f (n + 1) y)) := by
        rw [← hexp]
        exact h1
    _ ≤ C * (Real.exp (P - f ((shift 1)^[n] y)) *
          (C * ν.real (cylinder fun k : Fin (n + 1) => y k))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le) hC.le
    _ = C ^ 2 * Real.exp (P - f ((shift 1)^[n] y)) *
          ν.real (cylinder fun k : Fin (n + 1) => y k) := by ring

/-- The extension to the past of tex lines 2378 to 2380, for an invariant Gibbs measure:
`ν([(σ𝐢)|_n]) ≤ C² exp(P - f(𝐢)) ν([𝐢|_{n+1}])` for `𝐢 ∈ Σ_Z` and `n ≥ 1`; by invariance the
left side is the measure of the cylinder `[i_1 ⋯ i_n]` and the right side adds the symbol `i_0`
in the past. -/
theorem IsGibbsPotential.measureReal_cylinder_succ_le_shift (h : IsGibbsPotential o f ν P C)
    {y : ℤ → ι × ZMod 2} (hy : y ∈ subshift o) {n : ℕ} (hn : 0 < n) :
    ν.real (cylinder fun k : Fin n => shift 1 y k) ≤
      C ^ 2 * Real.exp (P - f y) * ν.real (cylinder fun k : Fin (n + 1) => y k) := by
  obtain ⟨hC, hb⟩ := h
  have h1 := (hb (shift 1 y) (shift_mem_subshift o hy 1) n hn).2
  have h2 := (hb y hy (n + 1) n.succ_pos).1
  rw [inv_mul_le_iff₀ hC] at h2
  have hexp : Real.exp (-(n * P) + birkhoffSum (shift 1) f n (shift 1 y)) =
      Real.exp (P - f y) *
        Real.exp (-(((n + 1 : ℕ) : ℝ) * P) + birkhoffSum (shift 1) f (n + 1) y) := by
    rw [← Real.exp_add, birkhoffSum_succ_apply']
    congr 1
    push_cast
    ring
  calc ν.real (cylinder fun k : Fin n => shift 1 y k)
      ≤ C * (Real.exp (P - f y) *
          Real.exp (-(((n + 1 : ℕ) : ℝ) * P) + birkhoffSum (shift 1) f (n + 1) y)) := by
        rw [← hexp]
        exact h1
    _ ≤ C * (Real.exp (P - f y) * (C * ν.real (cylinder fun k : Fin (n + 1) => y k))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le) hC.le
    _ = C ^ 2 * Real.exp (P - f y) * ν.real (cylinder fun k : Fin (n + 1) => y k) := by ring

/-- The doubling constant `C² exp(P + B)` of a Gibbs measure for a potential with `-f ≤ B` on
`Σ_Z`. -/
noncomputable def gibbsDoublingConst (P C B : ℝ) : ℝ := C ^ 2 * Real.exp (P + B)

/-- The bound `ν([𝐢|_n]) ≤ C² exp(P + B) ν([𝐢|_{n+1}])` for all `n ∈ ℕ`, when `-f ≤ B` on `Σ_Z`;
the case `n = 0` uses that `ν` is a probability measure. -/
theorem IsGibbsPotential.measureReal_cylinder_le_const [IsProbabilityMeasure ν]
    (h : IsGibbsPotential o f ν P C) {B : ℝ} (hB : ∀ z ∈ subshift o, -f z ≤ B)
    {y : ℤ → ι × ZMod 2} (hy : y ∈ subshift o) (n : ℕ) :
    ν.real (cylinder fun k : Fin n => y k) ≤
      gibbsDoublingConst P C B * ν.real (cylinder fun k : Fin (n + 1) => y k) := by
  have hexp : ∀ z ∈ subshift o, Real.exp (P - f z) ≤ Real.exp (P + B) := fun z hz =>
    Real.exp_le_exp.2 (by linarith [hB z hz])
  have hC1 := h.one_le hy
  unfold gibbsDoublingConst
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 := (h.2 y hy 1 one_pos).1
    rw [inv_mul_le_iff₀ h.1] at h1
    have h2 : Real.exp (P - f y) *
        Real.exp (-(((1 : ℕ) : ℝ) * P) + birkhoffSum (shift 1) f 1 y) = 1 := by
      rw [← Real.exp_add, ← Real.exp_zero]
      congr 1
      simp
    calc ν.real (cylinder fun k : Fin 0 => y k) ≤ 1 := measureReal_le_one
      _ = Real.exp (P - f y) *
          Real.exp (-(((1 : ℕ) : ℝ) * P) + birkhoffSum (shift 1) f 1 y) := h2.symm
      _ ≤ Real.exp (P + B) * (C * ν.real (cylinder fun k : Fin (0 + 1) => y k)) :=
          mul_le_mul (hexp y hy) h1 (Real.exp_pos _).le (Real.exp_pos _).le
      _ ≤ C ^ 2 * Real.exp (P + B) * ν.real (cylinder fun k : Fin (0 + 1) => y k) := by
          have hnn : 0 ≤ Real.exp (P + B) * ν.real (cylinder fun k : Fin (0 + 1) => y k) :=
            mul_nonneg (Real.exp_pos _).le measureReal_nonneg
          nlinarith [mul_le_mul_of_nonneg_right hC1 (zero_le_one.trans hC1)]
  · refine (h.measureReal_cylinder_le_succ hy hn).trans ?_
    have hσ : (shift 1)^[n] y ∈ subshift o := by
      rw [iterate_shift_one]
      exact shift_mem_subshift o hy _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hexp _ hσ) (sq_nonneg C)) measureReal_nonneg

variable [MeasurableSingletonClass ι]

/-- An invariant measure gives `[i_{-m} ⋯ i_m]` the measure of the cylinder of the same symbols
read from time `0`. -/
theorem measureReal_symCyl (hinv : MeasurePreserving (shift 1) ν ν) (y : ℤ → ι × ZMod 2)
    (m : ℕ) :
    ν.real (symCyl y m) = ν.real (cylinder (block (2 * m + 1) (shift (-(m : ℤ)) y))) := by
  rw [← preimage_shift_symCyl, (measurePreserving_shift_natCast hinv m).measureReal_preimage]
  rw [symCyl_eq_preimage]
  exact ((measurableSet_cylinder _).preimage (measurable_shift _)).nullMeasurableSet

/-- Doubling of the cylinders `[i_{-m} ⋯ i_m]` for an invariant Gibbs probability measure with
`-f ≤ B` on `Σ_Z`: `ν([i_{-m} ⋯ i_m]) ≤ D ν([i_{-m-1} ⋯ i_{m+1}])` with
`D = (C² exp(P + B))²`; the cylinder is extended by one symbol to the future and, by invariance,
by one symbol to the past (tex lines 2374 to 2382). -/
theorem IsGibbsPotential.measureReal_symCyl_le_succ [IsProbabilityMeasure ν]
    (h : IsGibbsPotential o f ν P C) (hinv : MeasurePreserving (shift 1) ν ν) {B : ℝ}
    (hB : ∀ z ∈ subshift o, -f z ≤ B) {y : ℤ → ι × ZMod 2} (hy : y ∈ subshift o) (m : ℕ) :
    ν.real (symCyl y m) ≤ gibbsDoublingConst P C B ^ 2 * ν.real (symCyl y (m + 1)) := by
  set z := shift (-(m : ℤ)) y
  set z' := shift (-((m + 1 : ℕ) : ℤ)) y
  have hz : z ∈ subshift o := shift_mem_subshift o hy _
  have hz' : z' ∈ subshift o := shift_mem_subshift o hy _
  have hzz' : shift 1 z' = z := by
    simp only [z, z', shift_shift]
    congr 1
    push_cast
    ring
  have hK : 0 ≤ gibbsDoublingConst P C B := by unfold gibbsDoublingConst; positivity
  rw [measureReal_symCyl hinv y m, measureReal_symCyl hinv y (m + 1)]
  have h1 := h.measureReal_cylinder_le_const hB hz (2 * m + 1)
  have h2 := h.measureReal_cylinder_succ_le_shift hz' (n := 2 * m + 2) (by omega)
  rw [hzz'] at h2
  have hexp : Real.exp (P - f z') ≤ Real.exp (P + B) :=
    Real.exp_le_exp.2 (by linarith [hB z' hz'])
  have h3 : ν.real (cylinder fun k : Fin (2 * m + 2) => z k) ≤
      gibbsDoublingConst P C B * ν.real (cylinder fun k : Fin (2 * m + 3) => z' k) := by
    refine h2.trans ?_
    unfold gibbsDoublingConst
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexp (sq_nonneg C)) measureReal_nonneg
  calc ν.real (cylinder (block (2 * m + 1) z))
      ≤ gibbsDoublingConst P C B * ν.real (cylinder fun k : Fin (2 * m + 1 + 1) => z k) := h1
    _ ≤ gibbsDoublingConst P C B *
        (gibbsDoublingConst P C B * ν.real (cylinder fun k : Fin (2 * m + 3) => z' k)) :=
        mul_le_mul_of_nonneg_left h3 hK
    _ = gibbsDoublingConst P C B ^ 2 * ν.real (cylinder (block (2 * (m + 1) + 1) z')) := by
        rw [← mul_assoc, ← sq]
        rfl

/-- Tex lines 2497 to 2501: an invariant Gibbs probability measure for a potential with `-f ≤ B`
on `Σ_Z` is doubling, `ν(B(𝐢, r)) ≤ D ν(B(𝐢, r/2))` for every `𝐢 ∈ Σ_Z` and every `r > 0`, with
`D = (C² exp(P + B))²`, for the balls of the standard metric of the two-sided shift. -/
theorem IsGibbsPotential.doubling [IsProbabilityMeasure ν] (h : IsGibbsPotential o f ν P C)
    (hinv : MeasurePreserving (shift 1) ν ν) {B : ℝ} (hB : ∀ z ∈ subshift o, -f z ≤ B)
    {y : ℤ → ι × ZMod 2} (hy : y ∈ subshift o) {r : ℝ} (hr : 0 < r) :
    ν.real (symBall y r) ≤ gibbsDoublingConst P C B ^ 2 * ν.real (symBall y (r / 2)) := by
  have hK1 : 1 ≤ gibbsDoublingConst P C B := by
    unfold gibbsDoublingConst
    have hC1 := h.one_le hy
    have h1 := (h.2 y hy 1 one_pos).1
    have h2 : (0 : ℝ) < ν.real (cylinder fun k : Fin 1 => y k) :=
      lt_of_lt_of_le (mul_pos (inv_pos.2 h.1) (Real.exp_pos _)) h1
    have h3 : ν.real (cylinder fun k : Fin 1 => y k) ≤ 1 := measureReal_le_one
    rw [inv_mul_le_iff₀ h.1] at h1
    have h4 : Real.exp (-((1 : ℕ) * P) + birkhoffSum (shift 1) f 1 y) ≤ C := by
      nlinarith [mul_le_mul_of_nonneg_left h3 (zero_le_one.trans hC1)]
    rw [birkhoffSum_one, Nat.cast_one, one_mul] at h4
    have h5 : 1 ≤ C * Real.exp (P - f y) := by
      rw [show P - f y = -(-P + f y) by ring, Real.exp_neg, ← div_eq_mul_inv,
        le_div_iff₀ (Real.exp_pos _), one_mul]
      exact h4
    calc (1 : ℝ) ≤ C * Real.exp (P - f y) := h5
      _ ≤ C ^ 2 * Real.exp (P + B) := by
        refine mul_le_mul (by nlinarith) (Real.exp_le_exp.2 (by linarith [hB y hy]))
          (Real.exp_pos _).le (by positivity)
  rcases le_or_gt r 1 with hr1 | hr1
  · obtain ⟨m, hm1, hm2⟩ := exists_pow_lt_le hr hr1
    rw [symBall_eq_symCyl y hm1 hm2, symBall_eq_symCyl y (m := m + 1)
      (by rw [pow_succ]; linarith) (by rw [pow_succ]; linarith)]
    exact h.measureReal_symCyl_le_succ hinv hB hy m
  · rw [symBall_eq_univ y hr1, probReal_univ]
    have hsub : symCyl y 0 ⊆ symBall y (r / 2) := by
      rcases le_or_gt (r / 2) 1 with hr2 | hr2
      · rw [symBall_eq_symCyl y (m := 0) (by norm_num; linarith) (by norm_num; linarith)]
      · rw [symBall_eq_univ y hr2]
        exact subset_univ _
    have h0 := h.measureReal_symCyl_le_succ hinv hB hy 0
    have hmono : ν.real (symCyl y 0) ≤ ν.real (symBall y (r / 2)) :=
      measureReal_mono hsub
    have h1 := h.measureReal_cylinder_le_const hB hy 0
    have hcyl0 : ν.real (cylinder fun k : Fin 0 => y k) = 1 := by
      have : (cylinder fun k : Fin 0 => y k) = univ := eq_univ_of_forall fun z k => k.elim0
      rw [this, probReal_univ]
    rw [hcyl0] at h1
    have hsym0 : ν.real (symCyl y 0) = ν.real (cylinder fun k : Fin 1 => y k) := by
      congr 1
      ext z
      simp only [symCyl, mem_ofPred_eq, mem_cylinder]
      constructor
      · intro hz k
        have hk : ((k : ℕ) : ℤ) = 0 := by omega
        rw [hk]
        exact hz 0 le_rfl
      · intro hz k hk
        have hk' : k = 0 := by omega
        subst hk'
        exact hz 0
    rw [← hsym0] at h1
    calc (1 : ℝ) ≤ gibbsDoublingConst P C B * ν.real (symCyl y 0) := h1
      _ ≤ gibbsDoublingConst P C B ^ 2 * ν.real (symCyl y 0) := by
        refine mul_le_mul_of_nonneg_right ?_ measureReal_nonneg
        nlinarith
      _ ≤ gibbsDoublingConst P C B ^ 2 * ν.real (symBall y (r / 2)) :=
        mul_le_mul_of_nonneg_left hmono (sq_nonneg _)

/-- The doubling property for the balls of `Σ_Z` itself, `B_{Σ_Z}(𝐢, r) = B(𝐢, r) ∩ Σ_Z`, for a
measure carried by `Σ_Z`. -/
theorem IsGibbsPotential.doubling_subshift [IsProbabilityMeasure ν] (h : IsGibbsPotential o f ν P C)
    (hinv : MeasurePreserving (shift 1) ν ν) (hν : ν (subshift o)ᶜ = 0) {B : ℝ}
    (hB : ∀ z ∈ subshift o, -f z ≤ B) {y : ℤ → ι × ZMod 2} (hy : y ∈ subshift o) {r : ℝ}
    (hr : 0 < r) :
    ν.real (symBall y r ∩ subshift o) ≤
      gibbsDoublingConst P C B ^ 2 * ν.real (symBall y (r / 2) ∩ subshift o) := by
  simp only [measureReal_def, measure_inter_conull hν]
  exact h.doubling hinv hB hy hr

/-- Tex lines 2497 to 2501 for the one-symbol potentials of the library: an invariant Gibbs
probability measure `ν` of `IsGibbs` over a finite alphabet is doubling,
`ν(B(𝐢, r)) ≤ D ν(B(𝐢, r/2))` for every `𝐢 ∈ Σ_Z` and every `r > 0`. -/
theorem IsGibbs.doubling_symBall [Fintype ι] [IsProbabilityMeasure ν] {φ : ι × ZMod 2 → ℝ}
    (h : IsGibbs o φ ν) (hinv : MeasurePreserving (shift 1) ν ν) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ y ∈ subshift o, ∀ r : ℝ, 0 < r →
      ν.real (symBall y r) ≤ D * ν.real (symBall y (r / 2)) := by
  obtain ⟨P, C, hPC⟩ := isGibbs_iff.1 h
  have hg := (isGibbsPotential_iff_isGibbsWith φ).2 hPC
  refine ⟨gibbsDoublingConst P C ‖φ‖ ^ 2, sq_nonneg _, fun y hy r hr => ?_⟩
  refine hg.doubling hinv (fun z _ => ?_) hy hr
  exact (neg_le_abs _).trans (Real.norm_eq_abs (φ (z 0)) ▸ norm_le_pi_norm φ (z 0))

end Gibbs

end BoxLike
