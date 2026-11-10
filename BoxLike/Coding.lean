module

/-
The sub-shift of finite type `Σ_Z` and the codings `τ, ω : Σ → Σ_Z` of `sec:subshift`.

The alphabet `{1, …, 2N}` of `Σ_Z` is `ι × ZMod 2`: the symbol `(i, 0)` is the paper's
`i ∈ {1, …, N}` and `(i, 1)` is `i + N`. The second component records which coordinate
axis is being followed. With this alphabet the transition matrix `Z` reads
`Z((i, c), (j, c')) = 1 ↔ c' = c + o(i)`.

* `Trans`, `trans_iff`: the transition rule and its agreement with the case distinction
  defining `Z` in the paper.
* `exists_trans_trans`: `Z²` is positive when both orientations occur, so `Σ_Z` is mixing.
* `subshift`: the set `Σ_Z`.
* `tau`, `omega`: the codings of `eq:def_of_tau_omega`; `unCode` is their common inverse
  `\overline{τ}`, `\overline{ω}`.
* `range_tau`, `range_omega`, `range_tau_union_range_omega`, `disjoint_range_tau_range_omega`:
  `eq:tau_omega_partition` and the cylinder description of `τ(Σ)` and `ω(Σ)`.
* `tau_shift_of_eps_eq_zero`, …, `omega_shift_of_eps_eq_one`:
  `thm:tau_omega_sigma_commutative`.
-/
public import BoxLike.Orientation

@[expose] public section

namespace BoxLike

variable {ι : Type*} (o : ι → ZMod 2)

/-- The transition rule of the matrix `Z` of `sec:subshift`: the symbol `(i, c)` may be
followed by `(j, c')` exactly when `c' = c + o(i)`. -/
def Trans (p q : ι × ZMod 2) : Prop := q.2 = p.2 + o p.1

/-- `Trans` is the case distinction defining `Z` in the paper: the symbols `(i, c)` with
`c = o(i)`, that is `i ∈ {1, …, ℓ} ∪ {N+ℓ+1, …, 2N}`, are followed by the symbols `(j, 0)`,
and the remaining symbols by the symbols `(j, 1)`. -/
theorem trans_iff (p q : ι × ZMod 2) :
    Trans o p q ↔ (p.2 = o p.1 ∧ q.2 = 0) ∨ (p.2 ≠ o p.1 ∧ q.2 = 1) := by
  unfold Trans
  generalize o p.1 = a
  generalize p.2 = c
  generalize q.2 = c'
  revert a c c'; decide

/-- `Z²` is a positive matrix when both orientations occur; hence `Σ_Z` is mixing. -/
theorem exists_trans_trans (h0 : ∃ i, o i = 0) (h1 : ∃ i, o i = 1) (p q : ι × ZMod 2) :
    ∃ r, Trans o p r ∧ Trans o r q := by
  obtain ⟨i0, hi0⟩ := h0
  obtain ⟨i1, hi1⟩ := h1
  have key : ∀ d : ZMod 2, ∃ j, o j = d := by
    intro d
    have : d = 0 ∨ d = 1 := by revert d; decide
    rcases this with rfl | rfl
    exacts [⟨i0, hi0⟩, ⟨i1, hi1⟩]
  obtain ⟨j, hj⟩ := key (q.2 + (p.2 + o p.1))
  refine ⟨(j, p.2 + o p.1), rfl, ?_⟩
  change q.2 = p.2 + o p.1 + o j
  rw [hj]
  generalize o p.1 = a
  generalize p.2 = c
  generalize q.2 = c'
  revert a c c'; decide

/-- The two-sided sub-shift of finite type `Σ_Z` of `sec:subshift`. -/
def subshift : Set (ℤ → ι × ZMod 2) := {y | ∀ n, Trans o (y n) (y (n + 1))}

theorem mem_subshift {y : ℤ → ι × ZMod 2} :
    y ∈ subshift o ↔ ∀ n, (y (n + 1)).2 = (y n).2 + o (y n).1 := Iff.rfl

/-- `Σ_Z` is invariant under every iterate of the shift. -/
theorem shift_mem_subshift {y : ℤ → ι × ZMod 2} (hy : y ∈ subshift o) (n : ℤ) :
    shift n y ∈ subshift o := by
  intro k
  have h := hy (n + k)
  rw [mem_subshift] at hy
  simpa [Trans, add_assoc] using hy (n + k)

/-- The coding `τ` of `eq:def_of_tau_omega`: `τ_n(𝐢) = i_n + N ε_n(𝐢)`. -/
def tau (x : ℤ → ι) : ℤ → ι × ZMod 2 := fun n => (x n, eps o x n)

/-- The coding `ω` of `eq:def_of_tau_omega`: `ω_n(𝐢) = i_n + N (1 - ε_n(𝐢))`. -/
def omega (x : ℤ → ι) : ℤ → ι × ZMod 2 := fun n => (x n, eps o x n + 1)

/-- The common inverse `\overline{τ}`, `\overline{ω}` of the codings: forget the axis. -/
def unCode (y : ℤ → ι × ZMod 2) : ℤ → ι := fun n => (y n).1

variable {o}

@[simp] theorem tau_apply (x : ℤ → ι) (n : ℤ) : tau o x n = (x n, eps o x n) := rfl

@[simp] theorem omega_apply (x : ℤ → ι) (n : ℤ) : omega o x n = (x n, eps o x n + 1) := rfl

@[simp] theorem unCode_apply (y : ℤ → ι × ZMod 2) (n : ℤ) : unCode y n = (y n).1 := rfl

@[simp] theorem unCode_tau (x : ℤ → ι) : unCode (tau o x) = x := rfl

@[simp] theorem unCode_omega (x : ℤ → ι) : unCode (omega o x) = x := rfl

/-- `τ_0(𝐢) = i_0`. -/
theorem tau_zero (x : ℤ → ι) : tau o x 0 = (x 0, 0) := by simp

/-- `ω_0(𝐢) = i_0 + N`. -/
theorem omega_zero (x : ℤ → ι) : omega o x 0 = (x 0, 1) := by simp

theorem tau_mem_subshift (x : ℤ → ι) : tau o x ∈ subshift o := fun n => by
  simp [Trans, eps_add_one]

theorem omega_mem_subshift (x : ℤ → ι) : omega o x ∈ subshift o := fun n => by
  simp [Trans, eps_add_one, add_right_comm]

theorem tau_injective : Function.Injective (tau o) :=
  Function.LeftInverse.injective (g := unCode) unCode_tau

theorem omega_injective : Function.Injective (omega o) :=
  Function.LeftInverse.injective (g := unCode) unCode_omega

/-- A point of `Σ_Z` is determined by its symbols in `ι` and the axis at time `0`. -/
theorem snd_eq_of_mem_subshift {y : ℤ → ι × ZMod 2} (hy : y ∈ subshift o) (n : ℤ) :
    (y n).2 = (y 0).2 + eps o (unCode y) n := by
  have h : (fun n => (y 0).2 + (y n).2) = eps o (unCode y) := by
    apply eq_eps_of_succ
    · exact CharTwo.add_self_eq_zero _
    · intro m
      rw [mem_subshift] at hy
      rw [hy m, unCode_apply, add_assoc]
  rw [← h, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- `τ(Σ) = ⋃_{i ≤ N} [i]`: the points of `Σ_Z` following the first axis at time `0`. -/
theorem range_tau : Set.range (tau o) = {y ∈ subshift o | (y 0).2 = 0} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨tau_mem_subshift x, by simp⟩
  · rintro ⟨hy, h0⟩
    refine ⟨unCode y, funext fun n => ?_⟩
    rw [tau_apply, unCode_apply, Prod.ext_iff]
    exact ⟨rfl, by rw [snd_eq_of_mem_subshift hy n, h0, zero_add]⟩

/-- `ω(Σ) = ⋃_{i > N} [i]`: the points of `Σ_Z` following the second axis at time `0`. -/
theorem range_omega : Set.range (omega o) = {y ∈ subshift o | (y 0).2 = 1} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨omega_mem_subshift x, by simp⟩
  · rintro ⟨hy, h0⟩
    refine ⟨unCode y, funext fun n => ?_⟩
    rw [omega_apply, unCode_apply, Prod.ext_iff]
    exact ⟨rfl, by rw [snd_eq_of_mem_subshift hy n, h0, add_comm]⟩

/-- `eq:tau_omega_partition`, the covering half: `Σ_Z = τ(Σ) ∪ ω(Σ)`. -/
theorem range_tau_union_range_omega :
    Set.range (tau o) ∪ Set.range (omega o) = subshift o := by
  rw [range_tau, range_omega]
  ext y
  constructor
  · rintro (h | h) <;> exact h.1
  · intro hy
    have : (y 0).2 = 0 ∨ (y 0).2 = 1 := by
      generalize (y 0).2 = c
      revert c; decide
    exact this.imp (fun h => ⟨hy, h⟩) fun h => ⟨hy, h⟩

/-- `eq:tau_omega_partition`, the disjointness half: `τ(Σ) ∩ ω(Σ) = ∅`. -/
theorem disjoint_range_tau_range_omega :
    Disjoint (Set.range (tau o)) (Set.range (omega o)) := by
  rw [range_tau, range_omega, Set.disjoint_left]
  rintro y ⟨-, h0⟩ ⟨-, h1⟩
  rw [h0] at h1
  exact absurd h1 (by decide)

/-- `thm:tau_omega_sigma_commutative`, first half for `τ`: if `ε_n(𝐢) = 0`, then
`τ(σ^n 𝐢) = σ^n(τ 𝐢)`. -/
theorem tau_shift_of_eps_eq_zero {x : ℤ → ι} {n : ℤ} (h : eps o x n = 0) :
    tau o (shift n x) = shift n (tau o x) := by
  funext k
  simp [eps_shift, h]

/-- `thm:tau_omega_sigma_commutative`, first half for `ω`: if `ε_n(𝐢) = 0`, then
`ω(σ^n 𝐢) = σ^n(ω 𝐢)`. -/
theorem omega_shift_of_eps_eq_zero {x : ℤ → ι} {n : ℤ} (h : eps o x n = 0) :
    omega o (shift n x) = shift n (omega o x) := by
  funext k
  simp [eps_shift, h]

/-- `thm:tau_omega_sigma_commutative`, second half for `τ`: if `ε_n(𝐢) = 1`, then
`τ(σ^n 𝐢) = σ^n(ω 𝐢)`. -/
theorem tau_shift_of_eps_eq_one {x : ℤ → ι} {n : ℤ} (h : eps o x n = 1) :
    tau o (shift n x) = shift n (omega o x) := by
  funext k
  simp [eps_shift, h, add_comm]

/-- `thm:tau_omega_sigma_commutative`, second half for `ω`: if `ε_n(𝐢) = 1`, then
`ω(σ^n 𝐢) = σ^n(τ 𝐢)`. -/
theorem omega_shift_of_eps_eq_one {x : ℤ → ι} {n : ℤ} (h : eps o x n = 1) :
    omega o (shift n x) = shift n (tau o x) := by
  funext k
  simp only [omega_apply, tau_apply, shift_apply, eps_shift, h, Prod.mk.injEq, true_and]
  generalize eps o x (n + k) = c
  revert c; decide

end BoxLike
