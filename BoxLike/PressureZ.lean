module

/-
The pressure `P_Z(f)` on the sub-shift of finite type `Σ_Z` of `sec:gibbs_measures`, and the
first three lines of `thm:eq_state_is_sum`: `P(𝖠, s) = P_Z(f_{1,s}) = P_Z(f_{2,s})`,
`λ_1(𝖠, μ) = ∫ f_{1,1} dμ_1 = ∫ f_{2,1} dμ_2` and `λ_2(𝖠, μ) = ∫ f_{1,1} dμ_2 = ∫ f_{2,1} dμ_1`.

The potentials depend on the symbol `j_0` only, so `sup_{𝐣 ∈ [𝐢|_n]} S_n f(𝐣) = ∑_{k<n} φ(i_k)`,
and the periodic points of period `n` of `Σ_Z` correspond to the cyclically admissible words of
length `n`.

* `IsAdmissible`, `IsCyclicAdmissible`: admissible and cyclically admissible words over the
  alphabet `ι × ZMod 2` of `Σ_Z`.
* `IsAdmissible.exists_block_eq`, `isAdmissible_iff_mem_range_liftBlock`: the admissible words
  are the blocks of the points of `Σ_Z`, and they are the lifts of the words over `ι`.
* `periodicPoints`, `bijOn_block_periodicPoints`: the periodic points of period `n` of `Σ_Z`
  correspond to the cyclically admissible words of length `n`.
* `admissibleSum`, `periodicSum`, `periodicSum_eq_finsum`: the sums of `exp(S_n f)` over the
  admissible words and over the periodic points; the last statement is the sum in the article's
  definition of `P_Z(f)`, verbatim.
* `pressureZ`, `tendsto_pressureZ`, `tendsto_pressureZ_admissibleSum`: the pressure `P_Z(f)`, the
  existence of the limit defining it, and its form through the admissible words.
* `periodicSum_le_admissibleSum`, `exists_mul_admissibleSum_le_periodicSum`: the two sums are
  comparable up to a multiplicative constant.
* `periodicSum_eq_zero_of_odd`: without a diagonal generator there are no periodic points of odd
  period, so the hypothesis of `tendsto_pressureZ` is needed.
* `flipSymbol`, `flipAxis`, `pressureZ_comp_flipSymbol`: the symmetry exchanging the two axes,
  and `P_Z(f ∘ flip) = P_Z(f)`.
* `IsGibbsAt`, `IsGibbsAt.tendsto_log_admissibleSum`, `IsGibbsAt.pressure_eq`,
  `IsGibbs.pressure_eq`: the constant `P` in the Gibbs bounds of a probability measure carried by
  `Σ_Z` is `P_Z(φ)`.
* `System.svfSum_le_admissibleSum`, `System.pressure_eq_pressureZ₁`,
  `System.pressure_eq_pressureZ₂`: `P(𝖠, s) = P_Z(f_{1,s}) = P_Z(f_{2,s})` for `0 < s < 2`.
* `System.GibbsDecomposition.map_unCode_tau₂`, `System.GibbsDecomposition.map_unCode_omega₂`,
  `System.GibbsDecomposition.map_flip`: `\overline{τ}_*μ_2 = \overline{ω}_*μ_1`,
  `\overline{ω}_*μ_2 = \overline{τ}_*μ_1` and `μ_2 = flip_*μ_1`.
* `System.decomposition₂_of_decompositions`: the fourth decomposition of `thm:eq_state_is_sum`
  follows from the other three.
* `System.GibbsDecomposition.lyapunov₁_eq_integral`,
  `System.GibbsDecomposition.lyapunov₁_eq_integral_potential₂`,
  `System.GibbsDecomposition.lyapunov₂_eq_integral`,
  `System.GibbsDecomposition.lyapunov₂_eq_integral_potential₂`: the integral formulas for the
  Lyapunov exponents.
* `System.GibbsDecomposition.isGibbsAt₁`, `System.GibbsDecomposition.isGibbsAt₂`: the Gibbs
  constants of `μ_1` and `μ_2` are `P(𝖠, s)`.
-/
public import BoxLike.Main
public import BoxLike.Variational
public import Mathlib.Algebra.BigOperators.Finprod

@[expose] public section

namespace BoxLike

open Filter Topology MeasureTheory

/-! ### Admissible words -/

section Words

variable {ι : Type*} (o : ι → ZMod 2) {n : ℕ}

/-- A word over the alphabet of `Σ_Z` is admissible when consecutive symbols obey the transition
rule of the matrix `Z` of `sec:subshift`. -/
def IsAdmissible (w : Fin n → ι × ZMod 2) : Prop :=
  ∀ (k : Fin n) (h : (k : ℕ) + 1 < n), Trans o (w k) (w ⟨k + 1, h⟩)

/-- A word is cyclically admissible when it is admissible and its last symbol may be followed by
its first symbol. These are the words `𝐢|_n` of the points `𝐢 ∈ Σ_Z` with `σ^n(𝐢) = 𝐢` in the
definition of `P_Z(f)` in `sec:gibbs_measures`; see `bijOn_block_periodicPoints`. -/
def IsCyclicAdmissible (w : Fin n → ι × ZMod 2) : Prop :=
  IsAdmissible o w ∧ ∀ h : 0 < n, Trans o (w ⟨n - 1, Nat.sub_lt h one_pos⟩) (w ⟨0, h⟩)

/-- A two-sided sequence with the prefix `w`. -/
def extendWord {α : Type*} (w : Fin (n + 1) → α) : ℤ → α :=
  fun k => w (Fin.ofNat (n + 1) k.toNat)

/-- The sequence `extendWord w` has the symbol `w k` at time `k`. -/
theorem extendWord_natCast {α : Type*} (w : Fin (n + 1) → α) (k : Fin (n + 1)) :
    extendWord w (k : ℤ) = w k := by
  simp [extendWord]

/-- The sequence `extendWord w` has the prefix `w`. -/
theorem block_extendWord {α : Type*} (w : Fin (n + 1) → α) :
    block (n + 1) (extendWord w) = w :=
  funext (extendWord_natCast w)

/-- The point of `Σ_Z` over `𝐢` that follows the axis `c` at time `0`; it is `τ(𝐢)` for `c = 0`
and `ω(𝐢)` for `c = 1`, as in `eq:def_of_tau_omega`. -/
def codeFrom (c : ZMod 2) (x : ℤ → ι) : ℤ → ι × ZMod 2 := fun k => (x k, c + eps o x k)

/-- The point `codeFrom o c 𝐢` lies in `Σ_Z`. -/
theorem codeFrom_mem_subshift (c : ZMod 2) (x : ℤ → ι) : codeFrom o c x ∈ subshift o :=
  fun k => by simp [codeFrom, Trans, eps_add_one, add_assoc]

/-- The point of `Σ_Z` over `𝐢` on the first axis at time `0` is `τ(𝐢)`. -/
theorem codeFrom_zero (x : ℤ → ι) : codeFrom o 0 x = tau o x := by
  funext k; simp [codeFrom]

/-- The point of `Σ_Z` over `𝐢` on the second axis at time `0` is `ω(𝐢)`. -/
theorem codeFrom_one (x : ℤ → ι) : codeFrom o 1 x = omega o x := by
  funext k; simp [codeFrom, add_comm]

variable {o}

/-- The blocks of the points of `Σ_Z` are admissible. -/
theorem isAdmissible_block {y : ℤ → ι × ZMod 2} (hy : y ∈ subshift o) (n : ℕ) :
    IsAdmissible o (block n y) := by
  intro k h
  have := hy (k : ℤ)
  simpa [block] using this

/-- The block of a point of `Σ_Z` is the lift of its base block along its axis at time `0`. -/
theorem block_eq_liftBlock {y : ℤ → ι × ZMod 2} (hy : y ∈ subshift o) (n : ℕ) :
    block n y = liftBlock o (y 0).2 (block n (unCode y)) :=
  funext fun k => mem_cylinder_liftBlock hy (w := block n (unCode y)) (fun _ => rfl) k

/-- Every admissible word of positive length is the block of a point of `Σ_Z`: every symbol has
a follower and a predecessor, since every column and every row of `Z` is non-zero. -/
theorem IsAdmissible.exists_block_eq {w : Fin (n + 1) → ι × ZMod 2} (hw : IsAdmissible o w) :
    ∃ y ∈ subshift o, block (n + 1) y = w := by
  set x : ℤ → ι := extendWord fun k => (w k).1 with hx
  have hy := codeFrom_mem_subshift o (w 0).2 x
  refine ⟨codeFrom o (w 0).2 x, hy, ?_⟩
  have key : ∀ (k : ℕ) (hk : k < n + 1), codeFrom o (w 0).2 x k = w ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h0 : x 0 = (w 0).1 := extendWord_natCast (fun k => (w k).1) 0
      simp [codeFrom, h0]
    | succ k ih =>
      intro hk
      have hk' : k < n + 1 := by omega
      have h1 : x ((k + 1 : ℕ) : ℤ) = (w ⟨k + 1, hk⟩).1 :=
        extendWord_natCast (fun k => (w k).1) ⟨k + 1, hk⟩
      have h2 := hy (k : ℤ)
      rw [ih hk'] at h2
      have h3 := hw ⟨k, hk'⟩ hk
      refine Prod.ext ?_ ?_
      · simpa [codeFrom] using h1
      · rw [Nat.cast_succ]
        exact h2.trans h3.symm
  exact funext fun k => key k k.isLt

/-- The lift of the word `w` along the axis `c` is the block of the point of `Σ_Z` over an
extension of `w` that starts on the axis `c`. -/
theorem block_codeFrom_extendWord (o : ι → ZMod 2) (c : ZMod 2) (w : Fin (n + 1) → ι) :
    block (n + 1) (codeFrom o c (extendWord w)) = liftBlock o c w := by
  have h := block_eq_liftBlock (codeFrom_mem_subshift o c (extendWord w)) (n + 1)
  have h0 : (codeFrom o c (extendWord w) 0).2 = c := by simp [codeFrom]
  have h1 : block (n + 1) (unCode (codeFrom o c (extendWord w))) = w := block_extendWord w
  rwa [h0, h1] at h

/-- The lifts of the words over `ι` are admissible. -/
theorem isAdmissible_liftBlock (o : ι → ZMod 2) (c : ZMod 2) (w : Fin (n + 1) → ι) :
    IsAdmissible o (liftBlock o c w) := by
  rw [← block_codeFrom_extendWord]
  exact isAdmissible_block (codeFrom_mem_subshift o c (extendWord w)) _

/-- Every admissible word of positive length is the lift of its base word along its first
axis. -/
theorem IsAdmissible.mem_range_liftBlock {v : Fin (n + 1) → ι × ZMod 2}
    (hv : IsAdmissible o v) :
    v ∈ Set.range fun p : (Fin (n + 1) → ι) × ZMod 2 => liftBlock o p.2 p.1 := by
  obtain ⟨y, hy, rfl⟩ := hv.exists_block_eq
  exact ⟨(block (n + 1) (unCode y), (y 0).2), (block_eq_liftBlock hy _).symm⟩

/-- The admissible words of positive length are the lifts of the words over `ι` along the two
axes: there are `2 N^n` admissible words of length `n`. -/
theorem isAdmissible_iff_mem_range_liftBlock {v : Fin (n + 1) → ι × ZMod 2} :
    IsAdmissible o v ↔
      v ∈ Set.range fun p : (Fin (n + 1) → ι) × ZMod 2 => liftBlock o p.2 p.1 :=
  ⟨fun h => h.mem_range_liftBlock, by rintro ⟨p, rfl⟩; exact isAdmissible_liftBlock o p.2 p.1⟩

/-- A cyclically admissible word is admissible. -/
theorem IsCyclicAdmissible.isAdmissible {w : Fin n → ι × ZMod 2}
    (hw : IsCyclicAdmissible o w) : IsAdmissible o w := hw.1

/-- The two halves of an admissible word are admissible. -/
theorem IsAdmissible.of_append {m : ℕ} {u : Fin m → ι × ZMod 2} {v : Fin n → ι × ZMod 2}
    (h : IsAdmissible o (Fin.append u v)) : IsAdmissible o u ∧ IsAdmissible o v := by
  constructor
  · intro k hk
    have h' := h (Fin.castAdd n k) (by simp; omega)
    rw [Fin.append_left] at h'
    have e : (⟨((Fin.castAdd n k : Fin (m + n)) : ℕ) + 1, by simp; omega⟩ : Fin (m + n)) =
        Fin.castAdd n ⟨k + 1, hk⟩ := rfl
    rw [e, Fin.append_left] at h'
    exact h'
  · intro k hk
    have h' := h (Fin.natAdd m k) (by simp; omega)
    rw [Fin.append_right] at h'
    have e : (⟨((Fin.natAdd m k : Fin (m + n)) : ℕ) + 1, by simp; omega⟩ : Fin (m + n)) =
        Fin.natAdd m ⟨k + 1, hk⟩ := rfl
    rw [e, Fin.append_right] at h'
    exact h'

/-- An admissible word `w` and a symbol `r` that may follow the last symbol of `w` and precede
its first symbol give the cyclically admissible word `r w`. -/
theorem IsCyclicAdmissible.cons {w : Fin (n + 1) → ι × ZMod 2} (hw : IsAdmissible o w)
    {r : ι × ZMod 2} (h1 : Trans o r (w 0)) (h2 : Trans o (w (Fin.last n)) r) :
    IsCyclicAdmissible o (Fin.cons r w : Fin (n + 2) → ι × ZMod 2) := by
  refine ⟨fun k => ?_, fun _ => ?_⟩
  · refine Fin.cases ?_ (fun j => ?_) k
    · intro h
      have e : (⟨((0 : Fin (n + 2)) : ℕ) + 1, h⟩ : Fin (n + 2)) = Fin.succ 0 := rfl
      rw [e, Fin.cons_zero, Fin.cons_succ]
      exact h1
    · intro h
      have hj : (j : ℕ) + 1 < n + 1 := by simpa using h
      have e : (⟨((Fin.succ j : Fin (n + 2)) : ℕ) + 1, h⟩ : Fin (n + 2)) =
          Fin.succ ⟨j + 1, hj⟩ := rfl
      rw [e, Fin.cons_succ, Fin.cons_succ]
      exact hw j hj
  · have e1 : (⟨n + 2 - 1, Nat.sub_lt (Nat.succ_pos _) one_pos⟩ : Fin (n + 2)) =
        Fin.succ (Fin.last n) := rfl
    have e2 : (⟨0, Nat.succ_pos _⟩ : Fin (n + 2)) = 0 := rfl
    rw [e1, e2, Fin.cons_zero, Fin.cons_succ]
    exact h2

/-- If some generator is diagonal, then every admissible word of positive length is closed up by
one symbol: the axis after the last symbol of `w` differs from the axis of the first symbol by
the parity of the anti-diagonal letters of `w`, and a letter of `w` or the diagonal generator
has this orientation. When both orientations occur this is the positivity of `Z²`,
`exists_trans_trans`. -/
theorem IsAdmissible.exists_closing (h0 : ∃ i, o i = 0) {w : Fin (n + 1) → ι × ZMod 2}
    (hw : IsAdmissible o w) : ∃ r, Trans o r (w 0) ∧ Trans o (w (Fin.last n)) r := by
  obtain ⟨y, hy, rfl⟩ := hw.exists_block_eq
  obtain ⟨i0, hi0⟩ := h0
  have key : ∃ j, o j = eps o (unCode y) ((n + 1 : ℕ) : ℤ) := by
    rcases zmod_two_cases (eps o (unCode y) ((n + 1 : ℕ) : ℤ)) with h | h
    · exact ⟨i0, hi0.trans h.symm⟩
    · have hne : eps o (unCode y) ((n + 1 : ℕ) : ℤ) ≠ 0 := by rw [h]; decide
      rw [eps_natCast] at hne
      obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      refine ⟨unCode y a, ?_⟩
      rw [h]
      exact (zmod_two_cases (o (unCode y a))).resolve_left ha
  obtain ⟨j, hj⟩ := key
  have hs := snd_eq_of_mem_subshift hy ((n + 1 : ℕ) : ℤ)
  refine ⟨(j, (y ((n + 1 : ℕ) : ℤ)).2), ?_, ?_⟩
  · change (y ((0 : Fin (n + 1)) : ℕ)).2 = (y ((n + 1 : ℕ) : ℤ)).2 + o j
    rw [hs, hj, add_assoc, CharTwo.add_self_eq_zero, add_zero, Fin.val_zero, Nat.cast_zero]
  · have h := hy (n : ℤ)
    rw [Nat.cast_succ]
    exact h

end Words

/-! ### Periodic points and cyclically admissible words -/

section Periodic

variable {ι : Type*} {o : ι → ZMod 2} {n : ℕ}

/-- The points `𝐢 ∈ Σ_Z` with `σ^n(𝐢) = 𝐢`, over which the sum in the definition of `P_Z(f)` in
`sec:gibbs_measures` runs. -/
def periodicPoints (o : ι → ZMod 2) (n : ℕ) : Set (ℤ → ι × ZMod 2) :=
  {y | y ∈ subshift o ∧ shift n y = y}

/-- The two-sided sequence of period `n + 1` that repeats the word `w`. -/
def periodicExtension {α : Type*} (w : Fin (n + 1) → α) : ℤ → α := fun k =>
  extendWord w (k % ((n + 1 : ℕ) : ℤ))

/-- The periodic sequence over `w` has the symbol `w k` at time `k`. -/
theorem periodicExtension_natCast {α : Type*} (w : Fin (n + 1) → α) (k : Fin (n + 1)) :
    periodicExtension w (k : ℤ) = w k := by
  have h : ((k : ℕ) : ℤ) % ((n + 1 : ℕ) : ℤ) = (k : ℕ) :=
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast k.isLt)
  rw [periodicExtension, h, extendWord_natCast]

/-- The periodic sequence over a word of length `n + 1` is fixed by `σ^{n+1}`. -/
theorem shift_periodicExtension {α : Type*} (w : Fin (n + 1) → α) :
    shift ((n + 1 : ℕ) : ℤ) (periodicExtension w) = periodicExtension w := by
  funext k
  simp only [shift_apply, periodicExtension, Int.add_emod_left]

/-- A sequence fixed by `σ^{n+1}` is determined by its block of length `n + 1`. -/
theorem eq_of_shift_eq_of_block_eq {α : Type*} {y y' : ℤ → α}
    (hy : shift ((n + 1 : ℕ) : ℤ) y = y) (hy' : shift ((n + 1 : ℕ) : ℤ) y' = y')
    (h : block (n + 1) y = block (n + 1) y') : y = y' := by
  have key : ∀ z : ℤ → α, shift ((n + 1 : ℕ) : ℤ) z = z →
      ∀ k : ℤ, z k = z (k % ((n + 1 : ℕ) : ℤ)) := by
    intro z hz k
    have hstep : ∀ a : ℤ, z (((n + 1 : ℕ) : ℤ) + a) = z a := fun a => congrFun hz a
    have hmul : ∀ (j : ℤ) (a : ℤ), z (a + ((n + 1 : ℕ) : ℤ) * j) = z a := by
      intro j
      induction j using Int.induction_on with
      | zero => intro a; simp
      | succ j ih =>
        intro a
        rw [mul_add, mul_one, ← add_assoc, add_comm, hstep, ih]
      | pred j ih =>
        intro a
        have h1 := hstep (a + ((n + 1 : ℕ) : ℤ) * (-(j : ℤ) - 1))
        rw [← h1, ← ih a]
        congr 1
        ring
    have h2 := hmul (k / ((n + 1 : ℕ) : ℤ)) (k % ((n + 1 : ℕ) : ℤ))
    rw [Int.emod_add_mul_ediv] at h2
    exact h2
  funext k
  have hk0 : 0 ≤ k % ((n + 1 : ℕ) : ℤ) := Int.emod_nonneg _ (by positivity)
  have hk1 : k % ((n + 1 : ℕ) : ℤ) < ((n + 1 : ℕ) : ℤ) := Int.emod_lt_of_pos _ (by positivity)
  have hlt : (k % ((n + 1 : ℕ) : ℤ)).toNat < n + 1 := (Int.toNat_lt hk0).2 hk1
  have h3 := congrFun h ⟨_, hlt⟩
  simp only [block_apply, Int.toNat_of_nonneg hk0] at h3
  rw [key y hy k, key y' hy' k, h3]

/-- The periodic sequence over a cyclically admissible word lies in `Σ_Z`. -/
theorem IsCyclicAdmissible.periodicExtension_mem_subshift {w : Fin (n + 1) → ι × ZMod 2}
    (hw : IsCyclicAdmissible o w) : periodicExtension w ∈ subshift o := by
  intro k
  have hN : (0 : ℤ) < ((n + 1 : ℕ) : ℤ) := by positivity
  have hk0 : 0 ≤ k % ((n + 1 : ℕ) : ℤ) := Int.emod_nonneg _ hN.ne'
  have hk1 : k % ((n + 1 : ℕ) : ℤ) < ((n + 1 : ℕ) : ℤ) := Int.emod_lt_of_pos _ hN
  have hsucc : (k + 1) % ((n + 1 : ℕ) : ℤ) =
      (k % ((n + 1 : ℕ) : ℤ) + 1) % ((n + 1 : ℕ) : ℤ) := (Int.emod_add_emod k _ 1).symm
  unfold periodicExtension
  rw [hsucc]
  generalize k % ((n + 1 : ℕ) : ℤ) = m at hk0 hk1
  lift m to ℕ using hk0
  have hm : m < n + 1 := by exact_mod_cast hk1
  rw [extendWord_natCast w ⟨m, hm⟩]
  by_cases hm' : m + 1 < n + 1
  · have h1 : ((m : ℤ) + 1) % ((n + 1 : ℕ) : ℤ) = ((m + 1 : ℕ) : ℤ) := by
      rw [Nat.cast_succ]
      exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hm')
    rw [h1, extendWord_natCast w ⟨m + 1, hm'⟩]
    exact hw.1 ⟨m, hm⟩ hm'
  · have hmn : m = n := by omega
    subst hmn
    have h1 : ((m : ℤ) + 1) % ((m + 1 : ℕ) : ℤ) = ((0 : ℕ) : ℤ) := by
      rw [Nat.cast_succ, Int.emod_self, Nat.cast_zero]
    rw [h1, extendWord_natCast w ⟨0, Nat.succ_pos m⟩]
    exact hw.2 (Nat.succ_pos m)

/-- The periodic points of period `n ≥ 1` of `Σ_Z` correspond to the cyclically admissible
words of length `n`, through `𝐢 ↦ 𝐢|_n`. -/
theorem bijOn_block_periodicPoints (o : ι → ZMod 2) (n : ℕ) :
    Set.BijOn (block (n + 1)) (periodicPoints o (n + 1)) {w | IsCyclicAdmissible o w} := by
  refine ⟨?_, ?_, ?_⟩
  · rintro y ⟨hy, hper⟩
    refine ⟨isAdmissible_block hy _, fun _ => ?_⟩
    have h := hy ((n : ℕ) : ℤ)
    have h0 : y (((n : ℕ) : ℤ) + 1) = y 0 := by
      have := congrFun hper 0
      simpa [add_comm] using this
    rw [h0] at h
    simpa [block] using h
  · rintro y ⟨-, hy⟩ y' ⟨-, hy'⟩ h
    exact eq_of_shift_eq_of_block_eq hy hy' h
  · intro w hw
    exact ⟨periodicExtension w, ⟨hw.periodicExtension_mem_subshift, shift_periodicExtension w⟩,
      funext (periodicExtension_natCast w)⟩

end Periodic

/-! ### The symmetry exchanging the two axes -/

section FlipSymbol

variable {ι : Type*} {o : ι → ZMod 2} {n : ℕ}

/-- The symbol over the same letter on the other axis: `i ↦ i + N` for `i ≤ N` and `i ↦ i - N`
for `i > N`, in the labelling of `sec:subshift`. -/
def flipSymbol (p : ι × ZMod 2) : ι × ZMod 2 := (p.1, p.2 + 1)

/-- Exchanging the axes keeps the letter. -/
@[simp] theorem flipSymbol_fst (p : ι × ZMod 2) : (flipSymbol p).1 = p.1 := rfl

/-- Exchanging the axes is an involution. -/
@[simp] theorem flipSymbol_flipSymbol (p : ι × ZMod 2) : flipSymbol (flipSymbol p) = p := by
  refine Prod.ext rfl ?_
  change p.2 + 1 + 1 = p.2
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- The matrix `Z` of `sec:subshift` is invariant under the exchange of the axes. -/
theorem trans_flipSymbol_iff (p q : ι × ZMod 2) :
    Trans o (flipSymbol p) (flipSymbol q) ↔ Trans o p q := by
  change q.2 + 1 = p.2 + 1 + o p.1 ↔ q.2 = p.2 + o p.1
  generalize o p.1 = a
  generalize p.2 = c
  generalize q.2 = c'
  revert a c c'; decide

/-- Exchanging the axes preserves admissible words. -/
theorem isAdmissible_flipSymbol_iff (w : Fin n → ι × ZMod 2) :
    IsAdmissible o (fun k => flipSymbol (w k)) ↔ IsAdmissible o w := by
  simp only [IsAdmissible, trans_flipSymbol_iff]

/-- Exchanging the axes preserves cyclically admissible words. -/
theorem isCyclicAdmissible_flipSymbol_iff (w : Fin n → ι × ZMod 2) :
    IsCyclicAdmissible o (fun k => flipSymbol (w k)) ↔ IsCyclicAdmissible o w := by
  simp only [IsCyclicAdmissible, isAdmissible_flipSymbol_iff, trans_flipSymbol_iff]

end FlipSymbol

/-! ### The pressure `P_Z(f)` -/

section Sums

variable {ι : Type*} [Fintype ι] (o : ι → ZMod 2) (φ : ι × ZMod 2 → ℝ)

open Classical in
/-- The sum of `exp(S_n f)` over the admissible words of length `n`, for the potential
`f(𝐣) = φ(j_0)`. -/
noncomputable def admissibleSum (n : ℕ) : ℝ :=
  ∑ w : Fin n → ι × ZMod 2, if IsAdmissible o w then Real.exp (∑ k, φ (w k)) else 0

open Classical in
/-- The sum `∑_{𝐢 ∈ Σ_Z : σ^n(𝐢) = 𝐢} exp(sup_{𝐣 ∈ [𝐢|_n]} S_n f(𝐣))` in the definition of
`P_Z(f)` in `sec:gibbs_measures`, for the potential `f(𝐣) = φ(j_0)`, as a sum over the cyclically
admissible words of length `n`; `periodicSum_eq_finsum` is the article's form. -/
noncomputable def periodicSum (n : ℕ) : ℝ :=
  ∑ w : Fin n → ι × ZMod 2, if IsCyclicAdmissible o w then Real.exp (∑ k, φ (w k)) else 0

/-- The pressure `P_Z(f)` of `sec:gibbs_measures`, for the potential `f(𝐣) = φ(j_0)`:
`P_Z(f) = lim_n n⁻¹ log ∑_{𝐢 ∈ Σ_Z : σ^n(𝐢) = 𝐢} exp(sup_{𝐣 ∈ [𝐢|_n]} S_n f(𝐣))`. -/
noncomputable def pressureZ : ℝ :=
  limUnder atTop fun n : ℕ => Real.log (periodicSum o φ n) / n

omit [Fintype ι] in
/-- A potential that depends on the symbol `j_0` only has a constant Birkhoff sum `S_n f` on the
cylinder `[𝐢|_n]` of `Σ_Z`, so `sup_{𝐣 ∈ [𝐢|_n]} S_n f(𝐣) = ∑_{k<n} φ(i_k)`. -/
theorem sSup_birkhoffSum_cylinder {y : ℤ → ι × ZMod 2} (hy : y ∈ subshift o) (n : ℕ) :
    sSup ((fun j : ℤ → ι × ZMod 2 => ∑ k ∈ Finset.range n, φ (j k)) ''
      (cylinder (block n y) ∩ subshift o)) = ∑ k ∈ Finset.range n, φ (y k) := by
  have h : (fun j : ℤ → ι × ZMod 2 => ∑ k ∈ Finset.range n, φ (j k)) ''
      (cylinder (block n y) ∩ subshift o) = {∑ k ∈ Finset.range n, φ (y k)} := by
    ext t
    rw [Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, ⟨hj, -⟩, rfl⟩
      refine Finset.sum_congr rfl fun k hk => ?_
      have hjk : j k = y k := hj ⟨k, Finset.mem_range.1 hk⟩
      rw [hjk]
    · rintro rfl
      exact ⟨y, ⟨fun _ => rfl, hy⟩, rfl⟩
  rw [h, csSup_singleton]

/-- The sum in the definition of `P_Z(f)` in `sec:gibbs_measures`, verbatim, for the potential
`f(𝐣) = φ(j_0)` and a period `n ≥ 1`: the set of periodic points is finite and the sum over it
is `periodicSum`. -/
theorem periodicSum_eq_finsum (n : ℕ) :
    periodicSum o φ (n + 1) = ∑ᶠ y ∈ periodicPoints o (n + 1),
      Real.exp (sSup ((fun j : ℤ → ι × ZMod 2 => ∑ k ∈ Finset.range (n + 1), φ (j k)) ''
        (cylinder (block (n + 1) y) ∩ subshift o))) := by
  classical
  have h := finsum_mem_eq_of_bijOn (block (n + 1)) (bijOn_block_periodicPoints o n)
    (f := fun y => Real.exp (sSup ((fun j : ℤ → ι × ZMod 2 =>
      ∑ k ∈ Finset.range (n + 1), φ (j k)) '' (cylinder (block (n + 1) y) ∩ subshift o))))
    (g := fun w => Real.exp (∑ k, φ (w k))) (by
      rintro y ⟨hy, -⟩
      rw [sSup_birkhoffSum_cylinder o φ hy, Finset.sum_range]
      rfl)
  rw [h, finsum_mem_def, finsum_eq_sum_of_fintype, periodicSum]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : IsCyclicAdmissible o w
  · rw [ite_eq_left hw, Set.indicator_of_mem (by exact hw)]
  · rw [ite_eq_right hw, Set.indicator_of_notMem (by exact hw)]

/-- The sum over the periodic points is at most the sum over the admissible words. -/
theorem periodicSum_le_admissibleSum (n : ℕ) : periodicSum o φ n ≤ admissibleSum o φ n := by
  classical
  refine Finset.sum_le_sum fun w _ => ?_
  by_cases h : IsCyclicAdmissible o w
  · rw [ite_eq_left h, ite_eq_left h.isAdmissible]
  · rw [ite_eq_right h]
    split_ifs <;> positivity

/-- When every generator is anti-diagonal, the axis alternates along every point of `Σ_Z`, so
`Σ_Z` has no periodic point of odd period and the sum in the definition of `P_Z(f)` vanishes for
odd `n`. The limit defining `P_Z(f)` needs a diagonal generator; see `tendsto_pressureZ`. -/
theorem periodicSum_eq_zero_of_odd (h1 : ∀ i, o i = 1) {n : ℕ} (hn : Odd n) :
    periodicSum o φ n = 0 := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := hn.pos; omega⟩
  refine Finset.sum_eq_zero fun w _ => ite_eq_right fun hw => ?_
  obtain ⟨y, ⟨hy, hper⟩, -⟩ := (bijOn_block_periodicPoints o k).surjOn hw
  have hs := snd_eq_of_mem_subshift hy ((k + 1 : ℕ) : ℤ)
  have h0 : y ((k + 1 : ℕ) : ℤ) = y 0 := by simpa using congrFun hper 0
  rw [h0, eps_natCast] at hs
  simp only [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hs
  exact Nat.not_even_iff_odd.2 hn (ZMod.natCast_eq_zero_iff_even.1 (left_eq_add.1 hs))

/-- The sums over the admissible words are sub-multiplicative. -/
theorem admissibleSum_add_le (m n : ℕ) :
    admissibleSum o φ (m + n) ≤ admissibleSum o φ m * admissibleSum o φ n := by
  classical
  calc admissibleSum o φ (m + n)
      = ∑ p : (Fin m → ι × ZMod 2) × (Fin n → ι × ZMod 2),
          if IsAdmissible o (Fin.append p.1 p.2) then
            Real.exp (∑ k, φ (Fin.append p.1 p.2 k)) else 0 :=
        (Fintype.sum_equiv (Fin.appendEquiv m n) _ _ fun p => rfl).symm
    _ = ∑ u : Fin m → ι × ZMod 2, ∑ v : Fin n → ι × ZMod 2,
          if IsAdmissible o (Fin.append u v) then
            Real.exp (∑ k, φ (Fin.append u v k)) else 0 := Fintype.sum_prod_type _
    _ ≤ admissibleSum o φ m * admissibleSum o φ n := by
        rw [admissibleSum, admissibleSum, Finset.sum_mul_sum]
        refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
        by_cases h : IsAdmissible o (Fin.append u v)
        · obtain ⟨hu, hv⟩ := h.of_append
          rw [ite_eq_left h, ite_eq_left hu, ite_eq_left hv, ← Real.exp_add, Fin.sum_univ_add]
          simp
        · rw [ite_eq_right h]
          positivity

/-- A potential on a finite non-empty alphabet is bounded below. -/
theorem exists_le_potential [Nonempty ι] : ∃ m, ∀ p, m ≤ φ p := by
  obtain ⟨p, -, hp⟩ := Finset.exists_min_image Finset.univ φ Finset.univ_nonempty
  exact ⟨φ p, fun q => hp q (Finset.mem_univ _)⟩

variable {φ}

/-- `exp(n m) ≤ ∑ exp(S_n f)` when `φ ≥ m`, since an admissible word of length `n` exists. -/
theorem exp_le_admissibleSum [Nonempty ι] {m : ℝ} (hm : ∀ p, m ≤ φ p) (n : ℕ) :
    Real.exp (n * m) ≤ admissibleSum o φ n := by
  classical
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hw := isAdmissible_block (tau_mem_subshift (o := o) fun _ => i) n
  have h1 : Real.exp (n * m) ≤ Real.exp (∑ k, φ (block n (tau o fun _ => i) k)) := by
    refine Real.exp_le_exp.2 ?_
    have := Finset.card_nsmul_le_sum Finset.univ
      (fun k : Fin n => φ (block n (tau o fun _ => i) k)) m fun k _ => hm _
    simpa using this
  refine h1.trans ?_
  have h2 := Finset.single_le_sum (f := fun w : Fin n → ι × ZMod 2 =>
    if IsAdmissible o w then Real.exp (∑ k, φ (w k)) else 0)
    (fun w _ => by positivity) (Finset.mem_univ (block n (tau o fun _ => i)))
  rwa [ite_eq_left hw] at h2

/-- The sums over the admissible words are positive. -/
theorem admissibleSum_pos [Nonempty ι] (n : ℕ) : 0 < admissibleSum o φ n := by
  obtain ⟨m, hm⟩ := exists_le_potential φ
  exact (Real.exp_pos _).trans_le (exp_le_admissibleSum o hm n)

/-- Closing up the admissible words by one symbol: `e^m ∑_{|w| = n} exp(S_n f)` is at most the
sum over the periodic points of period `n + 1`, when `φ ≥ m` and some generator is diagonal. -/
theorem exp_mul_admissibleSum_le_periodicSum (h0 : ∃ i, o i = 0) {m : ℝ} (hm : ∀ p, m ≤ φ p)
    (n : ℕ) : Real.exp m * admissibleSum o φ (n + 1) ≤ periodicSum o φ (n + 2) := by
  classical
  set G : (Fin (n + 2) → ι × ZMod 2) → ℝ := fun v =>
    if IsCyclicAdmissible o v then Real.exp (∑ k, φ (v k)) else 0 with hG
  have hG0 : ∀ v, 0 ≤ G v := fun v => by rw [hG]; positivity
  calc Real.exp m * admissibleSum o φ (n + 1)
      = ∑ w : Fin (n + 1) → ι × ZMod 2,
          Real.exp m * if IsAdmissible o w then Real.exp (∑ k, φ (w k)) else 0 := by
        rw [admissibleSum, Finset.mul_sum]
    _ ≤ ∑ w : Fin (n + 1) → ι × ZMod 2, ∑ r : ι × ZMod 2, G (Fin.cons r w) := by
        refine Finset.sum_le_sum fun w _ => ?_
        by_cases hw : IsAdmissible o w
        · obtain ⟨r, h1, h2⟩ := hw.exists_closing h0
          refine le_trans ?_ (Finset.single_le_sum (f := fun r : ι × ZMod 2 => G (Fin.cons r w))
            (fun r _ => hG0 _) (Finset.mem_univ r))
          have hGc : G (Fin.cons r w) =
              Real.exp (∑ k, φ ((Fin.cons r w : Fin (n + 2) → ι × ZMod 2) k)) :=
            ite_eq_left (IsCyclicAdmissible.cons hw h1 h2)
          have hsum : ∑ k, φ ((Fin.cons r w : Fin (n + 2) → ι × ZMod 2) k) =
              φ r + ∑ k, φ (w k) := by
            rw [Fin.sum_univ_succ]
            simp only [Fin.cons_zero, Fin.cons_succ]
          rw [hGc, ite_eq_left hw, ← Real.exp_add, hsum]
          exact Real.exp_le_exp.2 (add_le_add (hm r) le_rfl)
        · rw [ite_eq_right hw, mul_zero]
          exact Finset.sum_nonneg fun r _ => hG0 _
    _ = ∑ p : (ι × ZMod 2) × (Fin (n + 1) → ι × ZMod 2), G (Fin.cons p.1 p.2) :=
        (Fintype.sum_prod_type_right
          fun p : (ι × ZMod 2) × (Fin (n + 1) → ι × ZMod 2) => G (Fin.cons p.1 p.2)).symm
    _ = periodicSum o φ (n + 2) :=
        Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (n + 2) => ι × ZMod 2) _ _ fun p => rfl

/-- The sum over the periodic points of period `n` and the sum over the admissible words of
length `n` are comparable up to a multiplicative constant, when some generator is diagonal. The
other inequality is `periodicSum_le_admissibleSum`. -/
theorem exists_mul_admissibleSum_le_periodicSum (h0 : ∃ i, o i = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ n, 2 ≤ n → c * admissibleSum o φ n ≤ periodicSum o φ n := by
  have : Nonempty ι := ⟨h0.choose⟩
  obtain ⟨m, hm⟩ := exists_le_potential φ
  have h1 : 0 < admissibleSum o φ 1 := admissibleSum_pos o 1
  refine ⟨Real.exp m / admissibleSum o φ 1, div_pos (Real.exp_pos _) h1, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have h2 : admissibleSum o φ (k + 2) ≤ admissibleSum o φ 1 * admissibleSum o φ (k + 1) := by
    have h := admissibleSum_add_le o φ 1 (k + 1)
    rwa [show 1 + (k + 1) = k + 2 by omega] at h
  calc Real.exp m / admissibleSum o φ 1 * admissibleSum o φ (k + 2)
      ≤ Real.exp m / admissibleSum o φ 1 * (admissibleSum o φ 1 * admissibleSum o φ (k + 1)) :=
        mul_le_mul_of_nonneg_left h2 (div_pos (Real.exp_pos _) h1).le
    _ = Real.exp m * admissibleSum o φ (k + 1) := by field_simp
    _ ≤ periodicSum o φ (k + 2) := exp_mul_admissibleSum_le_periodicSum o h0 hm k

/-- The sequence `log ∑_{|w| = n} exp(S_n f)` over the admissible words is sub-additive. -/
theorem subadditive_log_admissibleSum [Nonempty ι] :
    Subadditive fun n => Real.log (admissibleSum o φ n) := by
  intro m n
  rw [← Real.log_mul (admissibleSum_pos o m).ne' (admissibleSum_pos o n).ne']
  exact Real.log_le_log (admissibleSum_pos o _) (admissibleSum_add_le o φ m n)

/-- The averages `n⁻¹ log ∑_{|w| = n} exp(S_n f)` are bounded below. -/
theorem bddBelow_log_admissibleSum_div [Nonempty ι] :
    BddBelow (Set.range fun n : ℕ => Real.log (admissibleSum o φ n) / n) := by
  obtain ⟨m, hm⟩ := exists_le_potential φ
  refine ⟨min 0 m, ?_⟩
  rintro _ ⟨n, rfl⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    refine (min_le_right _ _).trans ?_
    rw [le_div_iff₀ hn']
    have h := Real.log_le_log (Real.exp_pos _) (exp_le_admissibleSum o hm n)
    rw [Real.log_exp] at h
    linarith [mul_comm m (n : ℝ)]

/-- A limit of the averages over the admissible words is a limit of the averages over the
periodic points, when some generator is diagonal. -/
theorem tendsto_log_periodicSum_div (h0 : ∃ i, o i = 0) {L : ℝ}
    (hL : Tendsto (fun n : ℕ => Real.log (admissibleSum o φ n) / n) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => Real.log (periodicSum o φ n) / n) atTop (𝓝 L) := by
  have : Nonempty ι := ⟨h0.choose⟩
  obtain ⟨c, hc, hle⟩ := exists_mul_admissibleSum_le_periodicSum o (φ := φ) h0
  have hlow : Tendsto (fun n : ℕ => Real.log c / n + Real.log (admissibleSum o φ n) / n) atTop
      (𝓝 L) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (Real.log c)).add hL
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hL ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hA := admissibleSum_pos o (φ := φ) n
    have h := Real.log_le_log (mul_pos hc hA) (hle n hn)
    rw [Real.log_mul hc.ne' hA.ne'] at h
    rw [← add_div]
    exact div_le_div_of_nonneg_right h (Nat.cast_nonneg n)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hP : 0 < periodicSum o φ n := (mul_pos hc (admissibleSum_pos o n)).trans_le (hle n hn)
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hP (periodicSum_le_admissibleSum o φ n)) (Nat.cast_nonneg n)

variable (φ)

/-- The limit defining `P_Z(f)` in `sec:gibbs_measures` exists when some generator is diagonal,
in particular for a box-like tuple with rotations, for which `Σ_Z` is mixing. When every
generator is anti-diagonal, `Σ_Z` has no periodic points of odd period, by
`periodicSum_eq_zero_of_odd`. -/
theorem tendsto_pressureZ (h0 : ∃ i, o i = 0) :
    Tendsto (fun n : ℕ => Real.log (periodicSum o φ n) / n) atTop (𝓝 (pressureZ o φ)) := by
  have : Nonempty ι := ⟨h0.choose⟩
  have h := tendsto_log_periodicSum_div o h0
    ((subadditive_log_admissibleSum o (φ := φ)).tendsto_lim (bddBelow_log_admissibleSum_div o))
  rwa [pressureZ, h.limUnder_eq]

/-- `P_Z(f) = lim_n n⁻¹ log ∑_{|w| = n} exp(S_n f)` with the sum over all admissible words of
length `n`. -/
theorem tendsto_pressureZ_admissibleSum (h0 : ∃ i, o i = 0) :
    Tendsto (fun n : ℕ => Real.log (admissibleSum o φ n) / n) atTop (𝓝 (pressureZ o φ)) := by
  have : Nonempty ι := ⟨h0.choose⟩
  have hL := (subadditive_log_admissibleSum o (φ := φ)).tendsto_lim
    (bddBelow_log_admissibleSum_div o)
  rwa [tendsto_nhds_unique (tendsto_pressureZ o φ h0) (tendsto_log_periodicSum_div o h0 hL)]

/-- The sums over the periodic points are invariant under the exchange of the axes. -/
theorem periodicSum_comp_flipSymbol (n : ℕ) :
    periodicSum o (fun p => φ (flipSymbol p)) n = periodicSum o φ n := by
  classical
  refine Fintype.sum_equiv (Function.Involutive.toPerm
    (fun (w : Fin n → ι × ZMod 2) k => flipSymbol (w k)) fun w => by simp) _ _ fun w => ?_
  simp only [Function.Involutive.toPerm, Equiv.coe_fn_mk, isCyclicAdmissible_flipSymbol_iff]

/-- The sums over the admissible words are invariant under the exchange of the axes. -/
theorem admissibleSum_comp_flipSymbol (n : ℕ) :
    admissibleSum o (fun p => φ (flipSymbol p)) n = admissibleSum o φ n := by
  classical
  refine Fintype.sum_equiv (Function.Involutive.toPerm
    (fun (w : Fin n → ι × ZMod 2) k => flipSymbol (w k)) fun w => by simp) _ _ fun w => ?_
  simp only [Function.Involutive.toPerm, Equiv.coe_fn_mk, isAdmissible_flipSymbol_iff]

/-- `P_Z(f ∘ flip) = P_Z(f)`: the symmetry behind `P_Z(f_{1,s}) = P_Z(f_{2,s})` in
`sec:gibbs_measures` (tex lines 2462 to 2463). -/
theorem pressureZ_comp_flipSymbol :
    pressureZ o (fun p => φ (flipSymbol p)) = pressureZ o φ := by
  simp only [pressureZ, periodicSum_comp_flipSymbol]

/-- The sum over the admissible words of length `n ≥ 1` as a sum over the words over `ι` and the
two axes. -/
theorem admissibleSum_succ (n : ℕ) :
    admissibleSum o φ (n + 1) =
      ∑ w : Fin (n + 1) → ι, ∑ c : ZMod 2, Real.exp (∑ k, φ (liftBlock o c w k)) := by
  classical
  rw [admissibleSum, ← Fintype.sum_of_injective _ (liftBlock_injective o)
    (fun p : (Fin (n + 1) → ι) × ZMod 2 => Real.exp (∑ k, φ (liftBlock o p.2 p.1 k))) _
    (fun v hv => ite_eq_right fun h => hv h.mem_range_liftBlock)
    (fun p => (ite_eq_left (isAdmissible_liftBlock o p.2 p.1)).symm), Fintype.sum_prod_type]

end Sums

/-! ### The constant of a Gibbs measure -/

section Gibbs

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {o : ι → ZMod 2} {φ : ι × ZMod 2 → ℝ} {ν : Measure (ℤ → ι × ZMod 2)}

/-- The Gibbs bounds of `sec:gibbs_measures` with the number `P` in the place of `P_Z(f)`:
`C⁻¹ exp(-nP + S_n f(𝐢)) ≤ ν([𝐢|_n]) ≤ C exp(-nP + S_n f(𝐢))` for all `𝐢 ∈ Σ_Z` and `n ≥ 1`,
with some constant `C > 0`. -/
def IsGibbsAt (o : ι → ZMod 2) (φ : ι × ZMod 2 → ℝ) (ν : Measure (ℤ → ι × ZMod 2))
    (P : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ y ∈ subshift o, ∀ n : ℕ, 0 < n →
    C⁻¹ * Real.exp (-(n * P) + ∑ k ∈ Finset.range n, φ (y k)) ≤
        ν.real (cylinder fun k : Fin n => y k) ∧
      ν.real (cylinder fun k : Fin n => y k) ≤
        C * Real.exp (-(n * P) + ∑ k ∈ Finset.range n, φ (y k))

omit [Fintype ι] [MeasurableSingletonClass ι] in
/-- `IsGibbs` asks for the Gibbs bounds with some number `P`. -/
theorem isGibbs_iff_exists_isGibbsAt : IsGibbs o φ ν ↔ ∃ P, IsGibbsAt o φ ν P := Iff.rfl

open Classical in
/-- The cylinders of the admissible words of length `n` carry a probability measure that is
carried by `Σ_Z`. -/
theorem sum_measureReal_cylinder_of_isAdmissible [IsProbabilityMeasure ν]
    (hν : ν (subshift o)ᶜ = 0) (n : ℕ) :
    ∑ w : Fin n → ι × ZMod 2, (if IsAdmissible o w then ν.real (cylinder w) else 0) = 1 := by
  rw [← sum_measureReal_cylinder ν n]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs with hw
  · rfl
  · have hsub : cylinder w ⊆ (subshift o)ᶜ := fun y hy hys =>
      hw ((funext hy : block n y = w) ▸ isAdmissible_block hys n)
    rw [measureReal_def, measure_mono_null hsub hν, ENNReal.toReal_zero]

/-- The Gibbs bounds determine their constant `P`: summing them over the admissible words of
length `n` gives `C⁻¹ ≤ exp(-nP) ∑_{|w| = n} exp(S_n f) ≤ C`. No hypothesis on the orientations
is needed. -/
theorem IsGibbsAt.tendsto_log_admissibleSum [IsProbabilityMeasure ν]
    (hν : ν (subshift o)ᶜ = 0) {P : ℝ} (h : IsGibbsAt o φ ν P) :
    Tendsto (fun n : ℕ => Real.log (admissibleSum o φ n) / n) atTop (𝓝 P) := by
  classical
  have : Nonempty ι := ⟨((nonempty_of_isProbabilityMeasure ν).some 0).1⟩
  obtain ⟨C, hC, hb⟩ := h
  have key : ∀ n : ℕ,
      C⁻¹ * (Real.exp (-((n + 1 : ℕ) * P)) * admissibleSum o φ (n + 1)) ≤ 1 ∧
        1 ≤ C * (Real.exp (-((n + 1 : ℕ) * P)) * admissibleSum o φ (n + 1)) := by
    intro n
    rw [← sum_measureReal_cylinder_of_isAdmissible hν (n + 1), admissibleSum, Finset.mul_sum,
      Finset.mul_sum, Finset.mul_sum]
    refine ⟨Finset.sum_le_sum fun w _ => ?_, Finset.sum_le_sum fun w _ => ?_⟩ <;>
      by_cases hw : IsAdmissible o w
    · obtain ⟨y, hy, rfl⟩ := hw.exists_block_eq
      rw [ite_eq_left hw, ite_eq_left hw, ← Real.exp_add]
      have := (hb y hy (n + 1) (Nat.succ_pos n)).1
      rwa [Finset.sum_range] at this
    · rw [ite_eq_right hw, ite_eq_right hw]; simp
    · obtain ⟨y, hy, rfl⟩ := hw.exists_block_eq
      rw [ite_eq_left hw, ite_eq_left hw, ← Real.exp_add]
      have := (hb y hy (n + 1) (Nat.succ_pos n)).2
      rwa [Finset.sum_range] at this
    · rw [ite_eq_right hw, ite_eq_right hw]; simp
  have hlow : Tendsto (fun n : ℕ => P - Real.log C / n) atTop (𝓝 P) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (Real.log C))
  have hupp : Tendsto (fun n : ℕ => P + Real.log C / n) atTop (𝓝 P) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (Real.log C))
  have hlog : ∀ n : ℕ, 0 < n → (n : ℝ) * P - Real.log C ≤ Real.log (admissibleSum o φ n) ∧
      Real.log (admissibleSum o φ n) ≤ n * P + Real.log C := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hA := admissibleSum_pos o (φ := φ) (k + 1)
    have hE := Real.exp_pos (-((k + 1 : ℕ) * P))
    obtain ⟨h1, h2⟩ := key k
    have h1' := Real.log_le_log (mul_pos (inv_pos.2 hC) (mul_pos hE hA)) h1
    have h2' := Real.log_le_log one_pos h2
    rw [Real.log_mul (inv_pos.2 hC).ne' (mul_pos hE hA).ne', Real.log_mul hE.ne' hA.ne',
      Real.log_exp, Real.log_inv, Real.log_one] at h1'
    rw [Real.log_mul hC.ne' (mul_pos hE hA).ne', Real.log_mul hE.ne' hA.ne',
      Real.log_exp, Real.log_one] at h2'
    constructor <;> linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hn', sub_mul, div_mul_cancel₀ _ hn'.ne']
    linarith [(hlog n hn).1, mul_comm P (n : ℝ)]
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn', add_mul, div_mul_cancel₀ _ hn'.ne']
    linarith [(hlog n hn).2, mul_comm P (n : ℝ)]

/-- The constant `P` in the Gibbs bounds of a probability measure carried by `Σ_Z` is the
pressure `P_Z(f)`, as the definition of a Gibbs measure in `sec:gibbs_measures` requires. -/
theorem IsGibbsAt.pressure_eq (h0 : ∃ i, o i = 0) [IsProbabilityMeasure ν]
    (hν : ν (subshift o)ᶜ = 0) {P : ℝ} (h : IsGibbsAt o φ ν P) : P = pressureZ o φ :=
  tendsto_nhds_unique (h.tendsto_log_admissibleSum hν) (tendsto_pressureZ_admissibleSum o φ h0)

/-- A Gibbs measure in the sense of `IsGibbs`, with existentially quantified constants,
satisfies the Gibbs bounds of `sec:gibbs_measures` with `P = P_Z(f)`. -/
theorem IsGibbs.pressure_eq (h0 : ∃ i, o i = 0) [IsProbabilityMeasure ν]
    (hν : ν (subshift o)ᶜ = 0) (h : IsGibbs o φ ν) : IsGibbsAt o φ ν (pressureZ o φ) := by
  obtain ⟨P, hP⟩ := isGibbs_iff_exists_isGibbsAt.1 h
  rwa [← hP.pressure_eq h0 hν]

end Gibbs

/-! ### The exchange of the axes on `Σ_Z` -/

section FlipAxis

variable {ι : Type*}

/-- The involution of `Σ_Z` that exchanges the two axes; it conjugates `τ` and `ω`. -/
def flipAxis (y : ℤ → ι × ZMod 2) : ℤ → ι × ZMod 2 := fun n => flipSymbol (y n)

/-- The exchange of the axes, coordinate by coordinate. -/
@[simp] theorem flipAxis_apply (y : ℤ → ι × ZMod 2) (n : ℤ) :
    flipAxis y n = ((y n).1, (y n).2 + 1) := rfl

/-- The exchange of the axes maps `τ(𝐢)` to `ω(𝐢)`. -/
theorem flipAxis_tau (o : ι → ZMod 2) (x : ℤ → ι) : flipAxis (tau o x) = omega o x := rfl

/-- The exchange of the axes maps `ω(𝐢)` to `τ(𝐢)`. -/
theorem flipAxis_omega (o : ι → ZMod 2) (x : ℤ → ι) : flipAxis (omega o x) = tau o x :=
  funext fun n => flipSymbol_flipSymbol (tau o x n)

/-- The exchange of the axes is measurable. -/
theorem measurable_flipAxis [MeasurableSpace ι] :
    Measurable (flipAxis : (ℤ → ι × ZMod 2) → ℤ → ι × ZMod 2) :=
  Measurable.of_eval fun n => (measurable_fst.comp (measurable_pi_apply n)).prodMk
    ((measurable_snd.comp (measurable_pi_apply n)).add_const 1)

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

omit [Fintype ι] [MeasurableSingletonClass ι] in
/-- A coding `κ` with `κ ∘ \overline{κ} = id` on `R = κ(Σ)` carries `\overline{κ}_*(ν|_R)` back to
`ν|_R`, as in `eq:inverse-coding-restrictions`. -/
theorem map_map_unCode_restrict {κ : (ℤ → ι) → ℤ → ι × ZMod 2} (hκ : Measurable κ)
    {R : Set (ℤ → ι × ZMod 2)} (hRm : MeasurableSet R) (hR : ∀ y ∈ R, κ (unCode y) = y)
    (ν : Measure (ℤ → ι × ZMod 2)) :
    ((ν.restrict R).map unCode).map κ = ν.restrict R := by
  rw [Measure.map_map hκ measurable_unCode]
  conv_rhs => rw [← Measure.map_id (μ := ν.restrict R)]
  refine Measure.map_congr ?_
  filter_upwards [ae_restrict_mem hRm] with y hy
  exact hR y hy

/-- On `τ(Σ)` the exchange of the axes is `ω ∘ \overline{τ}`. -/
theorem map_flipAxis_restrict_range_tau (o : ι → ZMod 2) (ν : Measure (ℤ → ι × ZMod 2)) :
    ((ν.restrict (Set.range (tau o))).map unCode).map (omega o) =
      (ν.restrict (Set.range (tau o))).map flipAxis := by
  rw [Measure.map_map (measurable_omega o) measurable_unCode]
  refine Measure.map_congr ?_
  filter_upwards [ae_restrict_mem (measurableSet_range_tau o)] with y hy
  obtain ⟨x, rfl⟩ := hy
  rfl

/-- On `ω(Σ)` the exchange of the axes is `τ ∘ \overline{ω}`. -/
theorem map_flipAxis_restrict_range_omega (o : ι → ZMod 2) (ν : Measure (ℤ → ι × ZMod 2)) :
    ((ν.restrict (Set.range (omega o))).map unCode).map (tau o) =
      (ν.restrict (Set.range (omega o))).map flipAxis := by
  rw [Measure.map_map (measurable_tau o) measurable_unCode]
  refine Measure.map_congr ?_
  filter_upwards [ae_restrict_mem (measurableSet_range_omega o)] with y hy
  obtain ⟨x, rfl⟩ := hy
  exact (flipAxis_omega o x).symm

end FlipAxis

namespace System

/-! ### `P(𝖠, s) = P_Z(f_{1,s}) = P_Z(f_{2,s})` -/

section Pressure

variable {ι : Type*} (S : System ι) {n : ℕ}

/-- `φ^s(A_w) = max{exp S_n f_{1,s}(w, 0), exp S_n f_{1,s}(w, 1)}` for a word `w` of length
`n ≥ 1` and `0 < s < 2`, where `(w, c)` is the admissible word over `w` that starts on the axis
`c`: by `thm:matrix_products_g_derivatives` the entries of `A_w` have the moduli `|g'|` of the
two lifts of `w`. This is the identity of `sec:gibbs_measures` (tex lines 2444 to 2450) for
finite words. -/
theorem svf_matWord_ofFn (w : Fin (n + 1) → ι) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    svf s (S.matWord (List.ofFn w)) =
      max (Real.exp (∑ k, S.potential₁ s (liftBlock S.o 0 w k)))
        (Real.exp (∑ k, S.potential₁ s (liftBlock S.o 1 w k))) := by
  have h := S.svf_matWord_futureWord (extendWord w) (n + 1) hs0 hs2
  rw [futureWord_eq_ofFn_block, block_extendWord] at h
  have h0 := block_codeFrom_extendWord S.o 0 w
  have h1 := block_codeFrom_extendWord S.o 1 w
  rw [codeFrom_zero] at h0
  rw [codeFrom_one] at h1
  rw [h, Finset.sum_range, Finset.sum_range, ← h0, ← h1]
  rfl

variable [Fintype ι]

/-- `∑_{|w| = n} φ^s(A_w)` lies between one half of and the whole sum of `exp(S_n f_{1,s})` over
the admissible words of length `n ≥ 1`, for `0 < s < 2`. -/
theorem svfSum_le_admissibleSum (n : ℕ) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    S.svfSum s (n + 1) ≤ admissibleSum S.o (S.potential₁ s) (n + 1) ∧
      admissibleSum S.o (S.potential₁ s) (n + 1) ≤ 2 * S.svfSum s (n + 1) := by
  rw [admissibleSum_succ, svfSum, Finset.mul_sum]
  refine ⟨Finset.sum_le_sum fun w _ => ?_, Finset.sum_le_sum fun w _ => ?_⟩
  · rw [S.svf_matWord_ofFn w hs0 hs2, sum_zmod_two]
    exact max_le_add_of_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  · rw [S.svf_matWord_ofFn w hs0 hs2, sum_zmod_two]
    linarith [le_max_left (Real.exp (∑ k, S.potential₁ s (liftBlock S.o 0 w k)))
      (Real.exp (∑ k, S.potential₁ s (liftBlock S.o 1 w k))),
      le_max_right (Real.exp (∑ k, S.potential₁ s (liftBlock S.o 0 w k)))
      (Real.exp (∑ k, S.potential₁ s (liftBlock S.o 1 w k)))]

/-- `P(𝖠, s) = lim_n n⁻¹ log ∑_{|w| = n} exp(S_n f_{1,s})` with the sum over the admissible
words, for every box-like system and `0 < s < 2`. -/
theorem tendsto_log_admissibleSum_potential₁ [Nonempty ι] {s : ℝ} (hs0 : 0 < s)
    (hs2 : s < 2) :
    Tendsto (fun n : ℕ => Real.log (admissibleSum S.o (S.potential₁ s) n) / n) atTop
      (𝓝 (S.pressure s)) := by
  obtain ⟨δ, hδ⟩ := S.exists_ratioLowerBound
  have hP := hδ.tendsto_pressure hs0.le
  have hpos := fun n => hδ.svfSum_pos hs0.le n
  have hupp : Tendsto (fun n : ℕ => Real.log 2 / n + Real.log (S.svfSum s n) / n) atTop
      (𝓝 (S.pressure s)) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)).add hP
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hP hupp ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (hpos _) (S.svfSum_le_admissibleSum k hs0 hs2).1) (Nat.cast_nonneg _)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h := Real.log_le_log (admissibleSum_pos S.o (k + 1))
      (S.svfSum_le_admissibleSum k hs0 hs2).2
    rw [Real.log_mul two_ne_zero (hpos _).ne'] at h
    rw [← add_div]
    exact div_le_div_of_nonneg_right h (Nat.cast_nonneg _)

/-- `P(𝖠, s) = lim_n n⁻¹ log ∑_{|w| = n} exp(S_n f_{2,s})` with the sum over the admissible
words, for every box-like system and `0 < s < 2`. -/
theorem tendsto_log_admissibleSum_potential₂ [Nonempty ι] {s : ℝ} (hs0 : 0 < s)
    (hs2 : s < 2) :
    Tendsto (fun n : ℕ => Real.log (admissibleSum S.o (S.potential₂ s) n) / n) atTop
      (𝓝 (S.pressure s)) := by
  have h := S.tendsto_log_admissibleSum_potential₁ hs0 hs2
  simp only [← admissibleSum_comp_flipSymbol S.o (S.potential₁ s)] at h
  exact h

/-- `thm:eq_state_is_sum`, first line, first identity: `P(𝖠, s) = P_Z(f_{1,s})` for `0 < s < 2`.
It holds for every box-like system with a diagonal generator; neither an anti-diagonal
generator, nor proximality, nor an equilibrium state is needed. -/
theorem pressure_eq_pressureZ₁ (h0 : ∃ i, S.o i = 0) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    S.pressure s = pressureZ S.o (S.potential₁ s) :=
  haveI : Nonempty ι := ⟨h0.choose⟩
  tendsto_nhds_unique (S.tendsto_log_admissibleSum_potential₁ hs0 hs2)
    (tendsto_pressureZ_admissibleSum S.o (S.potential₁ s) h0)

/-- `thm:eq_state_is_sum`, first line, second identity: `P(𝖠, s) = P_Z(f_{2,s})` for
`0 < s < 2`, by the symmetry exchanging the axes. -/
theorem pressure_eq_pressureZ₂ (h0 : ∃ i, S.o i = 0) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    S.pressure s = pressureZ S.o (S.potential₂ s) :=
  (S.pressure_eq_pressureZ₁ h0 hs0 hs2).trans
    (pressureZ_comp_flipSymbol S.o (S.potential₁ s)).symm

end Pressure

/-! ### The symmetry of the two Gibbs measures and the Lyapunov exponents -/

section Decomposition

variable {ι : Type*} [MeasurableSpace ι] {S : System ι} {s : ℝ} {μ : Measure (ℤ → ι)}
  {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)}

/-- The fourth decomposition `μ = \overline{τ}_*μ_2 + \overline{ω}_*μ_2` of `thm:eq_state_is_sum`
follows from the other three, when `μ_1` is finite: cancelling `\overline{τ}_*μ_1` and
`\overline{ω}_*μ_1` gives `\overline{τ}_*μ_2 = \overline{ω}_*μ_1` and
`\overline{ω}_*μ_2 = \overline{τ}_*μ_1`. -/
theorem decomposition₂_of_decompositions {o : ι → ZMod 2} [IsFiniteMeasure μ₁]
    (h_tau : μ = (μ₁.restrict (Set.range (tau o))).map unCode +
      (μ₂.restrict (Set.range (tau o))).map unCode)
    (h_omega : μ = (μ₁.restrict (Set.range (omega o))).map unCode +
      (μ₂.restrict (Set.range (omega o))).map unCode)
    (h₁ : μ = (μ₁.restrict (Set.range (tau o))).map unCode +
      (μ₁.restrict (Set.range (omega o))).map unCode) :
    μ = (μ₂.restrict (Set.range (tau o))).map unCode +
      (μ₂.restrict (Set.range (omega o))).map unCode := by
  have e1 : (μ₂.restrict (Set.range (tau o))).map unCode =
      (μ₁.restrict (Set.range (omega o))).map unCode :=
    (Measure.add_right_inj _ _ _).1 (h_tau.symm.trans h₁)
  have e2 : (μ₂.restrict (Set.range (omega o))).map unCode =
      (μ₁.restrict (Set.range (tau o))).map unCode := by
    have h' := h_omega.symm.trans h₁
    rw [add_comm ((μ₁.restrict (Set.range (tau o))).map unCode)] at h'
    exact (Measure.add_right_inj _ _ _).1 h'
  rw [e1, e2, add_comm]
  exact h₁

/-- `\overline{τ}_*μ_2 = \overline{ω}_*μ_1`, as noted in `sec:gibbs_measures` (tex lines 2487 to
2607): the first and the third decomposition of `thm:eq_state_is_sum` share the finite summand
`\overline{τ}_*μ_1`. -/
theorem GibbsDecomposition.map_unCode_tau₂ (h : S.GibbsDecomposition s μ μ₁ μ₂) :
    (μ₂.restrict (Set.range (tau S.o))).map unCode =
      (μ₁.restrict (Set.range (omega S.o))).map unCode := by
  have := h.prob₁
  exact (Measure.add_right_inj _ _ _).1 (h.eq_tau.symm.trans h.eq₁)

/-- `\overline{ω}_*μ_2 = \overline{τ}_*μ_1`, as noted in `sec:gibbs_measures` (tex lines 2487 to
2607): the second and the third decomposition of `thm:eq_state_is_sum` share the finite summand
`\overline{ω}_*μ_1`. -/
theorem GibbsDecomposition.map_unCode_omega₂ (h : S.GibbsDecomposition s μ μ₁ μ₂) :
    (μ₂.restrict (Set.range (omega S.o))).map unCode =
      (μ₁.restrict (Set.range (tau S.o))).map unCode := by
  have := h.prob₁
  have h' := h.eq_omega.symm.trans h.eq₁
  rw [add_comm ((μ₁.restrict (Set.range (tau S.o))).map unCode)] at h'
  exact (Measure.add_right_inj _ _ _).1 h'

/-- `\overline{λ}(𝖠, ν) = ∫ f_{1,1} dν`, the second identity of the second and third lines of
`thm:eq_state_is_sum`. -/
theorem lyapBar_eq_integral (S : System ι) (ν : Measure (ℤ → ι × ZMod 2)) :
    S.lyapBar ν = ∫ y, S.potential₁ 1 (y 0) ∂ν := by
  simp [lyapBar, potential₁]

omit [MeasurableSpace ι] in
/-- `f_{2,s}` on the other axis is `f_{1,s}`, as noted in `sec:gibbs_measures`. -/
theorem potential₂_flipSymbol (S : System ι) (s : ℝ) (p : ι × ZMod 2) :
    S.potential₂ s (flipSymbol p) = S.potential₁ s p := by
  change S.potential₁ s (flipSymbol (flipSymbol p)) = S.potential₁ s p
  rw [flipSymbol_flipSymbol]

variable [Fintype ι] [MeasurableSingletonClass ι]

/-- The second Gibbs measure is the image of the first under the exchange of the axes:
`μ_2 = flip_*μ_1`. The first three decompositions of `thm:eq_state_is_sum` and the supports
force this; the fourth decomposition follows from it. -/
theorem GibbsDecomposition.map_flip (h : S.GibbsDecomposition s μ μ₁ μ₂) :
    μ₂ = μ₁.map flipAxis := by
  have hsplit : ∀ ν : Measure (ℤ → ι × ZMod 2), ν (subshift S.o)ᶜ = 0 →
      ν.restrict (Set.range (tau S.o)) + ν.restrict (Set.range (omega S.o)) = ν := by
    intro ν hν
    rw [← Measure.restrict_union disjoint_range_tau_range_omega
      (measurableSet_range_omega S.o), range_tau_union_range_omega]
    exact Measure.restrict_eq_self_of_ae_mem hν
  calc μ₂ = μ₂.restrict (Set.range (tau S.o)) + μ₂.restrict (Set.range (omega S.o)) :=
        (hsplit μ₂ h.supp₂).symm
    _ = ((μ₂.restrict (Set.range (tau S.o))).map unCode).map (tau S.o) +
          ((μ₂.restrict (Set.range (omega S.o))).map unCode).map (omega S.o) := by
        rw [map_map_unCode_restrict (measurable_tau S.o) (measurableSet_range_tau S.o)
            (by rintro _ ⟨x, rfl⟩; rfl),
          map_map_unCode_restrict (measurable_omega S.o) (measurableSet_range_omega S.o)
            (by rintro _ ⟨x, rfl⟩; rfl)]
    _ = (μ₁.restrict (Set.range (omega S.o))).map flipAxis +
          (μ₁.restrict (Set.range (tau S.o))).map flipAxis := by
        rw [h.map_unCode_tau₂, h.map_unCode_omega₂, map_flipAxis_restrict_range_tau,
          map_flipAxis_restrict_range_omega]
    _ = μ₁.map flipAxis := by
        rw [← Measure.map_add _ _ measurable_flipAxis, add_comm, hsplit μ₁ h.supp₁]

/-- `∫ f_{2,s} d(flip_*ν) = ∫ f_{1,s} dν`. -/
theorem integral_potential₂_map_flipAxis (S : System ι) (s : ℝ)
    (ν : Measure (ℤ → ι × ZMod 2)) :
    ∫ y, S.potential₂ s (y 0) ∂(ν.map flipAxis) = ∫ y, S.potential₁ s (y 0) ∂ν := by
  have hm : Measurable fun y : ℤ → ι × ZMod 2 => S.potential₂ s (y 0) :=
    (Measurable.of_discrete (f := S.potential₂ s)).comp (measurable_pi_apply 0)
  rw [integral_map measurable_flipAxis.aemeasurable hm.aestronglyMeasurable]
  exact integral_congr_ae (Eventually.of_forall fun y => S.potential₂_flipSymbol s (y 0))

/-- `∫ f_{1,s} d(flip_*ν) = ∫ f_{2,s} dν`. -/
theorem integral_potential₁_map_flipAxis (S : System ι) (s : ℝ)
    (ν : Measure (ℤ → ι × ZMod 2)) :
    ∫ y, S.potential₁ s (y 0) ∂(ν.map flipAxis) = ∫ y, S.potential₂ s (y 0) ∂ν := by
  have hm : Measurable fun y : ℤ → ι × ZMod 2 => S.potential₁ s (y 0) :=
    (Measurable.of_discrete (f := S.potential₁ s)).comp (measurable_pi_apply 0)
  rw [integral_map measurable_flipAxis.aemeasurable hm.aestronglyMeasurable]
  rfl

omit [Fintype ι] [MeasurableSingletonClass ι] in
/-- `thm:eq_state_is_sum`, second line: `λ_1(𝖠, μ) = ∫ f_{1,1} dμ_1`. -/
theorem GibbsDecomposition.lyapunov₁_eq_integral (h : S.GibbsDecomposition s μ μ₁ μ₂) :
    S.lyapunov₁ μ = ∫ y, S.potential₁ 1 (y 0) ∂μ₁ :=
  h.lyapunov₁_eq.trans (S.lyapBar_eq_integral μ₁)

/-- `thm:eq_state_is_sum`, second line: `λ_1(𝖠, μ) = ∫ f_{2,1} dμ_2`. -/
theorem GibbsDecomposition.lyapunov₁_eq_integral_potential₂
    (h : S.GibbsDecomposition s μ μ₁ μ₂) :
    S.lyapunov₁ μ = ∫ y, S.potential₂ 1 (y 0) ∂μ₂ := by
  rw [h.lyapunov₁_eq_integral, h.map_flip, integral_potential₂_map_flipAxis]

omit [Fintype ι] [MeasurableSingletonClass ι] in
/-- `thm:eq_state_is_sum`, third line: `λ_2(𝖠, μ) = ∫ f_{1,1} dμ_2`. -/
theorem GibbsDecomposition.lyapunov₂_eq_integral (h : S.GibbsDecomposition s μ μ₁ μ₂) :
    S.lyapunov₂ μ = ∫ y, S.potential₁ 1 (y 0) ∂μ₂ :=
  h.lyapunov₂_eq.trans (S.lyapBar_eq_integral μ₂)

/-- `thm:eq_state_is_sum`, third line: `λ_2(𝖠, μ) = ∫ f_{2,1} dμ_1`. -/
theorem GibbsDecomposition.lyapunov₂_eq_integral_potential₂
    (h : S.GibbsDecomposition s μ μ₁ μ₂) :
    S.lyapunov₂ μ = ∫ y, S.potential₂ 1 (y 0) ∂μ₁ := by
  rw [h.lyapunov₂_eq_integral, h.map_flip, integral_potential₁_map_flipAxis]

/-- The constant in the Gibbs bounds for `f_{1,s}` of a probability measure carried by `Σ_Z` is
`P(𝖠, s)`, for every box-like system and `0 < s < 2`. -/
theorem _root_.BoxLike.IsGibbsAt.eq_pressure₁ {ν : Measure (ℤ → ι × ZMod 2)}
    [IsProbabilityMeasure ν] (hν : ν (subshift S.o)ᶜ = 0) (hs0 : 0 < s) (hs2 : s < 2) {P : ℝ}
    (h : IsGibbsAt S.o (S.potential₁ s) ν P) : P = S.pressure s :=
  haveI : Nonempty ι := ⟨((nonempty_of_isProbabilityMeasure ν).some 0).1⟩
  tendsto_nhds_unique (h.tendsto_log_admissibleSum hν)
    (S.tendsto_log_admissibleSum_potential₁ hs0 hs2)

/-- The constant in the Gibbs bounds for `f_{2,s}` of a probability measure carried by `Σ_Z` is
`P(𝖠, s)`, for every box-like system and `0 < s < 2`. -/
theorem _root_.BoxLike.IsGibbsAt.eq_pressure₂ {ν : Measure (ℤ → ι × ZMod 2)}
    [IsProbabilityMeasure ν] (hν : ν (subshift S.o)ᶜ = 0) (hs0 : 0 < s) (hs2 : s < 2) {P : ℝ}
    (h : IsGibbsAt S.o (S.potential₂ s) ν P) : P = S.pressure s :=
  haveI : Nonempty ι := ⟨((nonempty_of_isProbabilityMeasure ν).some 0).1⟩
  tendsto_nhds_unique (h.tendsto_log_admissibleSum hν)
    (S.tendsto_log_admissibleSum_potential₂ hs0 hs2)

/-- The Gibbs measure `μ_1` of `thm:eq_state_is_sum` satisfies the Gibbs bounds for `f_{1,s}`
with the constant `P(𝖠, s) = P_Z(f_{1,s})`. -/
theorem GibbsDecomposition.isGibbsAt₁ (h : S.GibbsDecomposition s μ μ₁ μ₂) (hs0 : 0 < s)
    (hs2 : s < 2) : IsGibbsAt S.o (S.potential₁ s) μ₁ (S.pressure s) := by
  have := h.prob₁
  obtain ⟨P, hP⟩ := isGibbs_iff_exists_isGibbsAt.1 h.gibbs₁
  rwa [← hP.eq_pressure₁ h.supp₁ hs0 hs2]

/-- The Gibbs measure `μ_2` of `thm:eq_state_is_sum` satisfies the Gibbs bounds for `f_{2,s}`
with the constant `P(𝖠, s) = P_Z(f_{2,s})`. -/
theorem GibbsDecomposition.isGibbsAt₂ (h : S.GibbsDecomposition s μ μ₁ μ₂) (hs0 : 0 < s)
    (hs2 : s < 2) : IsGibbsAt S.o (S.potential₂ s) μ₂ (S.pressure s) := by
  have := h.prob₂
  obtain ⟨P, hP⟩ := isGibbs_iff_exists_isGibbsAt.1 h.gibbs₂
  rwa [← hP.eq_pressure₂ h.supp₂ hs0 hs2]

end Decomposition

end System

end BoxLike
