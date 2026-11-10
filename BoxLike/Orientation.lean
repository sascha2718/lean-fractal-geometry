module

/-
The two-sided full shift of `sec:two_sided_shift_space` and the orientation cocycle
`ε_n` of `eq:def_of_eps_mod2` in `sec:subshift`.

The alphabet is an arbitrary type `ι` and the orientation is a map `o : ι → ZMod 2`, with
`o i = 0` for a diagonal generator and `o i = 1` for an anti-diagonal one. The paper's
relabelling `{1, …, ℓ}` diagonal, `{ℓ+1, …, N}` anti-diagonal is the special case
`o i = 1 ↔ ℓ < i`.

* `shift`: the iterate `σ^n`, `n ∈ ℤ`, of the left shift on `ℤ → ι`.
* `eps`: the cocycle `ε_n(𝐢)`, the parity of the number of anti-diagonal symbols between
  time `0` and time `n`.
* `eps_add_one`, `eq_eps_of_succ`: the recursion `ε_{m+1} = ε_m + o(i_m)` and the fact
  that it determines `ε`; this is the function `S` in the proof of
  `thm:tau_omega_sigma_commutative`.
* `eps_shift`: the cocycle identity `eq:tau_omega_sigma_commutative1`.
-/
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace BoxLike

open Finset

variable {ι : Type*}

/-- The iterate `σ^n`, `n ∈ ℤ`, of the left shift of `sec:two_sided_shift_space`:
`(σ^n 𝐢)_k = i_{n+k}`. -/
def shift (n : ℤ) (x : ℤ → ι) : ℤ → ι := fun k => x (n + k)

@[simp] theorem shift_apply (n k : ℤ) (x : ℤ → ι) : shift n x k = x (n + k) := rfl

@[simp] theorem shift_zero (x : ℤ → ι) : shift 0 x = x := by
  funext k; simp

/-- `σ^m ∘ σ^n = σ^{n+m}`. -/
theorem shift_shift (m n : ℤ) (x : ℤ → ι) : shift m (shift n x) = shift (n + m) x := by
  funext k; simp [add_assoc]

/-- The orientation cocycle `ε_n(𝐢)` of `eq:def_of_eps_mod2`: the parity of the number of
anti-diagonal symbols among `i_0, …, i_{n-1}` when `n ≥ 0`, and among `i_{-1}, …, i_n`
when `n < 0`. -/
def eps (o : ι → ZMod 2) (x : ℤ → ι) : ℤ → ZMod 2
  | Int.ofNat n => ∑ j ∈ range n, o (x j)
  | Int.negSucc n => ∑ j ∈ range (n + 1), o (x (-(j + 1 : ℤ)))

variable (o : ι → ZMod 2) (x : ℤ → ι)

theorem eps_natCast (n : ℕ) : eps o x n = ∑ j ∈ range n, o (x j) := rfl

theorem eps_negSucc (n : ℕ) :
    eps o x (Int.negSucc n) = ∑ j ∈ range (n + 1), o (x (-(j + 1 : ℤ))) := rfl

/-- `ε_0 = 0`. -/
@[simp] theorem eps_zero : eps o x 0 = 0 := by
  simpa using eps_natCast o x 0

/-- The recursion `ε_{m+1}(𝐢) = ε_m(𝐢) + o(i_m)` for every `m ∈ ℤ`; this is the defining
property of the function `S` in the proof of `thm:tau_omega_sigma_commutative`. -/
theorem eps_add_one (m : ℤ) : eps o x (m + 1) = eps o x m + o (x m) := by
  rcases m with n | n
  · change eps o x ((n + 1 : ℕ) : ℤ) = eps o x (n : ℤ) + o (x (n : ℤ))
    rw [eps_natCast, eps_natCast, sum_range_succ]
  · rcases n with _ | n
    · change eps o x 0 = eps o x (Int.negSucc 0) + o (x (Int.negSucc 0))
      rw [eps_zero, eps_negSucc]
      simp [Int.negSucc_eq, CharTwo.add_self_eq_zero]
    · have h : Int.negSucc (n + 1) + 1 = Int.negSucc n := by
        simp only [Int.negSucc_eq]; omega
      rw [h, eps_negSucc, eps_negSucc, sum_range_succ _ (n + 1), add_assoc]
      have hx : x (Int.negSucc (n + 1)) = x (-(((n + 1 : ℕ) : ℤ) + 1)) := by
        simp [Int.negSucc_eq]
      rw [hx, CharTwo.add_self_eq_zero, add_zero]

/-- The recursion of `eps_add_one`, read backwards. -/
theorem eps_sub_one (m : ℤ) : eps o x (m - 1) = eps o x m + o (x (m - 1)) := by
  have h := eps_add_one o x (m - 1)
  rw [sub_add_cancel] at h
  rw [h, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- The recursion `S(0) = 0`, `S(m+1) = S(m) + o(i_m)` determines `ε`. -/
theorem eq_eps_of_succ {S : ℤ → ZMod 2} (h0 : S 0 = 0)
    (hS : ∀ m, S (m + 1) = S m + o (x m)) : S = eps o x := by
  funext n
  induction n using Int.induction_on with
  | zero => rw [h0, eps_zero]
  | succ n ih => rw [hS, eps_add_one, ih]
  | pred n ih =>
    have h := hS (-(n : ℤ) - 1)
    rw [sub_add_cancel] at h
    rw [eps_sub_one, ← ih, h, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- The cocycle identity `eq:tau_omega_sigma_commutative1`:
`ε_k(σ^n 𝐢) = ε_n(𝐢) + ε_{n+k}(𝐢)`. -/
theorem eps_shift (n k : ℤ) : eps o (shift n x) k = eps o x n + eps o x (n + k) := by
  have h : (fun k => eps o x n + eps o x (n + k)) = eps o (shift n x) := by
    apply eq_eps_of_succ
    · simp [CharTwo.add_self_eq_zero]
    · intro m
      rw [← add_assoc n m 1, eps_add_one, shift_apply, add_assoc]
  exact (congrFun h k).symm

/-- `ε_n(𝐢) = 1` exactly when `ε_n(𝐢) ≠ 0`. -/
theorem eps_eq_one_iff (n : ℤ) : eps o x n = 1 ↔ eps o x n ≠ 0 := by
  generalize eps o x n = c
  revert c; decide

end BoxLike
