module

/-
The canonical projections `\overline{π} : Σ_Z → ℝ` and `π : Σ → ℝ²` of
`sec:two_sided_shift_space` and `sec:projective_system`, and the self-affine set `X = π(Σ)`.

* `futureWord`: the prefix `𝐢|_n = i_0 ⋯ i_{n-1}`.
* `System.projBar`, `System.tendsto_gWord`: the projection `\overline{π}`, defined as the
  series `∑_k g'_{𝐣|_k} g_{j_k}(0)`, is the limit `lim_n g_{j_0} ∘ ⋯ ∘ g_{j_{n-1}}(0)`.
* `System.projBar_eq`: `\overline{π}(𝐣) = g_{j_0}(\overline{π}(σ 𝐣))`.
* `System.phiWord`, `System.coord_phiWord`: the composition `φ_𝐢` and its coordinates, the
  finite form of `eq:commutative_diagram`.
* `System.proj`, `System.tendsto_phiWord`: the projection `π`, and `eq:canonical_projection`,
  `π(𝐢) = lim_n φ_{i_0} ∘ ⋯ ∘ φ_{i_{n-1}}(0)`.
* `System.fst_proj`, `System.snd_proj`: `eq:commutative_diagram`.
* `System.Bounds.proj_eq`, `System.proj_congr`: `π(𝐢) = φ_{i_0}(π(σ 𝐢))`, and `π` depends only
  on the future `𝐢^+`.
* `System.attractor`, `System.attractor_eq_iUnion`: `X = π(Σ)` satisfies
  `eq:self_affine_set_def`.
-/
public import BoxLike.Separation
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

namespace BoxLike

open Filter Topology Finset

/-- The prefix `𝐢|_n = i_0 ⋯ i_{n-1}` of a two-sided sequence. -/
def futureWord {α : Type*} (x : ℤ → α) (n : ℕ) : List α :=
  (List.range n).map fun k : ℕ => x (k : ℤ)

section futureWord

variable {α : Type*} (x : ℤ → α)

@[simp] theorem futureWord_zero : futureWord x 0 = [] := rfl

@[simp] theorem length_futureWord (n : ℕ) : (futureWord x n).length = n := by
  simp [futureWord]

theorem futureWord_succ (n : ℕ) : futureWord x (n + 1) = futureWord x n ++ [x n] := by
  simp [futureWord, List.range_succ]

/-- `𝐢|_{n+1} = i_0 (σ 𝐢)|_n`. -/
theorem futureWord_succ' (n : ℕ) :
    futureWord x (n + 1) = x 0 :: futureWord (shift 1 x) n := by
  simp only [futureWord, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.cast_zero]
  congr 1
  apply List.map_congr_left
  intro k _
  simp [add_comm]

theorem futureWord_congr {y : ℤ → α} (h : ∀ k : ℕ, x k = y k) (n : ℕ) :
    futureWord x n = futureWord y n := by
  simp [futureWord, h]

end futureWord

namespace System

variable {ι : Type*} (S : System ι)

/-- A uniform bound for the contraction ratios and translations of the projective system. -/
structure Bounds (r M : ℝ) : Prop where
  r_nonneg : 0 ≤ r
  r_lt_one : r < 1
  abs_ratio_le : ∀ p, |S.ratio p| ≤ r
  abs_trans_le : ∀ p, |S.trans p| ≤ M

/-- A finite system has uniform bounds. -/
theorem exists_bounds [Finite ι] : ∃ r M, S.Bounds r M := by
  classical
  have := Fintype.ofFinite ι
  by_cases hι : Nonempty (ι × ZMod 2)
  · obtain ⟨p₁, -, h₁⟩ := Finset.exists_max_image Finset.univ (fun p => |S.ratio p|)
      Finset.univ_nonempty
    obtain ⟨p₂, -, h₂⟩ := Finset.exists_max_image Finset.univ (fun p => |S.trans p|)
      Finset.univ_nonempty
    exact ⟨|S.ratio p₁|, |S.trans p₂|, abs_nonneg _, S.abs_ratio_lt_one _,
      fun p => h₁ p (Finset.mem_univ _), fun p => h₂ p (Finset.mem_univ _)⟩
  · exact ⟨0, 0, le_rfl, zero_lt_one, fun p => (hι ⟨p⟩).elim, fun p => (hι ⟨p⟩).elim⟩

variable {S} {r M : ℝ}

theorem Bounds.abs_gDeriv_le (hS : S.Bounds r M) (u : List (ι × ZMod 2)) :
    |S.gDeriv u| ≤ r ^ u.length := by
  induction u with
  | nil => simp
  | cons p u ih =>
    rw [gDeriv_cons, abs_mul, List.length_cons, pow_succ']
    exact mul_le_mul (hS.abs_ratio_le p) ih (abs_nonneg _) hS.r_nonneg

variable (S)

/-- The `k`-th term `g'_{𝐣|_k} g_{j_k}(0)` of the series defining `\overline{π}(𝐣)`. -/
def projBarTerm (y : ℤ → ι × ZMod 2) (k : ℕ) : ℝ := S.gDeriv (futureWord y k) * S.trans (y k)

/-- The canonical projection `\overline{π}` of `sec:projective_system`. It is defined on every
sequence over `ι × ZMod 2`, in particular on `Σ_Z`. -/
noncomputable def projBar (y : ℤ → ι × ZMod 2) : ℝ := ∑' k, S.projBarTerm y k

/-- `g_{𝐣|_n}(0)` is the `n`-th partial sum of the series defining `\overline{π}(𝐣)`. -/
theorem gWord_futureWord (y : ℤ → ι × ZMod 2) (n : ℕ) :
    S.gWord (futureWord y n) 0 = ∑ k ∈ range n, S.projBarTerm y k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [futureWord_succ, gWord_append, Function.comp_apply, gWord_apply, ih, sum_range_succ,
      projBarTerm]
    simp [g, add_comm]

variable {S}

theorem Bounds.summable_projBarTerm (hS : S.Bounds r M) (y : ℤ → ι × ZMod 2) :
    Summable (S.projBarTerm y) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hS.abs_trans_le (y 0))
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hS.r_nonneg hS.r_lt_one).mul_right M) fun k => ?_
  rw [projBarTerm, Real.norm_eq_abs, abs_mul]
  have h := hS.abs_gDeriv_le (futureWord y k)
  rw [length_futureWord] at h
  exact mul_le_mul h (hS.abs_trans_le _) (abs_nonneg _) (pow_nonneg hS.r_nonneg _)

/-- The definition of `\overline{π}` in `sec:projective_system`:
`\overline{π}(𝐣) = lim_n g_{j_0} ∘ ⋯ ∘ g_{j_{n-1}}(0)`. -/
theorem Bounds.tendsto_gWord (hS : S.Bounds r M) (y : ℤ → ι × ZMod 2) :
    Tendsto (fun n => S.gWord (futureWord y n) 0) atTop (𝓝 (S.projBar y)) := by
  simp only [gWord_futureWord]
  exact (hS.summable_projBarTerm y).hasSum.tendsto_sum_nat

/-- `\overline{π}(𝐣) = g_{j_0}(\overline{π}(σ 𝐣))`. -/
theorem Bounds.projBar_eq (hS : S.Bounds r M) (y : ℤ → ι × ZMod 2) :
    S.projBar y = S.g (y 0) (S.projBar (shift 1 y)) := by
  have h1 : Tendsto (fun n => S.gWord (futureWord y (n + 1)) 0) atTop (𝓝 (S.projBar y)) :=
    (tendsto_add_atTop_iff_nat 1).2 (hS.tendsto_gWord y)
  have h2 : Tendsto (fun n => S.g (y 0) (S.gWord (futureWord (shift 1 y) n) 0)) atTop
      (𝓝 (S.g (y 0) (S.projBar (shift 1 y)))) := by
    have hc : Continuous (S.g (y 0)) := by unfold g; fun_prop
    exact (hc.tendsto _).comp (hS.tendsto_gWord (shift 1 y))
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  rw [futureWord_succ', gWord_cons, Function.comp_apply]

variable (S)

/-- `\overline{π}` depends only on the future of the sequence. -/
theorem projBar_congr {y y' : ℤ → ι × ZMod 2} (h : ∀ k : ℕ, y k = y' k) :
    S.projBar y = S.projBar y' := by
  unfold projBar projBarTerm
  congr 1
  funext k
  rw [futureWord_congr y h k, h k]

/-! ### The planar system -/

/-- The composition `φ_𝐢 = φ_{i_0} ∘ ⋯ ∘ φ_{i_{n-1}}`. -/
def phiWord : List ι → ℝ × ℝ → ℝ × ℝ
  | [] => id
  | i :: w => S.phi i ∘ phiWord w

@[simp] theorem phiWord_nil : S.phiWord [] = id := rfl

@[simp] theorem phiWord_cons (i : ι) (w : List ι) :
    S.phiWord (i :: w) = S.phi i ∘ S.phiWord w := rfl

/-- The finite form of `eq:commutative_diagram`: the coordinate `c` of `φ_𝐢` is `g` along the
path of `Σ_Z` over `𝐢` starting on the axis `c`. -/
theorem coord_phiWord (c : ZMod 2) (w : List ι) (z : ℝ × ℝ) :
    coord c (S.phiWord w z) = S.gWord (S.codeWord c w) (coord (c + S.oWord w) z) := by
  induction w generalizing c with
  | nil => simp
  | cons i w ih =>
    rw [phiWord_cons, Function.comp_apply, coord_phi, ih, codeWord_cons, gWord_cons,
      Function.comp_apply, oWord_cons, add_assoc]

theorem oWord_append (w w' : List ι) : S.oWord (w ++ w') = S.oWord w + S.oWord w' := by
  simp [oWord]

theorem codeWord_append (c : ZMod 2) (w w' : List ι) :
    S.codeWord c (w ++ w') = S.codeWord c w ++ S.codeWord (c + S.oWord w) w' := by
  induction w generalizing c with
  | nil => simp
  | cons i w ih => simp [ih, add_assoc]

/-- The product `A_{𝐢|_n}` is diagonal exactly when `ε_n(𝐢) = 0`. -/
theorem oWord_futureWord (x : ℤ → ι) (n : ℕ) : S.oWord (futureWord x n) = eps S.o x n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [futureWord_succ, oWord_append, ih, Nat.cast_succ, eps_add_one]
    simp

/-- The path of `Σ_Z` over `𝐢|_n` starting on the first axis is `τ(𝐢)|_n`. -/
theorem codeWord_futureWord_tau (x : ℤ → ι) (n : ℕ) :
    S.codeWord 0 (futureWord x n) = futureWord (tau S.o x) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [futureWord_succ, futureWord_succ, codeWord_append, ih, oWord_futureWord]
    simp

/-- The path of `Σ_Z` over `𝐢|_n` starting on the second axis is `ω(𝐢)|_n`. -/
theorem codeWord_futureWord_omega (x : ℤ → ι) (n : ℕ) :
    S.codeWord 1 (futureWord x n) = futureWord (omega S.o x) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [futureWord_succ, futureWord_succ, codeWord_append, ih, oWord_futureWord]
    simp [add_comm]

/-- The canonical projection `π` of `sec:two_sided_shift_space`, given through its
coordinates; `tendsto_phiWord` shows that it is the limit of `eq:canonical_projection`. -/
noncomputable def proj (x : ℤ → ι) : ℝ × ℝ :=
  (S.projBar (tau S.o x), S.projBar (omega S.o x))

/-- `eq:commutative_diagram`, first identity: `proj_x(π(𝐢)) = \overline{π}(τ(𝐢))`. -/
@[simp] theorem fst_proj (x : ℤ → ι) : (S.proj x).1 = S.projBar (tau S.o x) := rfl

/-- `eq:commutative_diagram`, second identity: `proj_y(π(𝐢)) = \overline{π}(ω(𝐢))`. -/
@[simp] theorem snd_proj (x : ℤ → ι) : (S.proj x).2 = S.projBar (omega S.o x) := rfl

variable {S}

/-- `eq:canonical_projection`: `π(𝐢) = lim_n φ_{i_0} ∘ ⋯ ∘ φ_{i_{n-1}}(0)`. -/
theorem Bounds.tendsto_phiWord (hS : S.Bounds r M) (x : ℤ → ι) :
    Tendsto (fun n => S.phiWord (futureWord x n) 0) atTop (𝓝 (S.proj x)) := by
  have h0 : ∀ n, (S.phiWord (futureWord x n) 0).1 = S.gWord (futureWord (tau S.o x) n) 0 := by
    intro n
    have h := S.coord_phiWord 0 (futureWord x n) 0
    rw [codeWord_futureWord_tau] at h
    simpa [coord] using h
  have h1 : ∀ n, (S.phiWord (futureWord x n) 0).2 = S.gWord (futureWord (omega S.o x) n) 0 := by
    intro n
    have h := S.coord_phiWord 1 (futureWord x n) 0
    rw [codeWord_futureWord_omega] at h
    simpa [coord] using h
  have := (hS.tendsto_gWord (tau S.o x)).prodMk_nhds (hS.tendsto_gWord (omega S.o x))
  refine this.congr fun n => ?_
  exact Prod.ext (h0 n).symm (h1 n).symm

theorem continuous_phi (S : System ι) (i : ι) : Continuous (S.phi i) := by
  unfold phi coord
  split_ifs <;> fun_prop

/-- `π(𝐢) = φ_{i_0}(π(σ 𝐢))`. -/
theorem Bounds.proj_eq (hS : S.Bounds r M) (x : ℤ → ι) :
    S.proj x = S.phi (x 0) (S.proj (shift 1 x)) := by
  have h1 : Tendsto (fun n => S.phiWord (futureWord x (n + 1)) 0) atTop (𝓝 (S.proj x)) :=
    (tendsto_add_atTop_iff_nat 1).2 (hS.tendsto_phiWord x)
  have h2 : Tendsto (fun n => S.phi (x 0) (S.phiWord (futureWord (shift 1 x) n) 0)) atTop
      (𝓝 (S.phi (x 0) (S.proj (shift 1 x)))) :=
    ((S.continuous_phi (x 0)).tendsto _).comp (hS.tendsto_phiWord (shift 1 x))
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  rw [futureWord_succ', phiWord_cons, Function.comp_apply]

variable (S)

theorem eps_congr {x x' : ℤ → ι} (h : ∀ k : ℕ, x k = x' k) (n : ℕ) :
    eps S.o x n = eps S.o x' n := by
  rw [eps_natCast, eps_natCast]
  exact Finset.sum_congr rfl fun j _ => by rw [h j]

/-- `π(𝐢) = π^+(𝐢^+)` depends only on the future of `𝐢`. -/
theorem proj_congr {x x' : ℤ → ι} (h : ∀ k : ℕ, x k = x' k) : S.proj x = S.proj x' := by
  unfold proj
  congr 1
  · exact S.projBar_congr fun k => by rw [tau_apply, tau_apply, h k, S.eps_congr h k]
  · exact S.projBar_congr fun k => by rw [omega_apply, omega_apply, h k, S.eps_congr h k]

/-- The self-affine set `X = π(Σ)`. -/
def attractor : Set (ℝ × ℝ) := Set.range S.proj

variable {S}

/-- `eq:self_affine_set_def` for `X = π(Σ)`: `X = ⋃_i φ_i(X)`. -/
theorem Bounds.attractor_eq_iUnion (hS : S.Bounds r M) :
    S.attractor = ⋃ i, S.phi i '' S.attractor := by
  ext z
  simp only [attractor, Set.mem_range, Set.mem_iUnion, Set.mem_image, exists_exists_eq_and]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x 0, shift 1 x, (hS.proj_eq x).symm⟩
  · rintro ⟨i, x, rfl⟩
    refine ⟨fun k => if k = 0 then i else x (k - 1), ?_⟩
    rw [hS.proj_eq]
    simp only [ite_true]
    congr 1
    apply S.proj_congr
    intro k
    have : (1 : ℤ) + k ≠ 0 := by omega
    simp [this]

end System

end BoxLike
