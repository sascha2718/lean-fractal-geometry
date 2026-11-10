module

/-
The grouping map `β : Σ → Σ^(2)` of `sec:normalisation` and the thermodynamic part of
`thm:two-block-normalisation`: the passage from `Φ` and `μ` to the second iterate `Φ^(2)` and
`μ^(2) = β_*μ` doubles the pressure, the entropy and the Lyapunov exponents, and leaves the
canonical projection and the projected measures unchanged.

* `group`, `group_shift_two`, `measurable_group`, `measurePreserving_shift_map_group`: the map
  `β((i_n)_n) = ((i_{2n}, i_{2n+1}))_n`, the identity `β ∘ σ² = σ^(2) ∘ β`, and the invariance
  of `μ^(2)`.
* `flatWord`, `flatWord_futureWord_group`, `sum_flatWord_ofFn`: a word of length `n` over the
  paired alphabet is a word of length `2n` over the original alphabet, and this correspondence
  is a bijection.
* `System.matWord_sq_futureWord_group`, `System.phiWord_sq_futureWord_group`: the two words
  have the same matrix product and the same map.
* `System.sq_withRotations`: `Φ^(2)` is box-like with rotations when `Φ` is.
* `System.proj_sq_group`, `System.marginal_sq_map_group`: `π^(2) ∘ β = π`, and the coordinate
  marginals of `π^(2)_*μ^(2)` and `π_*μ` agree.
* `tendsto_two_mul_div`: the even subsequence of a limit `a_n / n → L` gives `a_{2n} / n → 2L`.
* `System.svfSum_sq`, `System.pressure_sq`: `P(𝖠², s) = 2 P(𝖠, s)`.
* `cylinderList`, `preimage_group_cylinderList`, `blockEntropy_map_group`,
  `entropy_map_group`: `H_{μ^(2)}(𝒫_0^{n-1}) = H_μ(𝒫_0^{2n-1})` and `h_0(μ^(2)) = 2 h_0(μ)`.
* `System.lyapunov₁_sq_map_group`, `System.lyapunov₂_sq_map_group`:
  `λ_k(𝖠², μ^(2)) = 2 λ_k(𝖠, μ)`.
* `energy_two_mul`: the energy `Λ` is homogeneous in the Lyapunov exponents.
-/
public import BoxLike.SecondIterate
public import BoxLike.Thermodynamic
public import Mathlib.Data.List.FinRange
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.Filter.AtTopBot.Tendsto
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace BoxLike

open Filter Topology MeasureTheory
open scoped Matrix.Norms.L2Operator

/-! ### The grouping map -/

section Group

variable {α : Type*}

/-- The grouping map `β` of `sec:normalisation`. -/
def group {α : Type*} (x : ℤ → α) : ℤ → α × α := fun n => (x (2 * n), x (2 * n + 1))

/-- The `n`-th symbol of `β(𝐢)` is the pair `(i_{2n}, i_{2n+1})`. -/
@[simp] theorem group_apply (x : ℤ → α) (n : ℤ) : group x n = (x (2 * n), x (2 * n + 1)) := rfl

/-- `β ∘ σ² = σ^(2) ∘ β`, as in `sec:normalisation`. -/
theorem group_shift_two (x : ℤ → α) : group (shift 2 x) = shift 1 (group x) := by
  funext n
  simp only [group_apply, shift_apply]
  rw [show 2 + 2 * n = 2 * (1 + n) by ring, show 2 + (2 * n + 1) = 2 * (1 + n) + 1 by ring]

/-- The word of length `2n` over `α` underlying a word of length `n` over the paired alphabet
`α × α`. -/
def flatWord : List (α × α) → List α
  | [] => []
  | p :: l => p.1 :: p.2 :: flatWord l

/-- The empty word underlies the empty word. -/
@[simp] theorem flatWord_nil : flatWord ([] : List (α × α)) = [] := rfl

/-- The pair `(i, j)` contributes the two letters `i j` to the underlying word. -/
@[simp] theorem flatWord_cons (p : α × α) (l : List (α × α)) :
    flatWord (p :: l) = p.1 :: p.2 :: flatWord l := rfl

/-- The word underlying a word of length `n` has length `2n`. -/
@[simp] theorem length_flatWord (l : List (α × α)) : (flatWord l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons p l ih => simp [ih]; ring

/-- The word underlying a concatenation is the concatenation of the underlying words. -/
theorem flatWord_append (l l' : List (α × α)) :
    flatWord (l ++ l') = flatWord l ++ flatWord l' := by
  induction l with
  | nil => rfl
  | cons p l ih => simp [ih]

/-- Distinct words over the paired alphabet have distinct underlying words. -/
theorem flatWord_injective : Function.Injective (flatWord : List (α × α) → List α) := by
  intro l
  induction l with
  | nil =>
    intro l' h
    cases l' with
    | nil => rfl
    | cons p' l' => simp at h
  | cons p l ih =>
    intro l' h
    cases l' with
    | nil => simp at h
    | cons p' l' =>
      simp only [flatWord_cons, List.cons.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      rw [Prod.ext h1 h2, ih h3]

/-- The word `i_0 ⋯ i_{2n-1}` underlies the prefix of length `n` of `β(𝐢)`. -/
theorem flatWord_futureWord_group (x : ℤ → α) (n : ℕ) :
    flatWord (futureWord (group x) n) = futureWord x (2 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, futureWord_succ, futureWord_succ,
      futureWord_succ, flatWord_append, ih]
    simp

/-- The prefix `𝐢|_n` is the list of the entries of the block `i_0 ⋯ i_{n-1}`. -/
theorem futureWord_eq_ofFn (x : ℤ → α) (n : ℕ) : futureWord x n = List.ofFn (block n x) := by
  rw [List.ofFn_eq_map, futureWord, ← List.map_coe_finRange_eq_range, List.map_map]
  rfl

end Group

section GroupMeasurable

variable {α : Type*} [MeasurableSpace α]

/-- The grouping map `β` is measurable. -/
theorem measurable_group : Measurable (group : (ℤ → α) → ℤ → α × α) :=
  Measurable.of_eval fun n =>
    (measurable_pi_apply (2 * n)).prodMk (measurable_pi_apply (2 * n + 1))

/-- The measure `μ^(2) = β_*μ` of `sec:normalisation` is invariant when `μ` is. -/
theorem measurePreserving_shift_map_group {μ : Measure (ℤ → α)}
    (hμ : MeasurePreserving (shift 1) μ μ) :
    MeasurePreserving (shift 1) (μ.map group) (μ.map group) := by
  refine ⟨measurable_shift 1, ?_⟩
  have h2 : MeasurePreserving (shift 2) μ μ := by
    simpa using measurePreserving_shift_natCast hμ 2
  have hcomp : (shift 1 : (ℤ → α × α) → ℤ → α × α) ∘ group = group ∘ shift 2 :=
    funext fun x => (group_shift_two x).symm
  rw [Measure.map_map (measurable_shift 1) measurable_group, hcomp,
    ← Measure.map_map measurable_group (measurable_shift 2), h2.map_eq]

end GroupMeasurable

/-! ### Sums over words -/

/-- A sum over the words of length `m` depends only on the number `m`. -/
theorem sum_ofFn_congr {α M : Type*} [Fintype α] [AddCommMonoid M] {m m' : ℕ} (h : m = m')
    (G : List α → M) :
    ∑ v : Fin m → α, G (List.ofFn v) = ∑ v : Fin m' → α, G (List.ofFn v) := by
  subst h
  rfl

/-- The words of length `n` over the paired alphabet correspond bijectively to the words of
length `2n` over the original alphabet, as in `sec:normalisation`: a sum over the latter is a
sum over the former. -/
theorem sum_flatWord_ofFn {α M : Type*} [Fintype α] [AddCommMonoid M] (n : ℕ)
    (G : List α → M) :
    ∑ w : Fin n → α × α, G (flatWord (List.ofFn w)) = ∑ v : Fin (2 * n) → α, G (List.ofFn v) := by
  induction n generalizing G with
  | zero => simp
  | succ n ih =>
    have hone : ∀ F : List α → M,
        ∑ g : Fin 1 → α × α, F (flatWord (List.ofFn g)) = ∑ g : Fin 2 → α, F (List.ofFn g) := by
      intro F
      refine Fintype.sum_equiv
        ((Equiv.funUnique (Fin 1) (α × α)).trans (finTwoArrowEquiv α).symm) _ _ fun g => ?_
      simp [List.ofFn_succ]
    calc ∑ w : Fin (n + 1) → α × α, G (flatWord (List.ofFn w))
        = ∑ w : Fin (1 + n) → α × α, G (flatWord (List.ofFn w)) :=
          sum_ofFn_congr (Nat.add_comm n 1) fun l => G (flatWord l)
      _ = ∑ g : Fin 1 → α × α, ∑ h : Fin n → α × α,
            G (flatWord (List.ofFn g ++ List.ofFn h)) :=
          sum_ofFn_add 1 n fun l => G (flatWord l)
      _ = ∑ g : Fin 1 → α × α, ∑ v : Fin (2 * n) → α,
            G (flatWord (List.ofFn g) ++ List.ofFn v) :=
          Finset.sum_congr rfl fun g _ => by
            simp only [flatWord_append]
            exact ih fun l => G (flatWord (List.ofFn g) ++ l)
      _ = ∑ g : Fin 2 → α, ∑ v : Fin (2 * n) → α, G (List.ofFn g ++ List.ofFn v) :=
          hone fun l => ∑ v : Fin (2 * n) → α, G (l ++ List.ofFn v)
      _ = ∑ v : Fin (2 + 2 * n) → α, G (List.ofFn v) := (sum_ofFn_add 2 (2 * n) G).symm
      _ = ∑ v : Fin (2 * (n + 1)) → α, G (List.ofFn v) := sum_ofFn_congr (by ring) G

/-! ### The second iterate along the grouping map -/

namespace System

variable {ι : Type*} (S : System ι)

/-- The matrix product of `Φ^(2)` along a word is the matrix product of `Φ` along the
underlying word. -/
theorem matWord_flatWord (l : List (ι × ι)) : S.matWord (flatWord l) = S.sq.matWord l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [flatWord_cons, matWord_cons, matWord_cons, matWord_cons, ih, sq_mat, mul_assoc]

/-- The map of `Φ^(2)` along a word is the map of `Φ` along the underlying word. -/
theorem phiWord_flatWord (l : List (ι × ι)) : S.phiWord (flatWord l) = S.sq.phiWord l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    funext z
    simp only [flatWord_cons, phiWord_cons, Function.comp_apply, ih, sq_phi]

/-- The matrix product of `Φ^(2)` along the prefix of length `n` of `β(𝐢)` is
`A_{i_0} ⋯ A_{i_{2n-1}}`, as in `sec:normalisation`. -/
theorem matWord_sq_futureWord_group (x : ℤ → ι) (n : ℕ) :
    S.sq.matWord (futureWord (group x) n) = S.matWord (futureWord x (2 * n)) := by
  rw [← matWord_flatWord, flatWord_futureWord_group]

/-- The map of `Φ^(2)` along the prefix of length `n` of `β(𝐢)` is
`φ_{i_0} ∘ ⋯ ∘ φ_{i_{2n-1}}`. -/
theorem phiWord_sq_futureWord_group (x : ℤ → ι) (n : ℕ) :
    S.sq.phiWord (futureWord (group x) n) = S.phiWord (futureWord x (2 * n)) := by
  rw [← phiWord_flatWord, flatWord_futureWord_group]

/-- The second iterate of a box-like system with rotations is box-like with rotations: `A_i A_i`
is diagonal and `A_i A_j` is anti-diagonal for a diagonal `A_i` and an anti-diagonal `A_j`. -/
theorem sq_withRotations (h : S.WithRotations) : S.sq.WithRotations := by
  obtain ⟨⟨i, hi⟩, j, hj⟩ := h
  exact ⟨⟨(i, i), by simp [sq, hi]⟩, (i, j), by simp [sq, hi, hj]⟩

end System

/-! ### Even subsequences -/

/-- The sequence `n ↦ 2n` tends to infinity. -/
theorem tendsto_two_mul_atTop : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
  tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n two_pos) tendsto_id

/-- If `a_n / n → L` then `a_{2n} / n → 2L`: the even subsequence of the limits defining the
pressure, the entropy and the Lyapunov exponents. -/
theorem tendsto_two_mul_div {a : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun n : ℕ => a n / n) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => a (2 * n) / n) atTop (𝓝 (2 * L)) := by
  refine ((h.comp tendsto_two_mul_atTop).const_mul 2).congr fun n => ?_
  simp only [Function.comp_apply, Nat.cast_mul, Nat.cast_ofNat]
  rcases eq_or_ne (n : ℝ) 0 with h0 | h0
  · simp [h0]
  · field_simp

/-! ### The canonical projection -/

namespace System

variable {ι : Type*} (S : System ι)

/-- `π^(2) ∘ β = π`, as in `sec:normalisation`. -/
theorem proj_sq_group [Finite ι] (x : ℤ → ι) : S.sq.proj (group x) = S.proj x := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  obtain ⟨r', M', hS'⟩ := S.sq.exists_bounds
  refine tendsto_nhds_unique (hS'.tendsto_phiWord (group x)) ?_
  simp only [phiWord_sq_futureWord_group]
  exact (hS.tendsto_phiWord x).comp tendsto_two_mul_atTop

/-- `π^(2)_*μ^(2) = π_*μ`, as in `sec:normalisation`, for the coordinate marginals. -/
theorem marginal_sq_map_group [Finite ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (c : ZMod 2) (μ : Measure (ℤ → ι)) : S.sq.marginal c (μ.map group) = S.marginal c μ := by
  obtain ⟨r', M', hS'⟩ := S.sq.exists_bounds
  have hcomp : S.sq.proj ∘ group = S.proj := funext fun x => S.proj_sq_group x
  rw [marginal, marginal, Measure.map_map hS'.measurable_proj measurable_group, hcomp]

/-! ### The pressure -/

section Pressure

variable [Fintype ι]

/-- The sum `∑_{|𝐢| = n} φ^s(A_𝐢)` of `Φ^(2)` is the sum at length `2n` of `Φ`. -/
theorem svfSum_sq (s : ℝ) (n : ℕ) : S.sq.svfSum s n = S.svfSum s (2 * n) := by
  rw [svfSum, svfSum, ← sum_flatWord_ofFn n fun l => svf s (S.matWord l)]
  simp only [matWord_flatWord]

/-- `P(𝖠², s) = 2 P(𝖠, s)`, as in `sec:normalisation`. -/
theorem pressure_sq [Nonempty ι] {s : ℝ} (hs : 0 ≤ s) : S.sq.pressure s = 2 * S.pressure s := by
  obtain ⟨δ, hδ⟩ := S.exists_ratioLowerBound
  obtain ⟨δ', hδ'⟩ := S.sq.exists_ratioLowerBound
  refine tendsto_nhds_unique (hδ'.tendsto_pressure hs) ?_
  simp only [svfSum_sq]
  exact tendsto_two_mul_div (hδ.tendsto_pressure hs)

end Pressure

end System

/-! ### The entropy -/

section Entropy

variable {α : Type*}

/-- The cylinder `[l]` of a word given as a list. -/
def cylinderList (l : List α) : Set (ℤ → α) := {x | futureWord x l.length = l}

/-- The cylinder of a word `w : Fin n → α` is the cylinder of the list of its entries. -/
theorem cylinder_eq_cylinderList {n : ℕ} (w : Fin n → α) :
    cylinder w = cylinderList (List.ofFn w) := by
  ext x
  rw [cylinder_eq_preimage, cylinderList, Set.mem_ofPred_eq, List.length_ofFn,
    futureWord_eq_ofFn, List.ofFn_injective.eq_iff]
  rfl

/-- The preimage under `β` of the cylinder of a word over the paired alphabet is the cylinder
of the underlying word. -/
theorem preimage_group_cylinderList (l : List (α × α)) :
    group ⁻¹' cylinderList l = cylinderList (flatWord l) := by
  ext x
  rw [Set.mem_preimage, cylinderList, cylinderList, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
    length_flatWord, ← flatWord_futureWord_group, flatWord_injective.eq_iff]

end Entropy

section EntropyGroup

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The block entropy of `μ^(2) = β_*μ` at length `n` is the block entropy of `μ` at length
`2n`, as in `sec:normalisation`. -/
theorem blockEntropy_map_group (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (n : ℕ) :
    blockEntropy (μ.map group) n = blockEntropy μ (2 * n) := by
  have h : ∀ w : Fin n → ι × ι, (μ.map group).real (cylinder w) =
      μ.real (cylinderList (flatWord (List.ofFn w))) := by
    intro w
    rw [map_measureReal_apply measurable_group (measurableSet_cylinder w),
      cylinder_eq_cylinderList, preimage_group_cylinderList]
  simp only [blockEntropy, h]
  simp only [cylinder_eq_cylinderList]
  exact sum_flatWord_ofFn n fun l => Real.negMulLog (μ.real (cylinderList l))

/-- `h_0(μ^(2)) = 2 h_0(μ)`, as in `sec:normalisation`. -/
theorem entropy_map_group {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) : entropy (μ.map group) = 2 * entropy μ := by
  rw [entropy]
  simp only [blockEntropy_map_group]
  exact (tendsto_two_mul_div (tendsto_entropy hμ)).limUnder_eq

end EntropyGroup

/-! ### The Lyapunov exponents -/

namespace System

variable {ι : Type*} [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι)

/-- The integral over `μ^(2) = β_*μ` of a function of the prefix of length `n` is the integral
over `μ` of the same function of the prefix of length `n` of `β(𝐢)`. -/
theorem integral_map_group_futureWord (μ : Measure (ℤ → ι)) (n : ℕ)
    (F : List (ι × ι) → ℝ) :
    ∫ y, F (futureWord y n) ∂(μ.map group) = ∫ x, F (futureWord (group x) n) ∂μ := by
  have hF : Measurable fun y : ℤ → ι × ι => F (futureWord y n) := by
    simp only [futureWord_eq_ofFn]
    exact (Measurable.of_discrete (f := fun w : Fin n → ι × ι => F (List.ofFn w))).comp
      (measurable_block n)
  exact integral_map measurable_group.aemeasurable hF.aestronglyMeasurable

/-- `λ_1(𝖠², μ^(2)) = 2 λ_1(𝖠, μ)`, as in `sec:normalisation`, given that the limit defining
`λ_1(𝖠, μ)` exists. -/
theorem lyapunov₁_sq_map_group {μ : Measure (ℤ → ι)}
    (h : Tendsto (fun n : ℕ => (∫ x, Real.log ‖S.matWord (futureWord x n)‖ ∂μ) / n) atTop
      (𝓝 (S.lyapunov₁ μ))) : S.sq.lyapunov₁ (μ.map group) = 2 * S.lyapunov₁ μ := by
  rw [lyapunov₁]
  simp only [integral_map_group_futureWord μ _ fun l => Real.log ‖S.sq.matWord l‖,
    matWord_sq_futureWord_group]
  exact (tendsto_two_mul_div h).limUnder_eq

/-- `λ_2(𝖠², μ^(2)) = 2 λ_2(𝖠, μ)`, as in `sec:normalisation`, given that the limit defining
`λ_2(𝖠, μ)` exists. -/
theorem lyapunov₂_sq_map_group {μ : Measure (ℤ → ι)}
    (h : Tendsto (fun n : ℕ =>
      (∫ x, Real.log (|(S.matWord (futureWord x n)).det| / ‖S.matWord (futureWord x n)‖) ∂μ) / n)
      atTop (𝓝 (S.lyapunov₂ μ))) : S.sq.lyapunov₂ (μ.map group) = 2 * S.lyapunov₂ μ := by
  rw [lyapunov₂]
  simp only [integral_map_group_futureWord μ _
      fun l => Real.log (|(S.sq.matWord l).det| / ‖S.sq.matWord l‖),
    matWord_sq_futureWord_group]
  exact (tendsto_two_mul_div h).limUnder_eq

end System

/-- The energy `Λ` of `eq:energy_def` is homogeneous in the Lyapunov exponents. -/
theorem energy_two_mul (l1 l2 s : ℝ) : energy (2 * l1) (2 * l2) s = 2 * energy l1 l2 s := by
  unfold energy
  split_ifs <;> ring

end BoxLike
