module

/-
Rapaport's theorem on diagonal self-affine sets, `thm:rapaport` of `sec:intro_setting`, as a
`Prop`-valued definition, proved in `BoxLike/Rapaport/` as
`Rapaport.rapaportDiagonalDimension_holds` and used by case (iii) of `thm:main2`.

* `System.proximal_iff_of_diagonal`: for a system without rotations, proximality is
  `|a_i| ≠ |b_i|` for some `i`, the form in which `sec:intro_setting` states it.
* `RapaportDiagonalDimension`: the statement, with its source record.
* `System.dimaff_of_subsingleton`, `System.dimH_attractor_of_subsingleton`: for one map, `X` is
  a point and `dimaff(X) = 0`, so the conclusion of the statement holds.
* `RapaportDiagonalDimension.oneLetter`, `RapaportDiagonalDimension.degenerate_oneLetter`: the
  degenerate instance of one diagonal map with `|b| < |a|`.
-/
public import BoxLike.AffinityDim
public import BoxLike.AxisSeparation
public import BoxLike.Proximal
public import Mathlib.Topology.MetricSpace.HausdorffDimension

@[expose] public section

namespace BoxLike

universe u

namespace System

variable {ι : Type*} (S : System ι)

/-- For a system without rotations, `A_𝐢 = diag(a_{i_0} ⋯ a_{i_{n-1}}, b_{i_0} ⋯ b_{i_{n-1}})`,
so the tuple is proximal exactly when `|a_i| ≠ |b_i|` for some `i`: the form of proximality in
`sec:intro_setting` (tex lines 407 to 409) and the first hypothesis of Rapaport's Theorem 1.3. -/
theorem proximal_iff_of_diagonal (h : ∀ i, S.o i = 0) :
    S.Proximal ↔ ∃ i, |S.a i| ≠ |S.b i| := by
  constructor
  · rintro ⟨w, -, hB⟩
    obtain ⟨-, hne, -⟩ := S.isProximalMatrix_matWord hB
    rw [S.codeWord_eq_axisWord h, S.codeWord_eq_axisWord h, gDeriv_axisWord_zero,
      gDeriv_axisWord_one] at hne
    by_contra hcon
    have hall : ∀ i, |S.a i| = |S.b i| := fun i => not_not.1 fun hi => hcon ⟨i, hi⟩
    have key : ∀ w : List ι, |(w.map S.a).prod| = |(w.map S.b).prod| := fun w => by
      induction w with
      | nil => simp
      | cons i w ih =>
        rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, abs_mul, abs_mul,
          hall i, ih]
    exact hne (key w)
  · rintro ⟨i, hi⟩
    exact HasProximalDiagonal.proximal ⟨i, h i, hi⟩

/-! ### One map -/

variable [Fintype ι] [Nonempty ι]

/-- For one map `dimaff(X) = 0`: `P(𝖠, 0) = log 1 = 0`. -/
theorem dimaff_of_subsingleton [Subsingleton ι] : S.dimaff = 0 := by
  have hcard : Fintype.card ι = 1 :=
    le_antisymm (Fintype.card_le_one_iff_subsingleton.2 inferInstance) Fintype.card_pos
  refine S.dimaff_eq le_rfl ?_
  rw [S.pressure_zero, hcard, Nat.cast_one, Real.log_one]

/-- For one map `X` is a point, so `dim_H X = 0 = min{2, dimaff(X)}`: the conclusion of
`thm:rapaport` holds for every one-map system. -/
theorem dimH_attractor_of_subsingleton [Subsingleton ι] :
    dimH S.attractor = ENNReal.ofReal (min 2 S.dimaff) := by
  have hsub : S.attractor.Subsingleton := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [Subsingleton.elim x y]
  rw [hsub.dimH_zero, S.dimaff_of_subsingleton, min_eq_right zero_le_two, ENNReal.ofReal_zero]

end System

/-- Rapaport, *Dimension of diagonal self-affine sets and measures via non-conformal
partitions*, arXiv:2309.03985, Theorem 1.3, in the plane: `thm:rapaport` of `sec:intro_setting`
(tex lines 406 to 430). The statement was read in arXiv:2309.03985v1 (7 September 2023),
Section 1.1.

Source. `Λ` is a finite non-empty index set and `Φ = {φ_i(x) = A_i x + a_i}_{i ∈ Λ}` a diagonal
affine iterated function system on `ℝ^d`: `A_i = diag(r_{i,1}, …, r_{i,d})` with
`0 ≠ r_{i,j} ∈ (-1, 1)` and `a_i = (a_{i,1}, …, a_{i,d})`, with attractor `K_Φ`. For
`1 ≤ j ≤ d` the induced system `Φ_j = {t ↦ r_{i,j} t + a_{i,j}}_{i ∈ Λ}` is an affine iterated
function system on `ℝ`. For affine maps `ψ_1, ψ_2` of `ℝ` with `ψ_k(t) = s_k t + b_k` the
source sets `ρ(ψ_1, ψ_2) = ∞` if `s_1 ≠ s_2` and `ρ(ψ_1, ψ_2) = |b_1 - b_2|` otherwise
(Definition 1.1), and writes `ψ_u = ψ_{i_1} ∘ ⋯ ∘ ψ_{i_n}` for `u = i_1 ⋯ i_n ∈ Λ^n`. An affine
system `Ψ = {ψ_i}_{i ∈ Λ}` on `ℝ` is exponentially separated if there are `c > 0` and an
infinite set `Q ⊆ ℕ` with `ρ(ψ_{u_1}, ψ_{u_2}) ≥ c^n` for all `n ∈ Q` and all distinct
`u_1, u_2 ∈ Λ^n`. Theorem 1.3: if for each pair `1 ≤ j_1 < j_2 ≤ d` there is `i ∈ Λ` with
`|r_{i,j_1}| ≠ |r_{i,j_2}|`, and `Φ_j` is exponentially separated for each `1 ≤ j ≤ d`, then
`dim_H K_Φ = min{dim_A Φ, d}`, with `dim_A Φ` the affinity dimension of `Φ`, Falconer's
affinity dimension, which the source defines in its Section 7 (not consulted) and the library
as the zero of the singular value pressure of `(A_i)`.

The statement. `d = 2`; the alphabet is a finite non-empty type `ι`; a diagonal system is a
box-like `System ι` all of whose orientations are `0`, with `A_i = diag(a_i, b_i)` and
`v_i = (v_i^{(1)}, v_i^{(2)})` (`System.phi_of_o_eq_zero`); its attractor is `System.attractor`
and its affinity dimension `System.dimaff`, the zero of the singular value pressure. The
induced systems are the coordinate maps `g_{(i,0)}(x) = a_i x + v_i^{(1)}` and
`g_{(i,1)}(y) = b_i y + v_i^{(2)}` of the projective system, and the composition
`g_{(i_0,c)} ∘ ⋯ ∘ g_{(i_{n-1},c)}` is `S.gWord (axisWord c 𝐢)`, in the order of the source.
The hypothesis on the ratios is `S.Proximal`, which for a diagonal system is `|a_i| ≠ |b_i|`
for some `i` (`System.proximal_iff_of_diagonal`), the form of `sec:intro_setting`. Exponential
separation of the induced system on the axis `c` is `System.AxisExpSeparation c`: the gap
`System.axisGap c n`, the minimum of `|g_𝐢(0) - g_𝐣(0)|` over distinct words of length `n`
with equal derivatives and `⊤` for the empty minimum, is the minimum of `ρ` over all distinct
pairs, since `ρ = ∞` for pairs with distinct derivatives; and a strictly increasing sequence of
lengths is an infinite set (`System.axisExpSeparation_iff_frequently`). The conclusion is
`dim_H X = min{2, dimaff(X)}` in `ℝ≥0∞`, with the supremum metric on the plane, which has the
same Hausdorff dimension as the Euclidean metric.

Deviations. None in the hypotheses or the conclusion. The source allows the alphabet to index
equal maps, as does the statement.

Degenerate instance. One diagonal map with `|b| < |a|` (`RapaportDiagonalDimension.oneLetter`,
`φ(x, y) = (x/2, y/4)`) is proximal, each induced system has one word of each length, so both
axis gaps are `⊤` and both separations hold, the attractor is a point, so `dim_H X = 0`, and
`dimaff(X) = 0` (`RapaportDiagonalDimension.degenerate_oneLetter`,
`System.dimH_attractor_of_subsingleton`). -/
def RapaportDiagonalDimension : Prop :=
  ∀ {ι : Type u} [Fintype ι] [Nonempty ι] (S : System ι), (∀ i, S.o i = 0) → S.Proximal →
    S.AxisExpSeparation 0 → S.AxisExpSeparation 1 →
    dimH S.attractor = ENNReal.ofReal (min 2 S.dimaff)

namespace RapaportDiagonalDimension

/-! ### The degenerate instance of one letter -/

/-- The one-letter diagonal system `φ(x, y) = (x/2, y/4)`. -/
noncomputable def oneLetter : System Unit where
  o _ := 0
  a _ := 1 / 2
  b _ := 1 / 4
  v _ := 0
  a_ne_zero _ := by norm_num
  b_ne_zero _ := by norm_num
  abs_a_lt_one _ := by rw [abs_of_pos (by norm_num)]; norm_num
  abs_b_lt_one _ := by rw [abs_of_pos (by norm_num)]; norm_num

/-- The one-letter system is diagonal and proximal, since `|1/2| ≠ |1/4|`. -/
theorem oneLetter_proximal : oneLetter.Proximal :=
  (oneLetter.proximal_iff_of_diagonal fun _ => rfl).2 ⟨(), by
    rw [show oneLetter.a () = 1 / 2 from rfl, show oneLetter.b () = 1 / 4 from rfl,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    norm_num⟩

/-- The degenerate test of the premise: the one-letter system satisfies every hypothesis of
`RapaportDiagonalDimension`, and its conclusion holds there, with both sides `0`. -/
theorem degenerate_oneLetter :
    (∀ i, oneLetter.o i = 0) ∧ oneLetter.Proximal ∧ oneLetter.AxisExpSeparation 0 ∧
      oneLetter.AxisExpSeparation 1 ∧
      dimH oneLetter.attractor = ENNReal.ofReal (min 2 oneLetter.dimaff) :=
  ⟨fun _ => rfl, oneLetter_proximal, oneLetter.axisExpSeparation_of_subsingleton 0,
    oneLetter.axisExpSeparation_of_subsingleton 1, oneLetter.dimH_attractor_of_subsingleton⟩

/-- Both sides of the conclusion vanish at the one-letter system. -/
theorem degenerate_oneLetter_eq_zero :
    dimH oneLetter.attractor = 0 ∧ oneLetter.dimaff = 0 :=
  ⟨by rw [oneLetter.dimH_attractor_of_subsingleton, oneLetter.dimaff_of_subsingleton,
      min_eq_right zero_le_two, ENNReal.ofReal_zero], oneLetter.dimaff_of_subsingleton⟩

end RapaportDiagonalDimension

end BoxLike
