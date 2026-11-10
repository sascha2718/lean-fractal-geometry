module

/-
Case `it:main2_pesc` of `thm:main2`, the projective exponential separation condition, along the
prose of `sec:dimension_result_proof`. The proof fixes `t = s` if `s < 2` and `0 < t < 2`
otherwise, reduces to a proximal diagonal generator through `thm:two-block-normalisation`, and
takes the `t`-equilibrium state `μ_t`, for which "`h + Λ(𝖠, μ_t, t) = P(𝖠, t) ≥ P(𝖠, s) = 0`.
Hence `\dim_L(𝖠, μ_t) ≥ t`, with equality when `t = s`." The typical families `W_n` of
`eq:diagonal-subsystem-limits` then give: "Let `X_n ⊆ X` be the attractor of `(φ_w)_{w ∈ W_n}`.
Fix `0 < c < 1` such that `Δ_m^Ψ ≥ c^m` for infinitely many `m`. A composition of `k` subsystem
maps acts on either coordinate axis by a map `g_𝐢` with `|𝐢| = kn` ... Hence, both induced
systems are exponentially separated. Since `|b_n| < |a_n|`, the subsystem is proximal, and
`thm:rapaport` gives `\dim_H(X_n) = min{2, dimaff(X_n)}`. The pressure of this subsystem at
`u ≥ 0` is `log #W_n + log φ^u(diag(a_n, b_n))`. By `eq:diml_min2` and the three limits above,
`dimaff(X_n) → \dim_L(𝖠, μ_t)`. Thus `\dim_H(X) ≥ lim_n \dim_H(X_n) = min{2, \dim_L(𝖠, μ_t)} ≥ t`.
Since `t = s`, or `t` is arbitrarily close to `2`, we obtained the required lower bound. The
upper bound is `eq:hausdorff_affinity_upper_bound`." The manuscript settles `s ≤ 1` beforehand
from the projection bound; the statements below take every `0 < t < 2` with `t ≤ dimaff(X)`.

The axis separation of the subsystems is `BoxLike/MainTwoProse/AxisSeparationSubsystem.lean`,
the pressure and the affinity dimension of the homogeneous subsystems and the limit of
`eq:diml_min2` are `BoxLike/MainTwoProse/HomogeneousAffinity.lean`, and Rapaport's theorem
`thm:rapaport` is `Rapaport.rapaportDiagonalDimension_holds` (`BoxLike/Rapaport/`).

* `System.IsEquilibriumState.le_lyapDim`: `\dim_L(𝖠, μ_t) ≥ t` for a `t`-equilibrium state with
  `t ≤ dimaff(𝖠)`.
* `System.dimH_subsystem_attractor_eq`: `\dim_H X_n = min{2, dimaff(X_n)}`, with `dimaff(X_n)`
  the right-hand side of `eq:diml_min2` for `log #W_n`, `log |a_n|`, `log |b_n|`.
* `System.min_lyapDim_le_dimH_attractor_of_family`: `\dim_H X ≥ \dim_H X_n` for one family,
  since `X_n ⊆ X`.
* `System.le_dimH_attractor_of_family_pesc`: the corollary `\dim_H X ≥ u` when
  `log #W_n + Λ(log |a_n|, log |b_n|, u) ≥ 0` for some `u ≤ 2`.
* `System.main2_pesc_normalised`: `\dim_H X ≥ t` for a tuple containing a proximal diagonal
  generator and `0 < t < 2` with `t ≤ dimaff(X)`, by the limit `n → ∞`.
* `System.le_dimH_attractor_pesc`: the same for every proximal tuple, through
  `thm:two-block-normalisation`.
* `System.main2_pesc`: `thm:main2` under `it:main2_pesc`, `\dim_H X = min{2, dimaff(X)}`, with
  `t = s` if `s < 2` and `t → 2` otherwise; with the statements `ShannonMcMillanBreimanStatement`,
  `MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement` and `FraserJordanJurgaDecomposition`,
  which the library proves, and Rapaport's theorem, which the library proves as well.
* `System.main2_pesc_of_library`: the same with the library theorems plugged in, with no
  literature hypothesis.
-/
public import BoxLike.AffinityMain
public import BoxLike.EquilibriumExistence
public import BoxLike.EquilibriumGibbs
public import BoxLike.FalconerBound
public import BoxLike.FraserJordanJurga.Main
public import BoxLike.General
public import BoxLike.LiteratureRapaport
public import BoxLike.Rapaport.Core
public import BoxLike.MainTwoProse.AxisSeparationSubsystem
public import BoxLike.MainTwoProse.HomogeneousAffinity
public import BoxLike.MainTwoProse.TypicalWordsSMB
public import BoxLike.MorrisShmerkin
public import BoxLike.ShannonMcMillanBreiman

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set

universe u

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)

/-! ### The Lyapunov dimension of a `t`-equilibrium state -/

variable {S} in
/-- `\dim_L(𝖠, μ_t) ≥ t` for a `t`-equilibrium state `μ_t` with `0 ≤ t ≤ dimaff(𝖠)` (proof of
`thm:main2`): "By `eq:eq_state_def` and the monotonicity of the pressure,
`h + Λ(𝖠, μ_t, t) = P(𝖠, t) ≥ P(𝖠, s) = 0`. Hence `\dim_L(𝖠, μ_t) ≥ t`, with equality when
`t = s`"; the energy `Λ(𝖠, μ_t, ·)` is decreasing. -/
theorem IsEquilibriumState.le_lyapDim [Nonempty ι] {t : ℝ} (ht0 : 0 ≤ t) (hts : t ≤ S.dimaff)
    {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState t μ) :
    t ≤ lyapDim (entropy μ) (S.lyapunov₁ μ) (S.lyapunov₂ μ) := by
  refine le_lyapDim_of_add_energy_nonneg (S.lyapunov₂_le_lyapunov₁ hinv) (S.lyapunov₁_neg hinv)
    (entropy_nonneg hinv) ?_
  rw [← heq.pressure_eq hinv ht0]
  have := S.strictAntiOn_pressure.antitoneOn ht0 S.dimaff_nonneg hts
  rwa [S.pressure_dimaff] at this

/-! ### The subsystem of one family -/

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- `\dim_H X_n = min{2, dimaff(X_n)}` for the subsystem of distinct words of a common length
`n > 0` with the common planar matrix `diag(a, b)`, `|b| < |a|` (proof of `thm:main2`, case
`it:main2_pesc`): the subsystem is homogeneous diagonal, hence without rotations and proximal,
the systems it induces on both coordinate axes are exponentially separated
(`subsystem_axisExpSeparation`), so `thm:rapaport` gives `\dim_H X_n = min{2, dimaff(X_n)}`;
and `dimaff(X_n)` is the right-hand side of `eq:diml_min2` with entropy `log #W_n` and
Lyapunov exponents `log |a|`, `log |b|`, since the pressure of the homogeneous subsystem at
`u ≥ 0` is `log #W_n + log φ^u(diag(a, b))` (`IsHomDiag.dimaff_eq`).
`thm:rapaport` is `Rapaport.rapaportDiagonalDimension_holds`. -/
theorem dimH_subsystem_attractor_eq [Nonempty ι]
    (hsep : S.ProjExpSeparation) {κ : Type u} [Fintype κ] [Nonempty κ] {w : κ → List ι}
    {hw : ∀ k, w k ≠ []} {n : ℕ} (hn : 0 < n) (hlen : ∀ k, (w k).length = n)
    (hinj : Function.Injective w) {a b : ℝ} (hmat : ∀ k, S.matWord (w k) = boxMat 0 a b)
    (hab : |b| < |a|) :
    dimH (S.subsystem w hw).attractor =
      ENNReal.ofReal
        (min 2 (lyapDim (Real.log (Fintype.card κ)) (Real.log |a|) (Real.log |b|))) := by
  have hdiagW : ∀ k, S.oWord (w k) = 0 ∧ S.gDeriv (S.codeWord 0 (w k)) = a ∧
      S.gDeriv (S.codeWord 1 (w k)) = b := fun k =>
    (S.matWord_eq_boxMat_zero_iff _ _ _).1 (hmat k)
  -- the subsystem is homogeneous diagonal, hence proximal
  have hT : (S.subsystem w hw).IsHomDiag a b :=
    ⟨fun k => (hdiagW k).1, fun k => (hdiagW k).2.1, fun k => (hdiagW k).2.2⟩
  -- the systems it induces on both axes are exponentially separated
  have hax : ∀ c, (S.subsystem w hw).AxisExpSeparation c := fun c =>
    S.subsystem_axisExpSeparation hsep (fun k => (hdiagW k).1) hn hlen hinj c
  -- `thm:rapaport` and the affinity dimension of the homogeneous subsystem
  rw [Rapaport.rapaportDiagonalDimension_holds (S.subsystem w hw) hT.o_eq (hT.proximal hab)
    (hax 0) (hax 1), hT.dimaff_eq hab.le]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- `\dim_H X ≥ \dim_H X_n = min{2, dimaff(X_n)}` for one family `W` of diagonal planar words of
length `n` with the common matrix `diag(a, b)`, `|b| < |a|`, where `dimaff(X_n)` is the
right-hand side of `eq:diml_min2` for `log #W`, `log |a|`, `log |b|` (proof of `thm:main2`, case
`it:main2_pesc`): `X_n ⊆ X`. -/
theorem min_lyapDim_le_dimH_attractor_of_family [Nonempty ι] (hsep : S.ProjExpSeparation)
    {W : Finset (List ι)} (hW : W.Nonempty) {n : ℕ} (hn : 0 < n) {a b : ℝ}
    (hWn : ∀ w ∈ W, w.length = n ∧ S.matWord w = boxMat 0 a b) (hab : |b| < |a|) :
    ENNReal.ofReal (min 2 (lyapDim (Real.log W.card) (Real.log |a|) (Real.log |b|))) ≤
      dimH S.attractor := by
  classical
  have : Nonempty W := hW.to_subtype
  have hlen : ∀ w : W, (w : List ι).length = n := fun w => (hWn w w.2).1
  have hwne : ∀ w : W, (w : List ι) ≠ [] := fun w h => by
    have := hlen w
    rw [h] at this
    simp at this
    omega
  have hdim := S.dimH_subsystem_attractor_eq hsep (w := fun w : W => (w : List ι))
    (hw := hwne) hn hlen Subtype.val_injective (fun w => (hWn w w.2).2) hab
  rw [Fintype.card_coe] at hdim
  rw [← hdim]
  exact dimH_mono S.subsystem_attractor_subset

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- A corollary of `min_lyapDim_le_dimH_attractor_of_family`: `\dim_H X ≥ u` for `0 ≤ u ≤ 2`
when the pressure `log #W_n + Λ(log |a_n|, log |b_n|, u)` of the homogeneous diagonal subsystem
of the family `W` is non-negative at `u`, so that `dimaff(X_n) ≥ u`
(`le_lyapDim_of_add_energy_nonneg`). -/
theorem le_dimH_attractor_of_family_pesc [Nonempty ι]
    (hsep : S.ProjExpSeparation) {W : Finset (List ι)} (hW : W.Nonempty) {n : ℕ} (hn : 0 < n)
    {a b : ℝ} (hWn : ∀ w ∈ W, w.length = n ∧ S.matWord w = boxMat 0 a b) (hab : |b| < |a|)
    {u : ℝ} (hu0 : 0 ≤ u) (hu2 : u ≤ 2)
    (hpos : 0 ≤ Real.log W.card + energy (Real.log |a|) (Real.log |b|) u) :
    ENNReal.ofReal u ≤ dimH S.attractor := by
  -- `0 < |b| < |a| < 1`, from any word of the family
  obtain ⟨w, hw⟩ := id hW
  obtain ⟨-, hwa, hwb⟩ := (S.matWord_eq_boxMat_zero_iff _ _ _).1 (hWn w hw).2
  have hwne : S.codeWord 0 w ≠ [] := fun h => by
    have := congrArg List.length h
    rw [length_codeWord, (hWn w hw).1] at this
    simp at this
    omega
  have ha1 : |a| < 1 := hwa ▸ S.abs_gDeriv_lt_one hwne
  have ha0 : a ≠ 0 := hwa ▸ S.gDeriv_ne_zero _
  have hb0 : b ≠ 0 := hwb ▸ S.gDeriv_ne_zero _
  have hl1 : Real.log |a| < 0 := Real.log_neg (abs_pos.2 ha0) ha1
  have hl : Real.log |b| ≤ Real.log |a| := Real.log_le_log (abs_pos.2 hb0) hab.le
  have hh : 0 ≤ Real.log W.card := Real.log_nonneg (Nat.one_le_cast.2 hW.card_pos)
  have hu : u ≤ min 2 (lyapDim (Real.log W.card) (Real.log |a|) (Real.log |b|)) :=
    le_min hu2 (le_lyapDim_of_add_energy_nonneg hl hl1 hh hpos)
  exact ((ENNReal.ofReal_le_ofReal_iff (hu0.trans hu)).2 hu).trans
    (S.min_lyapDim_le_dimH_attractor_of_family hsep hW hn hWn hab)

/-! ### The lower bound -/

variable [Nonempty ι]

/-- `thm:main2`, case `it:main2_pesc`, the lower bound `\dim_H X ≥ t` for a tuple containing a
proximal diagonal generator and `0 < t < 2` with `t ≤ dimaff(X)`, along the prose. The
`t`-equilibrium state `μ_t` exists; the typical families `W_n` of `exists_typical_words_prose`
for `μ_t` have `log #W_n / n → h_0(μ_t)`, `log |a_n| / n → λ_1(𝖠, μ_t)` and
`log |b_n| / n → λ_2(𝖠, μ_t)` (`eq:diagonal-subsystem-limits`);
finitely many lengths are discarded so that `|b_n| < |a_n|`, since `λ_2 < λ_1`; for the
remaining lengths `\dim_H X ≥ \dim_H X_n = min{2, dimaff(X_n)}` with `dimaff(X_n)` the
right-hand side of `eq:diml_min2` for `log #W_n`, `log |a_n|`, `log |b_n|`
(`min_lyapDim_le_dimH_attractor_of_family`), which tends to `\dim_L(𝖠, μ_t)`
(`lyapDim_div`, `tendsto_lyapDim`); so `\dim_H X ≥ min{2, \dim_L(𝖠, μ_t)} ≥ min{2, t} = t`
(`IsEquilibriumState.le_lyapDim`).
Depends on: `ShannonMcMillanBreimanStatement`,
`MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`. -/
theorem main2_pesc_normalised (hsmb : ShannonMcMillanBreimanStatement.{u})
    (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u})
    (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal) (hsep : S.ProjExpSeparation)
    {t : ℝ} (ht0 : 0 < t) (ht2 : t < 2) (hts : t ≤ S.dimaff) :
    ENNReal.ofReal t ≤ dimH S.attractor := by
  -- the `t`-equilibrium state `μ_t`
  obtain ⟨μ, hprob, hinv, heq⟩ := S.exists_isEquilibriumState ht0.le
  have hl := hms S hrot hdiag ht0 ht2 μ hinv heq
  have hl1 := S.lyapunov₁_neg hinv
  have hl2 : S.lyapunov₂ μ < 0 := hl.trans hl1
  -- `\dim_L(𝖠, μ_t) ≥ t`, and `h_0(μ_t) > 0`
  have hL : t ≤ lyapDim (entropy μ) (S.lyapunov₁ μ) (S.lyapunov₂ μ) :=
    heq.le_lyapDim ht0.le hts hinv
  have hh : 0 < entropy μ := by
    have hPt : 0 ≤ entropy μ + energy (S.lyapunov₁ μ) (S.lyapunov₂ μ) t := by
      rw [← heq.pressure_eq hinv ht0.le]
      have := S.strictAntiOn_pressure.antitoneOn ht0.le S.dimaff_nonneg hts
      rwa [S.pressure_dimaff] at this
    have h0 : energy (S.lyapunov₁ μ) (S.lyapunov₂ μ) 0 = 0 := by simp [energy]
    have := energy_strictAnti hl1 hl2 ht0
    linarith
  -- the typical families `W_n` for `μ_t`
  obtain ⟨n, W, a, b, -, hnpos, hWne, hWn, hH, ha, hb⟩ :=
    S.exists_typical_words_prose hsmb hfk hfjj hrot hdiag ht0 ht2 μ hinv heq
  have hn0 : ∀ m, (0 : ℝ) < n m := fun m => by exact_mod_cast hnpos m
  -- the entries `a_n`, `b_n` are non-zero
  have hab0 : ∀ m, a m ≠ 0 ∧ b m ≠ 0 := fun m => by
    obtain ⟨w, hw⟩ := hWne m
    obtain ⟨-, hwa, hwb⟩ := (S.matWord_eq_boxMat_zero_iff _ _ _).1 (hWn m w hw).2
    exact ⟨hwa ▸ S.gDeriv_ne_zero _, hwb ▸ S.gDeriv_ne_zero _⟩
  -- finitely many lengths are discarded so that `|b_n| < |a_n|`, since `λ_2 < λ_1`
  have hlt : ∀ᶠ m in atTop, |b m| < |a m| := by
    filter_upwards [hb.eventually_lt ha hl] with m hm
    rw [div_lt_div_iff_of_pos_right (hn0 m)] at hm
    exact (Real.log_lt_log_iff (abs_pos.2 (hab0 m).2) (abs_pos.2 (hab0 m).1)).1 hm
  -- `\dim_H X ≥ \dim_H X_n = min{2, dimaff(X_n)}` for the remaining lengths
  have hle : ∀ᶠ m in atTop, ENNReal.ofReal
      (min 2 (lyapDim (Real.log (W m).card) (Real.log |a m|) (Real.log |b m|))) ≤
        dimH S.attractor := by
    filter_upwards [hlt] with m hm
    exact S.min_lyapDim_le_dimH_attractor_of_family hsep (hWne m) (hnpos m) (hWn m) hm
  -- `dimaff(X_n) → \dim_L(𝖠, μ_t)` by `eq:diml_min2` and the three limits
  -- `eq:diagonal-subsystem-limits`
  have hlim : Tendsto
      (fun m => lyapDim (Real.log (W m).card) (Real.log |a m|) (Real.log |b m|)) atTop
      (𝓝 (lyapDim (entropy μ) (S.lyapunov₁ μ) (S.lyapunov₂ μ))) :=
    (tendsto_lyapDim hH ha hb hl hl1 hh).congr fun m => lyapDim_div _ _ _ (hn0 m)
  -- `\dim_H X ≥ lim_n \dim_H X_n = min{2, \dim_L(𝖠, μ_t)} ≥ t`
  have hlim' : Tendsto (fun m => ENNReal.ofReal
      (min 2 (lyapDim (Real.log (W m).card) (Real.log |a m|) (Real.log |b m|)))) atTop
      (𝓝 (ENNReal.ofReal (min 2 (lyapDim (entropy μ) (S.lyapunov₁ μ) (S.lyapunov₂ μ))))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.min hlim)
  calc ENNReal.ofReal t = ENNReal.ofReal (min 2 t) := by rw [min_eq_right ht2.le]
    _ ≤ ENNReal.ofReal (min 2 (lyapDim (entropy μ) (S.lyapunov₁ μ) (S.lyapunov₂ μ))) :=
        ENNReal.ofReal_le_ofReal (min_le_min le_rfl hL)
    _ ≤ dimH S.attractor := le_of_tendsto hlim' hle

/-- `thm:main2`, case `it:main2_pesc`, the lower bound `\dim_H X ≥ t` for every proximal tuple
and `0 < t < 2` with `t ≤ dimaff(X)`: the reduction to a proximal diagonal generator through
`thm:two-block-normalisation`, the projective exponential separation condition passing to the
second iterate, which has the same attractor and the same affinity dimension.
Depends on: `ShannonMcMillanBreimanStatement`,
`MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`. -/
theorem le_dimH_attractor_pesc (hsmb : ShannonMcMillanBreimanStatement.{u})
    (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal) (hsep : S.ProjExpSeparation) {t : ℝ}
    (ht0 : 0 < t) (ht2 : t < 2) (hts : t ≤ S.dimaff) :
    ENNReal.ofReal t ≤ dimH S.attractor := by
  rcases hprox.hasProximalDiagonal_or_sq with h | h
  · exact S.main2_pesc_normalised hsmb hms hfk hfjj hrot h hsep ht0 ht2 hts
  · have hd : S.sq.dimaff = S.dimaff :=
      S.sq.dimaff_eq S.dimaff_nonneg
        (by rw [S.pressure_sq S.dimaff_nonneg, S.pressure_dimaff, mul_zero])
    have key := S.sq.main2_pesc_normalised hsmb hms hfk hfjj (S.sq_withRotations hrot) h
      (ProjExpSeparation.sq S hsep) ht0 ht2 (by rw [hd]; exact hts)
    rwa [S.attractor_sq] at key

/-! ### The theorem -/

/-- `thm:main2` under the projective exponential separation condition `it:main2_pesc`: for a
proximal box-like self-affine set with rotations, `\dim_H X = min{2, dimaff(X)}`. The lower
bound `\dim_H X ≥ t` holds for every `0 < t < 2` with `t ≤ dimaff(X)`; "since `t = s`, or `t` is
arbitrarily close to `2`", along `t_k = 2 - 1/(k + 1)`, this gives
`\dim_H X ≥ min{2, dimaff(X)}`; the opposite inequality is `eq:hausdorff_affinity_upper_bound`.
Depends on: `ShannonMcMillanBreimanStatement`,
`MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`. -/
theorem main2_pesc (hsmb : ShannonMcMillanBreimanStatement.{u}) (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal) (hsep : S.ProjExpSeparation) :
    dimH S.attractor = ENNReal.ofReal (min 2 S.dimaff) := by
  have := S.nontrivial_of_withRotations hrot
  have hs0 := S.dimaff_pos
  refine le_antisymm S.dimH_attractor_le ?_
  rcases lt_or_ge S.dimaff 2 with h2 | h2
  · -- `t = s`
    rw [min_eq_right h2.le]
    exact S.le_dimH_attractor_pesc hsmb hms hfk hfjj hrot hprox hsep hs0 h2 le_rfl
  · -- `t → 2` along `t_k = 2 - 1/(k + 1)`
    rw [min_eq_left h2]
    have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal (2 - 1 / ((k : ℝ) + 1))) atTop
        (𝓝 (ENNReal.ofReal 2)) := by
      have h := (tendsto_const_nhds (x := (2 : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
      rw [sub_zero] at h
      exact (ENNReal.continuous_ofReal.tendsto _).comp h
    refine le_of_tendsto hlim (Eventually.of_forall fun k => ?_)
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hk1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    exact S.le_dimH_attractor_pesc hsmb hms hfk hfjj hrot hprox hsep (by linarith)
      (by linarith) (by linarith)

/-- `thm:main2` under `it:main2_pesc` with the library theorems `shannonMcMillanBreiman`,
`morrisShmerkinLyapunov_holds`, `equilibriumGibbs` and `fraserJordanJurgaDecomposition_holds`
plugged in, with no literature hypothesis. -/
theorem main2_pesc_of_library (hrot : S.WithRotations)
    (hprox : S.Proximal) (hsep : S.ProjExpSeparation) :
    dimH S.attractor = ENNReal.ofReal (min 2 S.dimaff) :=
  S.main2_pesc shannonMcMillanBreiman morrisShmerkinLyapunov_holds equilibriumGibbs
    fraserJordanJurgaDecomposition_holds hrot hprox hsep

end System

end BoxLike
