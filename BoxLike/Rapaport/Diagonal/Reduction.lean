module

/-
Rapaport's Theorem 1.3 in the plane (arXiv:2309.03985, Section 7, lines 1930 to 2161 of
`rapaport.tex`), from the homogeneous case with arbitrary positive weights
(`Rapaport/Diagonal/Weighted.lean`), assuming the core theorem `HomogeneousCore`
for a diagonal system `S` with `|a_i| ≠ |b_i|`
for some `i` and exponentially separated induced systems on both axes,
`dim_H X = min{2, dimaff(X)}`.

The proof follows lines 2010 to 2159 of the source. The Käenmäki weights `p` at `s = dimaff`
(`kaenmaki_weights`) have `dim_L(H(p), λ_a, λ_b) = s`, so `H(p) + Λ(λ_a, λ_b, t) > 0` for
every `t < s`. In the `n`-th iterate the words are grouped by their linear part; a group `r` of
large entropy and typical exponents exists (`eventually_exists_good_group`), its words form a
homogeneous diagonal subsystem whose induced systems are exponentially separated (Lemma 7.4),
and the weighted homogeneous theorem bounds `dim_H X` from below by `min{2, dim_L}` of the group,
which is at least `t` by the linearity of the energy (Lemma 7.3 in the form needed). Rapaport
needs in addition `|r_1| ≠ |r_2|` for the group, through the central limit theorem (Lemma 7.2).
Here this is automatic when `λ_b < λ_a` strictly, since the exponents of the group are within
`n ε` of `n λ_a` and `n λ_b`; when `λ_a = λ_b` the Käenmäki weights are first perturbed to
weights with `λ_b < λ_a` and still `H + Λ(λ_a, λ_b, t) > 0` (`exists_perturbed_weights`), which
replaces Lemma 7.2. The case where the other coordinate dominates is reduced to this one by the
coordinate swap `coordSwap`, Rapaport's permutation of coordinates at line 2032.

* `energy_le_energy`, `energy_sub_sub`, `pos_add_energy_of_lt_lyapDim`: the energy `Λ` is
  non-decreasing in the exponents and shifts by `-t d` when both exponents shift by `-d`, and
  `h + Λ(l_1, l_2, t) > 0` for `t < dim_L(h, l_1, l_2)`.
* `coordSwap`, `coordSwap_o`, `coordSwap_a`, `coordSwap_b`, `coordSwap_v`, `coord_swap`,
  `coordSwap_phi`, `coordSwap_attractor`, `isometry_prod_swap`,
  `dimH_coordSwap_attractor`, `coordSwap_ratio`, `coordSwap_trans`, `coordSwap_g`,
  `coordSwap_gWord_axisWord`, `coordSwap_gDeriv_axisWord`, `coordSwap_axisGap`,
  `coordSwap_axisExpSeparation`, `coordSwap_dimaff`: the system with the two coordinates
  exchanged, its attractor `swap(X)`, its gaps and its affinity dimension (line 2032).
* `oWord_eq_zero_of_diag`, `axisGap_mul_le_axisGap_subsystem`,
  `subsystem_axisExpSeparation_of_axis`: Lemma 7.4 (lines 1987 to 2008) for the induced systems
  of a subsystem of distinct words of a common length.
* `gDeriv_codeWord_zero_ofFn`, `gDeriv_codeWord_one_ofFn`, `ofReal_min_lyapDim_le_dimH`: the
  subsystem of one group `W_r` with the conditional weights `q_r`, and the bound
  `dim_H X ≥ min{2, dim_L(H(q_r), log |r_1|, log |r_2|)}` for `|r_2| < |r_1|` (lines 2149 to
  2159).
* `ofReal_le_dimH_of_weights`: `dim_H X ≥ t` from weights `p` with `λ_b < λ_a`,
  `H(p) + Λ(λ_a, λ_b, t) > 0` and `0 ≤ t ≤ 2` (lines 2095 to 2159).
* `exists_perturbed_weights`, `exists_good_weights`: such weights exist for `S` or for
  `coordSwap S` whenever `t < dimaff` (lines 2028 to 2077, with the perturbation replacing
  Lemma 7.2).
* `ofReal_le_dimH_attractor`, `dimH_attractor_eq_of_core`, `rapaportDiagonalDimension_of_core`:
  the theorem.
-/
public import BoxLike.Rapaport.Diagonal.Iterate
public import BoxLike.Rapaport.Diagonal.Pressure
public import BoxLike.Rapaport.Diagonal.Weighted
public import BoxLike.AxisSeparation
public import BoxLike.FalconerBound
public import BoxLike.LiteratureRapaport
public import BoxLike.MainTwoProse.AxisSeparationSubsystem
public import BoxLike.MainTwoProse.HomogeneousAffinity
public import BoxLike.Subsystem

@[expose] public section

namespace BoxLike.Rapaport.Diagonal

open Finset Filter Topology

universe u

/-! ### The energy -/

/-- The energy `Λ(l_1, l_2, t)` of `eq:energy_def` is non-decreasing in both exponents for
`t ≥ 0`. -/
theorem energy_le_energy {l1 l2 m1 m2 t : ℝ} (ht : 0 ≤ t) (h1 : m1 ≤ l1) (h2 : m2 ≤ l2) :
    energy m1 m2 t ≤ energy l1 l2 t := by
  unfold energy
  split_ifs with h h'
  · exact mul_le_mul_of_nonneg_left h1 ht
  · nlinarith [mul_le_mul_of_nonneg_left h2 (show 0 ≤ t - 1 by linarith [not_le.1 h])]
  · nlinarith [mul_le_mul_of_nonneg_left (add_le_add h1 h2) (show 0 ≤ t / 2 by linarith)]

/-- Shifting both exponents by `-d` shifts the energy by `-t d`. -/
theorem energy_sub_sub (l1 l2 d t : ℝ) : energy (l1 - d) (l2 - d) t = energy l1 l2 t - t * d := by
  unfold energy
  split_ifs <;> ring

/-- `h + Λ(l_1, l_2, t) > 0` for `t < dim_L(h, l_1, l_2)`, when `l_2 ≤ l_1 < 0` and `h ≥ 0`: the
energy is strictly decreasing in `t` and vanishes at `dim_L` after adding `h`. -/
theorem pos_add_energy_of_lt_lyapDim {h l1 l2 t : ℝ} (hl : l2 ≤ l1) (hl1 : l1 < 0) (hh : 0 ≤ h)
    (ht : t < lyapDim h l1 l2) : 0 < h + energy l1 l2 t := by
  have h0 := add_energy_lyapDim hl hl1 hh
  have := energy_strictAnti hl1 (hl.trans_lt hl1) ht
  linarith

/-! ### The coordinate swap -/

section Swap

variable {ι : Type*} (S : System ι)

/-- The system `S` with the two coordinates of the plane exchanged: `φ'_i(y, x) = swap φ_i(x, y)`,
with the entries `a_i` and `b_i` exchanged. Rapaport's permutation of the coordinates of the
ambient space at line 2032 of the source. -/
def coordSwap : System ι where
  o := S.o
  a := S.b
  b := S.a
  v i := (S.v i).swap
  a_ne_zero := S.b_ne_zero
  b_ne_zero := S.a_ne_zero
  abs_a_lt_one := S.abs_b_lt_one
  abs_b_lt_one := S.abs_a_lt_one

/-- The orientations of `coordSwap S` are those of `S`. -/
@[simp] theorem coordSwap_o : (coordSwap S).o = S.o := rfl

/-- The first-row entries of `coordSwap S` are the entries `b` of `S`. -/
@[simp] theorem coordSwap_a : (coordSwap S).a = S.b := rfl

/-- The second-row entries of `coordSwap S` are the entries `a` of `S`. -/
@[simp] theorem coordSwap_b : (coordSwap S).b = S.a := rfl

/-- The translations of `coordSwap S` are the swapped translations of `S`. -/
@[simp] theorem coordSwap_v (i : ι) : (coordSwap S).v i = (S.v i).swap := rfl

/-- `proj_c (swap z) = proj_{c + 1} z`. -/
theorem coord_swap (c : ZMod 2) (z : ℝ × ℝ) : System.coord c z.swap = System.coord (c + 1) z := by
  rcases zmod_two_cases c with rfl | rfl
  · rfl
  · rw [show (1 : ZMod 2) + 1 = 0 from by decide]
    rfl

/-- `φ'_i ∘ swap = swap ∘ φ_i`. -/
theorem coordSwap_phi (i : ι) (z : ℝ × ℝ) : (coordSwap S).phi i z.swap = (S.phi i z).swap := by
  have h2 : S.o i + 1 + 1 = S.o i := by
    rw [add_assoc, show (1 : ZMod 2) + 1 = 0 from by decide, add_zero]
  simp only [System.phi, coordSwap, coord_swap, h2, Prod.swap_prod_mk, Prod.fst_swap,
    Prod.snd_swap]

/-- The attractor of `coordSwap S` is `swap(X)`: by Hutchinson's uniqueness, `swap(X)` is
compact, non-empty and invariant under the maps of `coordSwap S`. -/
theorem coordSwap_attractor [Finite ι] [Nonempty ι] :
    (coordSwap S).attractor = Prod.swap '' S.attractor := by
  refine ((coordSwap S).eq_attractor (S.isCompact_attractor.image continuous_swap)
    (S.attractor_nonempty.image _) ?_).symm
  conv_lhs => rw [S.attractor_eq_iUnion]
  rw [Set.image_iUnion]
  refine Set.iUnion_congr fun i => ?_
  rw [Set.image_image, Set.image_image]
  exact Set.image_congr fun z _ => (coordSwap_phi S i z).symm

/-- `swap` is an isometry of the plane with the supremum metric. -/
theorem isometry_prod_swap : Isometry (Prod.swap : ℝ × ℝ → ℝ × ℝ) :=
  Isometry.of_dist_eq fun x y => by
    rw [Prod.dist_eq, Prod.dist_eq, Prod.fst_swap, Prod.snd_swap, Prod.fst_swap, Prod.snd_swap,
      max_comm]

/-- The coordinate swap preserves the Hausdorff dimension of the attractor. -/
theorem dimH_coordSwap_attractor [Finite ι] [Nonempty ι] :
    dimH (coordSwap S).attractor = dimH S.attractor := by
  rw [coordSwap_attractor, isometry_prod_swap.dimH_image]

/-- The ratio of the symbol `(i, c)` of `coordSwap S` is that of `(i, c + 1)` of `S`. -/
theorem coordSwap_ratio (i : ι) (c : ZMod 2) :
    (coordSwap S).ratio (i, c) = S.ratio (i, c + 1) := by
  rcases zmod_two_cases c with rfl | rfl
  · rfl
  · rw [show (1 : ZMod 2) + 1 = 0 from by decide]
    rfl

/-- The translation of the symbol `(i, c)` of `coordSwap S` is that of `(i, c + 1)` of `S`. -/
theorem coordSwap_trans (i : ι) (c : ZMod 2) :
    (coordSwap S).trans (i, c) = S.trans (i, c + 1) :=
  coord_swap c (S.v i)

/-- The coordinate map of the symbol `(i, c)` of `coordSwap S` is that of `(i, c + 1)` of
`S`. -/
theorem coordSwap_g (i : ι) (c : ZMod 2) : (coordSwap S).g (i, c) = S.g (i, c + 1) := by
  funext t
  simp only [System.g, coordSwap_ratio, coordSwap_trans]

/-- The map induced on the axis `c` by a word of `coordSwap S` is the map induced on the axis
`c + 1` by the same word of `S`. -/
theorem coordSwap_gWord_axisWord (c : ZMod 2) (u : List ι) :
    (coordSwap S).gWord (axisWord c u) = S.gWord (axisWord (c + 1) u) := by
  induction u with
  | nil => rfl
  | cons i u ih => rw [axisWord_cons, axisWord_cons, System.gWord_cons, System.gWord_cons, ih,
      coordSwap_g]

/-- The derivative along the axis `c` of a word of `coordSwap S` is the derivative along the
axis `c + 1` of the same word of `S`. -/
theorem coordSwap_gDeriv_axisWord (c : ZMod 2) (u : List ι) :
    (coordSwap S).gDeriv (axisWord c u) = S.gDeriv (axisWord (c + 1) u) := by
  induction u with
  | nil => rfl
  | cons i u ih => rw [axisWord_cons, axisWord_cons, System.gDeriv_cons, System.gDeriv_cons, ih,
      coordSwap_ratio]

/-- The gaps of `coordSwap S` on the axis `c` are those of `S` on the axis `c + 1`. -/
theorem coordSwap_axisGap (c : ZMod 2) (n : ℕ) :
    (coordSwap S).axisGap c n = S.axisGap (c + 1) n := by
  simp only [System.axisGap, coordSwap_gWord_axisWord, coordSwap_gDeriv_axisWord]

/-- The system that `coordSwap S` induces on the axis `c` is exponentially separated exactly
when the system that `S` induces on the axis `c + 1` is. -/
theorem coordSwap_axisExpSeparation (c : ZMod 2) :
    (coordSwap S).AxisExpSeparation c ↔ S.AxisExpSeparation (c + 1) := by
  simp only [System.AxisExpSeparation, coordSwap_axisGap]

/-- The coordinate swap preserves the affinity dimension of a diagonal system: the two sums of
(7.1) are exchanged. -/
theorem coordSwap_dimaff [Fintype ι] [Nonempty ι] (hdiag : ∀ i, S.o i = 0) :
    (coordSwap S).dimaff = S.dimaff := by
  refine dimaff_eq_of_max_eq_one (coordSwap S) hdiag S.dimaff_nonneg ?_
  rw [show Φa (coordSwap S) = Φb S from rfl, show Φb (coordSwap S) = Φa S from rfl, max_comm]
  exact dimaff_diag S hdiag

end Swap

/-! ### Separation of iterates and subsystems: Lemma 7.4 -/

section Separation

variable {ι κ : Type*} (S : System ι) {w : κ → List ι} {hw : ∀ k, w k ≠ []}

/-- Every word of a system without rotations has a diagonal product. -/
theorem oWord_eq_zero_of_diag (hdiag : ∀ i, S.o i = 0) (u : List ι) : S.oWord u = 0 := by
  induction u with
  | nil => rfl
  | cons i u ih => rw [System.oWord_cons, hdiag i, ih, add_zero]

/-- `Δ_{nk} ≤ Δ'_k` for the systems that `S` and a subsystem of distinct words of a common
length `n > 0` induce on the axis `c`, for `S` without rotations (proof of Lemma 7.4, lines 1995
to 2008 of the source): a composition of `k` maps of the subsystem acts on the axis by `g_𝐢` for
the concatenated word `𝐢` of length `nk`, and distinct sequences give distinct words. -/
theorem axisGap_mul_le_axisGap_subsystem (hdiag : ∀ i, S.o i = 0) {n : ℕ} (hn : 0 < n)
    (hlen : ∀ k, (w k).length = n) (hinj : Function.Injective w) (c : ZMod 2) (k : ℕ) :
    S.axisGap c (n * k) ≤ (S.subsystem w hw).axisGap c k := by
  have ho : ∀ k, (S.subsystem w hw).o k = 0 := fun k => by
    rw [System.subsystem_o]
    exact oWord_eq_zero_of_diag S hdiag _
  refine le_iInf fun u => le_iInf fun u' => le_iInf fun hu => le_iInf fun hu' =>
    le_iInf fun hne => le_iInf fun hd => ?_
  rw [← (S.subsystem w hw).codeWord_eq_axisWord ho, ← (S.subsystem w hw).codeWord_eq_axisWord ho]
    at hd ⊢
  rw [System.subsystem_codeWord_gWord, System.subsystem_codeWord_gWord,
    S.codeWord_eq_axisWord hdiag, S.codeWord_eq_axisWord hdiag]
  rw [System.subsystem_codeWord_gDeriv, System.subsystem_codeWord_gDeriv,
    S.codeWord_eq_axisWord hdiag, S.codeWord_eq_axisWord hdiag] at hd
  refine S.axisGap_le ?_ ?_ ?_ hd
  · rw [length_flatWords hlen, hu]
  · rw [length_flatWords hlen, hu']
  · exact fun h => hne (flatWords_injective hn hlen hinj h)

/-- Lemma 7.4 (lines 1987 to 2008 of the source) for a subsystem of distinct words of a common
length `n > 0` of a system without rotations: if the system induced by `S` on the axis `c` is
exponentially separated with `Δ_m ≥ r^m`, `0 < r ≤ 1`, for infinitely many `m`, then so is the
system induced by the subsystem, with the constant `r^{2n}`: at `k = ⌊m/n⌋`,
`Δ'_k ≥ Δ_{nk} ≥ Δ_m ≥ r^m ≥ (r^{2n})^k`. -/
theorem subsystem_axisExpSeparation_of_axis [Nonempty ι] (hdiag : ∀ i, S.o i = 0) {n : ℕ}
    (hn : 0 < n) (hlen : ∀ k, (w k).length = n) (hinj : Function.Injective w) {c : ZMod 2}
    (hsep : S.AxisExpSeparation c) : (S.subsystem w hw).AxisExpSeparation c := by
  obtain ⟨c₀, hc₀, hfreq⟩ := (S.axisExpSeparation_iff_frequently c).1 hsep
  set r : ℝ := min c₀ 1 with hr_def
  have hr : 0 < r := lt_min hc₀ one_pos
  have hr1 : r ≤ 1 := min_le_right _ _
  have hfreq' : ∃ᶠ m : ℕ in atTop, ENNReal.ofReal (r ^ m) ≤ S.axisGap c m :=
    hfreq.mono fun m hm =>
      (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hr.le (min_le_left _ _) m)).trans hm
  refine (S.subsystem w hw).axisExpSeparation_of_frequently (pow_pos hr (2 * n))
    (frequently_atTop.2 fun N => ?_)
  obtain ⟨m, hmN, hm⟩ := frequently_atTop.1 hfreq' (n * (N + 1))
  have hNm : N * n ≤ m := by
    rw [mul_comm]
    exact (Nat.mul_le_mul_left n (Nat.le_succ N)).trans hmN
  have hnm : n ≤ m := (Nat.le_mul_of_pos_right n (Nat.succ_pos N)).trans hmN
  refine ⟨m / n, (Nat.le_div_iff_mul_le hn).2 hNm, ?_⟩
  have hk1 : 1 ≤ m / n := (Nat.le_div_iff_mul_le hn).2 (by rwa [one_mul])
  have hkm : n * (m / n) ≤ m := Nat.mul_div_le m n
  have hmk : m ≤ 2 * n * (m / n) := by
    have h1 := Nat.lt_mul_div_succ m hn
    have h2 : n * 1 ≤ n * (m / n) := Nat.mul_le_mul_left n hk1
    nlinarith
  calc ENNReal.ofReal ((r ^ (2 * n)) ^ (m / n))
      = ENNReal.ofReal (r ^ (2 * n * (m / n))) := by rw [← pow_mul]
    _ ≤ ENNReal.ofReal (r ^ m) :=
        ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hr.le hr1 hmk)
    _ ≤ S.axisGap c m := hm
    _ ≤ S.axisGap c (n * (m / n)) := S.axisGap_anti c hkm
    _ ≤ (S.subsystem w hw).axisGap c (m / n) :=
        axisGap_mul_le_axisGap_subsystem S hdiag hn hlen hinj c _

/-- The derivative along the first axis of a word of a system without rotations is the product
of the entries `a`. -/
theorem gDeriv_codeWord_zero_ofFn (hdiag : ∀ i, S.o i = 0) {n : ℕ} (u : Fin n → ι) :
    S.gDeriv (S.codeWord 0 (List.ofFn u)) = ∏ k, S.a (u k) := by
  rw [S.codeWord_eq_axisWord hdiag, S.gDeriv_axisWord_zero, List.map_ofFn, List.prod_ofFn]
  rfl

/-- The derivative along the second axis of a word of a system without rotations is the
product of the entries `b`. -/
theorem gDeriv_codeWord_one_ofFn (hdiag : ∀ i, S.o i = 0) {n : ℕ} (u : Fin n → ι) :
    S.gDeriv (S.codeWord 1 (List.ofFn u)) = ∏ k, S.b (u k) := by
  rw [S.codeWord_eq_axisWord hdiag, S.gDeriv_axisWord_one, List.map_ofFn, List.prod_ofFn]
  rfl

end Separation

/-! ### The subsystem of one group of the `n`-th iterate -/

section Group

variable {ι : Type u} [Fintype ι] [Nonempty ι] (S : System ι)

/-- The lower bound from one group of the `n`-th iterate (lines 2149 to 2159 of the source):
the words `u ∈ ι^n` with the linear part `r = diag(r_1, r_2)` of a word `u₀`, `|r_2| < |r_1|`,
form a homogeneous diagonal subsystem of `S` whose induced systems are exponentially separated
(Lemma 7.4); with the conditional weights `q_r`, the weighted homogeneous theorem
(`Weighted.le_dimH_attractor_weighted_of_library`) gives
`dim_H X ≥ min{2, dim_L(H(q_r), log |r_1|, log |r_2|)}`, since the attractor of the subsystem
lies in `X`.
Depends on: `HomogeneousCore`. -/
theorem ofReal_min_lyapDim_le_dimH (hcore : HomogeneousCore.{u}) (hdiag : ∀ i, S.o i = 0)
    (h0 : S.AxisExpSeparation 0) (h1 : S.AxisExpSeparation 1) {p : ι → ℝ} (hp : ∀ i, 0 < p i)
    {n : ℕ} (hn : 0 < n) (u₀ : Fin n → ι)
    (hxy : |(lin S.a S.b u₀).2| < |(lin S.a S.b u₀).1|) :
    ENNReal.ofReal (min 2 (lyapDim (fibEnt (pw p (n := n)) (lin S.a S.b) (lin S.a S.b u₀))
      (Real.log |(lin S.a S.b u₀).1|) (Real.log |(lin S.a S.b u₀).2|))) ≤ dimH S.attractor := by
  set r := lin S.a S.b u₀ with hr
  let : MeasurableSpace {u : Fin n → ι // lin S.a S.b u = r} := ⊤
  have : MeasurableSingletonClass {u : Fin n → ι // lin S.a S.b u = r} :=
    ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have : Nonempty {u : Fin n → ι // lin S.a S.b u = r} := ⟨⟨u₀, rfl⟩⟩
  let w : {u : Fin n → ι // lin S.a S.b u = r} → List ι := fun u => List.ofFn u.1
  have hlen : ∀ k, (w k).length = n := fun k => List.length_ofFn
  have hw : ∀ k, w k ≠ [] := fun k h => by
    have := hlen k
    rw [h, List.length_nil] at this
    omega
  have hinj : Function.Injective w := fun u v h => Subtype.ext (List.ofFn_injective h)
  have hT : (S.subsystem w hw).IsHomDiag r.1 r.2 :=
    ⟨fun k => oWord_eq_zero_of_diag S hdiag _,
      fun k => by
        change S.gDeriv (S.codeWord 0 (List.ofFn k.1)) = r.1
        rw [gDeriv_codeWord_zero_ofFn S hdiag]
        exact congrArg Prod.fst k.2,
      fun k => by
        change S.gDeriv (S.codeWord 1 (List.ofFn k.1)) = r.2
        rw [gDeriv_codeWord_one_ofFn S hdiag]
        exact congrArg Prod.snd k.2⟩
  have hT0 := subsystem_axisExpSeparation_of_axis S (hw := hw) hdiag hn hlen hinj h0
  have hT1 := subsystem_axisExpSeparation_of_axis S (hw := hw) hdiag hn hlen hinj h1
  let q : {u : Fin n → ι // lin S.a S.b u = r} → ℝ := fun u =>
    pw p u.1 / fibMass (pw p (n := n)) (lin S.a S.b) r
  have hq : ∀ k, 0 < q k := fun k => div_pos (pw_pos hp _) (fibMass_pos (pw_pos hp) _ u₀)
  have hsub : ∀ f : (Fin n → ι) → ℝ,
      ∑ u ∈ univ.filter (fun u => lin S.a S.b u = r), f u =
        ∑ u : {u : Fin n → ι // lin S.a S.b u = r}, f u.1 :=
    fun f => sum_subtype _ (fun u => by simp) f
  have hq1 : ∑ k, q k = 1 := by
    rw [← sum_div_fibMass (pw_pos hp) (lin S.a S.b) u₀,
      hsub (fun u => pw p u / fibMass (pw p (n := n)) (lin S.a S.b) r)]
  have hent : ∑ k, Real.negMulLog (q k) = fibEnt (pw p (n := n)) (lin S.a S.b) r := by
    rw [fibEnt, hsub]
  have key := Weighted.le_dimH_attractor_weighted_of_library hcore hT hxy hq hq1 hT0 hT1
  rw [hent] at key
  exact key.trans (dimH_mono S.subsystem_attractor_subset)

/-- `dim_H X ≥ t` from strictly positive weights `p` with `λ_b < λ_a` and
`H(p) + Λ(λ_a, λ_b, t) > 0`, for `0 ≤ t ≤ 2` (lines 2095 to 2159 of the source). For small
`ε > 0` and large `n` a group `r` of the `n`-th iterate has `H(q_r) ≥ n (H(p) - ε)` and exponents
`log |r_j|` within `n ε` of `n λ_j` (`eventually_exists_good_group`); for `2 ε < λ_a - λ_b` this
forces `|r_2| < |r_1|`, and `H(q_r) + Λ(log |r_1|, log |r_2|, t) ≥ n (H(p) + Λ(λ_a, λ_b, t) -
ε (1 + t)) ≥ 0`, so `t ≤ dim_L(H(q_r), log |r_1|, log |r_2|)`: Lemma 7.3 in the form needed.
Depends on: `HomogeneousCore`. -/
theorem ofReal_le_dimH_of_weights (hcore : HomogeneousCore.{u}) (hdiag : ∀ i, S.o i = 0)
    (h0 : S.AxisExpSeparation 0) (h1 : S.AxisExpSeparation 1) {p : ι → ℝ} (hp : ∀ i, 0 < p i)
    (hp1 : ∑ i, p i = 1)
    (hlt : ∑ i, p i * Real.log |S.b i| < ∑ i, p i * Real.log |S.a i|) {t : ℝ} (ht0 : 0 ≤ t)
    (ht2 : t ≤ 2)
    (hpos : 0 < ∑ i, Real.negMulLog (p i) +
      energy (∑ i, p i * Real.log |S.a i|) (∑ i, p i * Real.log |S.b i|) t) :
    ENNReal.ofReal t ≤ dimH S.attractor := by
  set H := ∑ i, Real.negMulLog (p i) with hH
  set la := ∑ i, p i * Real.log |S.a i| with hla
  set lb := ∑ i, p i * Real.log |S.b i| with hlb
  set ε := min ((H + energy la lb t) / (2 * (1 + t))) ((la - lb) / 4) with hε_def
  have ht1 : 0 < 1 + t := by linarith
  have hε : 0 < ε := lt_min (div_pos hpos (by positivity)) (by linarith)
  have hε1 : ε * (1 + t) < H + energy la lb t := by
    have h := min_le_left ((H + energy la lb t) / (2 * (1 + t))) ((la - lb) / 4)
    rw [← hε_def, le_div_iff₀ (by positivity)] at h
    have e : ε * (2 * (1 + t)) = 2 * (ε * (1 + t)) := by ring
    linarith
  have hε2 : 2 * ε < la - lb := by
    have h := (min_le_right _ _ : ε ≤ (la - lb) / 4)
    linarith
  obtain ⟨n, ⟨u₀, hent, hxa, hyb⟩, hn⟩ :=
    ((eventually_exists_good_group hp hp1 S.a_ne_zero S.b_ne_zero hε).and
      (eventually_gt_atTop 0)).exists
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set x := (lin S.a S.b u₀).1 with hx
  set y := (lin S.a S.b u₀).2 with hy
  have hx0 : x ≠ 0 := show ∏ k, S.a (u₀ k) ≠ 0 from prod_ne_zero_iff.2 fun k _ => S.a_ne_zero _
  have hy0 : y ≠ 0 := show ∏ k, S.b (u₀ k) ≠ 0 from prod_ne_zero_iff.2 fun k _ => S.b_ne_zero _
  obtain ⟨hxa1, -⟩ := abs_lt.1 hxa
  obtain ⟨hyb1, hyb2⟩ := abs_lt.1 hyb
  have hlog : Real.log |y| < Real.log |x| := by
    have := mul_lt_mul_of_pos_left hε2 hn'
    linarith
  have hxy : |y| < |x| := (Real.log_lt_log_iff (abs_pos.2 hy0) (abs_pos.2 hx0)).1 hlog
  have hx1 : Real.log |x| < 0 := by
    rw [hx, log_abs_lin_fst S.a_ne_zero S.b u₀]
    exact sum_neg (fun k _ => Real.log_neg (abs_pos.2 (S.a_ne_zero _)) (S.abs_a_lt_one _))
      ⟨⟨0, hn⟩, mem_univ _⟩
  have hHq := fibEnt_nonneg (pw_pos hp (n := n)) (lin S.a S.b) (lin S.a S.b u₀)
  have hen : energy (n * la) (n * lb) t - t * (n * ε) ≤ energy (Real.log |x|) (Real.log |y|) t := by
    rw [← energy_sub_sub]
    exact energy_le_energy ht0 (by linarith) (by linarith)
  rw [energy_mul] at hen
  have hsum : 0 ≤ fibEnt (pw p (n := n)) (lin S.a S.b) (lin S.a S.b u₀) +
      energy (Real.log |x|) (Real.log |y|) t := by
    have e : n * (H - ε) + (n * energy la lb t - t * (n * ε)) =
        n * (H + energy la lb t - ε * (1 + t)) := by ring
    have := mul_pos hn' (sub_pos.2 hε1)
    linarith
  have hle := le_lyapDim_of_add_energy_nonneg hlog.le hx1 hHq hsum
  exact (ENNReal.ofReal_le_ofReal (le_min ht2 hle)).trans
    (ofReal_min_lyapDim_le_dimH S hcore hdiag h0 h1 hp hn u₀ hxy)

end Group

/-! ### The weights -/

/-- A perturbation of strictly positive weights (replacing Lemma 7.2, lines 1959 to 1970 of the
source): if `f_{i₀} - g_{i₀} < f_{i₁} - g_{i₁}` and `H(p) + Λ(∑ p f, ∑ p g, t) > 0`, then moving a
little mass from `i₀` to `i₁` gives strictly positive weights `p'` with the same positivity and
`∑ p' g - ∑ p' f < ∑ p g - ∑ p f`. The entropy is continuous and the energy is linear in the
exponents for a fixed `t`. -/
theorem exists_perturbed_weights {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp : ∀ i, 0 < p i)
    (hp1 : ∑ i, p i = 1) {f g : ι → ℝ} {i₀ i₁ : ι} (hi : f i₀ - g i₀ < f i₁ - g i₁) {t : ℝ}
    (hpos : 0 < ∑ i, Real.negMulLog (p i) + energy (∑ i, p i * f i) (∑ i, p i * g i) t) :
    ∃ p' : ι → ℝ, (∀ i, 0 < p' i) ∧ ∑ i, p' i = 1 ∧
      ∑ i, p' i * g i - ∑ i, p' i * f i < ∑ i, p i * g i - ∑ i, p i * f i ∧
      0 < ∑ i, Real.negMulLog (p' i) + energy (∑ i, p' i * f i) (∑ i, p' i * g i) t := by
  classical
  set d : ι → ℝ := fun i => (if i = i₁ then 1 else 0) - (if i = i₀ then 1 else 0) with hd
  obtain ⟨c₁, c₂, hc⟩ := exists_energy_eq_linear t
  let F : ℝ → ℝ := fun η => ∑ i, Real.negMulLog (p i + η * d i) +
    (c₁ * ∑ i, (p i + η * d i) * f i + c₂ * ∑ i, (p i + η * d i) * g i)
  have hF : Continuous F := by fun_prop
  have hF0 : 0 < F 0 := by simpa [F, hc] using hpos
  have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < F η ∧ ∀ i, η < p i :=
    ((hF.continuousAt.eventually (lt_mem_nhds hF0)).and
      (eventually_all.2 fun i => eventually_lt_nhds (hp i))).filter_mono nhdsWithin_le_nhds
  obtain ⟨η, ⟨hFη, hηp⟩, hη0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hη0' : (0 : ℝ) < η := hη0
  have hdf : ∀ h : ι → ℝ,
      ∑ i, (p i + η * d i) * h i = ∑ i, p i * h i + η * (h i₁ - h i₀) := fun h => by
    simp only [hd, add_mul, sum_add_distrib, mul_assoc, ← mul_sum, sub_mul, sum_sub_distrib,
      ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]
  refine ⟨fun i => p i + η * d i, fun i => ?_, ?_, ?_, ?_⟩
  · have hd1 : -1 ≤ d i := by
      simp only [hd]
      split_ifs <;> norm_num
    nlinarith [hηp i, mul_le_mul_of_nonneg_left hd1 hη0'.le]
  · have := hdf (fun _ => 1)
    simp only [mul_one, sub_self, mul_zero, add_zero] at this
    rw [this, hp1]
  · rw [hdf f, hdf g]
    nlinarith [mul_pos hη0' (sub_pos.2 hi)]
  · rw [hc]
    exact hFη

/-- Weights for the reduction (lines 2028 to 2077 of the source): for `t < dimaff` there are
strictly positive weights `p` with `λ_b < λ_a` and `H(p) + Λ(λ_a, λ_b, t) > 0`, or with
`λ_a < λ_b` and `H(p) + Λ(λ_b, λ_a, t) > 0`. The Käenmäki weights at `s = dimaff`
(`kaenmaki_weights`) satisfy `dim_L(H(p), λ_weak, λ_strong) = s > t`, hence the positivity; if
the two exponents coincide, `c_i = log |a_i| - log |b_i|` is not constant (it has mean `0` and is
not identically `0` by proximality), and `exists_perturbed_weights` separates the exponents. -/
theorem exists_good_weights {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    (hdiag : ∀ i, S.o i = 0) (hprox : ∃ i, |S.a i| ≠ |S.b i|) {t : ℝ} (ht : t < S.dimaff) :
    ∃ p : ι → ℝ, (∀ i, 0 < p i) ∧ ∑ i, p i = 1 ∧
      ((∑ i, p i * Real.log |S.b i| < ∑ i, p i * Real.log |S.a i| ∧
          0 < ∑ i, Real.negMulLog (p i) +
            energy (∑ i, p i * Real.log |S.a i|) (∑ i, p i * Real.log |S.b i|) t) ∨
        (∑ i, p i * Real.log |S.a i| < ∑ i, p i * Real.log |S.b i| ∧
          0 < ∑ i, Real.negMulLog (p i) +
            energy (∑ i, p i * Real.log |S.b i|) (∑ i, p i * Real.log |S.a i|) t)) := by
  obtain ⟨p, hp, hp1, halt⟩ := kaenmaki_weights S hdiag
  have hH : 0 ≤ ∑ i, Real.negMulLog (p i) := sum_nonneg fun i _ => Real.negMulLog_nonneg
    (hp i).le (hp1 ▸ single_le_sum (fun j _ => (hp j).le) (mem_univ i))
  have hla : ∑ i, p i * Real.log |S.a i| < 0 := sum_mul_log_abs_neg hp S.a_ne_zero S.abs_a_lt_one
  have hlb : ∑ i, p i * Real.log |S.b i| < 0 := sum_mul_log_abs_neg hp S.b_ne_zero S.abs_b_lt_one
  -- equal exponents: perturb the weights
  have heqcase : ∑ i, p i * Real.log |S.b i| = ∑ i, p i * Real.log |S.a i| →
      0 < ∑ i, Real.negMulLog (p i) +
        energy (∑ i, p i * Real.log |S.a i|) (∑ i, p i * Real.log |S.b i|) t →
      ∃ p' : ι → ℝ, (∀ i, 0 < p' i) ∧ ∑ i, p' i = 1 ∧
        ((∑ i, p' i * Real.log |S.b i| < ∑ i, p' i * Real.log |S.a i| ∧
          0 < ∑ i, Real.negMulLog (p' i) +
            energy (∑ i, p' i * Real.log |S.a i|) (∑ i, p' i * Real.log |S.b i|) t) ∨
        (∑ i, p' i * Real.log |S.a i| < ∑ i, p' i * Real.log |S.b i| ∧
          0 < ∑ i, Real.negMulLog (p' i) +
            energy (∑ i, p' i * Real.log |S.b i|) (∑ i, p' i * Real.log |S.a i|) t)) := by
    intro heq hpos
    obtain ⟨i₀, i₁, hi⟩ : ∃ i₀ i₁, Real.log |S.a i₀| - Real.log |S.b i₀| <
        Real.log |S.a i₁| - Real.log |S.b i₁| := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      obtain ⟨j, hj⟩ := hprox
      have hconst : ∀ i, Real.log |S.a i| - Real.log |S.b i| =
          Real.log |S.a j| - Real.log |S.b j| := fun i => le_antisymm (hcon j i) (hcon i j)
      have hsum : ∑ i, p i * (Real.log |S.a i| - Real.log |S.b i|) =
          Real.log |S.a j| - Real.log |S.b j| := by
        simp only [hconst, ← sum_mul, hp1, one_mul]
      have h0 : Real.log |S.a j| - Real.log |S.b j| = 0 := by
        rw [← hsum]
        simp only [mul_sub, sum_sub_distrib, heq, sub_self]
      exact hj (Real.log_injOn_pos (Set.mem_Ioi.2 (abs_pos.2 (S.a_ne_zero j)))
        (Set.mem_Ioi.2 (abs_pos.2 (S.b_ne_zero j))) (sub_eq_zero.1 h0))
    obtain ⟨p', hp', hp1', hlt', hpos'⟩ := exists_perturbed_weights hp hp1
      (f := fun i => Real.log |S.a i|) (g := fun i => Real.log |S.b i|) hi hpos
    exact ⟨p', hp', hp1', Or.inl ⟨by linarith, hpos'⟩⟩
  rcases halt with ⟨-, hle, -, hdim⟩ | ⟨-, hle, -, hdim⟩
  · have hpos := pos_add_energy_of_lt_lyapDim hle hla hH (hdim ▸ ht)
    rcases hle.lt_or_eq with hlt | heq
    · exact ⟨p, hp, hp1, Or.inl ⟨hlt, hpos⟩⟩
    · exact heqcase heq hpos
  · have hpos := pos_add_energy_of_lt_lyapDim hle hlb hH (hdim ▸ ht)
    rcases hle.lt_or_eq with hlt | heq
    · exact ⟨p, hp, hp1, Or.inr ⟨hlt, hpos⟩⟩
    · refine heqcase heq.symm ?_
      rw [heq] at hpos ⊢
      exact hpos

/-! ### The theorem -/

/-- The lower bound `dim_H X ≥ t` for every `0 ≤ t < min{2, dimaff(X)}` (lines 2010 to 2159 of
the source): from good weights for `S` (`ofReal_le_dimH_of_weights`), or for `coordSwap S`,
which has the same attractor up to the isometry `swap`.
Depends on: `HomogeneousCore`. -/
theorem ofReal_le_dimH_attractor (hcore : HomogeneousCore.{u}) {ι : Type u} [Fintype ι]
    [Nonempty ι] (S : System ι) (hdiag : ∀ i, S.o i = 0) (hprox : ∃ i, |S.a i| ≠ |S.b i|)
    (h0 : S.AxisExpSeparation 0) (h1 : S.AxisExpSeparation 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < min 2 S.dimaff) : ENNReal.ofReal t ≤ dimH S.attractor := by
  have ht2 : t ≤ 2 := ht.le.trans (min_le_left _ _)
  obtain ⟨p, hp, hp1, h | h⟩ :=
    exists_good_weights S hdiag hprox (ht.trans_le (min_le_right _ _))
  · exact ofReal_le_dimH_of_weights S hcore hdiag h0 h1 hp hp1 h.1 ht0 ht2 h.2
  · have h0' : (coordSwap S).AxisExpSeparation 0 :=
      (coordSwap_axisExpSeparation S 0).2 (by rwa [zero_add])
    have h1' : (coordSwap S).AxisExpSeparation 1 :=
      (coordSwap_axisExpSeparation S 1).2 (by rwa [show (1 : ZMod 2) + 1 = 0 from by decide])
    rw [← dimH_coordSwap_attractor S]
    exact ofReal_le_dimH_of_weights (coordSwap S) hcore hdiag h0' h1' hp hp1 h.1 ht0 ht2 h.2

/-- Rapaport's Theorem 1.3 in the plane (lines 2010 to 2159 of the source), assuming the core
theorem: `dim_H X = min{2, dimaff(X)}` for a diagonal system with `|a_i| ≠ |b_i|` for some `i`
and exponentially separated induced systems on both axes. The upper bound is Falconer's
(`System.dimH_attractor_le`), the lower bound `ofReal_le_dimH_attractor`.
Depends on: `HomogeneousCore`. -/
theorem dimH_attractor_eq_of_core (hcore : HomogeneousCore.{u}) {ι : Type u} [Fintype ι]
    [Nonempty ι] (S : System ι) (hdiag : ∀ i, S.o i = 0) (hprox : ∃ i, |S.a i| ≠ |S.b i|)
    (h0 : S.AxisExpSeparation 0) (h1 : S.AxisExpSeparation 1) :
    dimH S.attractor = ENNReal.ofReal (min 2 S.dimaff) := by
  refine le_antisymm S.dimH_attractor_le (le_of_forall_lt_imp_le_of_dense fun c hc => ?_)
  rw [← ENNReal.ofReal_toReal (ne_top_of_lt hc)]
  exact ofReal_le_dimH_attractor hcore S hdiag hprox h0 h1 ENNReal.toReal_nonneg
    (ENNReal.toReal_lt_of_lt_ofReal hc)

/-- `RapaportDiagonalDimension` from the core theorem `HomogeneousCore`: Rapaport's Theorem 1.3
in the plane (arXiv:2309.03985, Section 7), with proximality in the form
`|a_i| ≠ |b_i|` for some `i` (`System.proximal_iff_of_diagonal`).
Depends on: `HomogeneousCore`. -/
theorem rapaportDiagonalDimension_of_core (hcore : HomogeneousCore.{u}) :
    RapaportDiagonalDimension.{u} := by
  intro ι _ _ S hdiag hprox h0 h1
  exact dimH_attractor_eq_of_core hcore S hdiag ((S.proximal_iff_of_diagonal hdiag).1 hprox) h0 h1

end BoxLike.Rapaport.Diagonal
