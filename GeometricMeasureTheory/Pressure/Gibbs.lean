/-
# Section 7.2: Cookie-cutter thermodynamic formalism

The pressure of a Lipschitz potential and the Gibbs measure it carries. The partition sums are
taken over the cylinders of each length; the notes sum `exp S_k φ(x_𝐢)` over a choice of point
`x_𝐢 ∈ X_𝐢`, which in branch coordinates is a choice of `u_𝐢 ∈ X` with `x_𝐢 = F_𝐢(u_𝐢)`.

The pressure is defined as a limit superior, and `pressure_gibbs` shows that it is a limit and does
not depend on the points chosen. The generalisations discussed in Section 7.2.1 are built in: any
finite number of branches is allowed, and the only regularity used is that the log-derivatives of
the branches are Lipschitz.

| Notes | Lean declaration | Location |
|---|---|---|
| The partition sum `s_k` | `CookieCutter.partitionSum` | here |
| The pressure `P(φ)` | `CookieCutter.pressure` | here |
| Theorem 7.7 (pressure and Gibbs measure) | `CookieCutter.pressure_gibbs` | here |
| Equation (7.1) for the partition sums | `CookieCutter.exists_partitionSum_bounds` | here |
| The approximating measures `μ_m` and their cylinder masses | `CookieCutter.gibbsApprox`, `CookieCutter.exists_gibbsApprox_cylinder_bounds` | here |
| The pressure over the fixed points of `f^k` (Section 7.2.1) | `CookieCutter.pressure_gibbs` applied to the fixed point of each `F_𝐢` | here |
| Weak compactness of the approximating measures | `weak_compactness`, `CompactSpace (MeasureTheory.ProbabilityMeasure E)` | `GeometricMeasureTheory.BasicMeasureTheory`, `Mathlib/MeasureTheory/Measure/Prokhorov.lean` |
| Identifying the limit on cylinders | `MeasureTheory.ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto` | `Mathlib/MeasureTheory/Measure/Portmanteau.lean` |
-/
import GeometricMeasureTheory.Pressure.Subadditive
import GeometricMeasureTheory.CookieCutter.BoundedDistortion

open MeasureTheory Filter Topology Set Metric

open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

/-- Splitting a word of length `k + n` into its first `k` and its last `n` letters reindexes a sum
over the words of length `k + n` as an iterated sum over the two halves. -/
theorem sum_ofFn_add {ι M : Type*} [Fintype ι] [AddCommMonoid M] (k n : ℕ) (G : List ι → M) :
    ∑ f : Fin (k + n) → ι, G (List.ofFn f)
      = ∑ g : Fin k → ι, ∑ h : Fin n → ι, G (List.ofFn g ++ List.ofFn h) :=
  calc ∑ f : Fin (k + n) → ι, G (List.ofFn f)
      = ∑ p : (Fin k → ι) × (Fin n → ι), G (List.ofFn p.1 ++ List.ofFn p.2) :=
        (Fintype.sum_equiv (Fin.appendEquiv k n) _ _ fun x => by simp [Fin.appendEquiv]).symm
    _ = ∑ g : Fin k → ι, ∑ h : Fin n → ι, G (List.ofFn g ++ List.ofFn h) :=
        Fintype.sum_prod_type _

/-- Every word of length `k` is the list of values of a function on `Fin k`. -/
theorem exists_ofFn_eq_of_length {ι : Type*} {v : List ι} {k : ℕ} (h : v.length = k) :
    ∃ f : Fin k → ι, List.ofFn f = v := by
  subst h
  exact ⟨v.get, List.ofFn_get v⟩

/-- A sequence of reals trapped between `a⁻¹ e^{kP}` and `a e^{kP}` has exponential growth rate
`P`. -/
theorem tendsto_log_div_of_exp_bounds {s : ℕ → ℝ} {a P : ℝ} (ha : 1 ≤ a)
    (h : ∀ k : ℕ, a⁻¹ * Real.exp (k * P) ≤ s k ∧ s k ≤ a * Real.exp (k * P)) :
    Tendsto (fun k : ℕ => Real.log (s k) / k) atTop (𝓝 P) := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le one_pos ha
  have hlow : Tendsto (fun k : ℕ => P - Real.log a / k) atTop (𝓝 P) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (Real.log a))
  have hhigh : Tendsto (fun k : ℕ => P + Real.log a / k) atTop (𝓝 P) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (Real.log a))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hlg := Real.log_le_log (by positivity) (h k).1
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_inv, Real.log_exp] at hlg
    rw [le_div_iff₀ hk0, show (P - Real.log a / k) * k = P * k - Real.log a by field_simp]
    linarith
  · filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hspos : (0 : ℝ) < s k := lt_of_lt_of_le (by positivity) (h k).1
    have hlg := Real.log_le_log hspos (h k).2
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp] at hlg
    rw [div_le_iff₀ hk0, show (P + Real.log a / k) * k = P * k + Real.log a by field_simp]
    linarith

namespace CookieCutter

variable {ι : Type*} [Fintype ι] (C : CookieCutter ι)

/-- The partition sum `s_k = ∑_{𝐢 ∈ I_k} exp S_k φ(x_𝐢)`, where the point `x_𝐢 = F_𝐢(u 𝐢)` of the
cylinder `X_𝐢` is chosen by `u`. -/
def partitionSum (C : CookieCutter ι) (φ : ι → ℝ → ℝ) (u : List ι → ℝ) (k : ℕ) : ℝ :=
  ∑ f : Fin k → ι, Real.exp (C.birkhoffSum φ (List.ofFn f) (u (List.ofFn f)))

/-- The pressure `P(φ)`. Theorem 7.7 shows that the limit superior is a limit and is unchanged if
the left endpoint of the interval is replaced by any other choice of points. -/
def pressure (C : CookieCutter ι) (φ : ι → ℝ → ℝ) : ℝ :=
  limsup (fun k : ℕ => Real.log (C.partitionSum φ (fun _ => C.a) k) / k) atTop

/-- The partition sum is positive. -/
theorem partitionSum_pos [Nonempty ι] (φ : ι → ℝ → ℝ) (u : List ι → ℝ) (k : ℕ) :
    0 < C.partitionSum φ u k :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-! ## Quasi-multiplicativity of the partition sums -/

/-- There is exactly one word of length zero, so the partition sums start at `1`. -/
@[simp]
theorem partitionSum_zero (φ : ι → ℝ → ℝ) (u : List ι → ℝ) : C.partitionSum φ u 0 = 1 := by
  simp [partitionSum]

omit [Fintype ι] in
/-- The left endpoint of the interval belongs to it, so it is a legitimate default choice of points
in the cylinders. -/
private theorem a_mem_X : C.a ∈ C.X := left_mem_Icc.2 C.lt_ab.le

omit [Fintype ι] in
/-- The upper half of the principle of bounded variation in exponential form. -/
theorem exp_birkhoffSum_le_mul {φ : ι → ℝ → ℝ} {b : ℝ}
    (hb : ∀ w : List ι, ∀ x ∈ C.X, ∀ y ∈ C.X, |C.birkhoffSum φ w x - C.birkhoffSum φ w y| ≤ b)
    (w : List ι) {x y : ℝ} (hx : x ∈ C.X) (hy : y ∈ C.X) :
    Real.exp (C.birkhoffSum φ w x) ≤ Real.exp b * Real.exp (C.birkhoffSum φ w y) := by
  rw [← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith [abs_le.1 (hb w x hx y hy)])

omit [Fintype ι] in
/-- The lower half of the principle of bounded variation in exponential form. -/
theorem mul_exp_birkhoffSum_le {φ : ι → ℝ → ℝ} {b : ℝ}
    (hb : ∀ w : List ι, ∀ x ∈ C.X, ∀ y ∈ C.X, |C.birkhoffSum φ w x - C.birkhoffSum φ w y| ≤ b)
    (w : List ι) {x y : ℝ} (hx : x ∈ C.X) (hy : y ∈ C.X) :
    Real.exp (-b) * Real.exp (C.birkhoffSum φ w y) ≤ Real.exp (C.birkhoffSum φ w x) := by
  rw [← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith [abs_le.1 (hb w x hx y hy)])

/-- Changing the points chosen in the cylinders changes a partition sum by at most the factor `e^b`
of the principle of bounded variation. -/
theorem partitionSum_le_mul {φ : ι → ℝ → ℝ} {b : ℝ}
    (hb : ∀ w : List ι, ∀ x ∈ C.X, ∀ y ∈ C.X, |C.birkhoffSum φ w x - C.birkhoffSum φ w y| ≤ b)
    {u u' : List ι → ℝ} (hu : ∀ w, u w ∈ C.X) (hu' : ∀ w, u' w ∈ C.X) (k : ℕ) :
    C.partitionSum φ u k ≤ Real.exp b * C.partitionSum φ u' k := by
  rw [partitionSum, partitionSum, Finset.mul_sum]
  exact Finset.sum_le_sum fun _ _ => C.exp_birkhoffSum_le_mul hb _ (hu _) (hu' _)

/-- The partition sums are quasi-multiplicative, with the constant `2 b` coming from the principle
of bounded variation. -/
theorem partitionSum_add {φ : ι → ℝ → ℝ} {b : ℝ}
    (hb : ∀ w : List ι, ∀ x ∈ C.X, ∀ y ∈ C.X, |C.birkhoffSum φ w x - C.birkhoffSum φ w y| ≤ b)
    {u : List ι → ℝ} (hu : ∀ w, u w ∈ C.X) (k n : ℕ) :
    Real.exp (-(2 * b)) * (C.partitionSum φ u k * C.partitionSum φ u n) ≤
        C.partitionSum φ u (k + n) ∧
      C.partitionSum φ u (k + n) ≤
        Real.exp (2 * b) * (C.partitionSum φ u k * C.partitionSum φ u n) := by
  set A : (Fin k → ι) → ℝ :=
    fun g => Real.exp (C.birkhoffSum φ (List.ofFn g) (u (List.ofFn g))) with hAdef
  set B : (Fin n → ι) → ℝ :=
    fun h => Real.exp (C.birkhoffSum φ (List.ofFn h) (u (List.ofFn h))) with hBdef
  have hPk : C.partitionSum φ u k = ∑ g, A g := rfl
  have hPn : C.partitionSum φ u n = ∑ h, B h := rfl
  have hsplit : C.partitionSum φ u (k + n)
      = ∑ g : Fin k → ι, ∑ h : Fin n → ι,
          Real.exp (C.birkhoffSum φ (List.ofFn g)
              (C.branchMap (List.ofFn h) (u (List.ofFn g ++ List.ofFn h)))) *
            Real.exp (C.birkhoffSum φ (List.ofFn h) (u (List.ofFn g ++ List.ofFn h))) := by
    rw [partitionSum]
    refine (sum_ofFn_add k n fun w => Real.exp (C.birkhoffSum φ w (u w))).trans ?_
    exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => by
      rw [← Real.exp_add, C.birkhoffSum_append]
  have hprod : ∀ e : ℝ, (∑ g, Real.exp e * A g) * (∑ h, Real.exp e * B h)
      = Real.exp (e + e) * (C.partitionSum φ u k * C.partitionSum φ u n) := by
    intro e
    rw [← Finset.mul_sum, ← Finset.mul_sum, hPk, hPn, Real.exp_add]
    ring
  constructor
  · rw [hsplit, show -(2 * b) = -b + -b by ring, ← hprod (-b), Finset.sum_mul_sum]
    exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ =>
      mul_le_mul (C.mul_exp_birkhoffSum_le hb _ (C.mapsTo_branchMap _ (hu _)) (hu _))
        (C.mul_exp_birkhoffSum_le hb _ (hu _) (hu _)) (by positivity) (Real.exp_pos _).le
  · rw [hsplit, two_mul, ← hprod b, Finset.sum_mul_sum]
    exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ =>
      mul_le_mul (C.exp_birkhoffSum_le_mul hb _ (C.mapsTo_branchMap _ (hu _)) (hu _))
        (C.exp_birkhoffSum_le_mul hb _ (hu _) (hu _)) (Real.exp_pos _).le (by positivity)

/-- Equation (7.1): the partition sums of a Lipschitz potential stay within a fixed factor of
`e^{k P(φ)}`, uniformly in the points chosen in the cylinders, and their logarithmic growth rate is
the pressure. -/
theorem exists_partitionSum_bounds [Nonempty ι] {φ : ι → ℝ → ℝ} {c : ℝ≥0}
    (hφ : ∀ i, LipschitzOnWith c (φ i) C.X) :
    ∃ a : ℝ, 1 ≤ a ∧ ∀ u : List ι → ℝ, (∀ w, u w ∈ C.X) →
      Tendsto (fun k : ℕ => Real.log (C.partitionSum φ u k) / k) atTop (𝓝 (C.pressure φ)) ∧
        ∀ k : ℕ, a⁻¹ * Real.exp (k * C.pressure φ) ≤ C.partitionSum φ u k ∧
          C.partitionSum φ u k ≤ a * Real.exp (k * C.pressure φ) := by
  obtain ⟨b, hb0, hb, -⟩ := C.bounded_variation hφ
  set u₀ : List ι → ℝ := fun _ => C.a with hu₀def
  have hu₀ : ∀ w : List ι, u₀ w ∈ C.X := fun _ => C.a_mem_X
  obtain ⟨P, hPtend, hPb⟩ := exists_tendsto_log_div_of_quasiMultiplicative
    (by positivity : (0 : ℝ) ≤ 2 * b) (fun k => C.partitionSum_pos φ u₀ k)
    (fun k n => C.partitionSum_add hb hu₀ k n)
  have hpres : C.pressure φ = P := hPtend.limsup_eq
  refine ⟨Real.exp (3 * b), ?_, fun u hu => ?_⟩
  · rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_le_exp.2 (by positivity)
  · have hbounds : ∀ k : ℕ, (Real.exp (3 * b))⁻¹ * Real.exp (k * C.pressure φ) ≤
        C.partitionSum φ u k ∧
        C.partitionSum φ u k ≤ Real.exp (3 * b) * Real.exp (k * C.pressure φ) := by
      intro k
      have hup := C.partitionSum_le_mul hb hu hu₀ k
      have hlo := C.partitionSum_le_mul hb hu₀ hu k
      have hexp : Real.exp (3 * b) = Real.exp b * Real.exp (2 * b) := by
        rw [← Real.exp_add]; ring_nf
      have hexpinv : (Real.exp (3 * b))⁻¹ = Real.exp (-b) * Real.exp (-(2 * b)) := by
        rw [← Real.exp_add, ← Real.exp_neg]; ring_nf
      have hmul : Real.exp (-b) * Real.exp b = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      constructor
      · rw [hexpinv, hpres, mul_assoc]
        calc Real.exp (-b) * (Real.exp (-(2 * b)) * Real.exp (k * P))
            ≤ Real.exp (-b) * C.partitionSum φ u₀ k :=
              mul_le_mul_of_nonneg_left (hPb k).1 (Real.exp_pos _).le
          _ ≤ Real.exp (-b) * (Real.exp b * C.partitionSum φ u k) :=
              mul_le_mul_of_nonneg_left hlo (Real.exp_pos _).le
          _ = C.partitionSum φ u k := by rw [← mul_assoc, hmul, one_mul]
      · rw [hexp, hpres, mul_assoc]
        exact hup.trans (mul_le_mul_of_nonneg_left (hPb k).2 (Real.exp_pos _).le)
    exact ⟨tendsto_log_div_of_exp_bounds (by
      rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      exact Real.exp_le_exp.2 (by positivity)) hbounds, hbounds⟩

/-! ## The approximating measures -/

omit [Fintype ι] in
/-- The image `F_𝐯(x)` of a point of the interval lies in the cylinder of a word `w` no longer than
`v` exactly when `w` is the initial segment of `v` of its own length. -/
theorem branchMap_mem_cylinder_iff {v w : List ι} (hlen : w.length ≤ v.length) {x : ℝ}
    (hx : x ∈ C.X) : C.branchMap v x ∈ C.cylinder w ↔ v.take w.length = w := by
  have hcomp : C.branchMap v x
      = C.branchMap (v.take w.length) (C.branchMap (v.drop w.length) x) := by
    conv_lhs => rw [C.branchMap_take_drop v w.length]
    rfl
  have hmem' : C.branchMap v x ∈ C.cylinder (v.take w.length) :=
    ⟨C.branchMap (v.drop w.length) x, C.mapsTo_branchMap _ hx, hcomp.symm⟩
  refine ⟨fun hmem => ?_, fun hEq => ?_⟩
  · by_contra hne
    have hlen' : (v.take w.length).length = w.length := by
      rw [List.length_take]; omega
    exact Set.disjoint_left.mp (C.disjoint_cylinder hlen' hne) hmem' hmem
  · rwa [hEq] at hmem'

/-- Each cylinder is relatively clopen in the repeller: it is compact, and its complement there is
the union of the finitely many other cylinders of the same length. -/
theorem isClopen_preimage_cylinder (w : List ι) :
    IsClopen ((Subtype.val : C.attractor → ℝ) ⁻¹' C.cylinder w) := by
  refine ⟨(C.isCompact_cylinder w).isClosed.preimage continuous_subtype_val, ?_⟩
  set T : Set ℝ := ⋃ f : {f : Fin w.length → ι // List.ofFn f ≠ w}, C.cylinder (List.ofFn f.1)
    with hTdef
  have hTclosed : IsClosed T := isClosed_iUnion_of_finite fun f => (C.isCompact_cylinder _).isClosed
  have hcompl : ((Subtype.val : C.attractor → ℝ) ⁻¹' C.cylinder w)ᶜ
      = (Subtype.val : C.attractor → ℝ) ⁻¹' T := by
    ext y
    simp only [mem_compl_iff, mem_preimage]
    refine ⟨fun hy => ?_, fun hy hycyl => ?_⟩
    · have hylev : (y : ℝ) ∈ C.level w.length := C.attractor_subset_level _ y.2
      simp only [level, mem_iUnion] at hylev
      obtain ⟨v, hv, hyv⟩ := hylev
      obtain ⟨f, hf⟩ := exists_ofFn_eq_of_length hv
      refine mem_iUnion.2 ⟨⟨f, ?_⟩, ?_⟩
      · rw [hf]
        rintro rfl
        exact hy hyv
      · rw [hf]
        exact hyv
    · obtain ⟨f, hf⟩ := mem_iUnion.1 hy
      exact Set.disjoint_left.mp (C.disjoint_cylinder (by simp) f.2) hf hycyl
  have hopen := (hTclosed.preimage (continuous_subtype_val (p := fun x => x ∈ C.attractor)))
    |>.isOpen_compl
  rw [← hcompl, compl_compl] at hopen
  exact hopen

/-- The discrete measure `μ_m` of the proof of Theorem 7.7: it gives each of the points `F_𝐢(p)`,
for `𝐢` a word of length `m`, the normalised mass `exp S_m φ(F_𝐢 p) / s_m`. -/
def gibbsApprox (C : CookieCutter ι) (φ : ι → ℝ → ℝ) (p : C.attractor) (m : ℕ) :
    Measure C.attractor :=
  ∑ f : Fin m → ι,
    ENNReal.ofReal (Real.exp (C.birkhoffSum φ (List.ofFn f) (p : ℝ)) /
        C.partitionSum φ (fun _ => (p : ℝ)) m) •
      Measure.dirac (⟨C.branchMap (List.ofFn f) (p : ℝ),
        C.mapsTo_branchMap_attractor (List.ofFn f) p.2⟩ : C.attractor)

/-- The mass that `μ_m` gives to the part of a measurable subset of the line lying in the
repeller. -/
theorem gibbsApprox_apply (φ : ι → ℝ → ℝ) (p : C.attractor) (m : ℕ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    C.gibbsApprox φ p m (Subtype.val ⁻¹' A)
      = ∑ f : Fin m → ι, A.indicator
          (fun _ => ENNReal.ofReal (Real.exp (C.birkhoffSum φ (List.ofFn f) (p : ℝ)) /
            C.partitionSum φ (fun _ => (p : ℝ)) m)) (C.branchMap (List.ofFn f) (p : ℝ)) := by
  rw [gibbsApprox, Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ (hA.preimage measurable_subtype_coe)]
  by_cases hmem : C.branchMap (List.ofFn f) (p : ℝ) ∈ A
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show (⟨C.branchMap (List.ofFn f) (p : ℝ),
      C.mapsTo_branchMap_attractor (List.ofFn f) p.2⟩ : C.attractor) ∈ Subtype.val ⁻¹' A from hmem)]
    simp
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (show (⟨C.branchMap (List.ofFn f)
      (p : ℝ), C.mapsTo_branchMap_attractor (List.ofFn f) p.2⟩ : C.attractor) ∉
      Subtype.val ⁻¹' A from hmem)]
    simp

/-- The approximating measures are probability measures. -/
instance isProbabilityMeasure_gibbsApprox [Nonempty ι] (φ : ι → ℝ → ℝ) (p : C.attractor) (m : ℕ) :
    IsProbabilityMeasure (C.gibbsApprox φ p m) := by
  have hs0 : 0 < C.partitionSum φ (fun _ => (p : ℝ)) m := C.partitionSum_pos φ _ _
  constructor
  rw [show (Set.univ : Set C.attractor) = Subtype.val ⁻¹' (Set.univ : Set ℝ) from rfl,
    C.gibbsApprox_apply φ p m MeasurableSet.univ]
  simp only [Set.indicator_univ]
  rw [← ENNReal.ofReal_sum_of_nonneg fun f _ => div_nonneg (Real.exp_pos _).le hs0.le,
    ← Finset.sum_div,
    show (∑ f : Fin m → ι, Real.exp (C.birkhoffSum φ (List.ofFn f) (p : ℝ)))
      = C.partitionSum φ (fun _ => (p : ℝ)) m from rfl,
    div_self hs0.ne', ENNReal.ofReal_one]

/-- The mass that `μ_m` gives to a cylinder of length `k ≤ m`: the words of length `m` that
contribute are exactly those beginning with the given word. -/
theorem gibbsApprox_apply_cylinder [Nonempty ι] (φ : ι → ℝ → ℝ) (p : C.attractor) (w : List ι)
    (n : ℕ) :
    C.gibbsApprox φ p (w.length + n) (Subtype.val ⁻¹' C.cylinder w)
      = ENNReal.ofReal ((∑ h : Fin n → ι, Real.exp (C.birkhoffSum φ (w ++ List.ofFn h) (p : ℝ))) /
          C.partitionSum φ (fun _ => (p : ℝ)) (w.length + n)) := by
  have hp : (p : ℝ) ∈ C.X := C.attractor_subset_X p.2
  have hs0 : 0 < C.partitionSum φ (fun _ => (p : ℝ)) (w.length + n) := C.partitionSum_pos φ _ _
  set s := C.partitionSum φ (fun _ => (p : ℝ)) (w.length + n) with hs
  set G : List ι → ℝ≥0∞ := fun v => (C.cylinder w).indicator
    (fun _ => ENNReal.ofReal (Real.exp (C.birkhoffSum φ v (p : ℝ)) / s))
    (C.branchMap v (p : ℝ)) with hG
  obtain ⟨gw, hgw⟩ : ∃ f : Fin w.length → ι, List.ofFn f = w := ⟨w.get, List.ofFn_get w⟩
  rw [C.gibbsApprox_apply φ p _ (C.isCompact_cylinder w).isClosed.measurableSet]
  refine (sum_ofFn_add w.length n G).trans ?_
  rw [Finset.sum_eq_single_of_mem gw (Finset.mem_univ gw) ?_]
  · have hval : ∀ h : Fin n → ι, G (w ++ List.ofFn h)
        = ENNReal.ofReal (Real.exp (C.birkhoffSum φ (w ++ List.ofFn h) (p : ℝ)) / s) := by
      intro h
      rw [hG]
      refine Set.indicator_of_mem ?_ _
      rw [C.branchMap_mem_cylinder_iff (by simp) hp, List.take_left' rfl]
    rw [hgw]
    simp_rw [hval]
    rw [← ENNReal.ofReal_sum_of_nonneg fun h _ => div_nonneg (Real.exp_pos _).le hs0.le,
      Finset.sum_div]
  · intro g _ hne
    refine Finset.sum_eq_zero fun h _ => ?_
    have hgw' : List.ofFn g ≠ w := fun hEq => hne (List.ofFn_injective (hEq.trans hgw.symm))
    have hlen : w.length ≤ (List.ofFn g ++ List.ofFn h).length := by simp
    have hnotmem : C.branchMap (List.ofFn g ++ List.ofFn h) (p : ℝ) ∉ C.cylinder w := by
      rw [C.branchMap_mem_cylinder_iff hlen hp, List.take_left' (by simp)]
      exact hgw'
    rw [hG]
    exact Set.indicator_of_notMem hnotmem _

/-- The arithmetic of the chain of estimates of the notes: `T` is the unnormalised mass of the
cylinder, `sm` the partition sum normalising it, and `sk`, `sn` the partition sums of the two
halves of the word. -/
private theorem div_le_and_le_div_of_bounds {T E sn sk sm a b P : ℝ} (ha : 1 ≤ a) (hsn : 0 < sn)
    (hsm : 0 < sm) (hE : 0 < E)
    (hT1 : Real.exp (-b) * (E * sn) ≤ T) (hT2 : T ≤ Real.exp b * (E * sn))
    (hm1 : Real.exp (-(2 * b)) * (sk * sn) ≤ sm) (hm2 : sm ≤ Real.exp (2 * b) * (sk * sn))
    (hk1 : a⁻¹ * Real.exp P ≤ sk) (hk2 : sk ≤ a * Real.exp P) :
    (Real.exp (3 * b) * a)⁻¹ * (E * Real.exp (-P)) ≤ T / sm ∧
      T / sm ≤ Real.exp (3 * b) * a * (E * Real.exp (-P)) := by
  have hane : a ≠ 0 := by positivity
  have h2 : Real.exp (-P) * Real.exp P = 1 := by rw [← Real.exp_add]; simp
  constructor
  · have h1 : (Real.exp (3 * b))⁻¹ * Real.exp (2 * b) = Real.exp (-b) := by
      rw [← Real.exp_neg, ← Real.exp_add]; ring_nf
    rw [le_div_iff₀ hsm, mul_inv, mul_comm ((Real.exp (3 * b))⁻¹) a⁻¹]
    calc a⁻¹ * (Real.exp (3 * b))⁻¹ * (E * Real.exp (-P)) * sm
        ≤ a⁻¹ * (Real.exp (3 * b))⁻¹ * (E * Real.exp (-P)) *
            (Real.exp (2 * b) * (sk * sn)) := by gcongr
      _ ≤ a⁻¹ * (Real.exp (3 * b))⁻¹ * (E * Real.exp (-P)) *
            (Real.exp (2 * b) * (a * Real.exp P * sn)) := by gcongr
      _ = Real.exp (-b) * (E * sn) := by
          rw [show a⁻¹ * (Real.exp (3 * b))⁻¹ * (E * Real.exp (-P)) *
              (Real.exp (2 * b) * (a * Real.exp P * sn))
              = (Real.exp (3 * b))⁻¹ * Real.exp (2 * b) * (a⁻¹ * a) *
                (Real.exp (-P) * Real.exp P) * (E * sn) from by ring,
            h1, h2, inv_mul_cancel₀ hane]
          ring
      _ ≤ T := hT1
  · have h1 : Real.exp (3 * b) * Real.exp (-(2 * b)) = Real.exp b := by
      rw [← Real.exp_add]; ring_nf
    rw [div_le_iff₀ hsm]
    calc T ≤ Real.exp b * (E * sn) := hT2
      _ = Real.exp (3 * b) * a * (E * Real.exp (-P)) *
            (Real.exp (-(2 * b)) * (a⁻¹ * Real.exp P * sn)) := by
          rw [show Real.exp (3 * b) * a * (E * Real.exp (-P)) *
              (Real.exp (-(2 * b)) * (a⁻¹ * Real.exp P * sn))
              = Real.exp (3 * b) * Real.exp (-(2 * b)) * (a * a⁻¹) *
                (Real.exp (-P) * Real.exp P) * (E * sn) from by ring,
            h1, h2, mul_inv_cancel₀ hane]
          ring
      _ ≤ Real.exp (3 * b) * a * (E * Real.exp (-P)) *
            (Real.exp (-(2 * b)) * (sk * sn)) := by gcongr
      _ ≤ Real.exp (3 * b) * a * (E * Real.exp (-P)) * sm := by gcongr

/-- The estimate of the notes on the approximating measures: for every `m ≥ k` the mass that `μ_m`
gives to a cylinder of length `k` is comparable to `exp(S_k φ(x) - k P(φ))`, with a factor that
does not depend on `m`. -/
theorem exists_gibbsApprox_cylinder_bounds [Nonempty ι] {φ : ι → ℝ → ℝ} {c : ℝ≥0}
    (hφ : ∀ i, LipschitzOnWith c (φ i) C.X) :
    ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ (p : C.attractor) (w : List ι), ∀ x ∈ C.X, ∀ n : ℕ,
      ENNReal.ofReal (a₀⁻¹ * Real.exp (C.birkhoffSum φ w x - w.length * C.pressure φ)) ≤
          C.gibbsApprox φ p (w.length + n) (Subtype.val ⁻¹' C.cylinder w) ∧
        C.gibbsApprox φ p (w.length + n) (Subtype.val ⁻¹' C.cylinder w) ≤
          ENNReal.ofReal (a₀ * Real.exp (C.birkhoffSum φ w x - w.length * C.pressure φ)) := by
  obtain ⟨b, hb0, hb, -⟩ := C.bounded_variation hφ
  obtain ⟨a, ha1, ha⟩ := C.exists_partitionSum_bounds hφ
  have ha₀ : (1 : ℝ) ≤ Real.exp (3 * b) * a :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by positivity)) ha1
  refine ⟨Real.exp (3 * b) * a, ha₀, fun p w x hx n => ?_⟩
  have hpX : (p : ℝ) ∈ C.X := C.attractor_subset_X p.2
  have hu : ∀ v : List ι, (fun _ : List ι => (p : ℝ)) v ∈ C.X := fun _ => hpX
  have hsn : (0 : ℝ) < C.partitionSum φ (fun _ => (p : ℝ)) n := C.partitionSum_pos φ _ _
  have hsm : (0 : ℝ) < C.partitionSum φ (fun _ => (p : ℝ)) (w.length + n) :=
    C.partitionSum_pos φ _ _
  have hE : (0 : ℝ) < Real.exp (C.birkhoffSum φ w x) := Real.exp_pos _
  have hsum : C.partitionSum φ (fun _ => (p : ℝ)) n
      = ∑ h : Fin n → ι, Real.exp (C.birkhoffSum φ (List.ofFn h) (p : ℝ)) := rfl
  have hT1 : Real.exp (-b) * (Real.exp (C.birkhoffSum φ w x) *
      C.partitionSum φ (fun _ => (p : ℝ)) n)
      ≤ ∑ h : Fin n → ι, Real.exp (C.birkhoffSum φ (w ++ List.ofFn h) (p : ℝ)) := by
    rw [hsum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun h _ => ?_
    rw [C.birkhoffSum_append, Real.exp_add, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (C.mul_exp_birkhoffSum_le hb w (C.mapsTo_branchMap _ hpX) hx) (Real.exp_pos _).le
  have hT2 : (∑ h : Fin n → ι, Real.exp (C.birkhoffSum φ (w ++ List.ofFn h) (p : ℝ)))
      ≤ Real.exp b * (Real.exp (C.birkhoffSum φ w x) *
        C.partitionSum φ (fun _ => (p : ℝ)) n) := by
    rw [hsum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun h _ => ?_
    rw [C.birkhoffSum_append, Real.exp_add, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (C.exp_birkhoffSum_le_mul hb w (C.mapsTo_branchMap _ hpX) hx) (Real.exp_pos _).le
  obtain ⟨hm1, hm2⟩ := C.partitionSum_add hb hu w.length n
  obtain ⟨hk1, hk2⟩ := (ha _ hu).2 w.length
  obtain ⟨hlow, hhigh⟩ := div_le_and_le_div_of_bounds ha1 hsn hsm hE hT1 hT2 hm1 hm2 hk1 hk2
  have hexp : Real.exp (C.birkhoffSum φ w x - w.length * C.pressure φ)
      = Real.exp (C.birkhoffSum φ w x) * Real.exp (-(w.length * C.pressure φ)) := by
    rw [← Real.exp_add]
    ring_nf
  rw [C.gibbsApprox_apply_cylinder φ p w n, hexp]
  exact ⟨ENNReal.ofReal_le_ofReal hlow, ENNReal.ofReal_le_ofReal hhigh⟩

/-! ## Theorem 7.7 -/

/-- Theorem 7.7: for a Lipschitz potential the pressure is a limit, independent of the points
chosen in the cylinders, and there is a Gibbs measure on the repeller, a Borel probability measure
whose cylinder masses are comparable to `exp(S_k φ(x) - k P(φ))`. -/
theorem pressure_gibbs [Nonempty ι] {φ : ι → ℝ → ℝ} {c : ℝ≥0}
    (hφ : ∀ i, LipschitzOnWith c (φ i) C.X) :
    (∀ u : List ι → ℝ, (∀ w, u w ∈ C.X) →
        Tendsto (fun k : ℕ => Real.log (C.partitionSum φ u k) / k) atTop (𝓝 (C.pressure φ))) ∧
      ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ C.attractorᶜ = 0 ∧
        ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ w : List ι, ∀ x ∈ C.X,
          ENNReal.ofReal
              (a₀⁻¹ * Real.exp (C.birkhoffSum φ w x - w.length * C.pressure φ)) ≤
                μ (C.cylinder w) ∧
            μ (C.cylinder w) ≤
              ENNReal.ofReal (a₀ * Real.exp (C.birkhoffSum φ w x - w.length * C.pressure φ)) := by
  obtain ⟨a, ha1, ha⟩ := C.exists_partitionSum_bounds hφ
  refine ⟨fun u hu => (ha u hu).1, ?_⟩
  obtain ⟨a₀, ha₀, hbounds⟩ := C.exists_gibbsApprox_cylinder_bounds hφ
  haveI : CompactSpace C.attractor := isCompact_iff_compactSpace.mp C.isCompact_attractor
  obtain ⟨p₀, hp₀⟩ := C.attractor_nonempty
  set p : C.attractor := ⟨p₀, hp₀⟩ with hp
  set ν : ℕ → ProbabilityMeasure C.attractor :=
    fun m => ⟨C.gibbsApprox φ p m, inferInstance⟩ with hν
  obtain ⟨μ, hμ⟩ := exists_clusterPt_of_compactSpace (map ν atTop)
  haveI hL : (𝓝 μ ⊓ map ν atTop).NeBot := hμ
  have htend : Tendsto (id : ProbabilityMeasure C.attractor → ProbabilityMeasure C.attractor)
      (𝓝 μ ⊓ map ν atTop) (𝓝 μ) := tendsto_id.mono_left inf_le_left
  refine ⟨(μ : Measure C.attractor).map Subtype.val,
    inferInstance, ?_,
    a₀, lt_of_lt_of_le one_pos ha₀, fun w x hx => ?_⟩
  · rw [Measure.map_apply measurable_subtype_coe
      (C.isCompact_attractor.isClosed.measurableSet).compl,
      show (Subtype.val : C.attractor → ℝ) ⁻¹' C.attractorᶜ = ∅ from
        Set.eq_empty_iff_forall_notMem.2 fun y hy => hy y.2]
    exact measure_empty
  · rw [Measure.map_apply measurable_subtype_coe (C.isCompact_cylinder w).isClosed.measurableSet]
    have hconv : Tendsto (fun σ : ProbabilityMeasure C.attractor =>
        (σ : Measure C.attractor) (Subtype.val ⁻¹' C.cylinder w)) (𝓝 μ ⊓ map ν atTop)
        (𝓝 ((μ : Measure C.attractor) (Subtype.val ⁻¹' C.cylinder w))) := by
      have h := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto htend
        (C.isClopen_preimage_cylinder w)
      simpa only [id, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
        using ENNReal.tendsto_coe.2 h
    have hev : ∀ᶠ σ : ProbabilityMeasure C.attractor in 𝓝 μ ⊓ map ν atTop,
        ENNReal.ofReal (a₀⁻¹ * Real.exp (C.birkhoffSum φ w x - w.length * C.pressure φ)) ≤
            (σ : Measure C.attractor) (Subtype.val ⁻¹' C.cylinder w) ∧
          (σ : Measure C.attractor) (Subtype.val ⁻¹' C.cylinder w) ≤
            ENNReal.ofReal (a₀ * Real.exp (C.birkhoffSum φ w x - w.length * C.pressure φ)) := by
      refine Filter.Eventually.filter_mono inf_le_right ?_
      rw [eventually_map]
      filter_upwards [eventually_ge_atTop w.length] with m hm
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
      exact hbounds p w x hx n
    exact ⟨ge_of_tendsto hconv (hev.mono fun σ h => h.1),
      le_of_tendsto hconv (hev.mono fun σ h => h.2)⟩

end CookieCutter

end GeometricMeasureTheory
