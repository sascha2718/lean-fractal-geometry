/-
# Section 5.1: The two-scale definition

Assouad dimension compares two scales: the radius `R` of the region inspected and the radius `r` of
the balls resolving it. It is defined here by the critical exponent of the two-scale covering
bound `N_r(E ∩ B(x, R)) ≤ C (R/r)^s`.

| Notes | Lean declaration | Location |
|---|---|---|
| Definition 5.1 (Assouad dimension) | `AssouadDimLE`, `assouadDim` | here |
| Proposition 5.2 (properties) | `assouadDim_mono`, `assouadDim_image`, `upperBoxDim_le_assouadDim`, `assouadDim_union`, `assouadDim_le_finrank` | here |
| Assouad dimension is unchanged by closure | `assouadDim_closure` | here |
| Explicit constants | `assouadDimLE_of_bound`, `assouadDimLE_of_bound_mul` | here |
| Bounded sets need only the small scales | `assouadDimLE_of_bound_of_le_scale` | here |
| Monotonicity of the bound | `AssouadDimLE.mono`, `AssouadDimLE.mono_exponent` | here |
| Unions and images | `AssouadDimLE.union`, `AssouadDimLE.image`, `AssouadDimLE.closure` | here |
| The bound bounds the dimension | `AssouadDimLE.assouadDim_le` | here |
| Extracting a bound | `assouadDimLE_of_assouadDim_lt`, `exists_assouadDimLE_of_ne_top` | here |
-/
import GeometricMeasureTheory.Box.ModifiedBox

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

variable {X : Type*} [MetricSpace X]

/-! ## Definition 5.1 (`def:assouad-dimension`) -/

/-- The two-scale covering bound `N_r(E ∩ B(x, R)) ≤ C (R/r)^s` of Definition 5.1. -/
def AssouadDimLE (E : Set X) (s : ℝ) : Prop :=
  ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ x ∈ E, ∀ r R : ℝ, 0 < r → r < R →
    (Metric.externalCoveringNumber r.toNNReal (E ∩ ball x R) : ℝ≥0∞) ≤
      C * ENNReal.ofReal ((R / r) ^ s)

/-- Definition 5.1 (`def:assouad-dimension`): the Assouad dimension. -/
def assouadDim (E : Set X) : ℝ≥0∞ :=
  ⨅ (s : ℝ≥0) (_ : AssouadDimLE E (s : ℝ)), (s : ℝ≥0∞)

/-! ## Auxiliary covering-number estimates

The two-scale bound is manipulated through three elementary properties of `N_r`: subadditivity in
the set, the cost of passing to a closure, and the effect of a Lipschitz map. -/

private theorem externalCoveringNumber_union_le_aux (r : ℝ≥0) (A B : Set X) :
    Metric.externalCoveringNumber r (A ∪ B) ≤
      Metric.externalCoveringNumber r A + Metric.externalCoveringNumber r B := by
  have key : ∀ C D : Set X, Metric.IsCover r A C → Metric.IsCover r B D →
      Metric.externalCoveringNumber r (A ∪ B) ≤ C.encard + D.encard := by
    intro C D hC hD
    have hcov : Metric.IsCover r (A ∪ B) (C ∪ D) := by
      rintro x (hx | hx)
      · obtain ⟨c, hc, hxc⟩ := hC hx
        exact ⟨c, Or.inl hc, hxc⟩
      · obtain ⟨d, hd, hxd⟩ := hD hx
        exact ⟨d, Or.inr hd, hxd⟩
    exact hcov.externalCoveringNumber_le_encard.trans (Set.encard_union_le C D)
  have hA : Metric.externalCoveringNumber r A
      = ⨅ (C : Set X) (_ : Metric.IsCover r A C), C.encard := rfl
  have hB : Metric.externalCoveringNumber r B
      = ⨅ (D : Set X) (_ : Metric.IsCover r B D), D.encard := rfl
  rw [hA, hB]
  exact ENat.le_iInf₂_add_iInf₂ fun C hC D hD => key C D hC hD

private theorem externalCoveringNumber_closure_le_aux {r r' : ℝ≥0} (hrr' : r < r') (A : Set X) :
    Metric.externalCoveringNumber r' (closure A) ≤ Metric.externalCoveringNumber r A := by
  have hA : Metric.externalCoveringNumber r A
      = ⨅ (C : Set X) (_ : Metric.IsCover r A C), C.encard := rfl
  rw [hA]
  refine le_iInf₂ fun C hC => Metric.IsCover.externalCoveringNumber_le_encard ?_
  intro x hx
  obtain ⟨y, hy, hxy⟩ := EMetric.mem_closure_iff.1 hx ((r' - r : ℝ≥0) : ℝ≥0∞)
    (by simpa using tsub_pos_of_lt hrr')
  obtain ⟨c, hc, hyc⟩ := hC hy
  have hyc' : edist y c ≤ (r : ℝ≥0∞) := hyc
  refine ⟨c, hc, ?_⟩
  calc edist x c ≤ edist x y + edist y c := edist_triangle _ _ _
    _ ≤ ((r' - r : ℝ≥0) : ℝ≥0∞) + (r : ℝ≥0∞) := add_le_add hxy.le hyc'
    _ = (r' : ℝ≥0∞) := by rw [← ENNReal.coe_add, tsub_add_cancel_of_le hrr'.le]

private theorem externalCoveringNumber_image_le_aux {Y : Type*} [MetricSpace Y] {f : X → Y}
    {L r : ℝ≥0} {A : Set X} (hf : LipschitzOnWith L f A) :
    Metric.externalCoveringNumber (2 * L * r) (f '' A) ≤ Metric.externalCoveringNumber r A := by
  refine le_trans ?_ (Metric.coveringNumber_two_mul_le_externalCoveringNumber r A)
  have hA : Metric.coveringNumber (2 * r) A
      = ⨅ (C : Set X) (_ : C ⊆ A) (_ : Metric.IsCover (2 * r) A C), C.encard := rfl
  rw [hA]
  refine le_iInf₂ fun C hCA => le_iInf fun hC => ?_
  refine le_trans (Metric.IsCover.externalCoveringNumber_le_encard ?_) (Set.encard_image_le f C)
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨c, hc, hac⟩ := hC ha
  have hac' : edist a c ≤ ((2 * r : ℝ≥0) : ℝ≥0∞) := hac
  refine ⟨f c, Set.mem_image_of_mem f hc, ?_⟩
  calc edist (f a) (f c) ≤ L * edist a c := hf ha (hCA hc)
    _ ≤ (L : ℝ≥0∞) * ((2 * r : ℝ≥0) : ℝ≥0∞) := by gcongr
    _ = ((2 * L * r : ℝ≥0) : ℝ≥0∞) := by push_cast; ring

/-! ## The two-scale bound -/

/-- The two-scale bound of Definition 5.1 with an explicit constant `C` gives `AssouadDimLE`. Since
the constant of the definition is only required to be at least one, this also says that the
constant may always be enlarged. -/
theorem assouadDimLE_of_bound {E : Set X} {s : ℝ} {C : ℝ≥0}
    (h : ∀ x ∈ E, ∀ r R : ℝ, 0 < r → r < R →
      (Metric.externalCoveringNumber r.toNNReal (E ∩ ball x R) : ℝ≥0∞) ≤
        C * ENNReal.ofReal ((R / r) ^ s)) :
    AssouadDimLE E s := by
  refine ⟨max 1 C, le_max_left _ _, fun x hx r R hr hrR => (h x hx r R hr hrR).trans ?_⟩
  gcongr
  exact_mod_cast le_max_right 1 C

/-- Rescaling the ratio of the two scales by a fixed factor `a` only changes the constant, so it
suffices to prove the two-scale bound in the form `N_r(E ∩ B(x, R)) ≤ C (a R / r)^s`. -/
theorem assouadDimLE_of_bound_mul {E : Set X} {s : ℝ} {C : ℝ≥0} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ x ∈ E, ∀ r R : ℝ, 0 < r → r < R →
      (Metric.externalCoveringNumber r.toNNReal (E ∩ ball x R) : ℝ≥0∞) ≤
        C * ENNReal.ofReal ((a * (R / r)) ^ s)) :
    AssouadDimLE E s := by
  refine assouadDimLE_of_bound (C := C * (a ^ s).toNNReal) fun x hx r R hr hrR => ?_
  refine (h x hx r R hr hrR).trans_eq ?_
  have hdiv : (0 : ℝ) ≤ R / r := div_nonneg (by linarith) hr.le
  rw [Real.mul_rpow ha hdiv, ENNReal.ofReal_mul (Real.rpow_nonneg ha s), ENNReal.coe_mul,
    show (((a ^ s).toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (a ^ s) from rfl]
  ring

/-- The two-scale bound passes to subsets: covering numbers use ambient centres, so restricting the
estimate for the larger set to centres in the smaller one loses nothing. -/
theorem AssouadDimLE.mono {E F : Set X} {s : ℝ} (h : AssouadDimLE F s) (hEF : E ⊆ F) :
    AssouadDimLE E s := by
  obtain ⟨C, hC1, hC⟩ := h
  refine ⟨C, hC1, fun x hx r R hr hrR => le_trans ?_ (hC x (hEF hx) r R hr hrR)⟩
  exact_mod_cast Metric.externalCoveringNumber_mono_set
    (Set.inter_subset_inter_left (ball x R) hEF)

/-- The two-scale bound is inherited by every larger exponent. -/
theorem AssouadDimLE.mono_exponent {E : Set X} {s t : ℝ} (h : AssouadDimLE E s) (hst : s ≤ t) :
    AssouadDimLE E t := by
  obtain ⟨C, hC1, hC⟩ := h
  refine ⟨C, hC1, fun x hx r R hr hrR => (hC x hx r R hr hrR).trans ?_⟩
  gcongr
  exact (one_le_div hr).2 hrR.le

/-- The two-scale bound at exponent `s` bounds the Assouad dimension by `s`. -/
theorem AssouadDimLE.assouadDim_le {E : Set X} {s : ℝ≥0} (h : AssouadDimLE E (s : ℝ)) :
    assouadDim E ≤ s :=
  iInf₂_le s h

/-- An exponent above the Assouad dimension satisfies the two-scale bound. -/
theorem assouadDimLE_of_assouadDim_lt {E : Set X} {s : ℝ≥0} (h : assouadDim E < s) :
    AssouadDimLE E (s : ℝ) := by
  rw [assouadDim, iInf_lt_iff] at h
  obtain ⟨t, ht⟩ := h
  by_cases hE : AssouadDimLE E (t : ℝ)
  · rw [iInf_pos hE] at ht
    exact hE.mono_exponent (by exact_mod_cast ht.le)
  · rw [iInf_neg hE] at ht
    exact absurd ht (by simp)

/-- A set of finite Assouad dimension satisfies the two-scale bound at some exponent. -/
theorem exists_assouadDimLE_of_ne_top {E : Set X} (h : assouadDim E ≠ ⊤) :
    ∃ s : ℝ≥0, AssouadDimLE E (s : ℝ) := by
  by_contra hcon
  simp only [not_exists] at hcon
  exact h (by simp [assouadDim, hcon])

/-- For a bounded set it suffices to check the two-scale bound for `R` below a fixed scale `R₀`
larger than the diameter: a larger region contains all of `E`. -/
theorem assouadDimLE_of_bound_of_le_scale {E : Set X} {s : ℝ} (hs : 0 ≤ s) {C : ℝ≥0} (hC : 1 ≤ C)
    {R₀ : ℝ} (hb : Bornology.IsBounded E) (hR₀ : Metric.diam E < R₀)
    (h : ∀ x ∈ E, ∀ r R : ℝ, 0 < r → r < R → R ≤ R₀ →
      (Metric.externalCoveringNumber r.toNNReal (E ∩ ball x R) : ℝ≥0∞) ≤
        C * ENNReal.ofReal ((R / r) ^ s)) :
    AssouadDimLE E s := by
  refine assouadDimLE_of_bound (C := C) fun x hx r R hr hrR => ?_
  rcases le_or_gt R R₀ with hR | hR
  · exact h x hx r R hr hrR hR
  rcases lt_or_ge r R₀ with hrR₀ | hrR₀
  · have hsub : E ∩ ball x R ⊆ E ∩ ball x R₀ := by
      rintro y ⟨hy, -⟩
      exact ⟨hy, mem_ball.2 ((dist_le_diam_of_mem hb hy hx).trans_lt hR₀)⟩
    have hratio : R₀ / r ≤ R / r := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hR.le (inv_pos.2 hr).le
    calc (Metric.externalCoveringNumber r.toNNReal (E ∩ ball x R) : ℝ≥0∞)
        ≤ (Metric.externalCoveringNumber r.toNNReal (E ∩ ball x R₀) : ℝ≥0∞) := by
          exact_mod_cast Metric.externalCoveringNumber_mono_set hsub
      _ ≤ C * ENNReal.ofReal ((R₀ / r) ^ s) := h x hx r R₀ hr hrR₀ le_rfl
      _ ≤ C * ENNReal.ofReal ((R / r) ^ s) :=
          mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
            (Real.rpow_le_rpow (div_nonneg (by linarith) hr.le) hratio hs))
  · have hone : (Metric.externalCoveringNumber r.toNNReal (E ∩ ball x R) : ℝ≥0∞) ≤ 1 := by
      have hcount : Metric.externalCoveringNumber r.toNNReal (E ∩ ball x R) ≤ 1 := by
        refine Metric.externalCoveringNumber_le_one_of_ediam_le ?_
        refine le_trans (Metric.ediam_mono Set.inter_subset_left) (Metric.ediam_le ?_)
        intro y hy z hz
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal
          ((dist_le_diam_of_mem hb hy hz).trans (hR₀.le.trans hrR₀))
      exact_mod_cast hcount
    refine hone.trans ?_
    have hC' : (1 : ℝ≥0∞) ≤ (C : ℝ≥0∞) := by exact_mod_cast hC
    have hpow : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((R / r) ^ s) :=
      ENNReal.one_le_ofReal.2 (Real.one_le_rpow ((one_le_div hr).2 hrR.le) hs)
    calc (1 : ℝ≥0∞) = 1 * 1 := (one_mul 1).symm
      _ ≤ C * ENNReal.ofReal ((R / r) ^ s) := mul_le_mul' hC' hpow

@[simp]
theorem assouadDim_empty : assouadDim (∅ : Set X) = 0 := by
  have h : AssouadDimLE (∅ : Set X) ((0 : ℝ≥0) : ℝ) := ⟨1, le_rfl, by simp⟩
  simpa using h.assouadDim_le

/-! ## Proposition 5.2 (`thm:assouad-basic-properties`) -/

theorem assouadDim_mono {E F : Set X} (h : E ⊆ F) : assouadDim E ≤ assouadDim F :=
  le_iInf₂ fun _ hs => (hs.mono h).assouadDim_le

/-- The two-scale bound is transported by a map that is Lipschitz on `E` and contracts distances
there by at most a fixed factor: the preimage of `f '' E ∩ B(f x, R)` lies in `E ∩ B(x, K R)`, and a
cover of the latter by balls of radius `r / (2 L)` maps forward to a cover by balls of radius
`r`. -/
theorem AssouadDimLE.image {Y : Type*} [MetricSpace Y] {f : X → Y} {K L : ℝ≥0} {E : Set X} {s : ℝ}
    (h : AssouadDimLE E s) (hL : LipschitzOnWith L f E)
    (hK : ∀ x ∈ E, ∀ y ∈ E, dist x y ≤ K * dist (f x) (f y)) :
    AssouadDimLE (f '' E) s := by
  obtain ⟨C, hC1, hC⟩ := h
  set L' : ℝ≥0 := max L 1 with hL'def
  set K' : ℝ≥0 := max K 1 with hK'def
  have hL1 : (1 : ℝ≥0) ≤ L' := le_max_right _ _
  have hK1 : (1 : ℝ≥0) ≤ K' := le_max_right _ _
  have hL1' : (1 : ℝ) ≤ (L' : ℝ) := by exact_mod_cast hL1
  have hK1' : (1 : ℝ) ≤ (K' : ℝ) := by exact_mod_cast hK1
  have hL0 : (0 : ℝ) < (L' : ℝ) := lt_of_lt_of_le zero_lt_one hL1'
  have hK0 : (0 : ℝ) < (K' : ℝ) := lt_of_lt_of_le zero_lt_one hK1'
  have hL' : LipschitzOnWith L' f E := hL.weaken (le_max_left _ _)
  have hK' : ∀ x ∈ E, ∀ y ∈ E, dist x y ≤ (K' : ℝ) * dist (f x) (f y) := by
    intro x hx y hy
    refine (hK x hx y hy).trans ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left K 1) dist_nonneg
  refine assouadDimLE_of_bound_mul (C := C) (a := 2 * (L' : ℝ) * (K' : ℝ)) (by positivity) ?_
  rintro y hy r R hr hrR
  obtain ⟨x, hxE, rfl⟩ := hy
  set r' : ℝ := r / (2 * (L' : ℝ)) with hr'def
  have hr' : 0 < r' := by positivity
  have hsub : (f '' E) ∩ ball (f x) R ⊆ f '' (E ∩ ball x ((K' : ℝ) * R)) := by
    rintro _ ⟨⟨z, hz, rfl⟩, hzb⟩
    refine ⟨z, ⟨hz, mem_ball.2 ?_⟩, rfl⟩
    calc dist z x ≤ (K' : ℝ) * dist (f z) (f x) := hK' z hz x hxE
      _ < (K' : ℝ) * R := mul_lt_mul_of_pos_left (mem_ball.1 hzb) hK0
  have hradius : 2 * L' * r'.toNNReal = r.toNNReal := by
    refine NNReal.coe_injective ?_
    push_cast [Real.coe_toNNReal _ hr'.le, Real.coe_toNNReal _ hr.le]
    rw [hr'def]
    field_simp
  have himg : Metric.externalCoveringNumber r.toNNReal (f '' (E ∩ ball x ((K' : ℝ) * R)))
      ≤ Metric.externalCoveringNumber r'.toNNReal (E ∩ ball x ((K' : ℝ) * R)) := by
    rw [← hradius]
    exact externalCoveringNumber_image_le_aux (hL'.mono Set.inter_subset_left)
  have hr'lt : r' < (K' : ℝ) * R := by
    have h1 : r' ≤ r := by
      rw [hr'def, div_le_iff₀ (by positivity)]
      nlinarith
    have h2 : R ≤ (K' : ℝ) * R := by nlinarith [hr.trans hrR]
    linarith
  have harg : (((K' : ℝ) * R) / r') = 2 * (L' : ℝ) * (K' : ℝ) * (R / r) := by
    rw [hr'def]
    field_simp
  calc (Metric.externalCoveringNumber r.toNNReal ((f '' E) ∩ ball (f x) R) : ℝ≥0∞)
      ≤ (Metric.externalCoveringNumber r.toNNReal (f '' (E ∩ ball x ((K' : ℝ) * R))) : ℝ≥0∞) := by
        exact_mod_cast Metric.externalCoveringNumber_mono_set hsub
    _ ≤ (Metric.externalCoveringNumber r'.toNNReal (E ∩ ball x ((K' : ℝ) * R)) : ℝ≥0∞) := by
        exact_mod_cast himg
    _ ≤ C * ENNReal.ofReal ((((K' : ℝ) * R) / r') ^ s) :=
        hC x hxE r' ((K' : ℝ) * R) hr' hr'lt
    _ = C * ENNReal.ofReal ((2 * (L' : ℝ) * (K' : ℝ) * (R / r)) ^ s) := by rw [harg]

/-- Proposition 5.2 (`thm:assouad-basic-properties`): Assouad dimension is bi-Lipschitz
invariant. -/
theorem assouadDim_image {Y : Type*} [MetricSpace Y] {f : X → Y} {K L : ℝ≥0} {E : Set X}
    (hL : LipschitzOnWith L f E) (hK : AntilipschitzWith K (E.restrict f)) :
    assouadDim (f '' E) = assouadDim E := by
  have hKd : ∀ x ∈ E, ∀ y ∈ E, dist x y ≤ K * dist (f x) (f y) := by
    intro x hx y hy
    exact hK.le_mul_dist ⟨x, hx⟩ ⟨y, hy⟩
  refine le_antisymm (le_iInf₂ fun s hs => (hs.image hL hKd).assouadDim_le) ?_
  rcases E.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  have : Nonempty X := ⟨x₀⟩
  have hinj : Set.InjOn f E := by
    intro x hx y hy hxy
    have hd := hKd x hx y hy
    rw [hxy] at hd
    simpa using dist_le_zero.1 (by simpa using hd)
  set g : Y → X := Function.invFunOn f E with hgdef
  have hgmem : ∀ u ∈ f '' E, g u ∈ E := by
    rintro _ ⟨z, hz, rfl⟩
    exact Function.invFunOn_mem ⟨z, hz, rfl⟩
  have hgf : ∀ u ∈ f '' E, f (g u) = u := by
    rintro _ ⟨z, hz, rfl⟩
    exact Function.invFunOn_eq ⟨z, hz, rfl⟩
  have hgimage : g '' (f '' E) = E := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      exact hgmem u hu
    · intro z hz
      exact ⟨f z, ⟨z, hz, rfl⟩, hinj.leftInvOn_invFunOn hz⟩
  have hgL : LipschitzOnWith K g (f '' E) := by
    refine LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_
    have hd := hKd (g u) (hgmem u hu) (g v) (hgmem v hv)
    rwa [hgf u hu, hgf v hv] at hd
  have hgK : ∀ u ∈ f '' E, ∀ v ∈ f '' E, dist u v ≤ L * dist (g u) (g v) := by
    intro u hu v hv
    have hd := hL.dist_le_mul (g u) (hgmem u hu) (g v) (hgmem v hv)
    rwa [hgf u hu, hgf v hv] at hd
  refine le_iInf₂ fun s hs => ?_
  have hle := (hs.image hgL hgK).assouadDim_le
  rwa [hgimage] at hle

/-- Proposition 5.2 (`thm:assouad-basic-properties`): the upper box dimension of a bounded set is
at most its Assouad dimension. -/
theorem upperBoxDim_le_assouadDim {E : Set X} (hb : Bornology.IsBounded E) (hne : E.Nonempty) :
    upperBoxDim E ≤ assouadDim E := by
  refine le_iInf₂ fun s hs => ?_
  obtain ⟨C, hC1, hC⟩ := hs
  obtain ⟨x, hx⟩ := hne
  set R : ℝ := Metric.diam E + 1 with hRdef
  have hR : 0 < R := by
    have := Metric.diam_nonneg (s := E)
    linarith
  have hEsub : E ⊆ ball x R := by
    intro y hy
    refine mem_ball.2 ?_
    have := dist_le_diam_of_mem hb hy hx
    linarith
  have hRs : (0 : ℝ) < R ^ (s : ℝ) := Real.rpow_pos_of_pos hR _
  refine upperBoxDim_le_of_forall (C := C * (R ^ (s : ℝ)).toNNReal) ?_ ?_
  · exact mul_pos (lt_of_lt_of_le zero_lt_one hC1) (Real.toNNReal_pos.2 hRs)
  · filter_upwards [Ioo_mem_nhdsGT hR] with r hr
    have hEeq : E ∩ ball x R = E := Set.inter_eq_left.2 hEsub
    have hbound := hC x hx r R hr.1 hr.2
    rw [hEeq] at hbound
    refine hbound.trans_eq ?_
    rw [Real.div_rpow hR.le hr.1.le, div_eq_mul_inv, ← Real.rpow_neg hr.1.le,
      ENNReal.ofReal_mul hRs.le, ENNReal.coe_mul,
      show (((R ^ (s : ℝ)).toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (R ^ (s : ℝ)) from rfl]
    ring

/-- The two-scale bound is stable under finite unions: a point of `Eᵢ ∩ B(x, R)` recentres the
region at a point of `Eᵢ` at the cost of doubling `R`. -/
theorem AssouadDimLE.union {E F : Set X} {s : ℝ} (hE : AssouadDimLE E s)
    (hF : AssouadDimLE F s) : AssouadDimLE (E ∪ F) s := by
  obtain ⟨C₁, hC₁1, hC₁⟩ := hE
  obtain ⟨C₂, hC₂1, hC₂⟩ := hF
  refine assouadDimLE_of_bound_mul (C := C₁ + C₂) (a := 2) (by norm_num) ?_
  intro x _ r R hr hrR
  have key : ∀ (A : Set X) (C : ℝ≥0), (∀ y ∈ A, ∀ r R : ℝ, 0 < r → r < R →
        (Metric.externalCoveringNumber r.toNNReal (A ∩ ball y R) : ℝ≥0∞) ≤
          C * ENNReal.ofReal ((R / r) ^ s)) →
      (Metric.externalCoveringNumber r.toNNReal (A ∩ ball x R) : ℝ≥0∞) ≤
        C * ENNReal.ofReal ((2 * (R / r)) ^ s) := by
    intro A C hA
    rcases (A ∩ ball x R).eq_empty_or_nonempty with hempty | ⟨y, hyA, hyb⟩
    · rw [hempty]
      simp
    · have hsub : A ∩ ball x R ⊆ A ∩ ball y (2 * R) := by
        rintro z ⟨hz, hzb⟩
        refine ⟨hz, mem_ball.2 ?_⟩
        calc dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
          _ < R + R := by
              refine add_lt_add (mem_ball.1 hzb) ?_
              rw [dist_comm]
              exact mem_ball.1 hyb
          _ = 2 * R := by ring
      calc (Metric.externalCoveringNumber r.toNNReal (A ∩ ball x R) : ℝ≥0∞)
          ≤ (Metric.externalCoveringNumber r.toNNReal (A ∩ ball y (2 * R)) : ℝ≥0∞) := by
            exact_mod_cast Metric.externalCoveringNumber_mono_set hsub
        _ ≤ C * ENNReal.ofReal (((2 * R) / r) ^ s) :=
            hA y hyA r (2 * R) hr (by linarith)
        _ = C * ENNReal.ofReal ((2 * (R / r)) ^ s) := by rw [mul_div_assoc]
  have hunion : (E ∪ F) ∩ ball x R = (E ∩ ball x R) ∪ (F ∩ ball x R) :=
    Set.union_inter_distrib_right E F (ball x R)
  rw [hunion]
  calc (Metric.externalCoveringNumber r.toNNReal ((E ∩ ball x R) ∪ (F ∩ ball x R)) : ℝ≥0∞)
      ≤ ((Metric.externalCoveringNumber r.toNNReal (E ∩ ball x R) : ℝ≥0∞)
        + (Metric.externalCoveringNumber r.toNNReal (F ∩ ball x R) : ℝ≥0∞)) := by
        exact_mod_cast externalCoveringNumber_union_le_aux r.toNNReal (E ∩ ball x R)
          (F ∩ ball x R)
    _ ≤ C₁ * ENNReal.ofReal ((2 * (R / r)) ^ s) + C₂ * ENNReal.ofReal ((2 * (R / r)) ^ s) :=
        add_le_add (key E C₁ hC₁) (key F C₂ hC₂)
    _ = ((C₁ + C₂ : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal ((2 * (R / r)) ^ s) := by
        rw [← add_mul, ENNReal.coe_add]

/-- Proposition 5.2 (`thm:assouad-basic-properties`): Assouad dimension is finitely stable. -/
theorem assouadDim_union (E F : Set X) :
    assouadDim (E ∪ F) = max (assouadDim E) (assouadDim F) := by
  refine le_antisymm ?_ (max_le (assouadDim_mono Set.subset_union_left)
    (assouadDim_mono Set.subset_union_right))
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨t, hmt, ht⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hcon
  rw [max_lt_iff] at hmt
  exact absurd ((assouadDimLE_of_assouadDim_lt hmt.1).union
    (assouadDimLE_of_assouadDim_lt hmt.2)).assouadDim_le (not_le.2 ht)

/-- In a `d`-dimensional real normed space, a ball of radius `R` meets any set in a set covered by
`(4 R / r)^d` balls of radius `r`: disjoint balls of radius `r/2` around a maximal `r`-separated
subset fit inside a ball of radius `2 R`. -/
private theorem externalCoveringNumber_inter_ball_le_aux {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (E : Set V) (x : V) {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) :
    (Metric.externalCoveringNumber r.toNNReal (E ∩ ball x R) : ℝ≥0∞) ≤
      ENNReal.ofReal ((4 * (R / r)) ^ (Module.finrank ℝ V : ℝ)) := by
  classical
  borelize V
  set μ : MeasureTheory.Measure V := (Module.finBasis ℝ V).addHaar with hμ
  have hR : 0 < R := hr.trans hrR
  have hAbounded : Bornology.IsBounded (E ∩ ball x R) :=
    Metric.isBounded_ball.subset Set.inter_subset_right
  have hAtb : TotallyBounded (E ∩ ball x R) :=
    TotallyBounded.subset subset_closure hAbounded.isCompact_closure.totallyBounded
  have hrnn : 0 < r.toNNReal := Real.toNNReal_pos.2 hr
  obtain ⟨S, hSA, hSfin, hSsep, hScard⟩ :=
    Metric.exists_set_encard_eq_packingNumber (packingNumber_ne_top hAtb hrnn)
  -- the count is at most the cardinality of a maximal separated set
  have hNS : Metric.externalCoveringNumber r.toNNReal (E ∩ ball x R) ≤ S.encard := by
    rw [hScard]
    exact (Metric.externalCoveringNumber_le_coveringNumber _ _).trans
      (Metric.coveringNumber_le_packingNumber _ _)
  -- the balls of radius `r/2` around `S` are disjoint and lie in `B(x, 2R)`
  have hsep : ∀ c ∈ S, ∀ c' ∈ S, c ≠ c' → r < dist c c' := by
    intro c hc c' hc' hne
    have hlt : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < edist c c' := hSsep hc hc' hne
    rw [edist_dist] at hlt
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr.le).1 hlt
  have hdisj : (hSfin.toFinset : Set V).PairwiseDisjoint fun c => ball c (r / 2) := by
    rw [hSfin.coe_toFinset]
    intro c hc c' hc' hne
    refine Metric.ball_disjoint_ball ?_
    have := hsep c hc c' hc' hne
    linarith
  have hballsub : ∀ c ∈ S, ball c (r / 2) ⊆ ball x (2 * R) := by
    intro c hc
    refine Metric.ball_subset_ball' ?_
    have hcb : dist c x < R := mem_ball.1 (hSA hc).2
    linarith
  -- a volume comparison bounds the cardinality
  have hμpos : μ (ball (0 : V) 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hμtop : μ (ball (0 : V) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hsum : ∑ c ∈ hSfin.toFinset, μ (ball c (r / 2))
      = (hSfin.toFinset.card : ℝ≥0∞) *
        (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ V) * μ (ball (0 : V) 1)) := by
    rw [Finset.sum_congr rfl fun c _ =>
      MeasureTheory.Measure.addHaar_ball_of_pos μ c (by positivity : (0 : ℝ) < r / 2),
      Finset.sum_const, nsmul_eq_mul]
  have hunion : μ (⋃ c ∈ hSfin.toFinset, ball c (r / 2)) ≤ μ (ball x (2 * R)) :=
    measure_mono (Set.iUnion₂_subset fun c hc => hballsub c (by simpa using hc))
  rw [MeasureTheory.measure_biUnion_finset hdisj fun c _ => measurableSet_ball, hsum,
    MeasureTheory.Measure.addHaar_ball_of_pos μ x (by positivity : (0 : ℝ) < 2 * R),
    ← mul_assoc] at hunion
  have hcancel : (hSfin.toFinset.card : ℝ≥0∞) * ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ V)
      ≤ ENNReal.ofReal ((2 * R) ^ Module.finrank ℝ V) :=
    (ENNReal.mul_le_mul_iff_left hμpos hμtop).1 hunion
  have hprod : ENNReal.ofReal ((4 * (R / r)) ^ Module.finrank ℝ V) *
      ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ V)
      = ENNReal.ofReal ((2 * R) ^ Module.finrank ℝ V) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]
    congr 2
    field_simp
    ring
  have hcard : (hSfin.toFinset.card : ℝ≥0∞)
      ≤ ENNReal.ofReal ((4 * (R / r)) ^ Module.finrank ℝ V) := by
    rw [← hprod] at hcancel
    exact (ENNReal.mul_le_mul_iff_left (by positivity) (by simp)).1 hcancel
  calc (Metric.externalCoveringNumber r.toNNReal (E ∩ ball x R) : ℝ≥0∞)
      ≤ (S.encard : ℝ≥0∞) := by exact_mod_cast hNS
    _ = (hSfin.toFinset.card : ℝ≥0∞) := by
        rw [hSfin.encard_eq_coe_toFinset_card]
        exact ENat.toENNReal_coe _
    _ ≤ ENNReal.ofReal ((4 * (R / r)) ^ Module.finrank ℝ V) := hcard
    _ = ENNReal.ofReal ((4 * (R / r)) ^ (Module.finrank ℝ V : ℝ)) := by
        rw [Real.rpow_natCast]

/-- Proposition 5.2 (`thm:assouad-basic-properties`): a subset of a finite-dimensional real normed
space has Assouad dimension at most the dimension of the space. -/
theorem assouadDim_le_finrank {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (E : Set V) : assouadDim E ≤ Module.finrank ℝ V := by
  have h : AssouadDimLE E ((Module.finrank ℝ V : ℝ≥0) : ℝ) := by
    refine assouadDimLE_of_bound_mul (C := 1) (a := 4) (by norm_num) ?_
    intro x _ r R hr hrR
    simpa using externalCoveringNumber_inter_ball_le_aux E x hr hrR
  simpa using h.assouadDim_le

/-- The two-scale bound passes to the closure: a cover of `E ∩ B(y, 3R)` by balls of radius `r/2`
becomes a cover of the closure by balls of radius `r`. -/
theorem AssouadDimLE.closure {E : Set X} {s : ℝ} (h : AssouadDimLE E s) :
    AssouadDimLE (_root_.closure E) s := by
  obtain ⟨C, hC1, hC⟩ := h
  refine assouadDimLE_of_bound_mul (C := C) (a := 6) (by norm_num) ?_
  intro x hx r R hr hrR
  have hR : 0 < R := hr.trans hrR
  obtain ⟨y, hyE, hxy⟩ := Metric.mem_closure_iff.1 hx R hR
  have hsub : _root_.closure E ∩ ball x R ⊆ _root_.closure (E ∩ ball y (3 * R)) := by
    rintro z ⟨hz, hzb⟩
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    obtain ⟨w, hwE, hwz⟩ := Metric.mem_closure_iff.1 hz (min ε R) (lt_min hε hR)
    refine ⟨w, ⟨hwE, mem_ball.2 ?_⟩, lt_of_lt_of_le hwz (min_le_left _ _)⟩
    have h1 : dist w z < R := by
      rw [dist_comm]
      exact lt_of_lt_of_le hwz (min_le_right _ _)
    have h2 : dist z x < R := mem_ball.1 hzb
    calc dist w y ≤ dist w z + dist z x + dist x y := dist_triangle4 _ _ _ _
      _ < R + R + R := add_lt_add (add_lt_add h1 h2) hxy
      _ = 3 * R := by ring
  have hhalf : (r / 2).toNNReal < r.toNNReal :=
    (Real.toNNReal_lt_toNNReal_iff hr).2 (by linarith)
  have harg : ((3 * R) / (r / 2)) = 6 * (R / r) := by
    field_simp
    ring
  calc (Metric.externalCoveringNumber r.toNNReal (_root_.closure E ∩ ball x R) : ℝ≥0∞)
      ≤ (Metric.externalCoveringNumber r.toNNReal
          (_root_.closure (E ∩ ball y (3 * R))) : ℝ≥0∞) := by
        exact_mod_cast Metric.externalCoveringNumber_mono_set hsub
    _ ≤ (Metric.externalCoveringNumber (r / 2).toNNReal (E ∩ ball y (3 * R)) : ℝ≥0∞) := by
        exact_mod_cast externalCoveringNumber_closure_le_aux hhalf (E ∩ ball y (3 * R))
    _ ≤ C * ENNReal.ofReal (((3 * R) / (r / 2)) ^ s) :=
        hC y hyE (r / 2) (3 * R) (by positivity) (by linarith)
    _ = C * ENNReal.ofReal ((6 * (R / r)) ^ s) := by rw [harg]

/-- Assouad dimension is unchanged by taking closures, as recorded in the table of Section 5.6. -/
theorem assouadDim_closure (E : Set X) : assouadDim (closure E) = assouadDim E :=
  le_antisymm (le_iInf₂ fun _ hs => hs.closure.assouadDim_le)
    (assouadDim_mono subset_closure)

end GeometricMeasureTheory
