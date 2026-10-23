/-
# Section 6: Cookie cutters

A cookie-cutter system is an expanding map `f` of a compact interval `X` that maps each of finitely
many pairwise disjoint closed subintervals bijectively onto `X`, together with its repeller, the set
of points that never leave those subintervals. The repeller is the attractor of the iterated
function system formed by the inverse branches of `f`, and those branches are the data here. This is
the setting of the paragraph *Expanding maps* of Section 7.2.1 of the notes, it removes the need to
invert a partially defined map, and it allows any finite number of branches where the notes take
two. The notes' map `f` is the inverse of `F i` on the image of the branch `F i`, and a potential
`φ` on `X₁ ∪ ⋯ ∪ X_N` becomes the family `i ↦ φ ∘ F i`.

Words are lists, read so that `F_{i₁ ⋯ i_k} = F_{i₁} ∘ ⋯ ∘ F_{i_k}`, and `X_𝐢 = F_𝐢(X)`. The
repeller is the intersection of the unions of the cylinders of each length.

| Notes | Lean declaration | Location |
|---|---|---|
| The system of Section 6 and its repeller | `CookieCutter`, `CookieCutter.attractor` | here |
| Cylinder sets `X_𝐢` | `CookieCutter.branchMap`, `CookieCutter.cylinder`, `CookieCutter.level` | here |
| `X_𝐢 ⊇ X_{𝐢,1} ∪ X_{𝐢,2}` and `E_k → E` | `CookieCutter.cylinder_append_subset`, `CookieCutter.level_antitone` | here |
| `E` is compact and `E = ⋃ F_i(E)` | `CookieCutter.isCompact_attractor`, `CookieCutter.attractor_eq_iUnion_image` | here |
| `|X_𝐢| ≤ c_max^k |X|` | `CookieCutter.diam_cylinder_le`, `CookieCutter.le_diam_cylinder` | here |
| Uniqueness of the attractor of an IFS | `ContractingWith.fixedPoint` on `TopologicalSpace.NonemptyCompacts` | `Mathlib/Topology/MetricSpace/Contracting.lean` |
-/
import GeometricMeasureTheory.Assouad.Comparison

open MeasureTheory Filter Topology Set Metric

open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

/-- A cookie-cutter system, presented through the inverse branches of its expanding map.

The branches `F i` map the compact interval `Icc a b` into itself, are differentiable there with
derivative `dF i` of absolute value in `[cmin, cmax] ⊆ (0, 1)`, have pairwise disjoint images, and
have log-derivative Lipschitz with constant `L`. The last condition is what the notes obtain from
`f` being twice differentiable, and is the only regularity the theory uses. -/
structure CookieCutter (ι : Type*) where
  /-- The left endpoint of the interval. -/
  a : ℝ
  /-- The right endpoint of the interval. -/
  b : ℝ
  /-- The inverse branches of the expanding map. -/
  F : ι → ℝ → ℝ
  /-- The derivative of each branch. -/
  dF : ι → ℝ → ℝ
  /-- A uniform lower bound for the absolute derivatives. -/
  cmin : ℝ
  /-- A uniform upper bound for the absolute derivatives. -/
  cmax : ℝ
  /-- A Lipschitz constant for the log-derivatives. -/
  L : ℝ≥0
  /-- The interval is nondegenerate. -/
  lt_ab : a < b
  /-- The branches are uniformly expanding for the inverse dynamics. -/
  cmin_pos : 0 < cmin
  /-- The branches are uniform contractions. -/
  cmax_lt_one : cmax < 1
  /-- Each branch maps the interval into itself. -/
  mapsTo_F : ∀ i, MapsTo (F i) (Icc a b) (Icc a b)
  /-- Each branch is differentiable on the interval, with derivative `dF i`. -/
  hasDerivWithinAt_F : ∀ i, ∀ x ∈ Icc a b, HasDerivWithinAt (F i) (dF i x) (Icc a b) x
  /-- The derivatives are bounded below. -/
  le_abs_dF : ∀ i, ∀ x ∈ Icc a b, cmin ≤ |dF i x|
  /-- The derivatives are bounded above. -/
  abs_dF_le : ∀ i, ∀ x ∈ Icc a b, |dF i x| ≤ cmax
  /-- The log-derivatives are Lipschitz, the regularity coming from `f` being `C²`. -/
  lipschitzOnWith_log_abs_dF : ∀ i, LipschitzOnWith L (fun x => Real.log |dF i x|) (Icc a b)
  /-- The branches have pairwise disjoint images. -/
  pairwise_disjoint_image : Pairwise (Function.onFun Disjoint fun i => F i '' Icc a b)

namespace CookieCutter

variable {ι : Type*} (C : CookieCutter ι)

/-- The interval on which the system acts. -/
def X : Set ℝ := Icc C.a C.b

/-- `F_𝐢 = F_{i₁} ∘ ⋯ ∘ F_{i_k}`, the composition of the branches along a word. -/
def branchMap (C : CookieCutter ι) : List ι → ℝ → ℝ
  | [] => id
  | i :: w => C.F i ∘ C.branchMap w

/-- The derivative of `F_𝐢`, given by the chain rule. -/
def branchDeriv (C : CookieCutter ι) : List ι → ℝ → ℝ
  | [], _ => 1
  | i :: w, x => C.dF i (C.branchMap w x) * C.branchDeriv w x

/-- The cylinder set `X_𝐢 = F_𝐢(X)`. -/
def cylinder (w : List ι) : Set ℝ := C.branchMap w '' C.X

/-- `E_k`, the union of the cylinders of length `k`. -/
def level (k : ℕ) : Set ℝ := ⋃ (w : List ι) (_ : w.length = k), C.cylinder w

/-- The repeller of the system, equivalently the attractor of the iterated function system of its
branches. -/
def attractor : Set ℝ := ⋂ k, C.level k

/-! ## The interval -/

theorem X_eq : C.X = Icc C.a C.b := rfl

theorem isCompact_X : IsCompact C.X := isCompact_Icc

theorem X_nonempty : C.X.Nonempty := nonempty_Icc.2 C.lt_ab.le

theorem diam_X : diam C.X = C.b - C.a := by
  rw [X_eq, Real.diam_Icc C.lt_ab.le]

theorem diam_X_pos : 0 < diam C.X := by
  rw [C.diam_X]
  linarith [C.lt_ab]

theorem cmin_le_cmax [Nonempty ι] : C.cmin ≤ C.cmax := by
  obtain ⟨x, hx⟩ := C.X_nonempty
  exact (C.le_abs_dF (Classical.arbitrary ι) x hx).trans (C.abs_dF_le _ x hx)

theorem cmin_lt_one [Nonempty ι] : C.cmin < 1 :=
  C.cmin_le_cmax.trans_lt C.cmax_lt_one

theorem cmax_pos [Nonempty ι] : 0 < C.cmax :=
  C.cmin_pos.trans_le C.cmin_le_cmax

/-! ## Words and branch maps -/

@[simp]
theorem branchMap_nil : C.branchMap ([] : List ι) = id := by simp [branchMap]

@[simp]
theorem branchMap_cons (i : ι) (w : List ι) :
    C.branchMap (i :: w) = C.F i ∘ C.branchMap w := by simp [branchMap]

theorem branchMap_append (v w : List ι) :
    C.branchMap (v ++ w) = C.branchMap v ∘ C.branchMap w := by
  induction v with
  | nil => simp
  | cons i v ih => simp [ih, Function.comp_assoc]

theorem branchMap_take_drop (w : List ι) (j : ℕ) :
    C.branchMap w = C.branchMap (w.take j) ∘ C.branchMap (w.drop j) := by
  rw [← C.branchMap_append, List.take_append_drop]

theorem mapsTo_branchMap (w : List ι) : MapsTo (C.branchMap w) C.X C.X := by
  induction w with
  | nil => simpa using mapsTo_id C.X
  | cons i w ih =>
      rw [branchMap_cons]
      exact (C.mapsTo_F i).comp ih

@[simp]
theorem branchDeriv_nil (x : ℝ) : C.branchDeriv ([] : List ι) x = 1 := by simp [branchDeriv]

@[simp]
theorem branchDeriv_cons (i : ι) (w : List ι) (x : ℝ) :
    C.branchDeriv (i :: w) x = C.dF i (C.branchMap w x) * C.branchDeriv w x := by
  simp [branchDeriv]

theorem hasDerivWithinAt_branchMap (w : List ι) {x : ℝ} (hx : x ∈ C.X) :
    HasDerivWithinAt (C.branchMap w) (C.branchDeriv w x) C.X x := by
  induction w with
  | nil => simpa using hasDerivWithinAt_id x C.X
  | cons i w ih =>
      rw [branchMap_cons, branchDeriv_cons]
      exact HasDerivWithinAt.comp x (C.hasDerivWithinAt_F i _ (C.mapsTo_branchMap w hx)) ih
        (C.mapsTo_branchMap w)

theorem pow_le_abs_branchDeriv (w : List ι) {x : ℝ} (hx : x ∈ C.X) :
    C.cmin ^ w.length ≤ |C.branchDeriv w x| := by
  induction w with
  | nil => simp
  | cons i w ih =>
      rw [branchDeriv_cons, abs_mul, List.length_cons, pow_succ']
      exact mul_le_mul (C.le_abs_dF i _ (C.mapsTo_branchMap w hx)) ih
        (pow_nonneg C.cmin_pos.le _) (abs_nonneg _)

theorem abs_branchDeriv_le_pow (w : List ι) {x : ℝ} (hx : x ∈ C.X) :
    |C.branchDeriv w x| ≤ C.cmax ^ w.length := by
  induction w with
  | nil => simp
  | cons i w ih =>
      have hd := C.abs_dF_le i _ (C.mapsTo_branchMap w hx)
      rw [branchDeriv_cons, abs_mul, List.length_cons, pow_succ']
      exact mul_le_mul hd ih (abs_nonneg _) ((abs_nonneg _).trans hd)

theorem branchDeriv_ne_zero (w : List ι) {x : ℝ} (hx : x ∈ C.X) : C.branchDeriv w x ≠ 0 := by
  refine abs_pos.mp ((pow_pos C.cmin_pos w.length).trans_le ?_)
  exact C.pow_le_abs_branchDeriv w hx

/-! ## The branch maps are bi-Lipschitz -/

theorem abs_sub_branchMap_le (w : List ι) {x y : ℝ} (hx : x ∈ C.X) (hy : y ∈ C.X) :
    |C.branchMap w x - C.branchMap w y| ≤ C.cmax ^ w.length * |x - y| := by
  have hconv : Convex ℝ C.X := by rw [X_eq]; exact convex_Icc _ _
  have hbound : ∀ z ∈ C.X, ‖C.branchDeriv w z‖ ≤ C.cmax ^ w.length := fun z hz => by
    simpa using C.abs_branchDeriv_le_pow w hz
  have h := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => C.hasDerivWithinAt_branchMap w hz) hbound hy hx
  simpa using h

/-- The lower Lipschitz bound for a branch map, proved by the mean value theorem on the
subinterval spanned by the two points. -/
private theorem le_abs_sub_branchMap_of_lt (w : List ι) {x y : ℝ} (hx : x ∈ C.X) (hy : y ∈ C.X)
    (hxy : x < y) : C.cmin ^ w.length * |x - y| ≤ |C.branchMap w x - C.branchMap w y| := by
  rw [X_eq] at hx hy
  have hsub : Icc x y ⊆ C.X := by rw [X_eq]; exact Icc_subset_Icc hx.1 hy.2
  have hcont : ContinuousOn (C.branchMap w) (Icc x y) := fun z hz =>
    ((C.hasDerivWithinAt_branchMap w (hsub hz)).continuousWithinAt).mono hsub
  have hderiv : ∀ z ∈ Ioo x y, HasDerivAt (C.branchMap w) (C.branchDeriv w z) z := by
    intro z hz
    refine (C.hasDerivWithinAt_branchMap w (hsub (Ioo_subset_Icc_self hz))).hasDerivAt ?_
    rw [X_eq]
    exact Icc_mem_nhds (hx.1.trans_lt hz.1) (hz.2.trans_le hy.2)
  obtain ⟨c, hc, hceq⟩ :=
    exists_hasDerivAt_eq_slope (C.branchMap w) (C.branchDeriv w) hxy hcont hderiv
  have hne : y - x ≠ 0 := sub_ne_zero.mpr hxy.ne'
  have heq : C.branchMap w y - C.branchMap w x = C.branchDeriv w c * (y - x) := by
    rw [hceq]; field_simp
  have habs : |C.branchMap w x - C.branchMap w y| = |C.branchDeriv w c| * |x - y| := by
    rw [abs_sub_comm, heq, abs_mul, abs_sub_comm y x]
  rw [habs]
  exact mul_le_mul_of_nonneg_right
    (C.pow_le_abs_branchDeriv w (hsub (Ioo_subset_Icc_self hc))) (abs_nonneg _)

theorem le_abs_sub_branchMap (w : List ι) {x y : ℝ} (hx : x ∈ C.X) (hy : y ∈ C.X) :
    C.cmin ^ w.length * |x - y| ≤ |C.branchMap w x - C.branchMap w y| := by
  rcases lt_trichotomy x y with h | h | h
  · exact C.le_abs_sub_branchMap_of_lt w hx hy h
  · subst h; simp
  · have hle := C.le_abs_sub_branchMap_of_lt w hy hx h
    rwa [abs_sub_comm y x, abs_sub_comm (C.branchMap w y)] at hle

theorem injOn_branchMap (w : List ι) : InjOn (C.branchMap w) C.X := by
  intro x hx y hy hxy
  have h := C.le_abs_sub_branchMap w hx hy
  rw [hxy, sub_self, abs_zero] at h
  have hpos := pow_pos C.cmin_pos w.length
  have h1 : |x - y| ≤ 0 :=
    le_of_mul_le_mul_left (by simpa using h) hpos
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _)))

theorem continuousOn_branchMap (w : List ι) : ContinuousOn (C.branchMap w) C.X :=
  fun _ hz => (C.hasDerivWithinAt_branchMap w hz).continuousWithinAt

/-! ## Cylinders -/

@[simp]
theorem cylinder_nil : C.cylinder ([] : List ι) = C.X := by
  simp [cylinder]

theorem cylinder_subset_X (w : List ι) : C.cylinder w ⊆ C.X :=
  (C.mapsTo_branchMap w).image_subset

theorem cylinder_append_subset (v w : List ι) : C.cylinder (v ++ w) ⊆ C.cylinder v := by
  simp only [cylinder, C.branchMap_append, image_comp]
  exact image_mono (C.mapsTo_branchMap w).image_subset

theorem cylinder_append_eq (v w : List ι) :
    C.cylinder (v ++ w) = C.branchMap v '' C.cylinder w := by
  simp only [cylinder, C.branchMap_append, image_comp]

/-- The cylinder of `i :: 𝐢` is the image under the branch `F i` of the cylinder of `𝐢`. -/
theorem cylinder_cons (i : ι) (w : List ι) : C.cylinder (i :: w) = C.F i '' C.cylinder w := by
  simp only [cylinder, branchMap_cons, image_comp]

theorem isCompact_cylinder (w : List ι) : IsCompact (C.cylinder w) :=
  C.isCompact_X.image_of_continuousOn (C.continuousOn_branchMap w)

theorem cylinder_nonempty (w : List ι) : (C.cylinder w).Nonempty :=
  C.X_nonempty.image _

/-- Every power of `cmax` appearing along a word is positive: a nonempty word supplies a branch,
and the empty word gives the power `1`. -/
private theorem cmax_pow_pos (w : List ι) : 0 < C.cmax ^ w.length := by
  cases w with
  | nil => simp
  | cons i w =>
      haveI : Nonempty ι := ⟨i⟩
      exact pow_pos C.cmax_pos _

theorem diam_cylinder_le (w : List ι) : diam (C.cylinder w) ≤ C.cmax ^ w.length * diam C.X := by
  have hnn : (0 : ℝ) ≤ C.cmax ^ w.length := (C.cmax_pow_pos w).le
  refine Metric.diam_le_of_forall_dist_le (mul_nonneg hnn diam_nonneg) ?_
  rintro u ⟨p, hp, rfl⟩ v ⟨q, hq, rfl⟩
  rw [Real.dist_eq]
  refine (C.abs_sub_branchMap_le w hp hq).trans (mul_le_mul_of_nonneg_left ?_ hnn)
  rw [← Real.dist_eq]
  exact dist_le_diam_of_mem C.isCompact_X.isBounded hp hq

theorem le_diam_cylinder (w : List ι) : C.cmin ^ w.length * diam C.X ≤ diam (C.cylinder w) := by
  have ha : C.a ∈ C.X := by rw [X_eq]; exact left_mem_Icc.mpr C.lt_ab.le
  have hb : C.b ∈ C.X := by rw [X_eq]; exact right_mem_Icc.mpr C.lt_ab.le
  have h3 := dist_le_diam_of_mem (C.isCompact_cylinder w).isBounded
    (mem_image_of_mem (C.branchMap w) ha) (mem_image_of_mem (C.branchMap w) hb)
  rw [Real.dist_eq] at h3
  have hdx : diam C.X = |C.a - C.b| := by
    rw [C.diam_X, abs_sub_comm, abs_of_nonneg (by linarith [C.lt_ab] : (0 : ℝ) ≤ C.b - C.a)]
  rw [hdx]
  exact (C.le_abs_sub_branchMap w ha hb).trans h3

theorem diam_cylinder_pos (w : List ι) : 0 < diam (C.cylinder w) :=
  lt_of_lt_of_le (mul_pos (pow_pos C.cmin_pos _) C.diam_X_pos) (C.le_diam_cylinder w)

/-- A map injective on the interval carries disjoint subsets of it to disjoint sets. -/
private theorem disjoint_image_of_injOn {f : ℝ → ℝ} (hf : InjOn f C.X) {s t : Set ℝ}
    (hs : s ⊆ C.X) (ht : t ⊆ C.X) (h : Disjoint s t) : Disjoint (f '' s) (f '' t) := by
  rw [Set.disjoint_left] at h ⊢
  rintro z ⟨p, hp, rfl⟩ ⟨q, hq, hqz⟩
  exact h hp (hf (ht hq) (hs hp) hqz ▸ hq)

/-- Each branch is injective on the interval. -/
private theorem injOn_F (i : ι) : InjOn (C.F i) C.X := by
  simpa using C.injOn_branchMap [i]

/-- Distinct words of the same length have disjoint cylinders. -/
theorem disjoint_cylinder {v w : List ι} (hlen : v.length = w.length) (hvw : v ≠ w) :
    Disjoint (C.cylinder v) (C.cylinder w) := by
  induction v generalizing w with
  | nil =>
      cases w with
      | nil => exact absurd rfl hvw
      | cons j w => simp at hlen
  | cons i v ih =>
      cases w with
      | nil => simp at hlen
      | cons j w =>
          simp only [List.length_cons] at hlen
          have hlen' : v.length = w.length := by omega
          by_cases hij : i = j
          · subst hij
            have hne : v ≠ w := fun h => hvw (by rw [h])
            rw [C.cylinder_cons, C.cylinder_cons]
            exact C.disjoint_image_of_injOn (C.injOn_F i) (C.cylinder_subset_X v)
              (C.cylinder_subset_X w) (ih hlen' hne)
          · refine Disjoint.mono ?_ ?_ (C.pairwise_disjoint_image hij)
            · rw [C.cylinder_cons]
              exact image_mono (C.cylinder_subset_X v)
            · rw [C.cylinder_cons]
              exact image_mono (C.cylinder_subset_X w)

/-! ## Levels and the attractor -/

/-- A point lies in `E_k` exactly when some word of length `k` has it in its cylinder. -/
theorem mem_level_iff {x : ℝ} {k : ℕ} :
    x ∈ C.level k ↔ ∃ w : List ι, w.length = k ∧ x ∈ C.cylinder w := by
  simp [level]

/-- A point lies in the repeller exactly when it lies in every level set. -/
theorem mem_attractor_iff {x : ℝ} : x ∈ C.attractor ↔ ∀ k, x ∈ C.level k := mem_iInter

@[simp]
theorem level_zero : C.level 0 = C.X := by
  ext x
  rw [C.mem_level_iff]
  constructor
  · rintro ⟨w, hw, hx⟩
    rw [List.length_eq_zero_iff] at hw
    subst hw
    simpa using hx
  · intro hx
    exact ⟨[], rfl, by simpa using hx⟩

theorem level_succ (k : ℕ) : C.level (k + 1) = ⋃ i, C.F i '' C.level k := by
  ext x
  rw [C.mem_level_iff, mem_iUnion]
  constructor
  · rintro ⟨w, hw, hx⟩
    match w, hw, hx with
    | i :: v, hw, hx =>
        rw [C.cylinder_cons] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact ⟨i, y, C.mem_level_iff.mpr ⟨v, by simpa using hw, hy⟩, rfl⟩
  · rintro ⟨i, y, hy, rfl⟩
    obtain ⟨v, hv, hyv⟩ := C.mem_level_iff.mp hy
    exact ⟨i :: v, by simp [hv], by rw [C.cylinder_cons]; exact ⟨y, hyv, rfl⟩⟩

theorem level_subset_X (k : ℕ) : C.level k ⊆ C.X := by
  intro x hx
  obtain ⟨w, -, hxw⟩ := C.mem_level_iff.mp hx
  exact C.cylinder_subset_X w hxw

theorem level_antitone : Antitone C.level := by
  refine antitone_nat_of_succ_le fun k x hx => ?_
  obtain ⟨w, hw, hxw⟩ := C.mem_level_iff.mp hx
  refine C.mem_level_iff.mpr ⟨w.take k, by rw [List.length_take, hw]; omega, ?_⟩
  have h := C.cylinder_append_subset (w.take k) (w.drop k)
  rw [List.take_append_drop] at h
  exact h hxw

theorem isCompact_level [Finite ι] (k : ℕ) : IsCompact (C.level k) := by
  have hfin : {w : List ι | w.length = k}.Finite := List.finite_length_eq ι k
  have hlev : C.level k = ⋃ w ∈ {w : List ι | w.length = k}, C.cylinder w := rfl
  rw [hlev]
  exact hfin.isCompact_biUnion fun w _ => C.isCompact_cylinder w

theorem level_nonempty [Nonempty ι] (k : ℕ) : (C.level k).Nonempty := by
  obtain ⟨x, hx⟩ := C.cylinder_nonempty (List.replicate k (Classical.arbitrary ι))
  exact ⟨x, C.mem_level_iff.mpr ⟨_, by simp, hx⟩⟩

theorem attractor_subset_level (k : ℕ) : C.attractor ⊆ C.level k :=
  iInter_subset _ k

theorem attractor_subset_X : C.attractor ⊆ C.X := by
  have h := C.attractor_subset_level 0
  rwa [C.level_zero] at h

theorem isCompact_attractor [Finite ι] : IsCompact C.attractor :=
  (C.isCompact_level 0).of_isClosed_subset
    (isClosed_iInter fun k => (C.isCompact_level k).isClosed) (C.attractor_subset_level 0)

theorem attractor_nonempty [Finite ι] [Nonempty ι] : C.attractor.Nonempty :=
  IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C.level
    (fun k => C.level_antitone (Nat.le_succ k)) C.level_nonempty (C.isCompact_level 0)
    fun k => (C.isCompact_level k).isClosed

/-- The repeller is invariant under the iterated function system of the branches. -/
theorem attractor_eq_iUnion_image :
    C.attractor = ⋃ i, C.F i '' C.attractor := by
  refine Subset.antisymm (fun x hx => ?_) ?_
  · obtain ⟨u, hu, hxu⟩ := C.mem_level_iff.mp (C.mem_attractor_iff.mp hx 1)
    obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp hu
    have key : ∀ k, x ∈ C.F i '' C.level k := by
      intro k
      obtain ⟨w, hw, hxw⟩ := C.mem_level_iff.mp (C.mem_attractor_iff.mp hx (k + 1))
      match w, hw, hxw with
      | j :: v, hw, hxw =>
          have hxj : x ∈ C.cylinder [j] := by
            have h := C.cylinder_append_subset [j] v
            rw [List.singleton_append] at h
            exact h hxw
          have hij : i = j := by
            by_contra hc
            exact Set.disjoint_left.mp (C.disjoint_cylinder (v := [i]) (w := [j]) rfl
              (by simpa using hc)) hxu hxj
          subst hij
          rw [C.cylinder_cons] at hxw
          obtain ⟨y, hy, rfl⟩ := hxw
          exact ⟨y, C.mem_level_iff.mpr ⟨v, by simpa using hw, hy⟩, rfl⟩
    have hsub : (⋃ k, C.level k) ⊆ C.X := iUnion_subset C.level_subset_X
    have himg : C.F i '' C.attractor = ⋂ k, C.F i '' C.level k :=
      ((C.injOn_F i).mono hsub).image_iInter_eq
    exact mem_iUnion.mpr ⟨i, by rw [himg]; exact mem_iInter.mpr key⟩
  · refine iUnion_subset fun i x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    refine C.mem_attractor_iff.mpr fun k => ?_
    refine C.level_antitone (Nat.le_succ k) ?_
    rw [C.level_succ]
    exact mem_iUnion.mpr ⟨i, y, C.mem_attractor_iff.mp hy k, rfl⟩

theorem mapsTo_branchMap_attractor (w : List ι) :
    MapsTo (C.branchMap w) C.attractor C.attractor := by
  intro x hx
  refine C.mem_attractor_iff.mpr fun k => ?_
  obtain ⟨v, hv, hxv⟩ := C.mem_level_iff.mp (C.mem_attractor_iff.mp hx k)
  have hmem : C.branchMap w x ∈ C.level (w.length + k) :=
    C.mem_level_iff.mpr ⟨w ++ v, by simp [hv], by rw [C.cylinder_append_eq]; exact ⟨x, hxv, rfl⟩⟩
  exact C.level_antitone (Nat.le_add_left k w.length) hmem

/-- Every cylinder meets the repeller. -/
theorem cylinder_inter_attractor_nonempty [Finite ι] [Nonempty ι] (w : List ι) :
    (C.cylinder w ∩ C.attractor).Nonempty := by
  obtain ⟨y, hy⟩ := C.attractor_nonempty
  exact ⟨C.branchMap w y, ⟨y, C.attractor_subset_X hy, rfl⟩, C.mapsTo_branchMap_attractor w hy⟩

/-- Every point of the repeller lies in a cylinder of each length. -/
theorem exists_cylinder_mem [Nonempty ι] {x : ℝ} (hx : x ∈ C.attractor) (k : ℕ) :
    ∃ w : List ι, w.length = k ∧ x ∈ C.cylinder w :=
  C.mem_level_iff.mp (C.attractor_subset_level k hx)

end CookieCutter

end GeometricMeasureTheory
