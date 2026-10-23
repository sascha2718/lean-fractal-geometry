/-
# Section 8: Quasi-self-similar sets

Corollary 6.6 is promoted to a definition: a set is quasi-self-similar with distortion `D` if every
ball centred on it receives a bounded-distortion copy of the whole set, scaled by the radius. The
packings of such a set are bounded at every scale, so its Hausdorff measure at its dimension is
finite. The notes work in `ℝ^d`; the statements here are for a metric space, using that a compact
set is totally bounded.

| Notes | Lean declaration | Location |
|---|---|---|
| Definition 8.1 (quasi-self-similar) | `IsQuasiSelfSimilar` | here |
| Theorem 8.2 (packings are bounded, `𝓗^s(E) ≤ 4^s D^s`) | `qss_packing_finite` | here |
| Remark 8.3 (only the lower bound is used) | `qss_packing_finite` takes `IsQuasiSelfSimilarLower` | here |
| Cookie cutters are quasi-self-similar | `CookieCutter.isQuasiSelfSimilar_attractor` | here |
| The Moran construction behind Theorem 8.2 | `wordComp`, `le_dimH_of_separated_maps` | here |
| Theorem 8.2 at a single scale | `qss_packing_bound` | here |
| Packing numbers | `Metric.packingNumber`, `Metric.IsSeparated` | `Mathlib/Topology/MetricSpace/CoveringNumbers.lean` |
-/
import GeometricMeasureTheory.Pressure.Dimension
import GeometricMeasureTheory.QuasiSelfSimilar.SelfSimilar

open MeasureTheory Filter Topology Set Metric

open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Definition 8.1: `E` is quasi-self-similar with distortion `D` if every ball centred on `E` of
radius less than the diameter of `E` receives a copy of `E` under a map that distorts distances by
a factor between `D⁻¹ r` and `D r`. -/
def IsQuasiSelfSimilar (D : ℝ) (E : Set X) : Prop :=
  ∀ x ∈ E, ∀ r : ℝ, 0 < r → r < diam E →
    ∃ g : X → X, MapsTo g E (E ∩ closedBall x r) ∧
      ∀ y ∈ E, ∀ z ∈ E,
        D⁻¹ * r * dist y z ≤ dist (g y) (g z) ∧ dist (g y) (g z) ≤ D * r * dist y z

/-- Remark 8.3: only the lower bound of Definition 8.1 is used for Theorem 8.2. -/
def IsQuasiSelfSimilarLower (D : ℝ) (E : Set X) : Prop :=
  ∀ x ∈ E, ∀ r : ℝ, 0 < r → r < diam E →
    ∃ g : X → X, MapsTo g E (E ∩ closedBall x r) ∧
      ∀ y ∈ E, ∀ z ∈ E, D⁻¹ * r * dist y z ≤ dist (g y) (g z)

omit [MeasurableSpace X] [BorelSpace X] in
theorem IsQuasiSelfSimilar.lower {D : ℝ} {E : Set X} (h : IsQuasiSelfSimilar D E) :
    IsQuasiSelfSimilarLower D E := by
  intro x hx r hr hrd
  obtain ⟨g, hg, hbound⟩ := h x hx r hr hrd
  exact ⟨g, hg, fun y hy z hz => (hbound y hy z hz).1⟩

/-! ## Theorem 8.2 -/

/-! ### Iterated compositions along words

The proof of Theorem 8.2 turns a packing of `E` into an iterated function system. These lemmas
record the composition of the maps of such a system along a finite word. -/

/-- The composition of a family of maps along a word, the first letter of the word acting last:
`wordComp g [i₁, …, i_q] = g i₁ ∘ ⋯ ∘ g i_q`. -/
def wordComp {Y ι : Type*} (g : ι → Y → Y) (w : List ι) : Y → Y :=
  fun y => w.foldr (fun i z => g i z) y

/-- The empty word gives the identity. -/
@[simp] theorem wordComp_nil {Y ι : Type*} (g : ι → Y → Y) : wordComp g [] = id := rfl

/-- The first letter of a word acts last. -/
@[simp] theorem wordComp_cons {Y ι : Type*} (g : ι → Y → Y) (i : ι) (w : List ι) :
    wordComp g (i :: w) = g i ∘ wordComp g w := rfl

/-- Concatenating words composes the associated maps. -/
theorem wordComp_append {Y ι : Type*} (g : ι → Y → Y) (w v : List ι) :
    wordComp g (w ++ v) = wordComp g w ∘ wordComp g v := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.cons_append, wordComp_cons, ih, Function.comp_assoc]

/-- If every map of the family sends `E` into itself then so does every composition. -/
theorem mapsTo_wordComp {Y ι : Type*} {g : ι → Y → Y} {E : Set Y} (hg : ∀ i, MapsTo (g i) E E)
    (w : List ι) : MapsTo (wordComp g w) E E := by
  induction w with
  | nil => simpa using mapsTo_id E
  | cons i w ih => exact (hg i).comp ih

section Words

variable {Y ι : Type*} [PseudoMetricSpace Y]

/-- Iterating a lower Lipschitz bound along a word of length `n` gives the bound with `q ^ n`. -/
theorem mul_dist_le_dist_wordComp {g : ι → Y → Y} {E : Set Y} {q : ℝ} (hq : 0 ≤ q)
    (hg : ∀ i, MapsTo (g i) E E)
    (hlow : ∀ i, ∀ y ∈ E, ∀ z ∈ E, q * dist y z ≤ dist (g i y) (g i z)) (w : List ι)
    {y z : Y} (hy : y ∈ E) (hz : z ∈ E) :
    q ^ w.length * dist y z ≤ dist (wordComp g w y) (wordComp g w z) := by
  induction w with
  | nil => simp
  | cons i w ih =>
      have hy' := mapsTo_wordComp hg w hy
      have hz' := mapsTo_wordComp hg w hz
      calc q ^ (i :: w).length * dist y z = q * (q ^ w.length * dist y z) := by
            rw [List.length_cons, pow_succ]; ring
        _ ≤ q * dist (wordComp g w y) (wordComp g w z) := mul_le_mul_of_nonneg_left ih hq
        _ ≤ dist (g i (wordComp g w y)) (g i (wordComp g w z)) := hlow i _ hy' _ hz'
        _ = dist (wordComp g (i :: w) y) (wordComp g (i :: w) z) := rfl

/-- Distinct words of the same length `n` have images separated by at least `d * q ^ n`, where `d`
separates the images of distinct single maps and `q` is the lower Lipschitz constant. -/
theorem le_dist_of_wordComp_ne {g : ι → Y → Y} {E : Set Y} {q d : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hd : 0 ≤ d) (hg : ∀ i, MapsTo (g i) E E)
    (hlow : ∀ i, ∀ y ∈ E, ∀ z ∈ E, q * dist y z ≤ dist (g i y) (g i z))
    (hsep : ∀ i j, i ≠ j → ∀ y ∈ E, ∀ z ∈ E, d ≤ dist (g i y) (g j z)) :
    ∀ {w w' : List ι}, w.length = w'.length → w ≠ w' → ∀ {y z : Y},
      y ∈ wordComp g w '' E → z ∈ wordComp g w' '' E → d * q ^ w.length ≤ dist y z := by
  intro w
  induction w with
  | nil =>
      intro w' hlen hne y z _ _
      exact absurd (List.eq_nil_of_length_eq_zero hlen.symm).symm hne
  | cons i u ih =>
      intro w' hlen hne y z hy hz
      match w' with
      | [] => simp at hlen
      | i' :: u' =>
        obtain ⟨a, ha, rfl⟩ := hy
        obtain ⟨b, hb, rfl⟩ := hz
        have hlen' : u.length = u'.length := by simpa using hlen
        have hau : wordComp g u a ∈ E := mapsTo_wordComp hg u ha
        have hbu : wordComp g u' b ∈ E := mapsTo_wordComp hg u' hb
        simp only [wordComp_cons, Function.comp_apply]
        by_cases hii : i = i'
        · subst hii
          have hne' : u ≠ u' := fun h => hne (by rw [h])
          have key : d * q ^ u.length ≤ dist (wordComp g u a) (wordComp g u' b) :=
            ih hlen' hne' ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
          calc d * q ^ (i :: u).length = q * (d * q ^ u.length) := by
                rw [List.length_cons, pow_succ]; ring
            _ ≤ q * dist (wordComp g u a) (wordComp g u' b) := mul_le_mul_of_nonneg_left key hq0
            _ ≤ _ := hlow i _ hau _ hbu
        · calc d * q ^ (i :: u).length ≤ d * 1 :=
                mul_le_mul_of_nonneg_left (pow_le_one₀ hq0 hq1) hd
            _ = d := mul_one d
            _ ≤ _ := hsep i i' hii _ hau _ hbu

end Words

/-! ### A Moran-type lower bound for the dimension -/

/-- A Moran-type lower bound for the Hausdorff dimension of a compact set `E`: if a finite family
of maps `g i` sends `E` into itself, expands distances in the weak sense
`q * dist y z ≤ dist (g i y) (g i z)`, and has the images of distinct maps at distance at least
`d`, then `dimH E` is at least every `t > 0` with `(card ι)⁻¹ < q ^ t`. -/
theorem le_dimH_of_separated_maps {ι : Type*} [Fintype ι] [Nonempty ι] {E : Set X}
    (hE : IsCompact E) (hne : E.Nonempty) {g : ι → X → X} (hg : ∀ i, MapsTo (g i) E E)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hlow : ∀ i, ∀ y ∈ E, ∀ z ∈ E, q * dist y z ≤ dist (g i y) (g i z))
    {d : ℝ} (hd : 0 < d)
    (hsep : ∀ i j, i ≠ j → ∀ y ∈ E, ∀ z ∈ E, d ≤ dist (g i y) (g j z))
    {t : ℝ} (ht : 0 < t) (hcard : ((Fintype.card ι : ℝ))⁻¹ < q ^ t) :
    ENNReal.ofReal t ≤ dimH E := by
  classical
  obtain ⟨z₀, hz₀⟩ := hne
  set N := Fintype.card ι with hNdef
  have hNpos : 0 < N := Fintype.card_pos
  haveI : CompactSpace ↥E := isCompact_iff_compactSpace.mp hE
  have hmem : ∀ w : List ι, wordComp g w z₀ ∈ E := fun w => mapsTo_wordComp hg w hz₀
  obtain ⟨pt, hpt⟩ : ∃ pt : ∀ m : ℕ, List.Vector ι m → ↥E,
      ∀ (m : ℕ) (v : List.Vector ι m), (pt m v : X) = wordComp g v.1 z₀ :=
    ⟨fun _ v => ⟨wordComp g v.1 z₀, hmem v.1⟩, fun _ _ => rfl⟩
  obtain ⟨mu, hmu⟩ : ∃ mu : ℕ → Measure ↥E, ∀ m : ℕ,
      mu m = ((N : ℝ≥0∞) ^ m)⁻¹ • ∑ v : List.Vector ι m, Measure.dirac (pt m v) :=
    ⟨_, fun _ => rfl⟩
  have hNne : ((N : ℝ≥0∞)) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hNtop : ((N : ℝ≥0∞)) ≠ ⊤ := ENNReal.natCast_ne_top N
  have hmusum : ∀ (m : ℕ) (S : Set ↥E), MeasurableSet S →
      mu m S = ((N : ℝ≥0∞) ^ m)⁻¹ * ∑ v : List.Vector ι m, Set.indicator S 1 (pt m v) := by
    intro m S hS
    rw [hmu m, Measure.smul_apply, smul_eq_mul]
    congr 1
    rw [Measure.coe_finsetSum]
    simp only [Finset.sum_apply, Measure.dirac_apply' _ hS]
  have hmutotal : ∀ m, mu m Set.univ = 1 := by
    intro m
    rw [hmusum m Set.univ MeasurableSet.univ]
    simp only [Set.indicator_univ, Pi.one_apply, Finset.sum_const, Finset.card_univ, card_vector,
      nsmul_eq_mul, mul_one, ← hNdef, Nat.cast_pow]
    exact ENNReal.inv_mul_cancel (pow_ne_zero _ hNne) (ENNReal.pow_ne_top hNtop)
  have hmule : ∀ (m : ℕ) (S : Set ↥E) (T : Finset (List.Vector ι m)), MeasurableSet S →
      (∀ v, pt m v ∈ S → v ∈ T) → mu m S ≤ ((N : ℝ≥0∞) ^ m)⁻¹ * (T.card : ℝ≥0∞) := by
    intro m S T hS hT
    rw [hmusum m S hS]
    gcongr
    calc ∑ v : List.Vector ι m, Set.indicator S 1 (pt m v)
        ≤ ∑ v : List.Vector ι m, (if v ∈ T then (1 : ℝ≥0∞) else 0) := by
          refine Finset.sum_le_sum fun v _ => ?_
          rw [Set.indicator_apply]
          by_cases hv : pt m v ∈ S
          · simp [hv, hT v hv]
          · simp [hv]
      _ = (T.card : ℝ≥0∞) := by
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  haveI hprob : ∀ m, IsProbabilityMeasure (mu m) := fun m => ⟨hmutotal m⟩
  obtain ⟨fm, hfm⟩ : ∃ fm : ℕ → FiniteMeasure ↥E, ∀ m, (fm m : Measure ↥E) = mu m :=
    ⟨fun m => ⟨mu m, inferInstance⟩, fun _ => rfl⟩
  have hmassone : ∀ n, ((fm n).mass : ℝ≥0∞) = 1 := by
    intro n
    rw [FiniteMeasure.ennreal_mass, hfm n]
    exact hmutotal n
  obtain ⟨φ, ν, hφ, hconv, hmassconv⟩ :=
    weak_compactness fm ⟨1, fun n => by exact_mod_cast (hmassone n).le⟩
  have hνuniv : (ν : Measure ↥E) Set.univ = 1 := by
    have h1 : Tendsto (fun k => ((fm (φ k)).mass : ℝ≥0)) atTop (𝓝 (1 : ℝ≥0)) := by
      have hconst : (fun k => ((fm (φ k)).mass : ℝ≥0)) = fun _ => (1 : ℝ≥0) := by
        funext k; exact_mod_cast hmassone (φ k)
      rw [hconst]; exact tendsto_const_nhds
    have hm1 : ν.mass = 1 := tendsto_nhds_unique hmassconv h1
    rw [← FiniteMeasure.ennreal_mass, hm1]; norm_num
  have hνle : ∀ (U : Set ↥E) (k : ℕ) (c : ℝ≥0∞), IsOpen U → (∀ m, k ≤ m → mu m U ≤ c) →
      (ν : Measure ↥E) U ≤ c := by
    intro U k c hU hc
    refine le_trans (le_liminf_measure_open_of_tendsto hconv hU) ?_
    refine liminf_le_of_frequently_le (Filter.Eventually.frequently ?_)
    filter_upwards [eventually_ge_atTop k] with j hj
    simp only [Function.comp_apply]
    rw [hfm (φ j)]
    exact hc (φ j) (hj.trans hφ.le_apply)
  have hbase : (0:ℝ) < 2 / (d * q) := by positivity
  have hball : ∀ x ∈ E, ∀ ρ : ℝ, 0 < ρ →
      (Measure.map (Subtype.val : ↥E → X) (ν : Measure ↥E)) (ball x ρ) ≤
        (((2 / (d * q)) ^ t).toNNReal : ℝ≥0∞) * ENNReal.ofReal ρ ^ t := by
    intro x _ ρ hρ
    have hrhs : ((((2 / (d * q)) ^ t).toNNReal : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal ρ ^ t
        = ENNReal.ofReal ((2 / (d * q)) ^ t * ρ ^ t) := by
      rw [ENNReal.ofReal_rpow_of_pos hρ,
        show (((2 / (d * q)) ^ t).toNNReal : ℝ≥0∞) = ENNReal.ofReal ((2 / (d * q)) ^ t) from rfl,
        ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hbase t).le]
    rw [Measure.map_apply measurable_subtype_coe measurableSet_ball, hrhs]
    rcases le_or_gt d (2 * ρ) with hcase | hcase
    · refine le_trans (measure_mono (subset_univ _)) ?_
      rw [hνuniv, ENNReal.one_le_ofReal]
      have hsplit : (2 / (d * q)) ^ t * ρ ^ t = (2 * ρ / (d * q)) ^ t := by
        rw [show 2 * ρ / (d * q) = (2 / (d * q)) * ρ by ring, Real.mul_rpow hbase.le hρ.le]
      rw [hsplit]
      have h1 : (1:ℝ) ≤ 2 * ρ / (d * q) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      calc (1:ℝ) = (1:ℝ) ^ t := (Real.one_rpow t).symm
        _ ≤ (2 * ρ / (d * q)) ^ t := Real.rpow_le_rpow (by norm_num) h1 ht.le
    · obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, d * q ^ (k + 1) ≤ 2 * ρ ∧ 2 * ρ < d * q ^ k := by
        have hex : ∃ n : ℕ, d * q ^ (n + 1) ≤ 2 * ρ := by
          obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < 2 * ρ / d by positivity) hq1
          rw [lt_div_iff₀ hd] at hn
          refine ⟨n, ?_⟩
          have h1 : q ^ (n + 1) ≤ q ^ n := pow_le_pow_of_le_one hq0.le hq1.le (Nat.le_succ n)
          nlinarith
        refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
        rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
        · rw [h0, pow_zero, mul_one]; exact hcase
        · have hmin := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
          rw [not_le] at hmin
          have heq : Nat.find hex - 1 + 1 = Nat.find hex := by omega
          rwa [heq] at hmin
      set T : Finset (List.Vector ι k) :=
        Finset.univ.filter (fun v => ((wordComp g v.1 '' E) ∩ ball x ρ).Nonempty) with hTdef
      have hTsub : ∀ v ∈ T, ∀ v' ∈ T, v = v' := by
        intro v hv v' hv'
        by_contra hvv
        rw [hTdef, Finset.mem_filter] at hv hv'
        obtain ⟨y, hy1, hy2⟩ := hv.2
        obtain ⟨z, hz1, hz2⟩ := hv'.2
        have hlen : v.1.length = v'.1.length := by rw [v.2, v'.2]
        have hne' : v.1 ≠ v'.1 := fun h => hvv (Subtype.ext h)
        have hsd := le_dist_of_wordComp_ne hq0.le hq1.le hd.le hg hlow hsep hlen hne' hy1 hz1
        rw [v.2] at hsd
        have hlt : dist y z < 2 * ρ := by
          calc dist y z ≤ dist y x + dist x z := dist_triangle y x z
            _ < ρ + ρ := add_lt_add (mem_ball.mp hy2) (by rw [dist_comm]; exact mem_ball.mp hz2)
            _ = 2 * ρ := by ring
        linarith
      set U : Set ↥E :=
        (⋃ v ∈ (Finset.univ \ T), closure ((Subtype.val : ↥E → X) ⁻¹' (wordComp g v.1 '' E)))ᶜ
        with hUdef
      have hUopen : IsOpen U := by
        rw [hUdef]
        exact (isClosed_biUnion_finset (fun v _ => isClosed_closure)).isOpen_compl
      have hBU : (Subtype.val : ↥E → X) ⁻¹' ball x ρ ⊆ U := by
        intro y hy
        rw [hUdef]
        simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
        intro v hv hmemc
        have hopen : IsOpen ((Subtype.val : ↥E → X) ⁻¹' ball x ρ) :=
          isOpen_ball.preimage continuous_subtype_val
        obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp hmemc _ hopen hy
        have hvT : v ∈ T := by
          rw [hTdef, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, ⟨(w : X), hw2, hw1⟩⟩
        rw [Finset.mem_sdiff] at hv
        exact hv.2 hvT
      have hprefix : ∀ (m : ℕ), k ≤ m → ∀ v : List.Vector ι m, pt m v ∈ U →
          ∃ u : List.Vector ι k, u ∈ T ∧ u.1 = v.1.take k := by
        intro m hm v hvU
        have hlen : (v.1.take k).length = k := by
          rw [List.length_take, v.2]; omega
        refine ⟨⟨v.1.take k, hlen⟩, ?_, rfl⟩
        by_contra hnotT
        have hmemimg : pt m v ∈ (Subtype.val : ↥E → X) ⁻¹' (wordComp g (v.1.take k) '' E) := by
          simp only [Set.mem_preimage, hpt m v]
          refine ⟨wordComp g (v.1.drop k) z₀, hmem _, ?_⟩
          rw [show wordComp g (v.1.take k) (wordComp g (v.1.drop k) z₀)
              = (wordComp g (v.1.take k) ∘ wordComp g (v.1.drop k)) z₀ from rfl,
            ← wordComp_append, List.take_append_drop]
        have hin : pt m v ∈ ⋃ u ∈ (Finset.univ \ T),
            closure ((Subtype.val : ↥E → X) ⁻¹' (wordComp g u.1 '' E)) :=
          Set.mem_biUnion (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnotT⟩) (subset_closure hmemimg)
        rw [hUdef] at hvU
        exact hvU hin
      have hcount : ∀ m : ℕ, k ≤ m → mu m U ≤ ((N : ℝ≥0∞) ^ k)⁻¹ := by
        intro m hm
        obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
        set T' : Finset (List.Vector ι (k + j)) :=
          Finset.univ.filter (fun v => pt (k + j) v ∈ U) with hT'def
        obtain ⟨dropv, hdropv⟩ : ∃ f : List.Vector ι (k + j) → List.Vector ι j,
            ∀ v, (f v).1 = v.1.drop k :=
          ⟨fun v => ⟨v.1.drop k, by rw [List.length_drop, v.2]; omega⟩, fun _ => rfl⟩
        have hT'card : T'.card ≤ N ^ j := by
          have hinj : Set.InjOn dropv (T' : Set (List.Vector ι (k + j))) := by
            intro v hv v' hv' heq
            rw [hT'def, Finset.coe_filter, Set.mem_setOf_eq] at hv hv'
            obtain ⟨u, hu, hu1⟩ := hprefix (k + j) (by omega) v hv.2
            obtain ⟨u', hu', hu1'⟩ := hprefix (k + j) (by omega) v' hv'.2
            have htake : v.1.take k = v'.1.take k := by
              rw [← hu1, ← hu1', hTsub u hu u' hu']
            have hdrop : v.1.drop k = v'.1.drop k := by
              rw [← hdropv v, ← hdropv v', heq]
            refine Subtype.ext ?_
            rw [← List.take_append_drop k v.1, ← List.take_append_drop k v'.1, htake, hdrop]
          have hle := Finset.card_le_card_of_injOn (t := (Finset.univ : Finset (List.Vector ι j)))
            dropv (fun v _ => Finset.mem_univ _) hinj
          rwa [Finset.card_univ, card_vector, ← hNdef] at hle
        calc mu (k + j) U ≤ ((N : ℝ≥0∞) ^ (k + j))⁻¹ * (T'.card : ℝ≥0∞) := by
              refine hmule _ _ _ hUopen.measurableSet fun v hvU => ?_
              rw [hT'def, Finset.mem_filter]
              exact ⟨Finset.mem_univ _, hvU⟩
          _ ≤ ((N : ℝ≥0∞) ^ (k + j))⁻¹ * ((N : ℝ≥0∞) ^ j) :=
              mul_le_mul' le_rfl (by exact_mod_cast hT'card)
          _ = ((N : ℝ≥0∞) ^ k)⁻¹ := by
              rw [pow_add, ENNReal.mul_inv (Or.inl (pow_ne_zero _ hNne))
                  (Or.inl (ENNReal.pow_ne_top hNtop)), mul_assoc,
                ENNReal.inv_mul_cancel (pow_ne_zero _ hNne) (ENNReal.pow_ne_top hNtop), mul_one]
      have hNk : ((N : ℝ≥0∞) ^ k)⁻¹ = ENNReal.ofReal (((N : ℝ) ^ k)⁻¹) := by
        rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by positivity),
          ENNReal.ofReal_natCast]
      calc (ν : Measure ↥E) ((Subtype.val : ↥E → X) ⁻¹' ball x ρ)
          ≤ (ν : Measure ↥E) U := measure_mono hBU
        _ ≤ ((N : ℝ≥0∞) ^ k)⁻¹ := hνle U k _ hUopen hcount
        _ = ENNReal.ofReal (((N : ℝ) ^ k)⁻¹) := hNk
        _ ≤ ENNReal.ofReal ((2 / (d * q)) ^ t * ρ ^ t) := by
            refine ENNReal.ofReal_le_ofReal ?_
            calc ((N : ℝ) ^ k)⁻¹ = ((N : ℝ)⁻¹) ^ k := (inv_pow _ _).symm
              _ ≤ (q ^ t) ^ k := pow_le_pow_left₀ (by positivity) hcard.le k
              _ = (q ^ k) ^ t := by
                  rw [← Real.rpow_natCast (q ^ t) k, ← Real.rpow_mul hq0.le,
                    mul_comm t (k : ℝ), Real.rpow_mul hq0.le, Real.rpow_natCast]
              _ ≤ (2 * ρ / (d * q)) ^ t := by
                  refine Real.rpow_le_rpow (by positivity) ?_ ht.le
                  rw [le_div_iff₀ (by positivity)]
                  calc q ^ k * (d * q) = d * q ^ (k + 1) := by rw [pow_succ]; ring
                    _ ≤ 2 * ρ := hk1
              _ = (2 / (d * q)) ^ t * ρ ^ t := by
                  rw [show 2 * ρ / (d * q) = (2 / (d * q)) * ρ by ring,
                    Real.mul_rpow hbase.le hρ.le]
  have hCne : (((2 / (d * q)) ^ t).toNNReal : ℝ≥0) ≠ 0 := by
    simp only [ne_eq, Real.toNNReal_eq_zero, not_le]
    exact Real.rpow_pos_of_pos hbase t
  refine (mass_distribution _ ht hCne hball).2 ?_
  rw [Measure.map_apply measurable_subtype_coe hE.isClosed.measurableSet]
  have hpre : (Subtype.val : ↥E → X) ⁻¹' E = Set.univ := by
    ext y; simp
  rw [hpre, hνuniv]
  exact one_pos

/-! ### The packing bound at a single scale -/

/-- The first conclusion of Theorem 8.2 at a single scale: a set satisfying the lower bound of the
quasi-self-similarity condition carries at most `D^s r^{-s}` disjoint closed balls of radius `r`
centred on it, once `r < min {|E|, D}`. -/
theorem qss_packing_bound {D : ℝ} (hD : 0 < D) {E : Set X} (hE : IsCompact E) (hne : E.Nonempty)
    (hQ : IsQuasiSelfSimilarLower D E) {s : ℝ} (hs : 0 < s) (hdim : dimH E ≤ ENNReal.ofReal s)
    {r : ℝ} (hr : 0 < r) (hrE : r < diam E) (hrD : r < D) :
    (Metric.packingNumber (2 * r).toNNReal E : ℝ≥0∞) ≤ ENNReal.ofReal (D ^ s * r ^ (-s)) := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  set ε : ℝ≥0 := (2 * r).toNNReal with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; exact Real.toNNReal_pos.mpr (by linarith)
  have hfin : Metric.packingNumber ε E ≠ ⊤ := packingNumber_ne_top hE.totallyBounded hεpos
  obtain ⟨C₀, hC₀E, hC₀fin, hC₀sep, hC₀card⟩ := Metric.exists_set_encard_eq_packingNumber hfin
  haveI : Fintype ↥C₀ := hC₀fin.fintype
  set N := Fintype.card ↥C₀ with hNdef
  have hNcard : (N : ℕ∞) = Metric.packingNumber ε E := by
    rw [← hC₀card, ← Set.Finite.cast_ncard_eq hC₀fin, ← Nat.card_coe_set_eq,
      Nat.card_eq_fintype_card]
  have hcoe : ((Metric.packingNumber ε E : ℕ∞) : ℝ≥0∞) = (N : ℝ≥0∞) := by
    rw [← hNcard]; simp
  rw [hcoe] at hcon
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h] at hcon; simp at hcon
    · exact h
  have hAN : D ^ s * r ^ (-s) < (N : ℝ) := by
    rwa [← ENNReal.ofReal_natCast N,
      ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast hNpos)] at hcon
  have hDr : (1:ℝ) < D / r := (one_lt_div hr).mpr hrD
  have hAeq : D ^ s * r ^ (-s) = (D / r) ^ s := by
    rw [Real.div_rpow hD.le hr.le, Real.rpow_neg hr.le, div_eq_mul_inv]
  rw [hAeq] at hAN
  obtain ⟨t, hst, htN⟩ : ∃ t : ℝ, s < t ∧ (D / r) ^ t < (N : ℝ) := by
    have hc : ContinuousAt (fun u : ℝ => (D / r) ^ u) s :=
      Real.continuousAt_const_rpow (by positivity)
    have hev : ∀ᶠ u in 𝓝 s, (D / r) ^ u < (N : ℝ) := hc.eventually_lt_const hAN
    have h2 : ∀ᶠ u in 𝓝[>] s, (D / r) ^ u < (N : ℝ) := hev.filter_mono nhdsWithin_le_nhds
    obtain ⟨u, hu1, hu2⟩ := (h2.and self_mem_nhdsWithin).exists
    exact ⟨u, hu2, hu1⟩
  have htpos : 0 < t := hs.trans hst
  choose g hg1 hg2 using fun i : ↥C₀ => hQ (i : X) (hC₀E i.2) r hr hrE
  set q : ℝ := D⁻¹ * r with hqdef
  have hq0 : 0 < q := by rw [hqdef]; positivity
  have hq1 : q < 1 := by
    rw [hqdef, inv_mul_eq_div, div_lt_one hD]; exact hrD
  have hgE : ∀ i, MapsTo (g i) E E := fun i => (hg1 i).mono_right inter_subset_left
  haveI : Nonempty ↥C₀ := Fintype.card_pos_iff.mp hNpos
  set F : ↥C₀ × ↥C₀ → ℝ :=
    fun p => if p.1 = p.2 then 1 else dist (p.1 : X) (p.2 : X) - 2 * r with hFdef
  have hFpos : ∀ p : ↥C₀ × ↥C₀, 0 < F p := by
    intro p
    rw [hFdef]
    by_cases h : p.1 = p.2
    · simp [h]
    · have hne2 : (p.1 : X) ≠ (p.2 : X) := fun hh => h (Subtype.ext hh)
      have h0 : (ε : ℝ≥0∞) < edist (p.1 : X) (p.2 : X) := hC₀sep p.1.2 p.2.2 hne2
      rw [edist_dist, hεdef] at h0
      have hsp : 2 * r < dist (p.1 : X) (p.2 : X) :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp h0
      simp only [h, if_false]
      linarith
  set d : ℝ := Finset.univ.inf' Finset.univ_nonempty F with hddef
  have hdpos : 0 < d := by rw [hddef, Finset.lt_inf'_iff]; exact fun p _ => hFpos p
  have hsepd : ∀ i j : ↥C₀, i ≠ j → ∀ y ∈ E, ∀ z ∈ E, d ≤ dist (g i y) (g j z) := by
    intro i j hij y hy z hz
    have h1 : d ≤ F (i, j) := Finset.inf'_le _ (Finset.mem_univ _)
    rw [hFdef] at h1
    simp only [hij, if_false] at h1
    have hy' : dist (g i y) (i : X) ≤ r := mem_closedBall.mp (hg1 i hy).2
    have hz' : dist (g j z) (j : X) ≤ r := mem_closedBall.mp (hg1 j hz).2
    have htri : dist (i : X) (j : X)
        ≤ dist (i : X) (g i y) + dist (g i y) (g j z) + dist (g j z) (j : X) :=
      dist_triangle4 _ _ _ _
    rw [dist_comm (i : X) (g i y)] at htri
    linarith
  have hcard' : ((N : ℝ))⁻¹ < q ^ t := by
    have hqinv : q = (D / r)⁻¹ := by rw [hqdef, inv_div, div_eq_inv_mul]
    rw [hqinv, Real.inv_rpow (by positivity)]
    exact inv_strictAnti₀ (Real.rpow_pos_of_pos (by positivity) t) htN
  have hdimt : ENNReal.ofReal t ≤ dimH E :=
    le_dimH_of_separated_maps hE hne hgE hq0 hq1 (fun i => hg2 i) hdpos hsepd htpos hcard'
  have hfinal : ENNReal.ofReal t ≤ ENNReal.ofReal s := hdimt.trans hdim
  rw [ENNReal.ofReal_le_ofReal_iff hs.le] at hfinal
  linarith

/-- Theorem 8.2: a quasi-self-similar set carries at most `D^s r^{-s}` disjoint closed balls of
radius `r` centred on it, and its Hausdorff measure at its dimension is at most `4^s D^s`. Only the
lower bound of the quasi-self-similarity condition is used, which is Remark 8.3. -/
theorem qss_packing_finite {D : ℝ} (hD : 0 < D) {E : Set X} (hE : IsCompact E) (hne : E.Nonempty)
    (hQ : IsQuasiSelfSimilarLower D E) {s : ℝ} (hs : 0 < s) (hdim : dimH E ≤ ENNReal.ofReal s) :
    (∀ r : ℝ, 0 < r → r < diam E → r < D →
        (Metric.packingNumber (2 * r).toNNReal E : ℝ≥0∞) ≤
          ENNReal.ofReal (D ^ s * r ^ (-s))) ∧
      μH[s] E ≤ ENNReal.ofReal (4 ^ s * D ^ s) := by
  classical
  refine ⟨fun r hr hrE hrD => qss_packing_bound hD hE hne hQ hs hdim hr hrE hrD, ?_⟩
  rcases eq_or_lt_of_le (diam_nonneg : (0:ℝ) ≤ diam E) with hdiam | hdiam
  · obtain ⟨x, hx⟩ := hne
    have hsub : E ⊆ ({x} : Set X) := by
      intro y hy
      have h1 : dist y x ≤ diam E := dist_le_diam_of_mem hE.isBounded hy hx
      rw [← hdiam] at h1
      exact Set.mem_singleton_iff.mpr (dist_le_zero.mp h1)
    have h2 : μH[((s.toNNReal : ℝ≥0) : ℝ)] ({x} : Set X) = 0 := by
      refine hausdorffMeasure_of_dimH_lt ?_
      rw [dimH_singleton]
      exact_mod_cast Real.toNNReal_pos.mpr hs
    rw [Real.coe_toNNReal s hs.le] at h2
    calc μH[s] E ≤ μH[s] ({x} : Set X) := measure_mono hsub
      _ = 0 := h2
      _ ≤ ENNReal.ofReal (4 ^ s * D ^ s) := by simp
  · set ρ₀ : ℝ := min (diam E) D with hρ₀def
    have hρ₀ : 0 < ρ₀ := lt_min hdiam hD
    set rn : ℕ → ℝ := fun n => ρ₀ / ((n : ℝ) + 2) with hrndef
    have hrn0 : ∀ n, 0 < rn n := fun n => by rw [hrndef]; positivity
    have hrnlt : ∀ n, rn n < ρ₀ := by
      intro n
      rw [hrndef, div_lt_iff₀ (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hrnE : ∀ n, rn n < diam E := fun n => (hrnlt n).trans_le (min_le_left _ _)
    have hrnD : ∀ n, rn n < D := fun n => (hrnlt n).trans_le (min_le_right _ _)
    set Mn : ℕ → Set X := fun n => Metric.maximalSeparatedSet (2 * rn n).toNNReal E with hMndef
    have hεn : ∀ n, (0:ℝ≥0) < (2 * rn n).toNNReal :=
      fun n => Real.toNNReal_pos.mpr (by linarith [hrn0 n])
    have hfinn : ∀ n, Metric.packingNumber (2 * rn n).toNNReal E ≠ ⊤ :=
      fun n => packingNumber_ne_top hE.totallyBounded (hεn n)
    have hMnenc : ∀ n, (Mn n).encard = Metric.packingNumber (2 * rn n).toNNReal E :=
      fun n => Metric.encard_maximalSeparatedSet (hfinn n)
    have hMnfin : ∀ n, (Mn n).Finite := by
      intro n
      rw [← Set.encard_ne_top_iff, hMnenc n]
      exact hfinn n
    haveI hMnFintype : ∀ n, Fintype ↥(Mn n) := fun n => (hMnfin n).fintype
    haveI hMnCountable : ∀ n, Countable ↥(Mn n) := fun n => Finite.to_countable
    have hcard : ∀ n, ((Fintype.card ↥(Mn n) : ℕ) : ℝ≥0∞)
        ≤ ENNReal.ofReal (D ^ s * rn n ^ (-s)) := by
      intro n
      have h1 : ((Fintype.card ↥(Mn n) : ℕ) : ℕ∞) = (Mn n).encard := by
        rw [← Set.Finite.cast_ncard_eq (hMnfin n), ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
      have h2 := qss_packing_bound hD hE hne hQ hs hdim (hrn0 n) (hrnE n) (hrnD n)
      rw [← hMnenc n, ← h1] at h2
      have hcast : ∀ k : ℕ, (((k : ℕ∞)) : ℝ≥0∞) = (k : ℝ≥0∞) := fun k => by simp
      rwa [hcast] at h2
    have hcov : ∀ n, Metric.IsCover (2 * rn n).toNNReal E (Mn n) :=
      fun n => Metric.isCover_maximalSeparatedSet (hfinn n)
    have hsubE : ∀ n, E ⊆ ⋃ i : ↥(Mn n), closedBall (i : X) (2 * rn n) := by
      intro n y hy
      obtain ⟨z, hz, hdz⟩ := hcov n hy
      refine Set.mem_iUnion.mpr ⟨⟨z, hz⟩, ?_⟩
      rw [mem_closedBall]
      have hdz' : ENNReal.ofReal (dist y z) ≤ ENNReal.ofReal (2 * rn n) := by
        rw [← edist_dist]; exact hdz
      exact (ENNReal.ofReal_le_ofReal_iff (by linarith [hrn0 n])).mp hdz'
    have hdiamb : ∀ (n : ℕ) (i : ↥(Mn n)),
        ediam (closedBall (i : X) (2 * rn n)) ≤ ENNReal.ofReal (4 * rn n) := by
      intro n i
      refine ediam_le fun a ha b hb => ?_
      rw [edist_dist]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [mem_closedBall] at ha hb
      have h1 : dist a b ≤ dist a (i : X) + dist (i : X) b := dist_triangle a (i : X) b
      rw [dist_comm (i : X) b] at h1
      linarith
    have htend : Tendsto (fun n : ℕ => ENNReal.ofReal (4 * rn n)) atTop (𝓝 0) := by
      rw [show (0 : ℝ≥0∞) = ENNReal.ofReal 0 by simp]
      refine (ENNReal.continuous_ofReal.tendsto 0).comp ?_
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp h1
      have h3 := h2.const_mul (4 * ρ₀)
      rw [mul_zero] at h3
      refine h3.congr fun n => ?_
      rw [hrndef]
      field_simp
    have hsumle : ∀ n : ℕ, ∑' i : ↥(Mn n), ediam (closedBall (i : X) (2 * rn n)) ^ s
        ≤ ENNReal.ofReal (4 ^ s * D ^ s) := by
      intro n
      have hrns : (rn n) ^ s ≠ 0 := (Real.rpow_pos_of_pos (hrn0 n) s).ne'
      have hreal : D ^ s * rn n ^ (-s) * (4 * rn n) ^ s = 4 ^ s * D ^ s := by
        calc D ^ s * rn n ^ (-s) * (4 * rn n) ^ s
            = D ^ s * ((rn n) ^ s)⁻¹ * (4 ^ s * (rn n) ^ s) := by
              rw [Real.mul_rpow (by norm_num) (hrn0 n).le, Real.rpow_neg (hrn0 n).le]
          _ = 4 ^ s * D ^ s * (((rn n) ^ s)⁻¹ * (rn n) ^ s) := by ring
          _ = 4 ^ s * D ^ s := by rw [inv_mul_cancel₀ hrns, mul_one]
      calc ∑' i : ↥(Mn n), ediam (closedBall (i : X) (2 * rn n)) ^ s
          ≤ ∑' _i : ↥(Mn n), (ENNReal.ofReal (4 * rn n)) ^ s :=
            ENNReal.tsum_le_tsum fun i => ENNReal.rpow_le_rpow (hdiamb n i) hs.le
        _ = (Fintype.card ↥(Mn n) : ℝ≥0∞) * (ENNReal.ofReal (4 * rn n)) ^ s := by
            rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ ENNReal.ofReal (D ^ s * rn n ^ (-s)) * ENNReal.ofReal ((4 * rn n) ^ s) := by
            rw [ENNReal.ofReal_rpow_of_pos (by linarith [hrn0 n])]
            exact mul_le_mul' (hcard n) le_rfl
        _ = ENNReal.ofReal (4 ^ s * D ^ s) := by
            rw [← ENNReal.ofReal_mul (by positivity), hreal]
    refine le_trans (Measure.hausdorffMeasure_le_liminf_tsum s E
      (fun n => ENNReal.ofReal (4 * rn n)) htend
      (fun n (i : ↥(Mn n)) => closedBall (i : X) (2 * rn n))
      (Filter.Eventually.of_forall fun n => hdiamb n)
      (Filter.Eventually.of_forall hsubE)) ?_
    exact liminf_le_of_frequently_le (Filter.Eventually.frequently
      (Filter.Eventually.of_forall hsumle))

/-- The repeller of a cookie cutter is quasi-self-similar: this is Corollary 6.6. -/
theorem CookieCutter.isQuasiSelfSimilar_attractor {ι : Type*} [Finite ι] [Nonempty ι]
    (C : CookieCutter ι) : ∃ D : ℝ, 0 < D ∧ IsQuasiSelfSimilar D C.attractor := by
  obtain ⟨c, r₀, hc, hr₀, hmain⟩ := C.cookie_cutter_contraction
  set D : ℝ := max c (2 * c * diam C.attractor / r₀) with hDdef
  have hcD : c ≤ D := le_max_left _ _
  have hD : 0 < D := lt_of_lt_of_le hc hcD
  have hinvD : D⁻¹ ≤ c⁻¹ := inv_anti₀ hc hcD
  refine ⟨D, hD, ?_⟩
  intro x hx r hr hrdiam
  rcases lt_or_ge r r₀ with hcase | hcase
  · obtain ⟨g, hmaps, hbound⟩ := hmain x hx r hr hcase
    refine ⟨g, hmaps.mono_right (Set.inter_subset_inter Subset.rfl ball_subset_closedBall), ?_⟩
    intro y hy z hz
    obtain ⟨hlow, hup⟩ := hbound y hy z hz
    rw [Real.dist_eq, Real.dist_eq]
    exact ⟨le_trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hinvD hr.le) (abs_nonneg _)) hlow,
      hup.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcD hr.le) (abs_nonneg _))⟩
  · have hΔ : 0 < diam C.attractor := lt_trans hr hrdiam
    obtain ⟨g, hmaps, hbound⟩ := hmain x hx (r₀ / 2) (by positivity) (by linarith)
    have hsub : C.attractor ∩ ball x (r₀ / 2) ⊆ C.attractor ∩ closedBall x r :=
      Set.inter_subset_inter Subset.rfl
        (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
    refine ⟨g, hmaps.mono_right hsub, ?_⟩
    intro y hy z hz
    obtain ⟨hlow, hup⟩ := hbound y hy z hz
    rw [Real.dist_eq, Real.dist_eq]
    have hmax : 2 * c * diam C.attractor / r₀ ≤ D := le_max_right _ _
    have hkey : c * r ≤ D * (r₀ / 2) := by
      have h2 : (2 * c * diam C.attractor / r₀) * (r₀ / 2) = c * diam C.attractor := by
        field_simp
      calc c * r ≤ c * diam C.attractor := by nlinarith
        _ = (2 * c * diam C.attractor / r₀) * (r₀ / 2) := h2.symm
        _ ≤ D * (r₀ / 2) := by nlinarith
    have hinv : D⁻¹ * r ≤ c⁻¹ * (r₀ / 2) := by
      rw [inv_mul_eq_div, inv_mul_eq_div, div_le_div_iff₀ hD hc]
      linarith [hkey, mul_comm c r, mul_comm D (r₀ / 2)]
    refine ⟨le_trans (mul_le_mul_of_nonneg_right hinv (abs_nonneg _)) hlow,
      hup.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))⟩
    nlinarith [mul_nonneg (sub_nonneg.mpr hcD) hr.le, mul_nonneg hc.le (sub_nonneg.mpr hcase)]

end GeometricMeasureTheory
