import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.Configuration
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.LawInvariance
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.Processes
import FractalGeometry.Probability.GridPercolation.PrunedSurvival
import FractalGeometry.Probability.GridPercolation.RetainedTreeEvents
import FractalGeometry.Probability.GridPercolation.RootIndependence
import FractalGeometry.Probability.GridPercolation.ShallowEvents
import FractalGeometry.Probability.GridPercolation.Subtrees
import FractalGeometry.Probability.GridPercolation.SurvivalMeasurability
import FractalGeometry.Probability.GridPercolation.WordSplitting

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory ProbabilityTheory Filter Topology

open scoped ENNReal

variable {A : GridLaw}

lemma wordOfCoordinates_map_fst {L : ℕ} (v : ColumnWord A L) (r : RowWord A L) :
    (wordOfCoordinates v r).map Prod.fst = List.ofFn v := by
  simp [wordOfCoordinates, List.map_ofFn, Function.comp_def]

lemma columns_eq_of_wordOfCoordinates_eq {L : ℕ} {v v' : ColumnWord A L}
    {r r' : RowWord A L} (h : wordOfCoordinates v r = wordOfCoordinates v' r') : v = v' := by
  have h' := congrArg (List.map Prod.fst) h
  rw [wordOfCoordinates_map_fst, wordOfCoordinates_map_fst] at h'
  exact List.ofFn_injective h'

lemma exists_wordOfCoordinates_eq_of_length {w : Word A} {L : ℕ} (hwL : w.length = L) :
    ∃ (v : ColumnWord A L) (r : RowWord A L), wordOfCoordinates v r = w := by
  refine ⟨fun l => (w.get (Fin.cast hwL.symm l)).1, fun l => (w.get (Fin.cast hwL.symm l)).2, ?_⟩
  apply List.ext_getElem
  · simp [hwL]
  · intro i h1 h2
    simp [wordOfCoordinates]

lemma wordOfCoordinates_finSnoc {L : ℕ} (v : ColumnWord A L) (r : RowWord A L)
    (a : Fin A.M × Fin A.N) :
    wordOfCoordinates (Fin.snoc (α := fun _ => Fin A.M) v a.1)
        (Fin.snoc (α := fun _ => Fin A.N) r a.2) = wordOfCoordinates v r ++ [a] := by
  unfold wordOfCoordinates
  rw [List.ofFn_succ', List.concat_eq_append]
  simp

section Monotone

variable {Ω : Type*}

lemma exists_child_hasInfiniteDescentBelow {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}
    {ω : Ω} {w : Word A} (h : HasInfiniteDescentBelow X ω w) :
    ∃ a : Fin A.M × Fin A.N, RetainedBelow X ω w [a] ∧ HasInfiniteDescentBelow X ω (w ++ [a]) := by
  have hs : ω ∈ survival (shiftFamily X w) :=
    (hasInfiniteDescentBelow_nil_iff_mem_survival (shiftFamily X w) ω).mp h
  obtain ⟨w', hlen, hret, hdesc⟩ :=
    exists_retained_hasInfiniteDescent_of_mem_survival hs 1
  obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen
  refine ⟨a, hret, ?_⟩
  intro L
  obtain ⟨u, hu⟩ := hdesc L
  refine ⟨u, fun l => ?_⟩
  have := hu l
  simpa [shiftFamily, List.append_assoc] using this

theorem prunedColumnCount_le_succ (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (L : ℕ)
    (ω : Ω) : prunedColumnCount X L ω ≤ prunedColumnCount X (L + 1) ω := by
  classical
  unfold prunedColumnCount prunedColumnCountBelow
  refine Finset.card_le_card_of_surjOn (fun v : ColumnWord A (L + 1) => Fin.init v) ?_
  intro v hv
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
  obtain ⟨r, hret, hdesc⟩ := hv
  obtain ⟨a, ha, hadesc⟩ := exists_child_hasInfiniteDescentBelow hdesc
  refine ⟨Fin.snoc (α := fun _ => Fin A.M) v a.1, ?_, by simp⟩
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  refine ⟨Fin.snoc (α := fun _ => Fin A.N) r a.2, ?_, ?_⟩
  · rw [wordOfCoordinates_finSnoc, retainedBelow_append_iff]
    exact ⟨hret, by simpa using ha⟩
  · rw [wordOfCoordinates_finSnoc]
    simpa using hadesc

theorem monotone_prunedColumnCount (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (ω : Ω) :
    Monotone fun L => prunedColumnCount X L ω :=
  monotone_nat_of_le_succ fun L => prunedColumnCount_le_succ X L ω

end Monotone

noncomputable def blockRows (x : Configuration A) (c : Word A) {ℓ : ℕ}
    (σ : ColumnWord A ℓ) : Finset (RowWord A ℓ) := by
  classical
  exact (Finset.univ : Finset (RowWord A ℓ)).filter fun r =>
    retainedBelowConfig x c (wordOfCoordinates σ r)

lemma mem_blockRows {x : Configuration A} {c : Word A} {ℓ : ℕ} {σ : ColumnWord A ℓ}
    {r : RowWord A ℓ} : r ∈ blockRows x c σ ↔ retainedBelowConfig x c (wordOfCoordinates σ r) := by
  classical
  simp [blockRows]

noncomputable def blockChildOf (c : Word A) {ℓ : ℕ} (σ : ColumnWord A ℓ)
    (s : Finset (RowWord A ℓ)) : Option (Word A) :=
  if h : s.Nonempty then some (c ++ wordOfCoordinates σ h.choose) else none

noncomputable def blockChild (x : Configuration A) (c : Word A) {ℓ : ℕ}
    (σ : ColumnWord A ℓ) : Option (Word A) :=
  blockChildOf c σ (blockRows x c σ)

lemma blockChild_eq_some {x : Configuration A} {c : Word A} {ℓ : ℕ} {σ : ColumnWord A ℓ}
    {w : Word A} (h : blockChild x c σ = some w) :
    ∃ r : RowWord A ℓ, retainedBelowConfig x c (wordOfCoordinates σ r) ∧
      w = c ++ wordOfCoordinates σ r := by
  unfold blockChild blockChildOf at h
  split_ifs at h with hne
  · exact ⟨hne.choose, mem_blockRows.mp hne.choose_spec, (Option.some.inj h).symm⟩

lemma card_toFinset_blockChild (x : Configuration A) (c : Word A) {ℓ : ℕ}
    (σ : ColumnWord A ℓ) :
    (blockChild x c σ).toFinset.card = if (blockRows x c σ).Nonempty then 1 else 0 := by
  unfold blockChild blockChildOf
  split_ifs <;> simp

noncomputable def blockChildren (x : Configuration A) (ℓ : ℕ) (c : Word A) :
    Finset (Word A) :=
  (Finset.univ : Finset (ColumnWord A ℓ)).biUnion fun σ => (blockChild x c σ).toFinset

lemma mem_blockChildren {x : Configuration A} {ℓ : ℕ} {c w : Word A} :
    w ∈ blockChildren x ℓ c ↔ ∃ σ : ColumnWord A ℓ, blockChild x c σ = some w := by
  simp [blockChildren, Option.mem_def]

lemma card_blockChildren (x : Configuration A) (ℓ : ℕ) (c : Word A) :
    (blockChildren x ℓ c).card = occupiedColumnCountConfig x c ℓ := by
  classical
  unfold blockChildren
  rw [Finset.card_biUnion]
  · simp_rw [card_toFinset_blockChild]
    rw [← Finset.card_filter]
    unfold occupiedColumnCountConfig
    congr 1
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← Finset.card_pos]
    rfl
  · intro σ _ σ' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro w hw hw'
    rw [Option.mem_toFinset, Option.mem_def] at hw hw'
    obtain ⟨r, -, rfl⟩ := blockChild_eq_some hw
    obtain ⟨r', -, h⟩ := blockChild_eq_some hw'
    exact hne (columns_eq_of_wordOfCoordinates_eq (List.append_cancel_left h))

noncomputable def blockReps (x : Configuration A) (ℓ : ℕ) : ℕ → Finset (Word A)
  | 0 => {[]}
  | t + 1 => (blockReps x ℓ t).biUnion (blockChildren x ℓ)

theorem mem_blockReps {x : Configuration A} {ℓ : ℕ} :
    ∀ {t : ℕ} {w : Word A}, w ∈ blockReps x ℓ t → w.length = t * ℓ ∧ retainedBelowConfig x [] w
  | 0, w, hw => by
      simp only [blockReps, Finset.mem_singleton] at hw
      subst hw
      simp
  | t + 1, w, hw => by
      simp only [blockReps, Finset.mem_biUnion] at hw
      obtain ⟨c, hc, hw⟩ := hw
      obtain ⟨σ, hσ⟩ := mem_blockChildren.mp hw
      obtain ⟨r, hr, rfl⟩ := blockChild_eq_some hσ
      obtain ⟨hlen, hret⟩ := mem_blockReps hc
      refine ⟨by simp [hlen, Nat.succ_mul], ?_⟩
      exact (RetainedTreeEq.retainedBelowConfig_append_iff x [] c _).mpr ⟨hret, hr⟩

theorem card_blockReps_succ (x : Configuration A) (ℓ t : ℕ) :
    (blockReps x ℓ (t + 1)).card =
      ∑ c ∈ blockReps x ℓ t, occupiedColumnCountConfig x c ℓ := by
  rw [blockReps, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun c _ => card_blockChildren x ℓ c
  · intro c hc c' hc' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro w hw hw'
    obtain ⟨σ, hσ⟩ := mem_blockChildren.mp hw
    obtain ⟨σ', hσ'⟩ := mem_blockChildren.mp hw'
    obtain ⟨r, -, rfl⟩ := blockChild_eq_some hσ
    obtain ⟨r', -, h⟩ := blockChild_eq_some hσ'
    have hlen : c.length = c'.length := by
      rw [(mem_blockReps hc).1, (mem_blockReps hc').1]
    exact hne (List.append_inj h hlen).1

theorem blockReps_eq_of_map_fst_eq {x : Configuration A} {ℓ : ℕ} :
    ∀ {t : ℕ} {w w' : Word A}, w ∈ blockReps x ℓ t → w' ∈ blockReps x ℓ t →
      w.map Prod.fst = w'.map Prod.fst → w = w'
  | 0, w, w', hw, hw', _ => by
      simp only [blockReps, Finset.mem_singleton] at hw hw'
      rw [hw, hw']
  | t + 1, w, w', hw, hw', h => by
      simp only [blockReps, Finset.mem_biUnion] at hw hw'
      obtain ⟨c, hc, hw⟩ := hw
      obtain ⟨c', hc', hw'⟩ := hw'
      obtain ⟨σ, hσ⟩ := mem_blockChildren.mp hw
      obtain ⟨σ', hσ'⟩ := mem_blockChildren.mp hw'
      obtain ⟨r, -, hwr⟩ := blockChild_eq_some hσ
      obtain ⟨r', -, hwr'⟩ := blockChild_eq_some hσ'
      rw [hwr, hwr', List.map_append, List.map_append, wordOfCoordinates_map_fst,
        wordOfCoordinates_map_fst] at h
      have hl : (c.map Prod.fst).length = (c'.map Prod.fst).length := by
        rw [List.length_map, List.length_map, (mem_blockReps hc).1, (mem_blockReps hc').1]
      obtain ⟨h1, h2⟩ := List.append_inj h hl
      have hcc : c = c' := blockReps_eq_of_map_fst_eq hc hc' h1
      have hss : σ = σ' := List.ofFn_injective h2
      subst hcc hss
      exact Option.some.inj (hσ.symm.trans hσ')

lemma blockRows_congr {x y : Configuration A} {d : ℕ}
    (hxy : ∀ q : Word A × (Fin A.M × Fin A.N), q.1.length < d → x q = y q) {c : Word A}
    {ℓ : ℕ} (σ : ColumnWord A ℓ) (hlen : c.length + ℓ ≤ d) :
    blockRows x c σ = blockRows y c σ := by
  ext r
  rw [mem_blockRows, mem_blockRows]
  exact retainedBelowConfig_congr hxy (by rw [length_wordOfCoordinates]; exact hlen)

theorem blockReps_congr {x y : Configuration A} {ℓ : ℕ} :
    ∀ t : ℕ, (∀ q : Word A × (Fin A.M × Fin A.N), q.1.length < t * ℓ → x q = y q) →
      blockReps x ℓ t = blockReps y ℓ t
  | 0, _ => rfl
  | t + 1, hxy => by
      have hxy' : ∀ q : Word A × (Fin A.M × Fin A.N), q.1.length < t * ℓ → x q = y q :=
        fun q hq => hxy q (lt_of_lt_of_le hq (Nat.mul_le_mul_right ℓ (Nat.le_succ t)))
      simp only [blockReps]
      rw [blockReps_congr t hxy']
      refine Finset.biUnion_congr rfl fun c hc => ?_
      have hlen := (mem_blockReps hc).1
      unfold blockChildren blockChild
      refine Finset.biUnion_congr rfl fun σ _ => ?_
      rw [blockRows_congr hxy σ (by rw [hlen, Nat.succ_mul])]

open Classical in

theorem card_filter_blockReps_le_prunedColumnCountConfig (x : Configuration A)
    (ℓ t : ℕ) :
    ((blockReps x ℓ t).filter fun w => hasInfiniteDescentConfig x w).card ≤
      prunedColumnCountConfig x [] (t * ℓ) := by
  classical
  set S := (blockReps x ℓ t).filter fun w => hasInfiniteDescentConfig x w with hS
  set V := (Finset.univ : Finset (ColumnWord A (t * ℓ))).filter fun v =>
    ∃ r : RowWord A (t * ℓ), retainedBelowConfig x [] (wordOfCoordinates v r) ∧
      hasInfiniteDescentConfig x ([] ++ wordOfCoordinates v r) with hV
  have hinj : Set.InjOn (fun w : Word A => w.map Prod.fst) S := by
    intro w hw w' hw' h
    exact blockReps_eq_of_map_fst_eq (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp hw').1 h
  calc S.card = (S.image fun w => w.map Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (V.image fun v => List.ofFn v).card := by
        refine Finset.card_le_card fun l hl => ?_
        rw [Finset.mem_image] at hl ⊢
        obtain ⟨w, hw, rfl⟩ := hl
        obtain ⟨hwS, hdesc⟩ := Finset.mem_filter.mp hw
        obtain ⟨hlen, hret⟩ := mem_blockReps hwS
        obtain ⟨v, r, rfl⟩ := exists_wordOfCoordinates_eq_of_length hlen
        exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, r, hret, by simpa using hdesc⟩,
          (wordOfCoordinates_map_fst v r).symm⟩
    _ ≤ V.card := Finset.card_image_le
    _ = prunedColumnCountConfig x [] (t * ℓ) := by
        rw [hV]
        unfold prunedColumnCountConfig
        rfl

end FractalGeometry.Probability.GridPercolation
