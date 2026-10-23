import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.Configuration
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.Processes
import FractalGeometry.Probability.GridPercolation.RetainedTreeEvents
import FractalGeometry.Probability.GridPercolation.RootIndependence
import FractalGeometry.Probability.GridPercolation.ShallowEvents
import FractalGeometry.Probability.GridPercolation.WordSplitting

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

variable {A : GridLaw}

noncomputable def chooseSubset {α : Type*} (s : Finset α) (c : ℕ) : Finset α :=
  if h : c ≤ s.card then Classical.choose (Finset.exists_subset_card_eq h) else s

lemma chooseSubset_subset {α : Type*} (s : Finset α) (c : ℕ) : chooseSubset s c ⊆ s := by
  unfold chooseSubset
  split_ifs with h
  · exact (Classical.choose_spec (Finset.exists_subset_card_eq h)).1
  · exact subset_rfl

lemma chooseSubset_card {α : Type*} {s : Finset α} {c : ℕ} (h : c ≤ s.card) :
    (chooseSubset s c).card = c := by
  unfold chooseSubset
  rw [dite_eq_left h]
  exact (Classical.choose_spec (Finset.exists_subset_card_eq h)).2

def childrenConfig (x : Configuration A) (T : Finset (Word A)) : Finset (Word A) :=
  T.biUnion fun w =>
    ((Finset.univ : Finset (Fin A.M × Fin A.N)).filter fun a => x (w, a) = true).image
      fun a => w ++ [a]

lemma mem_childrenConfig {x : Configuration A} {T : Finset (Word A)} {v : Word A} :
    v ∈ childrenConfig x T ↔ ∃ w ∈ T, ∃ a, x (w, a) = true ∧ v = w ++ [a] := by
  unfold childrenConfig
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨w, hw, a, ha, rfl⟩
    exact ⟨w, hw, a, ha, rfl⟩
  · rintro ⟨w, hw, a, ha, rfl⟩
    exact ⟨w, hw, a, ha, rfl⟩

def offspringConfig (x : Configuration A) (w : Word A) : ℕ :=
  ((Finset.univ : Finset (Fin A.M × Fin A.N)).filter fun a => x (w, a) = true).card

lemma card_childrenConfig (x : Configuration A) (T : Finset (Word A)) :
    (childrenConfig x T).card = ∑ w ∈ T, offspringConfig x w := by
  unfold childrenConfig offspringConfig
  rw [Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun w _ => ?_
    exact Finset.card_image_of_injective _ fun a b h =>
      List.singleton_injective (List.append_cancel_left h)
  · intro w _ w' _ hww'
    rw [Function.onFun, Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hv hv'
    obtain ⟨a, -, rfl⟩ := hv
    obtain ⟨a', -, h⟩ := hv'
    exact hww' (List.append_inj' h rfl).1.symm

noncomputable def retainedLevel (x : Configuration A) (k : ℕ) : Finset (Word A) := by
  classical
  exact ((Finset.univ : Finset (DigitWord A k)).filter
    fun u => retainedBelowConfig x [] (wordOfDigits u)).image wordOfDigits

lemma mem_retainedLevel {x : Configuration A} {k : ℕ} {w : Word A} :
    w ∈ retainedLevel x k ↔ w.length = k ∧ retainedBelowConfig x [] w := by
  classical
  unfold retainedLevel
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨length_wordOfDigits u, hu⟩
  · rintro ⟨rfl, hret⟩
    exact ⟨w.get, by rwa [wordOfDigits, List.ofFn_get], by rw [wordOfDigits, List.ofFn_get]⟩

noncomputable def exploreG (x : Configuration A) (k₀ : ℕ) (c : ℕ → ℕ) :
    ℕ → Finset (Word A)
  | 0 => retainedLevel x k₀
  | j + 1 => childrenConfig x (exploreG x k₀ c j \ chooseSubset (exploreG x k₀ c j) (c j))

noncomputable def exploreA (x : Configuration A) (k₀ : ℕ) (c : ℕ → ℕ) (j : ℕ) :
    Finset (Word A) :=
  chooseSubset (exploreG x k₀ c j) (c j)

lemma exploreG_zero (x : Configuration A) (k₀ : ℕ) (c : ℕ → ℕ) :
    exploreG x k₀ c 0 = retainedLevel x k₀ := rfl

lemma exploreG_succ (x : Configuration A) (k₀ : ℕ) (c : ℕ → ℕ) (j : ℕ) :
    exploreG x k₀ c (j + 1) = childrenConfig x (exploreG x k₀ c j \ exploreA x k₀ c j) := rfl

lemma retainedBelowConfig_append_singleton {x : Configuration A} {w : Word A}
    {a : Fin A.M × Fin A.N} (hw : retainedBelowConfig x [] w) (ha : x (w, a) = true) :
    retainedBelowConfig x [] (w ++ [a]) := by
  rw [RetainedTreeEq.retainedBelowConfig_append_iff]
  refine ⟨hw, fun l => ?_⟩
  have hl : (l : ℕ) = 0 := by
    have := l.isLt
    simp only [List.length_singleton] at this
    omega
  simpa [hl] using ha

theorem mem_exploreG {x : Configuration A} {k₀ : ℕ} {c : ℕ → ℕ} :
    ∀ {j : ℕ} {w : Word A}, w ∈ exploreG x k₀ c j →
      w.length = k₀ + j ∧ retainedBelowConfig x [] w
  | 0, w, hw => by
      rw [exploreG_zero, mem_retainedLevel] at hw
      exact ⟨by simpa using hw.1, hw.2⟩
  | j + 1, w, hw => by
      rw [exploreG_succ, mem_childrenConfig] at hw
      obtain ⟨v, hv, a, ha, rfl⟩ := hw
      have hv' := mem_exploreG (Finset.mem_sdiff.mp hv).1
      refine ⟨?_, retainedBelowConfig_append_singleton hv'.2 ha⟩
      rw [List.length_append, hv'.1, List.length_singleton]
      ring

def exploreRegionOf (h : ℕ → Finset (Word A)) (k₀ : ℕ) (c : ℕ → ℕ) (J : ℕ) :
    Set (Word A × (Fin A.M × Fin A.N)) :=
  {q | q.1.length < k₀ ∨ ∃ j < J, q.1 ∈ h j \ chooseSubset (h j) (c j)}

def exploreRegion (x : Configuration A) (k₀ : ℕ) (c : ℕ → ℕ) (J : ℕ) :
    Set (Word A × (Fin A.M × Fin A.N)) :=
  exploreRegionOf (exploreG x k₀ c) k₀ c J

theorem exploreG_congr {x y : Configuration A} {k₀ : ℕ} {c : ℕ → ℕ} {J : ℕ}
    (hxy : ∀ q ∈ exploreRegion x k₀ c J, y q = x q) :
    ∀ j ≤ J, exploreG y k₀ c j = exploreG x k₀ c j
  | 0, _ => by
      ext w
      rw [exploreG_zero, exploreG_zero, mem_retainedLevel, mem_retainedLevel]
      refine and_congr_right fun hlen => retainedBelowConfig_congr (c := k₀) ?_ (by simp [hlen])
      intro q hq
      exact hxy q (Or.inl hq)
  | j + 1, hj => by
      have ih := exploreG_congr hxy j (by omega)
      have hA : exploreA y k₀ c j = exploreA x k₀ c j := by
        unfold exploreA
        rw [ih]
      rw [exploreG_succ, exploreG_succ, ih, hA]
      ext v
      rw [mem_childrenConfig, mem_childrenConfig]
      refine exists_congr fun w => and_congr_right fun hw => exists_congr fun a => ?_
      rw [hxy (w, a) (Or.inr ⟨j, by omega, hw⟩)]

end FractalGeometry.Probability.GridPercolation
