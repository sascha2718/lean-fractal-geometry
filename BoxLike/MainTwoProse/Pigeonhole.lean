module

/-
The pigeonhole step of the proof of `thm:main2` in `sec:dimension_result_proof`: "Write
`k⃗ = (k_1, …, k_{2N}) ∈ {0, …, n}^{2N}` for the vector of digit frequencies and set
`W_{n,ε}(k⃗) = {𝐢 ∈ W_{n,ε} : #{0 ≤ r < n : i_r = j} = k_j for j = 1, …, 2N}`. By pigeonholing, we
may choose `k⃗` such that `#W_{n,ε}(k⃗) ≥ (n+1)^{-2N} exp(n(h-ε))`. By construction, for all words
in `W_{n,ε}(k⃗)` both diagonal entries are products of the same scalar factors with the same
multiplicities, so the associated planar matrices coincide." The loss of the pigeonhole is the
factor `(n+1)^{2N}`, which is `e^{o(n)}`.

* `card_piFinset_range`: there are `(n+1)^{#D}` count vectors with entries at most `n`.
* `countVector_mem_piFinset`: the count vector of a word of length `n` is one of them.
* `exists_large_class`, `log_card_le_log_card_class_add`: a largest class has at least
  `#s / #t` elements, so `log #s ≤ log #(class) + log #t`.
* `tendsto_log_card_classes_div`: `log (n+1)^{2N} / n → 0`.
* `System.gDeriv_codeWord_eq_of_count_eq`: on a class both coordinate derivatives are constant.
-/
public import BoxLike.TypicalWords

@[expose] public section

namespace BoxLike

open Filter Topology

/-- There are `(n+1)^{#D}` count vectors `D → {0, …, n}`. -/
theorem card_piFinset_range (D : Type*) [Fintype D] [DecidableEq D] (n : ℕ) :
    (Fintype.piFinset fun _ : D => Finset.range (n + 1)).card = (n + 1) ^ Fintype.card D := by
  rw [Fintype.card_piFinset]
  simp [Finset.prod_const, Finset.card_range]

/-- The count vector of a word of length `n` has entries at most `n`. -/
theorem countVector_mem_piFinset {D : Type*} [Fintype D] [DecidableEq D] {u : List D} {n : ℕ}
    (hu : u.length = n) :
    (fun p => u.count p) ∈ Fintype.piFinset fun _ : D => Finset.range (n + 1) := by
  rw [Fintype.mem_piFinset]
  intro p
  rw [Finset.mem_range]
  have := List.count_le_length (a := p) (l := u)
  omega

/-- The pigeonhole: if a non-empty finite set `s` is mapped into a finite set `t` of classes,
some class `k ∈ t` has at least `#s / #t` elements, `#s ≤ #(class) · #t`. -/
theorem exists_large_class {α β : Type*} [DecidableEq β] {s : Finset α} {t : Finset β}
    {key : α → β} (hmaps : ∀ a ∈ s, key a ∈ t) (hs : s.Nonempty) :
    ∃ k ∈ t, (s.filter fun a => key a = k).Nonempty ∧
      (s.card : ℝ) ≤ (s.filter fun a => key a = k).card * t.card := by
  obtain ⟨a₀, ha₀⟩ := hs
  have ht : t.Nonempty := ⟨key a₀, hmaps a₀ ha₀⟩
  have htpos : (0 : ℝ) < t.card := Nat.cast_pos.2 (Finset.card_pos.2 ht)
  have hspos : (0 : ℝ) < s.card := Nat.cast_pos.2 (Finset.card_pos.2 ⟨a₀, ha₀⟩)
  obtain ⟨k, hk, hle⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (b := (s.card : ℝ) / t.card) hmaps ht (by rw [nsmul_eq_mul, mul_div_cancel₀ _ htpos.ne'])
  refine ⟨k, hk, ?_, ?_⟩
  · have : (0 : ℝ) < (s.filter fun a => key a = k).card := lt_of_lt_of_le (by positivity) hle
    exact Finset.card_pos.1 (Nat.cast_pos.1 this)
  · rwa [div_le_iff₀ htpos] at hle

/-- The loss of the pigeonhole in logarithmic form: `log #s ≤ log #(class) + log #t`. -/
theorem log_card_le_log_card_class_add {α : Type*} {s c : Finset α} {T : ℕ} (hc : c.Nonempty)
    (hT : 0 < T) (h : (s.card : ℝ) ≤ c.card * T) (hs : s.Nonempty) :
    Real.log s.card ≤ Real.log c.card + Real.log T := by
  have hcpos : (0 : ℝ) < c.card := Nat.cast_pos.2 (Finset.card_pos.2 hc)
  have hspos : (0 : ℝ) < s.card := Nat.cast_pos.2 (Finset.card_pos.2 hs)
  have hTpos : (0 : ℝ) < T := Nat.cast_pos.2 hT
  calc Real.log s.card ≤ Real.log (c.card * T) := Real.log_le_log hspos h
    _ = Real.log c.card + Real.log T := Real.log_mul hcpos.ne' hTpos.ne'

/-- The pigeonhole loss is `e^{o(n)}`: `log (n+1)^{2N} / n → 0`. -/
theorem tendsto_log_card_classes_div (D : ℕ) :
    Tendsto (fun n : ℕ => Real.log (((n + 1) ^ D : ℕ) : ℝ) / n) atTop (𝓝 0) := by
  have h := tendsto_errorTerm_div 0 D
  refine h.congr fun n => ?_
  push_cast
  rw [Real.log_pow, zero_add]

namespace System

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (S : System ι)

/-- On a class of words with a common count vector of the `2N` symbols of their horizontal
paths, both coordinate derivatives, including their signs, are constant: they are products of
the same scalar factors (proof of `thm:main2`). -/
theorem gDeriv_codeWord_eq_of_count_eq {u u' : List ι}
    (h : ∀ p, (S.codeWord 0 u).count p = (S.codeWord 0 u').count p) (c : ZMod 2) :
    S.gDeriv (S.codeWord c u) = S.gDeriv (S.codeWord c u') := by
  rcases zmod_two_cases c with rfl | rfl
  · rw [gDeriv_eq_prod_count, gDeriv_eq_prod_count]
    simp only [h]
  · rw [gDeriv_eq_prod_count, gDeriv_eq_prod_count]
    simp only [count_codeWord_one, h]

end System

end BoxLike
