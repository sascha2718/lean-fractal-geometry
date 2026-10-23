import Mathlib
import FractalGeometry.Entropy.Lq.BSG.Basic

open Finset

open scoped Pointwise

namespace FractalGeometry.Lq.BSG

lemma sum_le_sum_filter_add {ι : Type*} (s : Finset ι) (f : ι → ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∑ i ∈ s, f i ≤ ∑ i ∈ s with θ ≤ f i, f i + θ * #s := by
  classical
  rw [← sum_filter_add_sum_filter_not s (fun i => θ ≤ f i)]
  have h2 : ∑ i ∈ s with ¬ θ ≤ f i, f i ≤ #{i ∈ s | ¬ θ ≤ f i} * θ := by
    simpa using sum_le_card_nsmul _ _ θ (fun i hi => (not_le.1 (mem_filter.1 hi).2).le)
  have h3 : (#{i ∈ s | ¬ θ ≤ f i} : ℝ) ≤ #s := by exact_mod_cast card_filter_le _ _
  nlinarith

set_option maxHeartbeats 400000 in

lemma paths {α : Type*} [DecidableEq α] (U V : Finset α) (Γ : Finset (α × α))
    (hΓ : Γ ⊆ U ×ˢ V) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hcard : δ * #U * #V ≤ #Γ) :
    ∃ U' ⊆ U, ∃ V' ⊆ V, δ / 6 * #U ≤ #U' ∧ δ / 4 * #V ≤ #V' ∧
      ∀ u ∈ U', ∀ v ∈ V', δ ^ 5 / 2 ^ 14 * #U * #V ≤
        #{q ∈ V ×ˢ U | (u, q.1) ∈ Γ ∧ (q.2, q.1) ∈ Γ ∧ (q.2, v) ∈ Γ} := by
  classical
  rcases U.eq_empty_or_nonempty with rfl | hU
  · refine ⟨∅, empty_subset _, V, Subset.rfl, by simp, ?_, by simp⟩
    have : (0 : ℝ) ≤ #V := by positivity
    nlinarith
  rcases V.eq_empty_or_nonempty with rfl | hV
  · refine ⟨U, Subset.rfl, ∅, empty_subset _, ?_, by simp, by simp⟩
    have : (0 : ℝ) ≤ #U := by positivity
    nlinarith
  have hU0' : (0 : ℝ) < #U := by exact_mod_cast hU.card_pos
  have hV0' : (0 : ℝ) < #V := by exact_mod_cast hV.card_pos

  set N : α → Finset α := fun u => V.filter (fun v => (u, v) ∈ Γ) with hN
  set U0 := U.filter (fun u => δ / 2 * #V ≤ (#(N u) : ℝ)) with hU0def
  have hΓsum : (#Γ : ℝ) = ∑ u ∈ U, (#(N u) : ℝ) := by
    have : #Γ = ∑ u ∈ U, #(N u) := by
      rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := U)
        (fun p hp => (mem_product.1 (hΓ hp)).1)]
      refine sum_congr rfl fun u _ => ?_
      refine card_nbij' (fun p => p.2) (fun v => (u, v)) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [mem_coe, mem_filter, hN] at hp ⊢
        refine ⟨(mem_product.1 (hΓ hp.1)).2, ?_⟩
        rw [← hp.2]; exact hp.1
      · intro v hv
        simp only [mem_coe, mem_filter, hN] at hv ⊢
        exact ⟨hv.2, trivial⟩
      · intro p hp
        simp only [mem_coe, mem_filter] at hp
        ext
        · exact hp.2.symm
        · rfl
      · intro v _; rfl
    exact_mod_cast this
  have hsumU0 : δ / 2 * #U * #V ≤ ∑ u ∈ U0, (#(N u) : ℝ) := by
    have := sum_le_sum_filter_add U (fun u => (#(N u) : ℝ)) (θ := δ / 2 * #V) (by positivity)
    rw [← hΓsum] at this
    nlinarith

  set W : α → Finset α := fun v => U0.filter (fun u => (u, v) ∈ Γ) with hW
  have hW1 : ∑ v ∈ V, (#(W v) : ℝ) = ∑ u ∈ U0, (#(N u) : ℝ) := by
    have : ∑ v ∈ V, #(W v) = ∑ u ∈ U0, #(N u) := by
      simp_rw [hW, hN, card_filter]
      exact sum_comm
    exact_mod_cast this
  set c : α × α → ℕ := fun p => #{v ∈ V | (p.1, v) ∈ Γ ∧ (p.2, v) ∈ Γ} with hc
  have hW2 : ∑ v ∈ V, (#(W v) : ℝ) ^ 2 = ∑ p ∈ U0 ×ˢ U0, (c p : ℝ) := by
    have : ∑ v ∈ V, #(W v) ^ 2 = ∑ p ∈ U0 ×ˢ U0, c p := by
      have hsq : ∀ v, #(W v) ^ 2 =
          ∑ p ∈ U0 ×ˢ U0, if (p.1, v) ∈ Γ ∧ (p.2, v) ∈ Γ then 1 else 0 := by
        intro v
        rw [← card_filter, sq, ← card_product]
        congr 1
        ext q
        simp only [mem_product, mem_filter, hW]
        tauto
      simp_rw [hsq, hc, card_filter]
      exact sum_comm
    exact_mod_cast this

  set η : ℝ := δ ^ 3 / 256 with hη
  set ε' : ℝ := δ / 32 with hε'
  have hε'0 : 0 < ε' := by positivity
  set bad : α → ℕ := fun v => #{p ∈ W v ×ˢ W v | (c p : ℝ) < η * #V} with hbad
  set B0 := (U0 ×ˢ U0).filter (fun p => (c p : ℝ) < η * #V) with hB0
  have hbadsum : ∑ v ∈ V, (bad v : ℝ) ≤ η * #V * #U ^ 2 := by
    have h1 : ∑ v ∈ V, bad v = ∑ p ∈ B0, c p := by
      have hb : ∀ v, bad v = ∑ p ∈ B0, if (p.1, v) ∈ Γ ∧ (p.2, v) ∈ Γ then 1 else 0 := by
        intro v
        rw [← card_filter]
        show #{p ∈ W v ×ˢ W v | (c p : ℝ) < η * #V} = _
        congr 1
        ext q
        simp only [mem_product, mem_filter, hW, hB0]
        tauto
      simp_rw [hb, hc, card_filter]
      exact sum_comm
    have h2 : ∑ p ∈ B0, (c p : ℝ) ≤ #B0 * (η * #V) := by
      simpa using sum_le_card_nsmul B0 (fun p => (c p : ℝ)) (η * #V)
        (fun p hp => (mem_filter.1 hp).2.le)
    have h3 : (#B0 : ℝ) ≤ #U ^ 2 := by
      have : #B0 ≤ #U ^ 2 := by
        calc #B0 ≤ #(U0 ×ˢ U0) := card_filter_le _ _
          _ = #U0 ^ 2 := by rw [card_product, sq]
          _ ≤ #U ^ 2 := by gcongr; exact filter_subset _ _
      exact_mod_cast this
    have h1' : ∑ v ∈ V, (bad v : ℝ) = ∑ p ∈ B0, (c p : ℝ) := by exact_mod_cast h1
    rw [h1']
    calc _ ≤ #B0 * (η * #V) := h2
      _ ≤ #U ^ 2 * (η * #V) := by gcongr
      _ = _ := by ring

  have hCS : δ ^ 2 / 4 * #U ^ 2 * #V ≤ ∑ v ∈ V, (#(W v) : ℝ) ^ 2 := by
    have h1 : (∑ v ∈ V, (#(W v) : ℝ)) ^ 2 ≤ #V * ∑ v ∈ V, (#(W v) : ℝ) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h2 : δ / 2 * #U * #V ≤ ∑ v ∈ V, (#(W v) : ℝ) := hW1 ▸ hsumU0
    have h3 : (δ / 2 * #U * #V) ^ 2 ≤ #V * ∑ v ∈ V, (#(W v) : ℝ) ^ 2 :=
      (pow_le_pow_left₀ (by positivity) h2 2).trans h1
    have key : δ ^ 2 / 4 * #U ^ 2 * #V * #V ≤ (∑ v ∈ V, (#(W v) : ℝ) ^ 2) * #V := by
      nlinarith
    exact le_of_mul_le_mul_right key hV0'

  obtain ⟨v0, hv0V, hv0⟩ : ∃ v ∈ V, δ ^ 2 / 8 * #U ^ 2 ≤ (#(W v) : ℝ) ^ 2 - bad v / ε' := by
    refine exists_le_of_sum_le hV ?_
    rw [sum_sub_distrib, ← sum_div, sum_const, nsmul_eq_mul]
    have : (∑ v ∈ V, (bad v : ℝ)) / ε' ≤ δ ^ 2 / 8 * #U ^ 2 * #V := by
      rw [div_le_iff₀ hε'0]
      calc _ ≤ η * #V * #U ^ 2 := hbadsum
        _ = _ := by rw [hη, hε']; ring
    nlinarith
  set W0 := W v0 with hW0
  have hbad0 : (bad v0 : ℝ) ≤ ε' * #W0 ^ 2 := by
    have : (0 : ℝ) ≤ δ ^ 2 / 8 * #U ^ 2 := by positivity
    have h := hv0
    rw [le_sub_iff_add_le] at h
    have h' : (bad v0 : ℝ) / ε' ≤ #W0 ^ 2 := by linarith
    rwa [div_le_iff₀ hε'0, mul_comm] at h'
  have hW0card : δ / 3 * #U ≤ #W0 := by
    have hb0 : (0 : ℝ) ≤ bad v0 / ε' := by positivity
    have h : δ ^ 2 / 8 * #U ^ 2 ≤ (#W0 : ℝ) ^ 2 := by linarith
    have h2 : (δ / 3 * #U) ^ 2 ≤ (#W0 : ℝ) ^ 2 := by
      calc (δ / 3 * #U) ^ 2 = δ ^ 2 / 9 * #U ^ 2 := by ring
        _ ≤ δ ^ 2 / 8 * #U ^ 2 := by gcongr; norm_num
        _ ≤ _ := h
    exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) h2

  set bset : α → Finset α := fun u => W0.filter (fun u' => (c (u, u') : ℝ) < η * #V)
    with hbset
  have hbsum : ∑ u ∈ W0, (#(bset u) : ℝ) = bad v0 := by
    have : ∑ u ∈ W0, #(bset u) = bad v0 := by
      show _ = #{p ∈ W0 ×ˢ W0 | (c p : ℝ) < η * #V}
      rw [card_filter, sum_product]
      simp_rw [hbset, card_filter]
    exact_mod_cast this
  set U' := W0.filter (fun u => (#(bset u) : ℝ) ≤ 2 * ε' * #W0) with hU'
  have hW0pos : (0 : ℝ) < #W0 := lt_of_lt_of_le (by positivity) hW0card
  have hU'card : (#W0 : ℝ) / 2 ≤ #U' := by
    have h1 : (#{u ∈ W0 | ¬ (#(bset u) : ℝ) ≤ 2 * ε' * #W0} : ℝ) * (2 * ε' * #W0) ≤
        ε' * #W0 ^ 2 := by
      calc _ ≤ ∑ u ∈ W0 with ¬ (#(bset u) : ℝ) ≤ 2 * ε' * #W0, (#(bset u) : ℝ) := by
            rw [← nsmul_eq_mul]
            exact card_nsmul_le_sum _ _ _ (fun u hu => (not_le.1 (mem_filter.1 hu).2).le)
        _ ≤ ∑ u ∈ W0, (#(bset u) : ℝ) :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
        _ = bad v0 := hbsum
        _ ≤ _ := hbad0
    have h2 : (#{u ∈ W0 | ¬ (#(bset u) : ℝ) ≤ 2 * ε' * #W0} : ℝ) * 2 ≤ #W0 := by
      have key : (#{u ∈ W0 | ¬ (#(bset u) : ℝ) ≤ 2 * ε' * #W0} : ℝ) * 2 * (ε' * #W0) ≤
          #W0 * (ε' * #W0) := by
        calc _ = (#{u ∈ W0 | ¬ (#(bset u) : ℝ) ≤ 2 * ε' * #W0} : ℝ) * (2 * ε' * #W0) := by ring
          _ ≤ ε' * #W0 ^ 2 := h1
          _ = _ := by ring
      exact le_of_mul_le_mul_right key (by positivity)
    have h3 : (#U' : ℝ) + #{u ∈ W0 | ¬ (#(bset u) : ℝ) ≤ 2 * ε' * #W0} = #W0 := by
      exact_mod_cast card_filter_add_card_filter_not _
    linarith

  set V' := V.filter (fun v => δ / 4 * #U' ≤ (#{u ∈ U' | (u, v) ∈ Γ} : ℝ)) with hV'
  have hU'pos : (0 : ℝ) < #U' := by linarith
  have hU'U0 : U' ⊆ U0 := (filter_subset _ _).trans (filter_subset _ _)
  have hV'card : δ / 4 * #V ≤ #V' := by
    have h1 : ∑ v ∈ V, (#{u ∈ U' | (u, v) ∈ Γ} : ℝ) = ∑ u ∈ U', (#(N u) : ℝ) := by
      have : ∑ v ∈ V, #{u ∈ U' | (u, v) ∈ Γ} = ∑ u ∈ U', #(N u) := by
        simp_rw [hN, card_filter]; exact sum_comm
      exact_mod_cast this
    have h2 : δ / 2 * #V * #U' ≤ ∑ u ∈ U', (#(N u) : ℝ) := by
      calc δ / 2 * #V * #U' = ∑ u ∈ U', δ / 2 * (#V : ℝ) := by
            rw [sum_const, nsmul_eq_mul]; ring
        _ ≤ _ := sum_le_sum fun u hu => (mem_filter.1 (hU'U0 hu)).2
    have h3 := sum_le_thr_add V (fun v => (#{u ∈ U' | (u, v) ∈ Γ} : ℝ)) (M := #U')
      (θ := δ / 4 * #U') (by positivity) (fun v _ => by exact_mod_cast card_filter_le _ _)
    have key : δ / 4 * #V * #U' ≤ #V' * #U' := by linarith
    exact le_of_mul_le_mul_right key hU'pos

  refine ⟨U', fun u hu => (mem_filter.1 (hU'U0 hu)).1, V', filter_subset _ _, by linarith,
    hV'card, ?_⟩
  intro u hu v hv
  set good := U'.filter (fun u1 => (u1, v) ∈ Γ ∧ η * #V ≤ (c (u, u1) : ℝ)) with hgood
  have hgoodcard : δ ^ 2 / 48 * #U ≤ #good := by
    have h1 : U'.filter (fun u1 => (u1, v) ∈ Γ) ⊆ good ∪ bset u := by
      intro u1 hu1
      simp only [mem_filter, mem_union, hgood, hbset] at hu1 ⊢
      by_cases h : η * #V ≤ (c (u, u1) : ℝ)
      · left; exact ⟨hu1.1, hu1.2, h⟩
      · right; exact ⟨(mem_filter.1 hu1.1).1, not_le.1 h⟩
    have h2 : (#(U'.filter (fun u1 => (u1, v) ∈ Γ)) : ℝ) ≤ #good + #(bset u) := by
      exact_mod_cast (card_le_card h1).trans (card_union_le _ _)
    have h3 : δ / 4 * #U' ≤ (#(U'.filter (fun u1 => (u1, v) ∈ Γ)) : ℝ) := (mem_filter.1 hv).2
    have h4 : (#(bset u) : ℝ) ≤ 2 * ε' * #W0 := (mem_filter.1 hu).2
    rw [hε'] at h4
    have h5 : δ / 4 * (#W0 / 2) ≤ δ / 4 * #U' := by gcongr
    have h6 : δ / 16 * (δ / 3 * #U) ≤ δ / 16 * #W0 := by gcongr
    have h7 : δ ^ 2 / 48 * #U = δ / 16 * (δ / 3 * #U) := by ring
    rw [h7]
    linarith
  have hpaths : ∑ u1 ∈ good, (c (u, u1) : ℝ) ≤
      #{q ∈ V ×ˢ U | (u, q.1) ∈ Γ ∧ (q.2, q.1) ∈ Γ ∧ (q.2, v) ∈ Γ} := by
    have hgoodU : good ⊆ U :=
      (filter_subset _ _).trans (hU'U0.trans (filter_subset _ _))
    have : ∑ u1 ∈ good, c (u, u1) ≤
        #{q ∈ V ×ˢ U | (u, q.1) ∈ Γ ∧ (q.2, q.1) ∈ Γ ∧ (q.2, v) ∈ Γ} := by
      rw [card_eq_sum_card_fiberwise (f := Prod.snd) (t := U)
        (fun q hq => (mem_product.1 (mem_filter.1 hq).1).2)]
      calc ∑ u1 ∈ good, c (u, u1) = ∑ u1 ∈ good, #{q ∈ {q ∈ V ×ˢ U | (u, q.1) ∈ Γ ∧
            (q.2, q.1) ∈ Γ ∧ (q.2, v) ∈ Γ} | q.2 = u1} := by
            refine sum_congr rfl fun u1 hu1 => ?_
            have hu1U : u1 ∈ U := hgoodU hu1
            have hu1v : (u1, v) ∈ Γ := (mem_filter.1 hu1).2.1
            refine card_nbij' (fun v1 => (v1, u1)) (fun q => q.1) ?_ ?_ ?_ ?_
            · intro v1 hv1
              simp only [mem_coe, mem_filter, mem_product] at hv1 ⊢
              exact ⟨⟨⟨hv1.1, hu1U⟩, hv1.2.1, hv1.2.2, hu1v⟩, trivial⟩
            · intro q hq
              simp only [mem_coe, mem_filter, mem_product] at hq ⊢
              obtain ⟨⟨⟨h1, h2⟩, h3, h4, h5⟩, h6⟩ := hq
              exact ⟨h1, h3, h6 ▸ h4⟩
            · intro v1 _; rfl
            · intro q hq
              simp only [mem_coe, mem_filter] at hq
              ext
              · rfl
              · exact hq.2.symm
        _ ≤ _ := sum_le_sum_of_subset hgoodU
    exact_mod_cast this
  calc δ ^ 5 / 2 ^ 14 * #U * #V ≤ (δ ^ 2 / 48 * #U) * (η * #V) := by
        rw [hη]
        have : (0 : ℝ) ≤ δ ^ 5 * #U * #V := by positivity
        nlinarith
    _ ≤ #good * (η * #V) := by gcongr
    _ = ∑ u1 ∈ good, η * #V := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ u1 ∈ good, (c (u, u1) : ℝ) := sum_le_sum (fun u1 hu1 => (mem_filter.1 hu1).2.2)
    _ ≤ _ := hpaths

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

lemma diff_bsg (U D : Finset G) {δ M : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hU : U.Nonempty)
    (hcard : δ * #U ^ 2 ≤ #{p ∈ U ×ˢ U | p.1 - p.2 ∈ D}) (hD : #D ≤ M * #U) :
    ∃ H ⊆ U, δ / 6 * #U ≤ #H ∧ #(H - H) ≤ 2 ^ 33 * M ^ 6 / δ ^ 12 * #H := by
  classical
  set Γ := (U ×ˢ U).filter (fun p => p.1 - p.2 ∈ D) with hΓ
  have hU0 : (0 : ℝ) < #U := by exact_mod_cast hU.card_pos
  obtain ⟨U', hU'U, V', hV'U, hU'card, hV'card, hpath⟩ :=
    paths U U Γ (filter_subset _ _) hδ hδ1 (by rw [mul_assoc, ← sq]; exact hcard)
  have hV'pos : (0 : ℝ) < #V' := lt_of_lt_of_le (by positivity) hV'card
  have hM : 0 ≤ M := by
    by_contra h
    have h := lt_of_not_ge h
    have : M * #U < 0 := mul_neg_of_neg_of_pos h hU0
    have : (0 : ℝ) ≤ #D := by positivity
    linarith

  set P : ℝ := δ ^ 5 / 2 ^ 14 * #U * #U with hP
  have hPpos : 0 < P := by positivity
  have hdiff : (#(U' - V') : ℝ) * P ≤ #D ^ 3 := by
    have hy : ∀ y ∈ U' - V',
        P ≤ (#{t ∈ D ×ˢ (D ×ˢ D) | t.1 - t.2.1 + t.2.2 = y} : ℝ) := by
      intro y hy
      obtain ⟨u, hu, v, hv, rfl⟩ := mem_sub.1 hy
      refine (hpath u hu v hv).trans ?_
      refine Nat.cast_le.2 (card_le_card_of_injOn
        (fun q => (u - q.1, q.2 - q.1, q.2 - v)) ?_ ?_)
      · intro q hq
        simp only [mem_coe, mem_filter, mem_product, hΓ] at hq ⊢
        obtain ⟨-, ⟨-, h1⟩, ⟨-, h2⟩, ⟨-, h3⟩⟩ := hq
        exact ⟨⟨h1, h2, h3⟩, by abel⟩
      · intro q _ q' _ h
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, -, h3⟩ := h
        ext
        · exact sub_right_injective h1
        · exact sub_left_injective h3
    have hsum : ∑ y ∈ U' - V', (#{t ∈ D ×ˢ (D ×ˢ D) | t.1 - t.2.1 + t.2.2 = y} : ℝ) ≤
        #D ^ 3 := by
      have : ∑ y ∈ U' - V', #{t ∈ D ×ˢ (D ×ˢ D) | t.1 - t.2.1 + t.2.2 = y} ≤ #D ^ 3 := by
        rw [sum_card_fiberwise_eq_card_filter]
        calc _ ≤ #(D ×ˢ (D ×ˢ D)) := card_filter_le _ _
          _ = #D ^ 3 := by rw [card_product, card_product]; ring
      exact_mod_cast this
    calc (#(U' - V') : ℝ) * P = ∑ y ∈ U' - V', P := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum hy
      _ ≤ _ := hsum
  have h1 : (#(U' - V') : ℝ) ≤ 2 ^ 14 * M ^ 3 * #U / δ ^ 5 := by
    have hD3 : (#D : ℝ) ^ 3 ≤ (M * #U) ^ 3 := pow_le_pow_left₀ (by positivity) hD 3
    have := (le_div_iff₀ hPpos).2 (hdiff.trans hD3)
    calc _ ≤ (M * #U) ^ 3 / P := this
      _ = _ := by rw [hP]; field_simp

  have hruzsa : (#(U' - U') : ℝ) * #V' ≤ #(U' - V') * #(U' - V') := by
    exact_mod_cast ruzsa_triangle_inequality_sub_sub_sub U' V' U'
  refine ⟨U', hU'U, hU'card, ?_⟩
  have h2 : (#(U' - U') : ℝ) ≤ (2 ^ 14 * M ^ 3 * #U / δ ^ 5) ^ 2 / (δ / 4 * #U) := by
    rw [le_div_iff₀ (by positivity)]
    calc (#(U' - U') : ℝ) * (δ / 4 * #U) ≤ #(U' - U') * #V' := by gcongr
      _ ≤ #(U' - V') * #(U' - V') := hruzsa
      _ = (#(U' - V') : ℝ) ^ 2 := by ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) h1 2
  have h3 : (2 ^ 14 * M ^ 3 * #U / δ ^ 5) ^ 2 / (δ / 4 * #U) =
      2 ^ 30 * M ^ 6 / δ ^ 11 * #U := by
    field_simp
    ring
  have h4 : (#U : ℝ) ≤ 6 / δ * #U' := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    linarith
  calc (#(U' - U') : ℝ) ≤ 2 ^ 30 * M ^ 6 / δ ^ 11 * #U := h2.trans h3.le
    _ ≤ 2 ^ 30 * M ^ 6 / δ ^ 11 * (6 / δ * #U') := by gcongr
    _ = 6 * 2 ^ 30 * M ^ 6 / δ ^ 12 * #U' := by field_simp
    _ ≤ 2 ^ 33 * M ^ 6 / δ ^ 12 * #U' := by gcongr; norm_num

end FractalGeometry.Lq.BSG
