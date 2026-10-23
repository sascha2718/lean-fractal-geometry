import Mathlib

open Finset

open scoped Pointwise

namespace FractalGeometry.Lq.BSG

section General

lemma sum_le_thr_add {ι : Type*} (s : Finset ι) (f : ι → ℝ) {M θ : ℝ} (hθ : 0 ≤ θ)
    (hf : ∀ i ∈ s, f i ≤ M) :
    ∑ i ∈ s, f i ≤ θ * #s + M * #{i ∈ s | θ ≤ f i} := by
  classical
  rw [← sum_filter_add_sum_filter_not s (fun i => θ ≤ f i)]
  have h1 : ∑ i ∈ s with θ ≤ f i, f i ≤ #{i ∈ s | θ ≤ f i} * M := by
    simpa using sum_le_card_nsmul _ _ M (fun i hi => hf i (mem_filter.1 hi).1)
  have h2 : ∑ i ∈ s with ¬ θ ≤ f i, f i ≤ #{i ∈ s | ¬ θ ≤ f i} * θ := by
    simpa using sum_le_card_nsmul _ _ θ (fun i hi => (not_le.1 (mem_filter.1 hi).2).le)
  have h3 : (#{i ∈ s | ¬ θ ≤ f i} : ℝ) ≤ #s := by exact_mod_cast card_filter_le _ _
  nlinarith

end General

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def rep (A : Finset G) (x : G) : ℕ := #{a ∈ A | a - x ∈ A}

lemma rep_le (A : Finset G) (x : G) : rep A x ≤ #A := card_filter_le _ _

lemma rep_pos_of_mem_sub {U : Finset G} {x : G} (hx : x ∈ U - U) : 0 < rep U x := by
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_sub.1 hx
  unfold rep
  exact card_pos.2 ⟨u, mem_filter.2 ⟨hu, by simpa using hv⟩⟩

lemma sum_rep_eq (A S : Finset G) :
    ∑ s ∈ S, rep A s = ∑ a ∈ A, #{s ∈ S | a - s ∈ A} := by
  unfold rep
  simp_rw [card_filter]
  exact sum_comm

lemma card_pairs_sub_mem (U D : Finset G) :
    #{p ∈ U ×ˢ U | p.1 - p.2 ∈ D} = ∑ x ∈ D, rep U x := by
  rw [← sum_card_fiberwise_eq_card_filter]
  refine sum_congr rfl fun x _ => ?_
  unfold rep
  refine card_nbij' (fun p => p.1) (fun a => (a, a - x)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [mem_coe, mem_filter, mem_product] at hp ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    refine ⟨h1, ?_⟩
    rw [← h3]; simpa using h2
  · intro a ha
    simp only [mem_coe, mem_filter, mem_product] at ha ⊢
    exact ⟨⟨ha.1, ha.2⟩, by abel⟩
  · intro p hp
    simp only [mem_coe, mem_filter, mem_product] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    ext <;> simp [← h3]
  · intro a _
    simp

lemma addEnergy_eq_sum_rep (A B : Finset G) :
    addEnergy A B = ∑ p ∈ B ×ˢ B, rep A (p.1 - p.2) := by
  unfold addEnergy
  rw [card_eq_sum_card_fiberwise (f := Prod.snd) (t := B ×ˢ B)]
  · refine sum_congr rfl fun p hp => ?_
    rw [filter_filter]
    unfold rep
    refine card_nbij' (fun x => x.1.2) (fun a => ((a - (p.1 - p.2), a), p)) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [mem_coe, mem_filter, mem_product] at hx ⊢
      obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, h6⟩ := hx
      refine ⟨h2, ?_⟩
      rw [← h6]
      have : x.1.2 - (x.2.1 - x.2.2) = x.1.1 := by
        calc x.1.2 - (x.2.1 - x.2.2) = (x.1.2 + x.2.2) - x.2.1 := by abel
          _ = (x.1.1 + x.2.1) - x.2.1 := by rw [h5]
          _ = x.1.1 := by abel
      rw [this]; exact h1
    · intro a ha
      simp only [mem_coe, mem_filter, mem_product] at ha hp ⊢
      refine ⟨⟨⟨ha.2, ha.1⟩, hp⟩, by abel, trivial⟩
    · intro x hx
      simp only [mem_coe, mem_filter, mem_product] at hx
      obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, h6⟩ := hx
      subst h6
      ext
      · show x.1.2 - (x.2.1 - x.2.2) = x.1.1
        calc x.1.2 - (x.2.1 - x.2.2) = (x.1.2 + x.2.2) - x.2.1 := by abel
          _ = (x.1.1 + x.2.1) - x.2.1 := by rw [h5]
          _ = x.1.1 := by abel
      · rfl
      · rfl
      · rfl
    · intro a _; simp
  · intro x hx
    simp only [mem_coe, mem_filter, mem_product] at hx
    simp only [coe_product, Set.mem_prod, mem_coe]
    exact hx.1.2

lemma energy_pairs (A B : Finset G) (hA : A.Nonempty) {ε : ℝ} (hε : 0 ≤ ε)
    (hE : ε * #A * #B ^ 2 ≤ addEnergy A B) :
    ε / 2 * #B ^ 2 ≤ #{p ∈ B ×ˢ B | ε / 2 * #A ≤ rep A (p.1 - p.2)} := by
  have hsum := sum_le_thr_add (B ×ˢ B) (fun p => (rep A (p.1 - p.2) : ℝ)) (M := #A)
    (θ := ε / 2 * #A) (by positivity) (fun p _ => by exact_mod_cast rep_le A _)
  have hE' : (addEnergy A B : ℝ) = ∑ p ∈ B ×ˢ B, (rep A (p.1 - p.2) : ℝ) := by
    exact_mod_cast addEnergy_eq_sum_rep A B
  rw [card_product] at hsum
  push_cast at hsum
  have hA0 : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
  have key : ε / 2 * #B ^ 2 * #A ≤ #{p ∈ B ×ˢ B | ε / 2 * #A ≤ rep A (p.1 - p.2)} * #A := by
    nlinarith
  exact le_of_mul_le_mul_right key hA0

lemma sym_pairs (A S : Finset G) (hA : A.Nonempty) {δ : ℝ} (hδ : 0 ≤ δ)
    (hS : ∀ s ∈ S, δ * #A ≤ rep A s) :
    δ ^ 2 / 2 * #S ^ 2 ≤ #{p ∈ S ×ˢ S | δ ^ 2 / 2 * #A ≤ rep A (p.1 - p.2)} := by
  classical
  set n : G → ℕ := fun a => #{s ∈ S | a - s ∈ A} with hn
  set T : G × G → ℕ := fun p => #{a ∈ A | a - p.1 ∈ A ∧ a - p.2 ∈ A} with hT
  have hA0 : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos

  have h1 : δ * #A * #S ≤ ∑ a ∈ A, (n a : ℝ) := by
    have : ∑ s ∈ S, (rep A s : ℝ) = ∑ a ∈ A, (n a : ℝ) := by exact_mod_cast sum_rep_eq A S
    rw [← this]
    calc δ * #A * #S = ∑ s ∈ S, δ * (#A : ℝ) := by rw [sum_const]; simp [mul_comm]
      _ ≤ _ := sum_le_sum hS

  have h2 : ∑ a ∈ A, (n a : ℝ) ^ 2 = ∑ p ∈ S ×ˢ S, (T p : ℝ) := by
    have : ∑ a ∈ A, n a ^ 2 = ∑ p ∈ S ×ˢ S, T p := by
      have hsq : ∀ a, n a ^ 2 = ∑ p ∈ S ×ˢ S, if a - p.1 ∈ A ∧ a - p.2 ∈ A then 1 else 0 := by
        intro a
        rw [← card_filter, sq, hn]
        simp only
        rw [← card_product]
        congr 1
        ext q
        simp only [mem_product, mem_filter]
        tauto
      simp_rw [hsq, hT, card_filter]
      exact sum_comm
    exact_mod_cast this

  have h3 : (δ * #A * #S) ^ 2 ≤ #A * ∑ p ∈ S ×ˢ S, (T p : ℝ) := by
    rw [← h2]
    calc (δ * #A * #S) ^ 2 ≤ (∑ a ∈ A, (n a : ℝ)) ^ 2 := by
          gcongr
      _ ≤ #A * ∑ a ∈ A, (n a : ℝ) ^ 2 := sq_sum_le_card_mul_sum_sq

  have hTrep : ∀ p, T p ≤ rep A (p.1 - p.2) := by
    intro p
    unfold rep
    refine card_le_card_of_injOn (fun a => a - p.2) ?_ ?_
    · intro a ha
      simp only [mem_coe, mem_filter] at ha ⊢
      refine ⟨ha.2.2, ?_⟩
      have : a - p.2 - (p.1 - p.2) = a - p.1 := by abel
      rw [this]; exact ha.2.1
    · intro a _ b _ h
      simpa using h
  have h4 := sum_le_thr_add (S ×ˢ S) (fun p => (T p : ℝ)) (M := #A) (θ := δ ^ 2 / 2 * #A)
    (by positivity) (fun p _ => by exact_mod_cast card_filter_le _ _)
  have h5 : (#{p ∈ S ×ˢ S | δ ^ 2 / 2 * #A ≤ (T p : ℝ)} : ℝ) ≤
      #{p ∈ S ×ˢ S | δ ^ 2 / 2 * #A ≤ rep A (p.1 - p.2)} := by
    exact_mod_cast card_le_card (fun p hp => by
      simp only [mem_filter] at hp ⊢
      exact ⟨hp.1, hp.2.trans (by exact_mod_cast hTrep p)⟩)
  rw [card_product] at h4
  push_cast at h4
  have key : δ ^ 2 / 2 * #S ^ 2 * (#A * #A) ≤
      #{p ∈ S ×ˢ S | δ ^ 2 / 2 * #A ≤ rep A (p.1 - p.2)} * (#A * #A) := by
    nlinarith
  exact le_of_mul_le_mul_right key (by positivity)

lemma regularize (A U : Finset G) (m : ℕ) (hU : #U ≤ 2 ^ m) {θ c : ℝ} (hc : 0 < c)
    (hUne : U.Nonempty)
    (hP : c * #U ^ 2 ≤ #{p ∈ U ×ˢ U | θ * #A ≤ rep A (p.1 - p.2)}) :
    ∃ V : Finset G, V.Nonempty ∧ (∀ x ∈ V, θ * #A ≤ rep A x) ∧
      ∀ x ∈ V, c / (2 * (m + 1)) * #U ^ 2 ≤ #V * rep U x := by
  classical
  set D := (U - U).filter (fun x => θ * #A ≤ (rep A x : ℝ)) with hD
  have hpairs : #{p ∈ U ×ˢ U | θ * #A ≤ rep A (p.1 - p.2)} = ∑ x ∈ D, rep U x := by
    rw [← card_pairs_sub_mem]
    congr 1
    ext p
    simp only [mem_filter, mem_product, hD]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h2⟩, sub_mem_sub h1 h2, h3⟩
    · rintro ⟨⟨h1, h2⟩, -, h3⟩
      exact ⟨⟨h1, h2⟩, h3⟩
  set g : G → ℕ := fun x => Nat.log 2 (rep U x) with hg
  have hgmaps : ∀ x ∈ D, g x ∈ range (m + 1) := by
    intro x hx
    have hx' : x ∈ U - U := (mem_filter.1 hx).1
    rw [mem_range]
    refine Nat.log_lt_of_lt_pow (rep_pos_of_mem_sub hx').ne' ?_
    calc rep U x ≤ #U := rep_le U x
      _ ≤ 2 ^ m := hU
      _ < 2 ^ (m + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hsum : (#(range (m + 1)) : ℕ) • (c * #U ^ 2 / (m + 1)) ≤ ∑ x ∈ D, (rep U x : ℝ) := by
    rw [card_range, nsmul_eq_mul]
    have : ((∑ x ∈ D, rep U x : ℕ) : ℝ) = ∑ x ∈ D, (rep U x : ℝ) := by push_cast; rfl
    rw [← this, ← hpairs]
    push_cast
    field_simp
    exact hP
  obtain ⟨k, -, hk⟩ := exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum hgmaps
    nonempty_range_add_one hsum
  set V := D.filter (fun x => g x = k) with hV
  have hVpos : 0 < ∑ x ∈ V, (rep U x : ℝ) := by
    refine lt_of_lt_of_le ?_ hk
    have : (0 : ℝ) < #U := by exact_mod_cast hUne.card_pos
    positivity
  have hVne : V.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, sum_empty] at hVpos
    exact lt_irrefl _ hVpos
  have hlow : ∀ x ∈ V, (2 : ℝ) ^ k ≤ rep U x := by
    intro x hx
    have hxD : x ∈ D := (mem_filter.1 hx).1
    have hxk : g x = k := (mem_filter.1 hx).2
    have hx' : x ∈ U - U := (mem_filter.1 hxD).1
    rw [← hxk]
    exact_mod_cast Nat.pow_log_le_self 2 (rep_pos_of_mem_sub hx').ne'
  have hup : ∑ x ∈ V, (rep U x : ℝ) ≤ #V * 2 ^ (k + 1) := by
    have : ∀ x ∈ V, (rep U x : ℝ) ≤ 2 ^ (k + 1) := by
      intro x hx
      have hxk : g x = k := (mem_filter.1 hx).2
      rw [← hxk]
      exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num) _).le
    simpa using sum_le_card_nsmul V _ _ this
  refine ⟨V, hVne, fun x hx => (mem_filter.1 (mem_filter.1 hx).1).2, fun x hx => ?_⟩
  have h1 : c * #U ^ 2 / (m + 1) ≤ #V * 2 ^ (k + 1) := hk.trans hup
  have h2 := hlow x hx
  have hm : (0 : ℝ) < m + 1 := by positivity
  rw [div_le_iff₀ hm] at h1
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have hV0 : (0 : ℝ) ≤ #V := by positivity
  calc c * #U ^ 2 ≤ #V * 2 ^ (k + 1) * (m + 1) := h1
    _ = #V * 2 ^ k * (2 * (m + 1)) := by ring
    _ ≤ #V * rep U x * (2 * (m + 1)) := by gcongr

lemma backprop_step (U V S : Finset G) {γ β : ℝ} (hγ : 0 ≤ γ) (hV : V.Nonempty)
    (hreg : ∀ x ∈ V, γ * #U ^ 2 ≤ #V * rep U x) (x : G)
    (hx : β * #V ≤ #{v ∈ V | v - x ∈ S}) :
    ∃ y : G, β * γ * #U ≤ #{u ∈ U | u - y ∈ S} := by
  classical
  rcases U.eq_empty_or_nonempty with rfl | hU
  · exact ⟨0, by simp⟩
  set W := V.filter (fun v => v - x ∈ S) with hW
  have hV0 : (0 : ℝ) < #V := by exact_mod_cast hV.card_pos

  have h1 : β * γ * #U ^ 2 ≤ ∑ z ∈ W, (rep U z : ℝ) := by
    have : ∀ z ∈ W, γ * #U ^ 2 / #V ≤ (rep U z : ℝ) := by
      intro z hz
      rw [div_le_iff₀ hV0, mul_comm (rep U z : ℝ)]
      exact hreg z (mem_filter.1 hz).1
    calc β * γ * #U ^ 2 = β * #V * (γ * #U ^ 2 / #V) := by field_simp
      _ ≤ #W * (γ * #U ^ 2 / #V) := by gcongr
      _ = ∑ z ∈ W, γ * #U ^ 2 / #V := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum this
  have h2 : ∑ z ∈ W, (rep U z : ℝ) = ∑ u' ∈ U, (#{u ∈ U | u - u' ∈ W} : ℝ) := by
    have : ∑ z ∈ W, rep U z = ∑ u' ∈ U, #{u ∈ U | u - u' ∈ W} := by
      rw [← card_pairs_sub_mem, card_filter, sum_product_right]
      simp_rw [card_filter]
    exact_mod_cast this
  obtain ⟨u', -, hu'⟩ := exists_le_of_sum_le hU (f := fun _ => β * γ * #U)
    (g := fun u' => (#{u ∈ U | u - u' ∈ W} : ℝ)) (by
      rw [← h2, sum_const, nsmul_eq_mul]
      calc (#U : ℝ) * (β * γ * #U) = β * γ * #U ^ 2 := by ring
        _ ≤ _ := h1)
  refine ⟨u' + x, hu'.trans ?_⟩
  exact_mod_cast card_le_card (fun u hu => by
    simp only [mem_filter, hW] at hu ⊢
    refine ⟨hu.1, ?_⟩
    have : u - (u' + x) = u - u' - x := by abel
    rw [this]; exact hu.2.2)

lemma cover (A H : Finset G) (hH : H.Nonempty) {θ : ℝ} (hθ : 0 < θ)
    (hrep : ∀ h ∈ H, θ * #A ≤ rep A h) :
    ∃ A₀ Λ : Finset G, A₀ ⊆ A ∧ θ / 2 * #A ≤ #A₀ ∧ A₀ ⊆ Λ + (H - H) ∧
      #Λ * #H * θ ≤ 2 * #A := by
  classical
  set w : G → ℕ := fun a => #{h ∈ H | a - h ∈ A} with hw
  set A₀ := A.filter (fun a => θ / 2 * #H ≤ (w a : ℝ)) with hA₀
  have hH0 : (0 : ℝ) < #H := by exact_mod_cast hH.card_pos

  have hsum : θ * #A * #H ≤ ∑ a ∈ A, (w a : ℝ) := by
    have : ∑ h ∈ H, (rep A h : ℝ) = ∑ a ∈ A, (w a : ℝ) := by exact_mod_cast sum_rep_eq A H
    rw [← this]
    calc θ * #A * #H = ∑ h ∈ H, θ * (#A : ℝ) := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := sum_le_sum hrep
  have hpop := sum_le_thr_add A (fun a => (w a : ℝ)) (M := #H) (θ := θ / 2 * #H)
    (by positivity) (fun a _ => by exact_mod_cast card_filter_le _ _)
  have hA₀card : θ / 2 * #A ≤ #A₀ := by
    have key : θ / 2 * #A * #H ≤ #A₀ * #H := by nlinarith
    exact le_of_mul_le_mul_right key hH0

  set F : G → Finset G := fun a => (H.filter (fun h => a - h ∈ A)).image (fun h => a - h)
    with hF
  have hFcard : ∀ a, #(F a) = w a := by
    intro a
    exact card_image_of_injective _ (sub_right_injective)
  have hFA : ∀ a, F a ⊆ A := by
    intro a z hz
    obtain ⟨h, hh, rfl⟩ := mem_image.1 hz
    exact (mem_filter.1 hh).2

  have : ∀ Λ : Finset G, Decidable ((Λ : Set G).PairwiseDisjoint F) := fun _ => Classical.dec _
  set C := A₀.powerset.filter (fun Λ : Finset G => (Λ : Set G).PairwiseDisjoint F) with hC
  obtain ⟨Λ, hΛmax⟩ := C.exists_maximal (filter_nonempty_iff.2
    ⟨∅, empty_mem_powerset _, by simp⟩)
  simp only [C, mem_filter, mem_powerset] at hΛmax
  obtain ⟨hΛA, hΛdisj⟩ := hΛmax.1
  refine ⟨A₀, Λ, filter_subset _ _, hA₀card, ?_, ?_⟩
  · intro a ha
    by_cases haΛ : a ∈ Λ
    · obtain ⟨h, hh⟩ := hH
      exact mem_add.2 ⟨a, haΛ, 0, mem_sub.2 ⟨h, hh, h, hh, sub_self h⟩, add_zero a⟩
    by_cases! Hd : ∀ b ∈ Λ, Disjoint (F a) (F b)
    · refine (hΛmax.not_gt ?_ (ssubset_insert haΛ)).elim
      refine ⟨insert_subset ha hΛA, ?_⟩
      rw [coe_insert]
      exact hΛdisj.insert fun b hb _ => Hd b hb
    obtain ⟨b, hb, hab⟩ := Hd
    obtain ⟨z, hza, hzb⟩ := not_disjoint_iff.1 hab
    obtain ⟨h, hh, hz⟩ := mem_image.1 hza
    obtain ⟨h', hh', hz'⟩ := mem_image.1 hzb
    refine mem_add.2 ⟨b, hb, h - h', mem_sub.2 ⟨h, (mem_filter.1 hh).1, h',
      (mem_filter.1 hh').1, rfl⟩, ?_⟩
    calc b + (h - h') = (b - h') + h := by abel
      _ = (a - h) + h := by rw [hz, hz']
      _ = a := by abel
  · have hdisj : ∀ x ∈ Λ, ∀ y ∈ Λ, x ≠ y → Disjoint (F x) (F y) :=
      fun x hx y hy hxy => hΛdisj (mem_coe.2 hx) (mem_coe.2 hy) hxy
    have h1 : ∑ b ∈ Λ, (#(F b) : ℝ) ≤ #A := by
      have : ∑ b ∈ Λ, #(F b) ≤ #A := by
        rw [← card_biUnion hdisj]
        exact card_le_card (biUnion_subset.2 fun b _ => hFA b)
      exact_mod_cast this
    have h2 : ∀ b ∈ Λ, θ / 2 * #H ≤ (#(F b) : ℝ) := by
      intro b hb
      rw [hFcard]
      exact (mem_filter.1 (hΛA hb)).2
    have h3 : #Λ * (θ / 2 * #H) ≤ (#A : ℝ) := by
      calc #Λ * (θ / 2 * #H) = ∑ b ∈ Λ, θ / 2 * (#H : ℝ) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ _ := sum_le_sum h2
        _ ≤ _ := h1
    linarith

end FractalGeometry.Lq.BSG
