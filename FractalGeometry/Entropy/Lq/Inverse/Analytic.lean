import Mathlib
import FractalGeometry.Entropy.Lq.Inverse.Basic
import FractalGeometry.Entropy.Lq.Statements
import FractalGeometry.Entropy.Lq.Theorem51

open Filter Topology

open scoped Pointwise

namespace FractalGeometry

namespace Lq

namespace Inverse

def reprCount (m : ℕ) (A B : Finset ℤ) (w : ZMod (2 ^ m)) : ℕ :=
  (((A.image (Int.cast : ℤ → ZMod (2 ^ m))) ×ˢ (B.image Int.cast)).filter
    fun xy => xy.1 + xy.2 = w).card

theorem val_cast_of_mem {m : ℕ} {i : ℤ} (hi : 0 ≤ i ∧ i < 2 ^ m) :
    (((i : ZMod (2 ^ m)).val : ℕ) : ℤ) = i := by
  rw [ZMod.val_intCast]
  push_cast
  exact Int.emod_eq_of_lt hi.1 hi.2

theorem circConv_ind_eq {m : ℕ} {A B : Finset ℤ} (hA : InUnit m A) (hB : InUnit m B) {k : ℤ}
    (hk : 0 ≤ k ∧ k < 2 ^ m) :
    circConv m (ind A) (ind B) k = reprCount m A B (k : ZMod (2 ^ m)) := by
  classical
  unfold circConv
  rw [ite_eq_of_pos hk]
  have hAsub : A ⊆ Finset.Ico (0 : ℤ) (2 ^ m) := fun i hi => Finset.mem_Ico.mpr (hA i hi)
  have h1 : ∑ i ∈ Finset.Ico (0 : ℤ) (2 ^ m), ind A i * ind B ((k - i) % 2 ^ m) =
      ((A.filter fun i => (k - i) % 2 ^ m ∈ B).card : ℝ) := by
    rw [← Finset.sum_subset hAsub fun i _ hi => by simp [ind, hi]]
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [ind, hi, ite_true, one_mul]
    split_ifs <;> simp
  rw [h1]
  congr 1
  refine Finset.card_nbij' (fun i => ((i : ZMod (2 ^ m)), ((k - i : ℤ) : ZMod (2 ^ m))))
    (fun xy => ((xy.1.val : ℕ) : ℤ)) (fun i hi => ?_) (fun xy hxy => ?_) (fun i hi => ?_)
    (fun xy hxy => ?_)
  · obtain ⟨hiA, hiB⟩ := Finset.mem_filter.mp hi
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, Finset.mem_image]
    refine ⟨⟨⟨i, hiA, rfl⟩, ⟨(k - i) % 2 ^ m, hiB, ?_⟩⟩, by push_cast; ring⟩
    have := ZMod.intCast_mod (k - i) (2 ^ m)
    push_cast at this
    rw [this]
    push_cast
    ring
  · simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, Finset.mem_image] at hxy
    obtain ⟨⟨⟨i, hiA, hi⟩, ⟨j, hjB, hj⟩⟩, hsum⟩ := hxy
    simp only [Finset.coe_filter, Set.mem_ofPred_eq]
    rw [← hi, val_cast_of_mem (hA i hiA)]
    refine ⟨hiA, ?_⟩
    have hkj : (k - i : ZMod (2 ^ m)) = (j : ZMod (2 ^ m)) := by
      rw [hj, ← hsum, ← hi]; ring
    have h2 := (ZMod.intCast_eq_intCast_iff' (k - i) j (2 ^ m)).mp (by push_cast; exact hkj)
    push_cast at h2
    rw [h2, Int.emod_eq_of_lt (hB j hjB).1 (hB j hjB).2]
    exact hjB
  · exact val_cast_of_mem (hA i (Finset.mem_filter.mp hi).1)
  · simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product] at hxy
    obtain ⟨-, hsum⟩ := hxy
    ext
    · simp
    · show ((k - ((xy.1.val : ℕ) : ℤ) : ℤ) : ZMod (2 ^ m)) = xy.2
      push_cast
      rw [ZMod.natCast_zmod_val, ← hsum]
      ring

theorem discLq_circConv_ind {m : ℕ} {A B : Finset ℤ} (hA : InUnit m A) (hB : InUnit m B)
    (q : ℝ) : discLq m q (circConv m (ind A) (ind B)) =
      ∑ w : ZMod (2 ^ m), (reprCount m A B w : ℝ) ^ q := by
  unfold discLq
  refine Finset.sum_nbij' (fun k => (k : ZMod (2 ^ m))) (fun w => ((w.val : ℕ) : ℤ))
    (fun _ _ => Finset.mem_univ _) (fun w _ => ?_) (fun k hk => ?_) (fun w _ => ?_)
    (fun k hk => ?_)
  · refine Finset.mem_Ico.mpr ⟨Int.natCast_nonneg _, ?_⟩
    exact_mod_cast ZMod.val_lt w
  · exact val_cast_of_mem (Finset.mem_Ico.mp hk)
  · simp
  · rw [circConv_ind_eq hA hB (Finset.mem_Ico.mp hk)]

theorem sum_reprCount {m : ℕ} {A B : Finset ℤ} (hA : InUnit m A) (hB : InUnit m B) :
    ∑ w : ZMod (2 ^ m), reprCount m A B w = A.card * B.card := by
  classical
  unfold reprCount
  rw [← card_image_cast hA, ← card_image_cast hB, ← Finset.card_product]
  exact (Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)).symm

theorem reprCount_le {m : ℕ} {A B : Finset ℤ} (hB : InUnit m B) (w : ZMod (2 ^ m)) :
    reprCount m A B w ≤ B.card := by
  classical
  unfold reprCount
  rw [← card_image_cast hB]
  refine Finset.card_le_card_of_injOn (fun xy => xy.2) (fun xy hxy => ?_)
    (fun xy hxy xy' hxy' h => ?_)
  · exact (Finset.mem_product.mp (Finset.mem_filter.mp hxy).1).2
  · have h1 := (Finset.mem_filter.mp hxy).2
    have h2 := (Finset.mem_filter.mp hxy').2
    simp only at h
    have : xy.1 = xy'.1 := by rw [← h] at h2; exact add_right_cancel (h1.trans h2.symm)
    exact Prod.ext this h

theorem addEnergy_eq_sum {m : ℕ} (A B : Finset ℤ) :
    (Finset.addEnergy (A.image (Int.cast : ℤ → ZMod (2 ^ m))) (B.image Int.cast) : ℝ) =
      ∑ w : ZMod (2 ^ m), (reprCount m A B w : ℝ) ^ 2 := by
  rw [Finset.addEnergy_eq_sum_sq]
  push_cast
  rfl

theorem sum_rpow_le_interp {ι : Type*} (s : Finset ι) {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i) {q : ℝ}
    (hq1 : 1 < q) (hq2 : q < 2) :
    ∑ i ∈ s, r i ^ q ≤ (∑ i ∈ s, r i) ^ (2 - q) * (∑ i ∈ s, r i ^ (2 : ℝ)) ^ (q - 1) := by
  have hp : ((2 - q)⁻¹).HolderConjugate (q - 1)⁻¹ := by
    rw [Real.holderConjugate_iff, inv_inv, inv_inv]
    refine ⟨?_, by ring⟩
    rw [lt_inv_comm₀ one_pos (by linarith)]; simp; linarith
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg s hp (f := fun i => r i ^ (2 - q))
    (g := fun i => r i ^ (2 * (q - 1))) (fun i _ => Real.rpow_nonneg (hr i) _)
    (fun i _ => Real.rpow_nonneg (hr i) _)
  have e1 : ∀ i, r i ^ (2 - q) * r i ^ (2 * (q - 1)) = r i ^ q := fun i => by
    rw [← Real.rpow_add' (hr i) (by linarith)]; ring_nf
  have e2 : ∀ i, (r i ^ (2 - q)) ^ (2 - q)⁻¹ = r i := fun i =>
    Real.rpow_rpow_inv (hr i) (by linarith)
  have e3 : ∀ i, (r i ^ (2 * (q - 1))) ^ (q - 1)⁻¹ = r i ^ (2 : ℝ) := fun i => by
    rw [← Real.rpow_mul (hr i), mul_assoc, mul_inv_cancel₀ (ne_of_gt (by linarith)), mul_one]
  simp only [e1, e2, e3, one_div, inv_inv] at h
  exact h

theorem lemma_3_4 {m : ℕ} {q κ : ℝ} (hq : 1 < q) (hκ : 0 ≤ κ) {A B : Finset ℤ}
    (hA : InUnit m A) (hB : InUnit m B)
    (h : (2 : ℝ) ^ (-(κ * q * m)) * A.card * (B.card : ℝ) ^ q ≤
      discLq m q (circConv m (ind A) (ind B))) :
    (2 : ℝ) ^ (-(max q (q / (q - 1)) * κ * m)) * A.card * (B.card : ℝ) ^ 2 ≤
      Finset.addEnergy (A.image (Int.cast : ℤ → ZMod (2 ^ m))) (B.image Int.cast) := by
  rw [discLq_circConv_ind hA hB] at h
  rw [addEnergy_eq_sum]
  set r : ZMod (2 ^ m) → ℝ := fun w => (reprCount m A B w : ℝ) with hr
  set E := ∑ w, r w ^ 2 with hE
  have hr0 : ∀ w, 0 ≤ r w := fun w => Nat.cast_nonneg _
  have hrB : ∀ w, r w ≤ B.card := fun w => by
    show (reprCount m A B w : ℝ) ≤ B.card
    exact_mod_cast reprCount_le hB w
  have hsum : ∑ w, r w = A.card * B.card := by
    show ∑ w, (reprCount m A B w : ℝ) = A.card * B.card
    exact_mod_cast sum_reprCount hA hB
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun w _ => sq_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hq1 : 0 < q - 1 := by linarith
  rcases Nat.eq_zero_or_pos A.card with hA0 | hA0
  · rw [hA0]; simpa using hE0
  rcases Nat.eq_zero_or_pos B.card with hB0 | hB0
  · rw [hB0]; simpa using hE0
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast hA0
  have hBp : (0 : ℝ) < B.card := by exact_mod_cast hB0
  by_cases hq2 : 2 ≤ q
  ·
    have h1 : ∑ w, r w ^ q ≤ (B.card : ℝ) ^ (q - 2) * E := by
      rw [hE, Finset.mul_sum]
      refine Finset.sum_le_sum fun w _ => ?_
      calc r w ^ q = r w ^ (q - 2) * r w ^ (2 : ℝ) := by
            rw [← Real.rpow_add' (hr0 w) (by linarith)]; ring_nf
        _ ≤ (B.card : ℝ) ^ (q - 2) * r w ^ 2 := by
            rw [Real.rpow_two]
            exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (hr0 w) (hrB w) (by linarith))
              (sq_nonneg _)
    have hBq : (B.card : ℝ) ^ q = (B.card : ℝ) ^ (q - 2) * (B.card : ℝ) ^ 2 := by
      rw [← Real.rpow_two, ← Real.rpow_add hBp]; ring_nf
    have h3 : (B.card : ℝ) ^ (q - 2) * ((2 : ℝ) ^ (-(κ * q * m)) * A.card * B.card ^ 2) ≤
        (B.card : ℝ) ^ (q - 2) * E := by
      calc (B.card : ℝ) ^ (q - 2) * ((2 : ℝ) ^ (-(κ * q * m)) * A.card * B.card ^ 2)
          = (2 : ℝ) ^ (-(κ * q * m)) * A.card * (B.card : ℝ) ^ q := by rw [hBq]; ring
        _ ≤ ∑ w, r w ^ q := h
        _ ≤ _ := h1
    refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le one_le_two ?_) hAp.le) (sq_nonneg _))
      (le_of_mul_le_mul_left h3 (by positivity))
    have h7 : q ≤ max q (q / (q - 1)) := le_max_left _ _
    have := mul_le_mul_of_nonneg_right h7 (mul_nonneg hκ hm0)
    linarith
  ·
    push Not at hq2
    have hint := sum_rpow_le_interp Finset.univ hr0 hq hq2
    simp only [Real.rpow_two] at hint
    rw [hsum, ← hE] at hint
    set q' := q / (q - 1) with hq'
    have hqq' : q' * (q - 1) = q := by rw [hq']; field_simp
    set X := (2 : ℝ) ^ (-(q' * κ * m)) * A.card * (B.card : ℝ) ^ 2 with hX
    have hX0 : 0 ≤ X := by positivity
    have key : ((A.card : ℝ) * B.card) ^ (2 - q) * X ^ (q - 1) =
        (2 : ℝ) ^ (-(κ * q * m)) * A.card * (B.card : ℝ) ^ q := by
      have f1 : ((A.card : ℝ) * B.card) ^ (2 - q) =
          (A.card : ℝ) ^ (2 - q) * (B.card : ℝ) ^ (2 - q) := Real.mul_rpow hAp.le hBp.le
      have f4 : ((B.card : ℝ) ^ 2) ^ (q - 1) = (B.card : ℝ) ^ (2 * (q - 1)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hBp.le]; norm_num
      have e3 : -(q' * κ * m) * (q - 1) = -(κ * q * m) := by
        rw [show -(q' * κ * m) * (q - 1) = -(q' * (q - 1) * κ * m) by ring, hqq']; ring
      have f3 : ((2 : ℝ) ^ (-(q' * κ * m))) ^ (q - 1) = (2 : ℝ) ^ (-(κ * q * m)) := by
        rw [← Real.rpow_mul (by norm_num), e3]
      have f2 : X ^ (q - 1) = (2 : ℝ) ^ (-(κ * q * m)) * (A.card : ℝ) ^ (q - 1) *
          (B.card : ℝ) ^ (2 * (q - 1)) := by
        rw [hX, Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity)
          hAp.le, f3, f4]
      have e1 : (A.card : ℝ) ^ (2 - q) * (A.card : ℝ) ^ (q - 1) = A.card := by
        rw [← Real.rpow_add hAp]; ring_nf; exact Real.rpow_one _
      have e2 : (B.card : ℝ) ^ (2 - q) * (B.card : ℝ) ^ (2 * (q - 1)) = (B.card : ℝ) ^ q := by
        rw [← Real.rpow_add hBp]; ring_nf
      rw [f1, f2]
      calc (A.card : ℝ) ^ (2 - q) * (B.card : ℝ) ^ (2 - q) * ((2 : ℝ) ^ (-(κ * q * m)) *
            (A.card : ℝ) ^ (q - 1) * (B.card : ℝ) ^ (2 * (q - 1)))
          = (2 : ℝ) ^ (-(κ * q * m)) * ((A.card : ℝ) ^ (2 - q) * (A.card : ℝ) ^ (q - 1)) *
            ((B.card : ℝ) ^ (2 - q) * (B.card : ℝ) ^ (2 * (q - 1))) := by ring
        _ = _ := by rw [e1, e2]
    have h4 : ((A.card : ℝ) * B.card) ^ (2 - q) * X ^ (q - 1) ≤
        ((A.card : ℝ) * B.card) ^ (2 - q) * E ^ (q - 1) := by
      rw [key]; exact le_trans h hint
    have h5 := le_of_mul_le_mul_left h4 (by positivity)
    have h6 : X ≤ E := (Real.rpow_le_rpow_iff hX0 hE0 hq1).mp h5
    refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le one_le_two ?_) hAp.le) (sq_nonneg _)) h6
    have h7 : q' ≤ max q q' := le_max_right _ _
    have := mul_le_mul_of_nonneg_right h7 (mul_nonneg hκ hm0)
    linarith

noncomputable def restr (μ : ℤ → ℝ) (A : Finset ℤ) (k : ℤ) : ℝ := if k ∈ A then μ k else 0

noncomputable def lqN (m : ℕ) (q : ℝ) (f : ℤ → ℝ) : ℝ := discLq m q f ^ (1 / q)

theorem restr_nonneg {μ : ℤ → ℝ} (hμ : ∀ k, 0 ≤ μ k) (A : Finset ℤ) (k : ℤ) :
    0 ≤ restr μ A k := by
  unfold restr; split_ifs
  · exact hμ k
  · exact le_rfl

theorem restr_le {μ : ℤ → ℝ} (hμ : ∀ k, 0 ≤ μ k) (A : Finset ℤ) (k : ℤ) : restr μ A k ≤ μ k := by
  unfold restr; split_ifs
  · exact le_rfl
  · exact hμ k

theorem discLq_nonneg {m : ℕ} {q : ℝ} {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k) : 0 ≤ discLq m q f :=
  Finset.sum_nonneg fun k _ => Real.rpow_nonneg (hf k) q

theorem lqN_nonneg {m : ℕ} {q : ℝ} {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k) : 0 ≤ lqN m q f :=
  Real.rpow_nonneg (discLq_nonneg hf) _

theorem discLq_mono {m : ℕ} {q : ℝ} (hq : 0 ≤ q) {f g : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hfg : ∀ k, f k ≤ g k) : discLq m q f ≤ discLq m q g :=
  Finset.sum_le_sum fun k _ => Real.rpow_le_rpow (hf k) (hfg k) hq

theorem lqN_mono {m : ℕ} {q : ℝ} (hq : 0 < q) {f g : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hfg : ∀ k, f k ≤ g k) : lqN m q f ≤ lqN m q g :=
  Real.rpow_le_rpow (discLq_nonneg hf) (discLq_mono hq.le hf hfg) (by positivity)

theorem discLq_smul {m : ℕ} {q : ℝ} {a : ℝ} (ha : 0 ≤ a) {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k) :
    discLq m q (fun k => a * f k) = a ^ q * discLq m q f := by
  unfold discLq
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => Real.mul_rpow ha (hf k)

theorem lqN_smul {m : ℕ} {q : ℝ} (hq : 0 < q) {a : ℝ} (ha : 0 ≤ a) {f : ℤ → ℝ}
    (hf : ∀ k, 0 ≤ f k) : lqN m q (fun k => a * f k) = a * lqN m q f := by
  unfold lqN
  rw [discLq_smul ha hf, Real.mul_rpow (by positivity) (discLq_nonneg hf),
    ← Real.rpow_mul ha, mul_one_div_cancel hq.ne', Real.rpow_one]

theorem lqN_zero {m : ℕ} {q : ℝ} (hq : 0 < q) : lqN m q (fun _ => 0) = 0 := by
  unfold lqN discLq
  rw [Finset.sum_eq_zero fun k _ => Real.zero_rpow hq.ne',
    Real.zero_rpow (one_div_pos.mpr hq).ne']

theorem lqN_add_le {m : ℕ} {q : ℝ} (hq : 1 ≤ q) {f g : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hg : ∀ k, 0 ≤ g k) : lqN m q (f + g) ≤ lqN m q f + lqN m q g := by
  have := Real.Lp_add_le_of_nonneg (Finset.Ico (0 : ℤ) (2 ^ m)) (f := f) (g := g) hq
    (fun k _ => hf k) (fun k _ => hg k)
  exact this

theorem lqN_sum_le {m : ℕ} {q : ℝ} (hq : 1 ≤ q) {ι : Type*} (s : Finset ι) {f : ι → ℤ → ℝ}
    (hf : ∀ i k, 0 ≤ f i k) : lqN m q (∑ i ∈ s, f i) ≤ ∑ i ∈ s, lqN m q (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [show (0 : ℤ → ℝ) = fun _ => 0 from rfl, lqN_zero (by linarith)]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine le_trans (lqN_add_le hq (hf a) fun k => ?_) (add_le_add_right ih _)
    rw [Finset.sum_apply]
    exact Finset.sum_nonneg fun i _ => hf i k

theorem circConv_nonneg {m : ℕ} {f g : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k) (hg : ∀ k, 0 ≤ g k) (k : ℤ) :
    0 ≤ circConv m f g k := by
  unfold circConv; split_ifs
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hf i) (hg _)
  · exact le_rfl

theorem circConv_mono {m : ℕ} {f₁ f₂ g₁ g₂ : ℤ → ℝ} (hf₁ : ∀ k, 0 ≤ f₁ k)
    (hf : ∀ k, f₁ k ≤ f₂ k) (hg₁ : ∀ k, 0 ≤ g₁ k) (hg : ∀ k, g₁ k ≤ g₂ k) (k : ℤ) :
    circConv m f₁ g₁ k ≤ circConv m f₂ g₂ k := by
  unfold circConv; split_ifs
  · exact Finset.sum_le_sum fun i _ => mul_le_mul (hf i) (hg _) (hg₁ _) (le_trans (hf₁ i) (hf i))
  · exact le_rfl

theorem circConv_smul {m : ℕ} (a b : ℝ) (f g : ℤ → ℝ) :
    circConv m (fun k => a * f k) (fun k => b * g k) = fun k => a * b * circConv m f g k := by
  funext k
  unfold circConv
  split_ifs
  · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  · ring

theorem circConv_add_left {m : ℕ} (f₁ f₂ g : ℤ → ℝ) :
    circConv m (f₁ + f₂) g = circConv m f₁ g + circConv m f₂ g := by
  funext k
  unfold circConv
  simp only [Pi.add_apply]
  split_ifs
  · rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  · ring

theorem circConv_add_right {m : ℕ} (f g₁ g₂ : ℤ → ℝ) :
    circConv m f (g₁ + g₂) = circConv m f g₁ + circConv m f g₂ := by
  rw [circConv_comm, circConv_add_left, circConv_comm m g₁, circConv_comm m g₂]

theorem circConv_sum_left {m : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℤ → ℝ) (g : ℤ → ℝ) :
    circConv m (∑ i ∈ s, f i) g = ∑ i ∈ s, circConv m (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext k
    simp only [Finset.sum_empty, Pi.zero_apply]
    unfold circConv; split_ifs <;> simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, circConv_add_left, ih]

theorem circConv_sum_right {m : ℕ} {ι : Type*} (s : Finset ι) (f : ℤ → ℝ) (g : ι → ℤ → ℝ) :
    circConv m f (∑ i ∈ s, g i) = ∑ i ∈ s, circConv m f (g i) := by
  rw [circConv_comm, circConv_sum_left]
  exact Finset.sum_congr rfl fun i _ => circConv_comm m _ _

theorem lqN_circConv_le {m : ℕ} {q : ℝ} (hq : 1 ≤ q) {f g : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hg : ∀ k, 0 ≤ g k) (hgs : ∀ k, g k ≠ 0 → 0 ≤ k ∧ k < 2 ^ m) :
    lqN m q (circConv m f g) ≤ lqN m q f * ∑ k ∈ Finset.Ico (0 : ℤ) (2 ^ m), g k := by
  set c := ∑ k ∈ Finset.Ico (0 : ℤ) (2 ^ m), g k with hc
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun k _ => hg k
  rcases eq_or_lt_of_le hc0 with hc' | hc'
  ·
    have hg0 : ∀ k, g k = 0 := by
      intro k
      by_contra hk
      have hkI := hgs k hk
      have := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hg k).mp hc'.symm k
        (Finset.mem_Ico.mpr hkI)
      exact hk this
    have : circConv m f g = fun _ => 0 := by
      funext k; unfold circConv; split_ifs <;> simp [hg0]
    rw [this, lqN_zero (by linarith), ← hc', mul_zero]
  · have hν : IsDyadicMeasure m (fun k => c⁻¹ * g k) := by
      refine ⟨fun k => mul_nonneg (inv_nonneg.mpr hc0) (hg k), fun k hk => hgs k ?_, ?_⟩
      · intro h; exact hk (by rw [h, mul_zero])
      · rw [← Finset.mul_sum, inv_mul_cancel₀ hc'.ne']
    have h1 := discLq_circConv_le hν hf hq
    have h2 : circConv m f g = fun k => c * circConv m (fun k => c⁻¹ * g k) f k := by
      rw [circConv_comm]
      funext k
      unfold circConv
      split_ifs
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        field_simp
      · simp
    rw [h2, lqN_smul (by linarith) hc0 (circConv_nonneg hν.nonneg hf), mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (discLq_nonneg (circConv_nonneg
      hν.nonneg hf)) h1 (by positivity)) hc0

noncomputable def lev (c : ℝ) (μ : ℤ → ℝ) (x : ℤ) : ℤ := Int.log 2 (c / μ x)

theorem lev_bounds {c : ℝ} (hc : 0 < c) {μ : ℤ → ℝ} {x : ℤ} (hx : 0 < μ x) :
    c * (2 : ℝ) ^ (-(lev c μ x : ℝ) - 1) < μ x ∧ μ x ≤ c * (2 : ℝ) ^ (-(lev c μ x : ℝ)) := by
  have h1 := Int.zpow_log_le_self (b := 2) (by norm_num) (show 0 < c / μ x by positivity)
  have h2 := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) (c / μ x)
  unfold lev
  generalize Int.log 2 (c / μ x) = j at h1 h2
  rw [← Real.rpow_intCast] at h1 h2
  push_cast at h1 h2
  constructor
  · rw [div_lt_iff₀ hx] at h2
    rw [show -(j : ℝ) - 1 = -((j : ℝ) + 1) by ring, Real.rpow_neg (by norm_num),
      ← div_eq_mul_inv, div_lt_iff₀ (by positivity)]
    linarith
  · rw [le_div_iff₀ hx] at h1
    rw [Real.rpow_neg (by norm_num), ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    linarith

theorem le_lev {c : ℝ} {μ : ℤ → ℝ} {x : ℤ} (hx : 0 < μ x) (hc : 0 < c) {k : ℤ}
    (h : (2 : ℝ) ^ (k : ℝ) ≤ c / μ x) : k ≤ lev c μ x := by
  unfold lev
  rw [← Int.zpow_le_iff_le_log (by norm_num) (by positivity)]
  rw [← Real.rpow_intCast]
  exact_mod_cast h

theorem decomp_level {m : ℕ} {μ : ℤ → ℝ} (hμ0 : ∀ k, 0 ≤ μ k)
    (hμs : ∀ k, μ k ≠ 0 → 0 ≤ k ∧ k < 2 ^ m) {c : ℝ}
    (hlev : ∀ x, 0 < μ x → -(m : ℤ) ≤ lev c μ x) (J₀ : ℤ) :
    μ = restr μ ((Finset.Ico (0 : ℤ) (2 ^ m)).filter fun x => 0 < μ x ∧ J₀ ≤ lev c μ x) +
      ∑ j ∈ Finset.Ico (-(m : ℤ)) J₀,
        restr μ ((Finset.Ico (0 : ℤ) (2 ^ m)).filter fun x => 0 < μ x ∧ lev c μ x = j) := by
  funext x
  simp only [Pi.add_apply, Finset.sum_apply]
  unfold restr
  by_cases hx : 0 < μ x
  · have hxI : x ∈ Finset.Ico (0 : ℤ) (2 ^ m) := Finset.mem_Ico.mpr (hμs x hx.ne')
    by_cases hJ : J₀ ≤ lev c μ x
    · rw [ite_eq_of_pos (Finset.mem_filter.mpr ⟨hxI, hx, hJ⟩),
        Finset.sum_eq_zero fun j hj => ite_eq_of_neg fun h => by
          have := (Finset.mem_filter.mp h).2.2
          have := (Finset.mem_Ico.mp hj).2
          omega]
      ring
    · rw [ite_eq_of_neg fun h => hJ (Finset.mem_filter.mp h).2.2, zero_add,
        Finset.sum_eq_single (lev c μ x)]
      · rw [ite_eq_of_pos (Finset.mem_filter.mpr ⟨hxI, hx, rfl⟩)]
      · intro j _ hj
        exact ite_eq_of_neg fun h => hj (Finset.mem_filter.mp h).2.2.symm
      · intro h
        exact absurd (Finset.mem_Ico.mpr ⟨hlev x hx, by omega⟩) h
  · have h0 : μ x = 0 := le_antisymm (not_lt.mp hx) (hμ0 x)
    rw [ite_eq_of_neg fun h => hx (Finset.mem_filter.mp h).2.1,
      Finset.sum_eq_zero fun j _ => ite_eq_of_neg fun h => hx (Finset.mem_filter.mp h).2.1, h0]
    ring

theorem restr_support {m : ℕ} {μ : ℤ → ℝ} {A : Finset ℤ} (hA : A ⊆ Finset.Ico (0 : ℤ) (2 ^ m))
    (k : ℤ) (hk : restr μ A k ≠ 0) : 0 ≤ k ∧ k < 2 ^ m := by
  unfold restr at hk
  split_ifs at hk with h
  · exact Finset.mem_Ico.mp (hA h)
  · exact absurd rfl hk

theorem discLq_restr {m : ℕ} {q : ℝ} (hq : 0 < q) {μ : ℤ → ℝ} {A : Finset ℤ}
    (hA : A ⊆ Finset.Ico (0 : ℤ) (2 ^ m)) : discLq m q (restr μ A) = ∑ x ∈ A, μ x ^ q := by
  unfold discLq restr
  rw [← Finset.sum_subset hA fun x _ hx => by rw [ite_eq_of_neg hx, Real.zero_rpow hq.ne']]
  exact Finset.sum_congr rfl fun x hx => by rw [ite_eq_of_pos hx]

theorem sum_restr {m : ℕ} {μ : ℤ → ℝ} {A : Finset ℤ} (hA : A ⊆ Finset.Ico (0 : ℤ) (2 ^ m)) :
    ∑ k ∈ Finset.Ico (0 : ℤ) (2 ^ m), restr μ A k = ∑ x ∈ A, μ x := by
  unfold restr
  rw [← Finset.sum_subset hA fun x _ hx => by rw [ite_eq_of_neg hx]]
  exact Finset.sum_congr rfl fun x hx => by rw [ite_eq_of_pos hx]

theorem eventually_sq_le_two_rpow (a : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, a * ((m : ℝ) + 1) ^ 2 ≤ (2 : ℝ) ^ (ε * m) := by
  have hr : 1 < (2 : ℝ) ^ ε := Real.one_lt_rpow one_lt_two hε
  have h := (((tendsto_pow_const_div_const_pow_of_one_lt 2 hr).add
    ((tendsto_pow_const_div_const_pow_of_one_lt 1 hr).const_mul 2)).add
    (tendsto_pow_const_div_const_pow_of_one_lt 0 hr)).const_mul a
  simp only [mul_zero, add_zero] at h
  filter_upwards [h.eventually (gt_mem_nhds zero_lt_one)] with m hm
  have hpos : 0 < ((2 : ℝ) ^ ε) ^ m := pow_pos (by positivity) m
  rw [Real.rpow_mul_natCast (by norm_num)]
  simp only [pow_one, pow_zero] at hm
  have : a * ((m : ℝ) + 1) ^ 2 / ((2 : ℝ) ^ ε) ^ m < 1 := by
    have e : a * ((m : ℝ) + 1) ^ 2 / ((2 : ℝ) ^ ε) ^ m = a * ((m : ℝ) ^ 2 / ((2 : ℝ) ^ ε) ^ m +
        2 * ((m : ℝ) / ((2 : ℝ) ^ ε) ^ m) + 1 / ((2 : ℝ) ^ ε) ^ m) := by
      field_simp; ring
    rw [e]; exact hm
  rw [div_lt_one hpos] at this
  exact this.le

noncomputable def levelSet (m : ℕ) (c : ℝ) (μ : ℤ → ℝ) (j : ℤ) : Finset ℤ :=
  open Classical in (Finset.Ico (0 : ℤ) (2 ^ m)).filter fun x => 0 < μ x ∧ lev c μ x = j

theorem levelSet_sub {m : ℕ} {c : ℝ} {μ : ℤ → ℝ} {j : ℤ} :
    levelSet m c μ j ⊆ Finset.Ico (0 : ℤ) (2 ^ m) := Finset.filter_subset _ _

theorem mem_levelSet {m : ℕ} {c : ℝ} {μ : ℤ → ℝ} {j x : ℤ} (h : x ∈ levelSet m c μ j) :
    0 < μ x ∧ lev c μ x = j := (Finset.mem_filter.mp h).2

theorem conclusions_of_pair {m : ℕ} {q ε c : ℝ} (hq : 1 < q) (hc : 0 < c) {μ ν : ℤ → ℝ}
    (hμ : IsDyadicMeasure m μ) (hν : IsDyadicMeasure m ν) (j j' : ℤ)
    (hK : 4 * (2 : ℝ) ^ (-(2 * ε * m)) * lqN m q μ ≤
      lqN m q (circConv m (restr μ (levelSet m c μ j))
        (restr ν (levelSet m ((2 : ℝ) ^ (-(m : ℝ))) ν j')))) :
    ∃ A B : Finset ℤ, InUnit m A ∧ InUnit m B ∧ A.Nonempty ∧ B.Nonempty ∧
      (∀ x ∈ A, 0 < μ x) ∧ (∀ y ∈ B, 0 < ν y) ∧
      (∀ x ∈ A, ∀ y ∈ A, μ y ≤ 2 * μ x) ∧ (∀ x ∈ B, ∀ y ∈ B, ν y ≤ 2 * ν x) ∧
      (2 : ℝ) ^ (-(2 * ε * q * m)) * A.card * (B.card : ℝ) ^ q ≤
        discLq m q (circConv m (ind A) (ind B)) ∧
      (2 : ℝ) ^ (-(2 * ε * q * m)) * discLq m q μ ≤ ∑ x ∈ A, μ x ^ q ∧
      (2 : ℝ) ^ (-(2 * ε * m)) ≤ ∑ y ∈ B, ν y := by
  classical
  set cν : ℝ := (2 : ℝ) ^ (-(m : ℝ)) with hcν
  have hcν0 : 0 < cν := by positivity
  set A := levelSet m c μ j with hA
  set B := levelSet m cν ν j' with hB
  have hq0 : 0 < q := by linarith
  set P := discLq m q μ with hP
  have hP0 : 0 < P := discLq_pos hμ q
  have hNμ : lqN m q μ = P ^ (1 / q) := rfl
  have hNμ0 : 0 < lqN m q μ := Real.rpow_pos_of_pos hP0 _
  set Np := lqN m q (circConv m (restr μ A) (restr ν B)) with hNp
  have hKpos : 0 < 4 * (2 : ℝ) ^ (-(2 * ε * m)) * lqN m q μ := by positivity
  have hrμ := restr_nonneg hμ.nonneg A
  have hrν := restr_nonneg hν.nonneg B
  have hsν : ∀ k, restr ν B k ≠ 0 → 0 ≤ k ∧ k < 2 ^ m := restr_support levelSet_sub

  have hYoung : Np ≤ lqN m q (restr μ A) * ∑ y ∈ B, ν y := by
    rw [← sum_restr levelSet_sub]
    exact lqN_circConv_le hq.le hrμ hrν hsν
  have hSB1 : ∑ y ∈ B, ν y ≤ 1 := by
    rw [← hν.sum_eq_one]
    exact Finset.sum_le_sum_of_subset_of_nonneg levelSet_sub fun y _ _ => hν.nonneg y
  have hNA : lqN m q (restr μ A) ≤ lqN m q μ := lqN_mono hq0 hrμ (restr_le hμ.nonneg A)
  have hNA0 : 0 ≤ lqN m q (restr μ A) := lqN_nonneg hrμ

  have hAne : A.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have : Np ≤ 0 := by
      calc Np ≤ lqN m q (restr μ A) * ∑ y ∈ B, ν y := hYoung
        _ = 0 := by
          have : restr μ A = fun _ => 0 := by funext k; simp [restr, h]
          rw [this, lqN_zero hq0, zero_mul]
    linarith
  have hBne : B.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have : Np ≤ 0 := by
      calc Np ≤ lqN m q (restr μ A) * ∑ y ∈ B, ν y := hYoung
        _ = 0 := by rw [h, Finset.sum_empty, mul_zero]
    linarith

  have hAval : ∀ x ∈ A, c * (2 : ℝ) ^ (-(j : ℝ) - 1) < μ x ∧ μ x ≤ c * (2 : ℝ) ^ (-(j : ℝ)) := by
    intro x hx
    obtain ⟨hx0, hxj⟩ := mem_levelSet hx
    have := lev_bounds hc hx0
    rwa [hxj] at this
  have hBval : ∀ y ∈ B, cν * (2 : ℝ) ^ (-(j' : ℝ) - 1) < ν y ∧
      ν y ≤ cν * (2 : ℝ) ^ (-(j' : ℝ)) := by
    intro y hy
    obtain ⟨hy0, hyj⟩ := mem_levelSet hy
    have := lev_bounds hcν0 hy0
    rwa [hyj] at this
  have hhalf : ∀ (a : ℝ) (k : ℤ), a * (2 : ℝ) ^ (-(k : ℝ) - 1) = a * (2 : ℝ) ^ (-(k : ℝ)) / 2 := by
    intro a k
    rw [Real.rpow_sub two_pos, Real.rpow_one]; ring
  have hflat : ∀ {f : ℤ → ℝ} {S : Finset ℤ} {a : ℝ},
      (∀ x ∈ S, a / 2 < f x ∧ f x ≤ a) → ∀ x ∈ S, ∀ y ∈ S, f y ≤ 2 * f x := by
    intro f S a h x hx y hy
    linarith [(h x hx).1, (h y hy).2]
  set t := c * (2 : ℝ) ^ (-(j : ℝ)) with ht
  set s := cν * (2 : ℝ) ^ (-(j' : ℝ)) with hs
  have hAval' : ∀ x ∈ A, t / 2 < μ x ∧ μ x ≤ t := fun x hx => by
    rw [ht, ← hhalf]; exact hAval x hx
  have hBval' : ∀ y ∈ B, s / 2 < ν y ∧ ν y ≤ s := fun y hy => by
    rw [hs, ← hhalf]; exact hBval y hy
  have ht0 : 0 < t := by positivity
  have hs0 : 0 < s := by positivity

  have hii : (2 : ℝ) ^ (-(2 * ε * q * m)) * P ≤ ∑ x ∈ A, μ x ^ q := by
    have h1 : (2 : ℝ) ^ (-(2 * ε * m)) * lqN m q μ ≤ lqN m q (restr μ A) := by
      have : Np ≤ lqN m q (restr μ A) :=
        le_trans hYoung (mul_le_of_le_one_right hNA0 hSB1)
      have h4 : (2 : ℝ) ^ (-(2 * ε * m)) * lqN m q μ ≤
          4 * (2 : ℝ) ^ (-(2 * ε * m)) * lqN m q μ := by
        have : 0 ≤ (2 : ℝ) ^ (-(2 * ε * m)) * lqN m q μ := by positivity
        linarith
      linarith
    rw [← discLq_restr hq0 levelSet_sub]
    have h2 := Real.rpow_le_rpow (by positivity) h1 hq0.le
    rw [Real.mul_rpow (by positivity) hNμ0.le, hNμ, ← Real.rpow_mul hP0.le,
      one_div_mul_cancel hq0.ne', Real.rpow_one, ← Real.rpow_mul (by norm_num)] at h2
    unfold lqN at h2
    rw [← Real.rpow_mul (discLq_nonneg hrμ), one_div_mul_cancel hq0.ne', Real.rpow_one] at h2
    calc (2 : ℝ) ^ (-(2 * ε * q * m)) * P = (2 : ℝ) ^ (-(2 * ε * m) * q) * P := by ring_nf
      _ ≤ _ := h2

  have hiii : (2 : ℝ) ^ (-(2 * ε * m)) ≤ ∑ y ∈ B, ν y := by
    have h1 : 4 * (2 : ℝ) ^ (-(2 * ε * m)) * lqN m q μ ≤ lqN m q μ * ∑ y ∈ B, ν y :=
      le_trans hK (le_trans hYoung (mul_le_mul_of_nonneg_right hNA
        (Finset.sum_nonneg fun y _ => hν.nonneg y)))
    have h2 : 4 * (2 : ℝ) ^ (-(2 * ε * m)) ≤ ∑ y ∈ B, ν y := by
      rw [mul_comm (lqN m q μ)] at h1
      exact le_of_mul_le_mul_right h1 hNμ0
    have : 0 ≤ (2 : ℝ) ^ (-(2 * ε * m)) := by positivity
    linarith

  have hi : (2 : ℝ) ^ (-(2 * ε * q * m)) * A.card * (B.card : ℝ) ^ q ≤
      discLq m q (circConv m (ind A) (ind B)) := by
    have hind : ∀ S : Finset ℤ, ∀ k, 0 ≤ ind S k := fun S k => by
      unfold ind; split_ifs <;> norm_num
    have hI0 := circConv_nonneg (m := m) (hind A) (hind B)
    have hμA : ∀ k, restr μ A k ≤ t * ind A k := fun k => by
      unfold restr ind; split_ifs with h
      · rw [mul_one]; exact (hAval' k h).2
      · rw [mul_zero]
    have hνB : ∀ k, restr ν B k ≤ s * ind B k := fun k => by
      unfold restr ind; split_ifs with h
      · rw [mul_one]; exact (hBval' k h).2
      · rw [mul_zero]
    have hNI : Np ≤ t * s * lqN m q (circConv m (ind A) (ind B)) := by
      have h1 : ∀ k, circConv m (restr μ A) (restr ν B) k ≤
          t * s * circConv m (ind A) (ind B) k := fun k => by
        have := circConv_mono (m := m) hrμ hμA hrν hνB k
        rwa [circConv_smul] at this
      rw [← lqN_smul hq0 (by positivity) hI0]
      exact lqN_mono hq0 (circConv_nonneg hrμ hrν) h1

    have hAsize : (A.card : ℝ) * (t / 2) ^ q ≤ P := by
      calc (A.card : ℝ) * (t / 2) ^ q = ∑ _x ∈ A, (t / 2) ^ q := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ x ∈ A, μ x ^ q := Finset.sum_le_sum fun x hx =>
            Real.rpow_le_rpow (by positivity) (hAval' x hx).1.le hq0.le
        _ ≤ P := Finset.sum_le_sum_of_subset_of_nonneg levelSet_sub fun x _ _ =>
            Real.rpow_nonneg (hμ.nonneg x) q
    have hBsize : (B.card : ℝ) * (s / 2) ≤ 1 := by
      calc (B.card : ℝ) * (s / 2) = ∑ _y ∈ B, s / 2 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ y ∈ B, ν y := Finset.sum_le_sum fun y hy => (hBval' y hy).1.le
        _ ≤ 1 := hSB1
    have hA0 : (0 : ℝ) < A.card := by exact_mod_cast hAne.card_pos
    have hB0 : (0 : ℝ) < B.card := by exact_mod_cast hBne.card_pos

    have hA1q : (A.card : ℝ) ^ (1 / q) * (t / 2) ≤ lqN m q μ := by
      have := Real.rpow_le_rpow (by positivity) hAsize (by positivity : (0 : ℝ) ≤ 1 / q)
      rw [Real.mul_rpow hA0.le (by positivity), ← Real.rpow_mul (by positivity),
        mul_one_div_cancel hq0.ne', Real.rpow_one] at this
      rw [hNμ]; exact this

    have hNI2 : (2 : ℝ) ^ (-(2 * ε * m)) * ((A.card : ℝ) ^ (1 / q) * B.card) ≤
        lqN m q (circConv m (ind A) (ind B)) := by
      have hNI0 := lqN_nonneg (m := m) (q := q) hI0
      have key : t * s * ((2 : ℝ) ^ (-(2 * ε * m)) * ((A.card : ℝ) ^ (1 / q) * B.card)) ≤
          t * s * lqN m q (circConv m (ind A) (ind B)) := by
        have e1 : t * s * ((2 : ℝ) ^ (-(2 * ε * m)) * ((A.card : ℝ) ^ (1 / q) * B.card)) =
            (2 : ℝ) ^ (-(2 * ε * m)) * ((A.card : ℝ) ^ (1 / q) * (t / 2)) * (B.card * (s / 2)) *
              4 := by ring
        rw [e1]
        have e2 : (2 : ℝ) ^ (-(2 * ε * m)) * ((A.card : ℝ) ^ (1 / q) * (t / 2)) *
            (B.card * (s / 2)) * 4 ≤ (2 : ℝ) ^ (-(2 * ε * m)) * lqN m q μ * 1 * 4 := by
          gcongr
        linarith
      exact le_of_mul_le_mul_left key (by positivity)
    have h3 := Real.rpow_le_rpow (by positivity) hNI2 hq0.le
    unfold lqN at h3
    rw [← Real.rpow_mul (discLq_nonneg hI0), one_div_mul_cancel hq0.ne', Real.rpow_one,
      Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hB0.le,
      ← Real.rpow_mul hA0.le, one_div_mul_cancel hq0.ne', Real.rpow_one,
      ← Real.rpow_mul (by norm_num)] at h3
    calc (2 : ℝ) ^ (-(2 * ε * q * m)) * A.card * (B.card : ℝ) ^ q
        = (2 : ℝ) ^ (-(2 * ε * m) * q) * (A.card * (B.card : ℝ) ^ q) := by ring_nf
      _ ≤ _ := h3
  refine ⟨A, B, fun x hx => Finset.mem_Ico.mp (levelSet_sub hx),
    fun y hy => Finset.mem_Ico.mp (levelSet_sub hy), hAne, hBne,
    fun x hx => (mem_levelSet hx).1, fun y hy => (mem_levelSet hy).1,
    hflat hAval', hflat hBval', hi, hii, hiii⟩

theorem card_Ico_two_pow (m : ℕ) : ((Finset.Ico (0 : ℤ) (2 ^ m)).card : ℝ) = 2 ^ m := by
  rw [Int.card_Ico, sub_zero, show ((2 : ℤ) ^ m) = ((2 ^ m : ℕ) : ℤ) by push_cast; rfl,
    Int.toNat_natCast]
  push_cast; rfl

theorem two_rpow_neg_le_lq {m : ℕ} {q : ℝ} (hq : 1 < q) {μ : ℤ → ℝ}
    (hμ : IsDyadicMeasure m μ) :
    (2 : ℝ) ^ (-(m : ℝ)) ≤ discLq m q μ ^ (1 / (q - 1)) := by
  have hq1 : 0 < q - 1 := by linarith
  have hP0 := discLq_pos hμ q
  have h1 := Real.rpow_sum_le_const_mul_sum_rpow (Finset.Ico (0 : ℤ) (2 ^ m)) μ hq.le
  simp only [abs_of_nonneg (hμ.nonneg _)] at h1
  rw [hμ.sum_eq_one, Real.one_rpow, card_Ico_two_pow] at h1

  have h2 : ((2 : ℝ) ^ (-(m : ℝ))) ^ (q - 1) ≤ discLq m q μ := by
    rw [← Real.rpow_mul (by norm_num)]
    have e : ((2 : ℝ) ^ m) ^ (q - 1) = (2 : ℝ) ^ ((m : ℝ) * (q - 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    rw [e] at h1
    rw [show -(m : ℝ) * (q - 1) = -((m : ℝ) * (q - 1)) by ring, Real.rpow_neg (by norm_num)]
    have hpos : 0 < (2 : ℝ) ^ ((m : ℝ) * (q - 1)) := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hpos.le)
    rw [mul_one, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul] at h3
    exact h3
  have h3 := Real.rpow_le_rpow (by positivity) h2 (by positivity : (0 : ℝ) ≤ 1 / (q - 1))
  rwa [← Real.rpow_mul (by positivity), mul_one_div_cancel hq1.ne', Real.rpow_one] at h3

theorem pigeon_numeric {N Np S X n : ℝ} (hX4 : 4 ≤ X) (hn : 8 * n ≤ X) (hn0 : 0 < n)
    (hN : 0 ≤ N) (hS : N * X⁻¹ - 2 * (N * (X ^ 2)⁻¹) ≤ S) (hSn : S ≤ n * Np) :
    4 * (X ^ 2)⁻¹ * N ≤ Np := by
  have hX0 : 0 < X := by linarith
  have h1 : N / (2 * X) ≤ n * Np := by
    have : 2 * (N * (X ^ 2)⁻¹) ≤ N / (2 * X) := by
      rw [show 2 * (N * (X ^ 2)⁻¹) = N * 2 / X ^ 2 by field_simp,
        div_le_div_iff₀ (by positivity) (by positivity)]
      have : 4 * X ≤ X ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this hN]
    have : N * X⁻¹ = N / (2 * X) + N / (2 * X) := by field_simp; ring
    linarith
  have hNp : 0 ≤ Np := by
    by_contra h
    push Not at h
    have : n * Np < 0 := mul_neg_of_pos_of_neg hn0 h
    have : 0 ≤ N / (2 * X) := by positivity
    linarith
  have h2 : n * Np ≤ X / 8 * Np := mul_le_mul_of_nonneg_right (by linarith) hNp
  have h3 : N / (2 * X) ≤ X / 8 * Np := le_trans h1 h2
  rw [div_le_iff₀ (by positivity)] at h3
  rw [show 4 * (X ^ 2)⁻¹ * N = N * 4 / X ^ 2 by ring, div_le_iff₀ (by positivity)]
  nlinarith

set_option maxHeartbeats 1000000 in

theorem lemma_3_3 {ε q : ℝ} (hε : 0 < ε) (hq : 1 < q) :
    ∀ᶠ m : ℕ in atTop, ∀ μ ν : ℤ → ℝ, IsDyadicMeasure m μ → IsDyadicMeasure m ν →
      (2 : ℝ) ^ (-(ε * m)) * discLq m q μ ^ (1 / q) ≤ discLq m q (circConv m μ ν) ^ (1 / q) →
      ∃ A B : Finset ℤ, InUnit m A ∧ InUnit m B ∧ A.Nonempty ∧ B.Nonempty ∧
        (∀ x ∈ A, 0 < μ x) ∧ (∀ y ∈ B, 0 < ν y) ∧
        (∀ x ∈ A, ∀ y ∈ A, μ y ≤ 2 * μ x) ∧ (∀ x ∈ B, ∀ y ∈ B, ν y ≤ 2 * ν x) ∧
        (2 : ℝ) ^ (-(2 * ε * q * m)) * A.card * (B.card : ℝ) ^ q ≤
          discLq m q (circConv m (ind A) (ind B)) ∧
        (2 : ℝ) ^ (-(2 * ε * q * m)) * discLq m q μ ≤ ∑ x ∈ A, μ x ^ q ∧
        (2 : ℝ) ^ (-(2 * ε * m)) ≤ ∑ y ∈ B, ν y := by
  classical
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q - 1 := by linarith
  set q' := q / (q - 1) with hq'
  have hq'1 : 1 ≤ q' := by rw [hq', le_div_iff₀ hq1]; linarith
  set a₀ : ℝ := 2 + 2 * ε * q' with ha₀
  filter_upwards [eventually_sq_le_two_rpow (8 * a₀ ^ 2) hε, eventually_sq_le_two_rpow 4 hε,
    eventually_ge_atTop 1] with m hm hm4 hm1
  intro μ ν hμ hν hconv
  set P := discLq m q μ with hP
  have hP0 : 0 < P := discLq_pos hμ q
  have hN0 : 0 < lqN m q μ := Real.rpow_pos_of_pos hP0 _
  set c := P ^ (1 / (q - 1)) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos hP0 _
  have hcP : c ^ (q - 1) = P := by
    rw [hc, ← Real.rpow_mul hP0.le, one_div_mul_cancel hq1.ne', Real.rpow_one]
  set cν : ℝ := (2 : ℝ) ^ (-(m : ℝ)) with hcν
  have hcν0 : 0 < cν := by positivity
  have hcm : cν ≤ c := two_rpow_neg_le_lq hq hμ
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m

  have hle1 : ∀ {f : ℤ → ℝ}, IsDyadicMeasure m f → ∀ x, f x ≤ 1 := fun {f} hf x => by
    by_cases hx : 0 ≤ x ∧ x < 2 ^ m
    · rw [← hf.sum_eq_one]
      exact Finset.single_le_sum (fun j _ => hf.nonneg j) (Finset.mem_Ico.mpr hx)
    · have : f x = 0 := by by_contra h; exact hx (hf.support x h)
      rw [this]; norm_num
  have hlev : ∀ {f : ℤ → ℝ} {c' : ℝ}, IsDyadicMeasure m f → 0 < c' → cν ≤ c' →
      ∀ x, 0 < f x → -(m : ℤ) ≤ lev c' f x := fun {f c'} hf hc' hc'm x hx => by
    refine le_lev hx hc' ?_
    push_cast
    calc (2 : ℝ) ^ (-(m : ℝ)) ≤ c' := hc'm
      _ ≤ c' / f x := by rw [le_div_iff₀ hx]; nlinarith [hle1 hf x]

  set J₀ : ℕ := ⌈2 * ε * q' * m⌉₊ with hJ₀
  have hJ₀1 : 2 * ε * q' * m ≤ J₀ := Nat.le_ceil _
  have hJ₀2 : (J₀ : ℝ) ≤ 2 * ε * q' * m + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  set Js := Finset.Ico (-(m : ℤ)) (J₀ : ℤ) with hJs
  set E := (Finset.Ico (0 : ℤ) (2 ^ m)).filter fun x => 0 < μ x ∧ (J₀ : ℤ) ≤ lev c μ x
    with hE
  set F := (Finset.Ico (0 : ℤ) (2 ^ m)).filter fun x => 0 < ν x ∧ (J₀ : ℤ) ≤ lev cν ν x
    with hF
  set μG := ∑ j ∈ Js, restr μ (levelSet m c μ j) with hμG
  set νG := ∑ j ∈ Js, restr ν (levelSet m cν ν j) with hνG
  have hdμ : μ = restr μ E + μG :=
    decomp_level hμ.nonneg hμ.support (hlev hμ hc0 hcm) (J₀ : ℤ)
  have hdν : ν = restr ν F + νG :=
    decomp_level hν.nonneg hν.support (hlev hν hcν0 le_rfl) (J₀ : ℤ)
  have hEnn := restr_nonneg hμ.nonneg E
  have hFnn := restr_nonneg hν.nonneg F
  have hμGnn : ∀ k, 0 ≤ μG k := fun k => by
    rw [hμG, Finset.sum_apply]; exact Finset.sum_nonneg fun j _ => restr_nonneg hμ.nonneg _ k
  have hνGnn : ∀ k, 0 ≤ νG k := fun k => by
    rw [hνG, Finset.sum_apply]; exact Finset.sum_nonneg fun j _ => restr_nonneg hν.nonneg _ k
  set pairs := Js ×ˢ Js with hpairs
  set Np : ℤ × ℤ → ℝ := fun p => lqN m q (circConv m (restr μ (levelSet m c μ p.1))
    (restr ν (levelSet m cν ν p.2))) with hNp
  have e1 : circConv m μ ν = circConv m (restr μ E) ν + (circConv m μG (restr ν F) +
      ∑ p ∈ pairs, circConv m (restr μ (levelSet m c μ p.1)) (restr ν (levelSet m cν ν p.2))) := by
    have e3 : circConv m μG νG = ∑ p ∈ pairs, circConv m (restr μ (levelSet m c μ p.1))
        (restr ν (levelSet m cν ν p.2)) := by
      rw [hμG, circConv_sum_left, hpairs, Finset.sum_product]
      exact Finset.sum_congr rfl fun j _ => circConv_sum_right _ _ _
    rw [← e3, ← circConv_add_right, ← hdν, ← circConv_add_left, ← hdμ]

  have htri : lqN m q (circConv m μ ν) ≤ lqN m q (circConv m (restr μ E) ν) +
      (lqN m q (circConv m μG (restr ν F)) + ∑ p ∈ pairs, Np p) := by
    have hnn3 : ∀ k, 0 ≤ (∑ p ∈ pairs, circConv m (restr μ (levelSet m c μ p.1))
        (restr ν (levelSet m cν ν p.2))) k := fun k => by
      rw [Finset.sum_apply]
      exact Finset.sum_nonneg fun p _ => circConv_nonneg (restr_nonneg hμ.nonneg _)
        (restr_nonneg hν.nonneg _) k
    rw [e1]
    refine le_trans (lqN_add_le hq.le (circConv_nonneg hEnn hν.nonneg) fun k =>
      add_nonneg (circConv_nonneg hμGnn hFnn k) (hnn3 k)) (add_le_add_right ?_ _)
    refine le_trans (lqN_add_le hq.le (circConv_nonneg hμGnn hFnn) hnn3) (add_le_add_right ?_ _)
    exact lqN_sum_le hq.le pairs fun p k => circConv_nonneg (restr_nonneg hμ.nonneg _)
      (restr_nonneg hν.nonneg _) k

  have hJexp : 2 * ε * m ≤ (J₀ : ℝ) * (q - 1) / q := by
    rw [le_div_iff₀ hq0]
    have : 2 * ε * q' * m * (q - 1) = 2 * ε * m * q := by rw [hq']; field_simp
    nlinarith
  have hb1 : lqN m q (circConv m (restr μ E) ν) ≤ (2 : ℝ) ^ (-(2 * ε * m)) * lqN m q μ := by
    have h1 := lqN_circConv_le hq.le hEnn hν.nonneg hν.support
    rw [hν.sum_eq_one, mul_one] at h1
    refine le_trans h1 ?_
    have hEsub : E ⊆ Finset.Ico (0 : ℤ) (2 ^ m) := Finset.filter_subset _ _
    have hval : ∀ x ∈ E, μ x ≤ c * (2 : ℝ) ^ (-(J₀ : ℝ)) := by
      intro x hx
      obtain ⟨-, hx0, hxJ⟩ := Finset.mem_filter.mp hx
      refine le_trans (lev_bounds hc0 hx0).2 (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le one_le_two ?_) hc0.le)
      have : (J₀ : ℝ) ≤ (lev c μ x : ℝ) := by exact_mod_cast hxJ
      linarith
    have h2 : discLq m q (restr μ E) ≤ P * (2 : ℝ) ^ (-((J₀ : ℝ) * (q - 1))) := by
      rw [discLq_restr hq0 hEsub]
      have h3 : ∀ x ∈ E, μ x ^ q ≤ (c * (2 : ℝ) ^ (-(J₀ : ℝ))) ^ (q - 1) * μ x := by
        intro x hx
        have hx0 := (Finset.mem_filter.mp hx).2.1
        rw [show μ x ^ q = μ x ^ (q - 1) * μ x by
          rw [← Real.rpow_add_one hx0.ne']; ring_nf]
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx0.le (hval x hx) hq1.le) hx0.le
      calc ∑ x ∈ E, μ x ^ q ≤ ∑ x ∈ E, (c * (2 : ℝ) ^ (-(J₀ : ℝ))) ^ (q - 1) * μ x :=
            Finset.sum_le_sum h3
        _ = (c * (2 : ℝ) ^ (-(J₀ : ℝ))) ^ (q - 1) * ∑ x ∈ E, μ x := by rw [Finset.mul_sum]
        _ ≤ (c * (2 : ℝ) ^ (-(J₀ : ℝ))) ^ (q - 1) * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [← hμ.sum_eq_one]
            exact Finset.sum_le_sum_of_subset_of_nonneg hEsub fun x _ _ => hμ.nonneg x
        _ = P * (2 : ℝ) ^ (-((J₀ : ℝ) * (q - 1))) := by
            rw [mul_one, Real.mul_rpow hc0.le (by positivity), hcP, ← Real.rpow_mul (by norm_num)]
            ring_nf
    have h4 := Real.rpow_le_rpow (discLq_nonneg hEnn) h2 (by positivity : (0 : ℝ) ≤ 1 / q)
    unfold lqN
    refine le_trans h4 ?_
    rw [Real.mul_rpow hP0.le (by positivity), ← Real.rpow_mul (by norm_num), mul_comm]
    refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le one_le_two ?_)
      (by positivity)
    rw [show -((J₀ : ℝ) * (q - 1)) * (1 / q) = -((J₀ : ℝ) * (q - 1) / q) by ring]
    linarith

  have hb2 : lqN m q (circConv m μG (restr ν F)) ≤ (2 : ℝ) ^ (-(2 * ε * m)) * lqN m q μ := by
    have hFsub : F ⊆ Finset.Ico (0 : ℤ) (2 ^ m) := Finset.filter_subset _ _
    have h1 := lqN_circConv_le hq.le hμGnn hFnn (restr_support hFsub)
    rw [sum_restr hFsub] at h1
    have hμGle : lqN m q μG ≤ lqN m q μ := lqN_mono hq0 hμGnn fun k => by
      have := congrFun hdμ k
      simp only [Pi.add_apply] at this
      linarith [hEnn k]
    have hval : ∀ y ∈ F, ν y ≤ cν * (2 : ℝ) ^ (-(J₀ : ℝ)) := by
      intro y hy
      obtain ⟨-, hy0, hyJ⟩ := Finset.mem_filter.mp hy
      refine le_trans (lev_bounds hcν0 hy0).2 (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le one_le_two ?_) hcν0.le)
      have : (J₀ : ℝ) ≤ (lev cν ν y : ℝ) := by exact_mod_cast hyJ
      linarith
    have hSF : ∑ y ∈ F, ν y ≤ (2 : ℝ) ^ (-(2 * ε * m)) := by
      calc ∑ y ∈ F, ν y ≤ ∑ _y ∈ F, cν * (2 : ℝ) ^ (-(J₀ : ℝ)) := Finset.sum_le_sum hval
        _ = F.card * (cν * (2 : ℝ) ^ (-(J₀ : ℝ))) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 : ℝ) ^ m * (cν * (2 : ℝ) ^ (-(J₀ : ℝ))) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            rw [← card_Ico_two_pow]; exact_mod_cast Finset.card_le_card hFsub
        _ = (2 : ℝ) ^ (-(J₀ : ℝ)) := by
            rw [hcν, ← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add two_pos, add_neg_cancel,
              Real.rpow_zero, one_mul]
        _ ≤ (2 : ℝ) ^ (-(2 * ε * m)) := by
            refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
            have : 2 * ε * m ≤ 2 * ε * q' * m := by
              have := mul_le_mul_of_nonneg_left hq'1 (by positivity : (0 : ℝ) ≤ 2 * ε * m)
              nlinarith
            linarith
    calc lqN m q (circConv m μG (restr ν F)) ≤ lqN m q μG * ∑ y ∈ F, ν y := h1
      _ ≤ lqN m q μ * (2 : ℝ) ^ (-(2 * ε * m)) :=
          mul_le_mul hμGle hSF (Finset.sum_nonneg fun y _ => hν.nonneg y) hN0.le
      _ = _ := by ring

  have hpairs0 : pairs.Nonempty := by
    refine Finset.Nonempty.product ?_ ?_ <;>
      exact ⟨-(m : ℤ), Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
  obtain ⟨p, hp, hpmax⟩ := Finset.exists_max_image pairs Np hpairs0
  have hsum_le : ∑ p' ∈ pairs, Np p' ≤ pairs.card * Np p := by
    have := Finset.sum_le_card_nsmul pairs Np (Np p) hpmax
    rwa [nsmul_eq_mul] at this
  have hcard : (pairs.card : ℝ) = ((m : ℝ) + J₀) ^ 2 := by
    rw [hpairs, Finset.card_product, hJs, Int.card_Ico]
    have : ((J₀ : ℤ) - -(m : ℤ)).toNat = m + J₀ := by omega
    rw [this]; push_cast; ring
  have hX : (2 : ℝ) ^ (-(ε * m)) = ((2 : ℝ) ^ (ε * m))⁻¹ := Real.rpow_neg (by norm_num) _
  have hX2 : (2 : ℝ) ^ (-(2 * ε * m)) = (((2 : ℝ) ^ (ε * m)) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    push_cast; ring_nf
  have hKp : 4 * (2 : ℝ) ^ (-(2 * ε * m)) * lqN m q μ ≤ Np p := by
    rw [hX2]
    refine pigeon_numeric (S := ∑ p' ∈ pairs, Np p') (n := pairs.card) ?_ ?_ ?_ hN0.le ?_ hsum_le
    · have : (4 : ℝ) * 1 ≤ 4 * ((m : ℝ) + 1) ^ 2 := by nlinarith
      linarith
    · rw [hcard]
      have : ((m : ℝ) + J₀) ^ 2 ≤ a₀ ^ 2 * ((m : ℝ) + 1) ^ 2 := by
        rw [← mul_pow]
        have : (m : ℝ) + J₀ ≤ a₀ * ((m : ℝ) + 1) := by
          rw [ha₀]; nlinarith
        exact pow_le_pow_left₀ (by positivity) this 2
      nlinarith
    · exact_mod_cast hpairs0.card_pos
    · have h1 : (2 : ℝ) ^ (-(ε * m)) * lqN m q μ ≤ lqN m q (circConv m μ ν) := hconv
      rw [hX] at h1
      rw [hX2] at hb1 hb2
      have := le_trans h1 htri
      linarith
  obtain ⟨j, j'⟩ := p
  exact conclusions_of_pair hq hc0 hμ hν j j' hKp

end Inverse

end Lq

end FractalGeometry
