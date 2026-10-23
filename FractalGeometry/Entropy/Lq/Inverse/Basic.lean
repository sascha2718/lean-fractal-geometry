import Mathlib
import FractalGeometry.Entropy.Lq.Statements
import FractalGeometry.Entropy.Lq.Theorem51

open Filter Topology

open scoped Pointwise

namespace FractalGeometry

namespace Lq

namespace Inverse

def InUnit (m : ℕ) (A : Finset ℤ) : Prop := ∀ x ∈ A, 0 ≤ x ∧ x < 2 ^ m

def IsUniform (D ℓ : ℕ) (A : Finset ℤ) (R : ℕ → ℕ) : Prop :=
  ∀ s < ℓ, ∀ x ∈ A, branching (ℓ * D) (s * D) ((s + 1) * D) A x = R s

noncomputable def ind (A : Finset ℤ) (k : ℤ) : ℝ := if k ∈ A then 1 else 0

def lift {m : ℕ} (Z : Finset (ZMod (2 ^ m))) : Finset ℤ := Z.image fun z => (z.val : ℤ)

theorem tendsto_mul_right_atTop {D : ℕ} (hD : 1 ≤ D) : Tendsto (fun ℓ : ℕ => ℓ * D) atTop atTop :=
  Tendsto.atTop_mul_one_le (fun ⦃_⦄ a => a) fun _ => hD

theorem eventually_linear_le_two_rpow (a : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ D : ℕ in atTop, a * (D + 1) ≤ (2 : ℝ) ^ (c * D) := by
  have hr : 1 < (2 : ℝ) ^ c := Real.one_lt_rpow one_lt_two hc
  have h := ((tendsto_pow_const_div_const_pow_of_one_lt 1 hr).add
    (tendsto_pow_const_div_const_pow_of_one_lt 0 hr)).const_mul a
  rw [add_zero, mul_zero] at h
  filter_upwards [h.eventually (gt_mem_nhds zero_lt_one)] with D hD
  have hpos : 0 < ((2 : ℝ) ^ c) ^ D := pow_pos (by positivity) D
  rw [Real.rpow_mul_natCast (by norm_num)]
  simp only [pow_one, pow_zero] at hD
  rw [← add_div, mul_div_assoc', div_lt_one hpos] at hD
  exact hD.le

theorem prod_eq_prod_ite_mul (ℓ : ℕ) (K : Finset ℕ) (R : ℕ → ℕ) :
    ∏ s ∈ Finset.range ℓ, R s =
      (∏ s ∈ Finset.range ℓ, if s ∈ K then 1 else R s) *
        ∏ s ∈ (Finset.range ℓ).filter (· ∈ K), R s := by
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.range ℓ) (· ∈ K) R,
    ← Finset.prod_filter_mul_prod_filter_not (Finset.range ℓ) (· ∈ K)
      (fun s => if s ∈ K then 1 else R s),
    Finset.prod_congr rfl (fun s hs => ite_eq_of_pos (Finset.mem_filter.mp hs).2),
    Finset.prod_congr rfl (fun s hs => ite_eq_of_neg (Finset.mem_filter.mp hs).2)]
  simp only [Finset.prod_const_one, one_mul]
  ring

theorem pow_card_le_prod_real {T : Finset ℕ} {f : ℕ → ℕ} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ s ∈ T, a ≤ f s) : a ^ T.card ≤ ((∏ s ∈ T, f s : ℕ) : ℝ) := by
  rw [Nat.cast_prod, ← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun _ _ => ha) h

theorem prod_le_pow_card_real {T : Finset ℕ} {f : ℕ → ℕ} {a : ℝ}
    (h : ∀ s ∈ T, (f s : ℝ) ≤ a) : ((∏ s ∈ T, f s : ℕ) : ℝ) ≤ a ^ T.card := by
  rw [Nat.cast_prod, ← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) h

theorem two_rpow_pow (a : ℝ) (n : ℕ) : ((2 : ℝ) ^ a) ^ n = (2 : ℝ) ^ (a * n) :=
  (Real.rpow_mul_natCast (by norm_num) a n).symm

theorem branching_pos {m n n' : ℕ} {A : Finset ℤ} {x : ℤ} (hx : x ∈ A) :
    1 ≤ branching m n n' A x := by
  unfold branching
  exact Finset.card_pos.mpr ⟨x / 2 ^ (m - n'),
    Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hx, rfl⟩)⟩

theorem branching_le_two_pow {m n n' : ℕ} (hn : n ≤ n') (hn' : n' ≤ m) (A : Finset ℤ)
    (x : ℤ) : branching m n n' A x ≤ 2 ^ (n' - n) := by
  unfold branching
  set k := x / 2 ^ (m - n)
  have hpos : (0 : ℤ) < 2 ^ (n' - n) := by positivity
  have hsub : (A.filter fun y => y / 2 ^ (m - n) = k).image (fun y => y / 2 ^ (m - n')) ⊆
      Finset.Ico (k * 2 ^ (n' - n)) ((k + 1) * 2 ^ (n' - n)) := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hc
    have hyk := (Finset.mem_filter.mp hy).2
    rw [← ediv_two_pow_ediv hn hn' y] at hyk
    rw [Finset.mem_Ico, ← hyk]
    exact ⟨Int.ediv_mul_le _ hpos.ne', Int.lt_ediv_add_one_mul_self _ hpos⟩
  calc _ ≤ (Finset.Ico (k * 2 ^ (n' - n)) ((k + 1) * 2 ^ (n' - n))).card :=
        Finset.card_le_card hsub
    _ = 2 ^ (n' - n) := by
        rw [Int.card_Ico, show (k + 1) * 2 ^ (n' - n) - k * 2 ^ (n' - n) = 2 ^ (n' - n) by ring]
        exact_mod_cast Int.toNat_natCast (2 ^ (n' - n))

theorem IsUniform.one_le {D ℓ : ℕ} {A : Finset ℤ} {R : ℕ → ℕ} (h : IsUniform D ℓ A R)
    (hne : A.Nonempty) : ∀ s < ℓ, 1 ≤ R s := by
  intro s hs
  obtain ⟨x, hx⟩ := hne
  rw [← h s hs x hx]
  exact branching_pos hx

theorem IsUniform.le_two_pow {D ℓ : ℕ} {A : Finset ℤ} {R : ℕ → ℕ} (h : IsUniform D ℓ A R)
    (hne : A.Nonempty) : ∀ s < ℓ, R s ≤ 2 ^ D := by
  intro s hs
  obtain ⟨x, hx⟩ := hne
  rw [← h s hs x hx]
  have h1 : s * D ≤ (s + 1) * D := Nat.mul_le_mul_right D (Nat.le_succ s)
  have h2 : (s + 1) * D ≤ ℓ * D := Nat.mul_le_mul_right D hs
  have h3 : (s + 1) * D - s * D = D := by rw [add_mul, one_mul, Nat.add_sub_cancel_left]
  have := branching_le_two_pow h1 h2 A x
  rwa [h3] at this

theorem branching_prefix {m k n n' : ℕ} (hn : n ≤ n') (hn' : n' ≤ m) (A : Finset ℤ) (x : ℤ) :
    branching (m + k) n n' A x = branching m n n' (A.image (· / 2 ^ k)) (x / 2 ^ k) := by
  unfold branching
  have e : ∀ y : ℤ, ∀ j ≤ m, y / 2 ^ (m + k - j) = y / 2 ^ k / 2 ^ (m - j) := by
    intro y j hj
    rw [Int.ediv_ediv_of_nonneg (by positivity), ← pow_add]
    congr 2
    omega
  have hnm : n ≤ m := le_trans hn hn'
  congr 1
  ext c
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨y, ⟨hy, hyx⟩, rfl⟩
    refine ⟨y / 2 ^ k, ⟨⟨y, hy, rfl⟩, ?_⟩, (e y n' hn').symm⟩
    rw [← e y n hnm, ← e x n hnm]
    exact hyx
  · rintro ⟨p, ⟨⟨y, hy, rfl⟩, hpx⟩, rfl⟩
    exact ⟨y, ⟨hy, by rw [e y n hnm, e x n hnm]; exact hpx⟩, e y n' hn'⟩

theorem IsUniform.card_eq {D ℓ : ℕ} {A : Finset ℤ} {R : ℕ → ℕ} (h : IsUniform D ℓ A R)
    (hA : InUnit (ℓ * D) A) (hne : A.Nonempty) : A.card = ∏ s ∈ Finset.range ℓ, R s :=
  card_eq_prod_branching rfl hne hA h

theorem branching_last {m k : ℕ} (hk : k ≤ m) (A : Finset ℤ) (x : ℤ) :
    branching m (m - k) m A x = (A.filter fun y => y / 2 ^ k = x / 2 ^ k).card := by
  unfold branching
  rw [show m - (m - k) = k by omega, Nat.sub_self, pow_zero]
  simp only [Int.ediv_one, Finset.image_id']

theorem inUnit_image_prefix {D ℓ : ℕ} {A : Finset ℤ} (hA : InUnit ((ℓ + 1) * D) A) :
    InUnit (ℓ * D) (A.image (· / 2 ^ D)) := by
  intro p hp
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
  have hy' := hA y hy
  refine ⟨Int.ediv_nonneg hy'.1 (by positivity), ?_⟩
  rw [Int.ediv_lt_iff_lt_mul (by positivity), ← pow_add]
  have : ℓ * D + D = (ℓ + 1) * D := by ring
  rw [this]
  exact hy'.2

theorem isUniform_succ_iff {D ℓ : ℕ} {A : Finset ℤ} {R : ℕ → ℕ} :
    IsUniform D (ℓ + 1) A R ↔ IsUniform D ℓ (A.image (· / 2 ^ D)) R ∧
      ∀ x ∈ A, (A.filter fun y => y / 2 ^ D = x / 2 ^ D).card = R ℓ := by
  have e : (ℓ + 1) * D = ℓ * D + D := by ring
  have hpre : ∀ s < ℓ, ∀ x, branching ((ℓ + 1) * D) (s * D) ((s + 1) * D) A x =
      branching (ℓ * D) (s * D) ((s + 1) * D) (A.image (· / 2 ^ D)) (x / 2 ^ D) := by
    intro s hs x
    rw [e]
    exact branching_prefix (Nat.mul_le_mul_right D (Nat.le_succ s))
      (Nat.mul_le_mul_right D hs) A x
  have hlast : ∀ x, branching ((ℓ + 1) * D) (ℓ * D) ((ℓ + 1) * D) A x =
      (A.filter fun y => y / 2 ^ D = x / 2 ^ D).card := by
    intro x
    have h := branching_last (m := (ℓ + 1) * D) (k := D) (by rw [e]; omega) A x
    rw [e, Nat.add_sub_cancel] at h
    rw [e]
    exact h
  constructor
  · intro h
    refine ⟨fun s hs p hp => ?_, fun x hx => ?_⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      rw [← hpre s hs x]
      exact h s (by omega) x hx
    · rw [← hlast x]
      exact h ℓ (by omega) x hx
  · rintro ⟨h1, h2⟩ s hs x hx
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
    · rw [hpre s hs x]
      exact h1 s hs _ (Finset.mem_image_of_mem _ hx)
    · rw [hlast x]
      exact h2 x hx

theorem card_fiber_le (D : ℕ) (A : Finset ℤ) (x : ℤ) :
    (A.filter fun y => y / 2 ^ D = x / 2 ^ D).card ≤ 2 ^ D := by
  rw [← branching_last (m := D) le_rfl A x]
  have h2 := branching_le_two_pow (m := D) (n := D - D) (n' := D) (Nat.sub_le _ _) le_rfl A x
  rw [Nat.sub_self, Nat.sub_zero] at h2
  rw [Nat.sub_self]
  exact h2

theorem card_eq_mul_card_image {D r : ℕ} {A : Finset ℤ}
    (h : ∀ x ∈ A, (A.filter fun y => y / 2 ^ D = x / 2 ^ D).card = r) :
    A.card = r * (A.image (· / 2 ^ D)).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := (· / 2 ^ D)) (t := A.image (· / 2 ^ D))
    (fun x hx => Finset.mem_image_of_mem _ hx), mul_comm]
  rw [Finset.sum_const_nat]
  intro p hp
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
  exact h x hx

theorem cast_injOn {m : ℕ} {A : Finset ℤ} (hA : InUnit m A) :
    Set.InjOn (Int.cast : ℤ → ZMod (2 ^ m)) A := by
  intro x hx y hy h
  have h' := (ZMod.intCast_eq_intCast_iff' x y (2 ^ m)).mp h
  push_cast at h'
  rwa [Int.emod_eq_of_lt (hA x hx).1 (hA x hx).2, Int.emod_eq_of_lt (hA y hy).1 (hA y hy).2] at h'

theorem card_image_cast {m : ℕ} {A : Finset ℤ} (hA : InUnit m A) :
    (A.image (Int.cast : ℤ → ZMod (2 ^ m))).card = A.card :=
  Finset.card_image_of_injOn (cast_injOn hA)

theorem card_add_le_two_mul {m : ℕ} {A B : Finset ℤ} (hA : InUnit m A) (hB : InUnit m B) :
    (A + B).card ≤ 2 * (A.image (Int.cast : ℤ → ZMod (2 ^ m)) + B.image Int.cast).card := by
  classical
  have himg : (A + B).image (Int.cast : ℤ → ZMod (2 ^ m)) =
      A.image (Int.cast : ℤ → ZMod (2 ^ m)) + B.image Int.cast :=
    Finset.image_add (Int.castAddHom (ZMod (2 ^ m)))
  rw [← himg, mul_comm, ← Finset.card_range 2, ← Finset.card_product]
  have hpos : ∀ z ∈ A + B, 0 ≤ z ∧ z < 2 * 2 ^ m := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
    have hx' := hA x hx
    have hy' := hB y hy
    constructor <;> linarith
  refine Finset.card_le_card_of_injOn (fun z => ((z : ZMod (2 ^ m)), (z / 2 ^ m).toNat))
    (fun z hz => ?_) (fun z hz w hw h => ?_)
  · refine Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hz, Finset.mem_range.mpr ?_⟩
    show (z / 2 ^ m).toNat < 2
    have h1 : z / 2 ^ m < 2 := by
      rw [Int.ediv_lt_iff_lt_mul (by positivity)]; linarith [(hpos z hz).2]
    have h2 : 0 ≤ z / 2 ^ m := Int.ediv_nonneg (hpos z hz).1 (by positivity)
    generalize z / 2 ^ m = t at h1 h2 ⊢
    omega
  · dsimp only at h
    have h1 : (z : ZMod (2 ^ m)) = w := congrArg Prod.fst h
    have h2 : (z / 2 ^ m).toNat = (w / 2 ^ m).toNat := congrArg Prod.snd h
    have hmod := (ZMod.intCast_eq_intCast_iff' _ _ (2 ^ m)).mp h1
    push_cast at hmod
    have hz0 : 0 ≤ z / 2 ^ m := Int.ediv_nonneg (hpos z hz).1 (by positivity)
    have hw0 : 0 ≤ w / 2 ^ m := Int.ediv_nonneg (hpos w hw).1 (by positivity)
    have hdiv : z / 2 ^ m = w / 2 ^ m := by
      generalize z / 2 ^ m = t at hz0 h2 ⊢
      generalize w / 2 ^ m = t' at hw0 h2 ⊢
      omega
    rw [← Int.mul_ediv_add_emod z (2 ^ m), ← Int.mul_ediv_add_emod w (2 ^ m), hdiv, hmod]

theorem inUnit_lift {m : ℕ} (Z : Finset (ZMod (2 ^ m))) : InUnit m (lift Z) := by
  intro x hx
  obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨Int.natCast_nonneg _, by exact_mod_cast ZMod.val_lt z⟩

theorem image_cast_lift {m : ℕ} (Z : Finset (ZMod (2 ^ m))) :
    (lift Z).image (Int.cast : ℤ → ZMod (2 ^ m)) = Z := by
  unfold lift
  rw [Finset.image_image]
  convert Finset.image_id (s := Z)
  funext z
  simp

theorem card_lift {m : ℕ} (Z : Finset (ZMod (2 ^ m))) : (lift Z).card = Z.card := by
  rw [← card_image_cast (inUnit_lift Z), image_cast_lift]

end Inverse

end Lq

end FractalGeometry
