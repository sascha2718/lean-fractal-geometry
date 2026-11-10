module

/-
Fibre counts between labellings, for the proof of Rapaport's theorem (arXiv:2309.03985,
Section 2.5, lines 737 to 775 of the source): the commensurability statements behind the
comparisons (2.5) translation, (2.6) scaling and (2.7) perturbation, in one dimension. The
planar statements are in `Rapaport/Entropy/Rect.lean`.

* `FiberBound f g N`: every fibre of the labelling `f` meets at most `N` labels of `g`; its
  calculus `FiberBound.mono`, `congr`, `comp_left`, `prod`, `of_factor`, `trans`, `pair_left`,
  `pair_right`, `comp_right`, `of_refine_left`, and `fiberBound_self`.
* Floors: `fiberBound_floor_of_mem_Icc` (the core count), `fiberBound_floor_mul`,
  `fiberBound_floor_mul_of_abs_le`, `fiberBound_floor_mul_of_ratio` and its `_symm` (scaling),
  `fiberBound_floor_add_const`, `fiberBound_floor_mul_add` and its `_symm` (translation),
  `abs_floor_sub_floor_le`, `fiberBound_floor_perturb`, `fiberBound_dyadicQuantize_perturb`
  (perturbation), `fiberBound_dyadicQuantize_add_nat` (the children of a dyadic cell).
-/
public import ExactOverlaps.Entropy.Dyadic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Int.Interval

@[expose] public section

namespace BoxLike.Rapaport

open ExactOverlaps.Entropy

/-! ### Fibre counts -/

section FiberBound

variable {X Y L L' L'' M M' : Type*}

/-- Every fibre of `f` meets at most `N` labels of `g`: the commensurability count between the
partitions into the fibres of `f` and of `g` in Section 2.5 of the source (lines 737 to 775). -/
def FiberBound (f : X → L) (g : X → L') (N : ℕ) : Prop :=
  ∀ a : L, ∃ s : Finset L', s.card ≤ N ∧ ∀ x, f x = a → g x ∈ s

namespace FiberBound

variable {f : X → L} {g : X → L'} {N N' : ℕ}

/-- A fibre count persists under a larger bound. -/
theorem mono (h : FiberBound f g N) (hN : N ≤ N') : FiberBound f g N' := fun a =>
  let ⟨s, hs, hg⟩ := h a
  ⟨s, hs.trans hN, hg⟩

/-- A fibre count transfers to pointwise equal labellings. -/
theorem congr {f' : X → L} {g' : X → L'} (h : FiberBound f g N) (hf : ∀ x, f' x = f x)
    (hg : ∀ x, g' x = g x) : FiberBound f' g' N := by
  intro a
  obtain ⟨s, hs, hfg⟩ := h a
  refine ⟨s, hs, fun x hx => ?_⟩
  rw [hg x]
  exact hfg x ((hf x).symm.trans hx)

/-- A fibre count pulls back along any map `ψ`. -/
theorem comp_left (h : FiberBound f g N) (ψ : Y → X) : FiberBound (f ∘ ψ) (g ∘ ψ) N := fun a =>
  let ⟨s, hs, hg⟩ := h a
  ⟨s, hs, fun y hy => hg (ψ y) hy⟩

/-- Fibre counts multiply under joins of partitions. -/
theorem prod {f' : X → M} {g' : X → M'} (h : FiberBound f g N) (h' : FiberBound f' g' N') :
    FiberBound (fun x => (f x, f' x)) (fun x => (g x, g' x)) (N * N') := by
  intro a
  obtain ⟨s, hs, hg⟩ := h a.1
  obtain ⟨s', hs', hg'⟩ := h' a.2
  refine ⟨s ×ˢ s', ?_, fun x hx => ?_⟩
  · rw [Finset.card_product]
    exact Nat.mul_le_mul hs hs'
  · rw [Prod.ext_iff] at hx
    exact Finset.mem_product.2 ⟨hg x hx.1, hg' x hx.2⟩

/-- A coarsening `g = φ ∘ f` meets one label per fibre of `f`. -/
theorem of_factor {φ : L → L'} (h : g = φ ∘ f) : FiberBound f g 1 := fun a =>
  ⟨{φ a}, by simp, fun x hx => by simp [h, hx]⟩

/-- Fibre counts compose multiplicatively. -/
theorem trans {h : X → L''} (hfg : FiberBound f g N) (hgh : FiberBound g h N') :
    FiberBound f h (N * N') := by
  classical
  intro a
  obtain ⟨s, hs, hg⟩ := hfg a
  choose t ht hh using hgh
  refine ⟨s.biUnion t, ?_, fun x hx => Finset.mem_biUnion.2 ⟨g x, hg x hx, hh (g x) x rfl⟩⟩
  calc (s.biUnion t).card ≤ ∑ b ∈ s, (t b).card := Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ s, N' := Finset.sum_le_sum fun b _ => ht b
    _ = s.card * N' := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ N * N' := Nat.mul_le_mul_right _ hs

/-- A common labelling `h` may be joined to both sides of a fibre count. -/
theorem pair_left {h : X → M} (hfg : FiberBound f g N) :
    FiberBound (fun x => (f x, h x)) (fun x => (g x, h x)) N := by
  intro a
  obtain ⟨s, hs, hg⟩ := hfg a.1
  refine ⟨s ×ˢ {a.2}, by simpa using hs, fun x hx => ?_⟩
  rw [Prod.ext_iff] at hx
  exact Finset.mem_product.2 ⟨hg x hx.1, Finset.mem_singleton.2 hx.2⟩

/-- A common labelling `h` may be joined on the left of both sides of a fibre count. -/
theorem pair_right {h : X → M} (hfg : FiberBound f g N) :
    FiberBound (fun x => (h x, f x)) (fun x => (h x, g x)) N := by
  intro a
  obtain ⟨s, hs, hg⟩ := hfg a.2
  refine ⟨{a.1} ×ˢ s, by simpa using hs, fun x hx => ?_⟩
  rw [Prod.ext_iff] at hx
  exact Finset.mem_product.2 ⟨Finset.mem_singleton.2 hx.1, hg x hx.2⟩

/-- A coarsening of the counted labelling keeps the fibre count. -/
theorem comp_right (hfg : FiberBound f g N) (φ : L' → L'') : FiberBound f (φ ∘ g) N := by
  classical
  intro a
  obtain ⟨s, hs, hg⟩ := hfg a
  exact ⟨s.image φ, Finset.card_image_le.trans hs,
    fun x hx => Finset.mem_image_of_mem φ (hg x hx)⟩

/-- A refinement of the conditioning labelling keeps the fibre count. -/
theorem of_refine_left {f' : X → L''} {φ : L → L''} (hf : f' = φ ∘ f)
    (h : FiberBound f' g N) : FiberBound f g N := by
  intro a
  obtain ⟨s, hs, hg⟩ := h (φ a)
  exact ⟨s, hs, fun x hx => hg x (by rw [hf, Function.comp_apply, hx])⟩

end FiberBound

/-- Every labelling meets one label of itself per fibre. -/
theorem fiberBound_self (f : X → L) : FiberBound f f 1 := FiberBound.of_factor (φ := id) rfl

end FiberBound

/-! ### Commensurability in one dimension -/

section Floor

variable {X : Type*}

/-- The core count: if every fibre of `f` is sent by `G` into an interval of length `Λ`, then
it meets at most `⌈Λ⌉₊ + 1` labels `⌊G x⌋`. -/
theorem fiberBound_floor_of_mem_Icc {L : Type*} {f : X → L} {G : X → ℝ} {Λ : ℝ}
    (h : ∀ a, ∃ y : ℝ, ∀ x, f x = a → y ≤ G x ∧ G x ≤ y + Λ) :
    FiberBound f (fun x => ⌊G x⌋) (⌈Λ⌉₊ + 1) := by
  intro a
  obtain ⟨y, hy⟩ := h a
  refine ⟨Finset.Icc ⌊y⌋ ⌊y + Λ⌋, ?_, fun x hx => Finset.mem_Icc.2
    ⟨Int.floor_mono (hy x hx).1, Int.floor_mono (hy x hx).2⟩⟩
  have : ⌊y + Λ⌋ ≤ ⌊y⌋ + ⌈Λ⌉₊ := by
    rw [← Int.floor_add_natCast]
    exact Int.floor_mono (by linarith [Nat.le_ceil Λ])
  rw [Int.card_Icc]
  omega

/-- Multiplication by `ρ` sends `[k, k + 1]` into an interval of length `|ρ|`. -/
private theorem mul_mem_Icc_min {ρ k u : ℝ} (h1 : k ≤ u) (h2 : u ≤ k + 1) :
    min (ρ * k) (ρ * (k + 1)) ≤ ρ * u ∧ ρ * u ≤ min (ρ * k) (ρ * (k + 1)) + |ρ| := by
  rcases le_total 0 ρ with hρ | hρ
  · rw [abs_of_nonneg hρ, min_eq_left (by nlinarith)]
    constructor <;> nlinarith
  · rw [abs_of_nonpos hρ, min_eq_right (by nlinarith)]
    constructor <;> nlinarith

/-- Rescaling the argument of a floor by `ρ`: a fibre of `⌊F⌋` meets at most `⌈|ρ|⌉₊ + 1` labels
of `⌊ρ F⌋`. -/
theorem fiberBound_floor_mul (F : X → ℝ) (ρ : ℝ) :
    FiberBound (fun x => ⌊F x⌋) (fun x => ⌊ρ * F x⌋) (⌈|ρ|⌉₊ + 1) :=
  fiberBound_floor_of_mem_Icc fun k => ⟨min (ρ * k) (ρ * (k + 1)), fun x hx => by
    have hx' := Int.floor_eq_iff.1 hx
    exact mul_mem_Icc_min hx'.1 hx'.2.le⟩

/-- One-sided scaling count: if `|t| ≤ 2 |s|` with `s ≠ 0`, a fibre of `⌊s x⌋` meets at most `3`
labels `⌊t x⌋`. -/
theorem fiberBound_floor_mul_of_abs_le {s t : ℝ} (hs : s ≠ 0) (h : |t| ≤ 2 * |s|) :
    FiberBound (fun x : ℝ => ⌊s * x⌋) (fun x => ⌊t * x⌋) 3 := by
  have hs' : 0 < |s| := abs_pos.2 hs
  have hc : ⌈|t / s|⌉₊ ≤ 2 := Nat.ceil_le.2 (by
    rw [abs_div, div_le_iff₀ hs']
    exact_mod_cast h)
  refine ((fiberBound_floor_mul (fun x : ℝ => s * x) (t / s)).mono (by omega)).congr
    (fun _ => rfl) fun x => ?_
  congr 1
  field_simp

/-- Scaling count of Rapaport (2.6) on the line: if `1/2 ≤ |t| / |s| ≤ 2`, a fibre of
`⌊s x⌋` meets at most `3` labels `⌊t x⌋`. -/
theorem fiberBound_floor_mul_of_ratio {s t : ℝ} (h₁ : 1 / 2 ≤ |t| / |s|) (h₂ : |t| / |s| ≤ 2) :
    FiberBound (fun x : ℝ => ⌊s * x⌋) (fun x => ⌊t * x⌋) 3 := by
  have hs : s ≠ 0 := by
    rintro rfl
    rw [abs_zero, div_zero] at h₁
    norm_num at h₁
  exact fiberBound_floor_mul_of_abs_le hs ((div_le_iff₀ (abs_pos.2 hs)).1 h₂)

/-- The reverse scaling count: if `1/2 ≤ |t| / |s| ≤ 2`, a fibre of `⌊t x⌋` meets at most `3`
labels `⌊s x⌋`. -/
theorem fiberBound_floor_mul_of_ratio_symm {s t : ℝ} (h₁ : 1 / 2 ≤ |t| / |s|)
    (h₂ : |t| / |s| ≤ 2) : FiberBound (fun x : ℝ => ⌊t * x⌋) (fun x => ⌊s * x⌋) 3 := by
  have hs : s ≠ 0 := by
    rintro rfl
    rw [abs_zero, div_zero] at h₁
    norm_num at h₁
  have hs' : 0 < |s| := abs_pos.2 hs
  have h := (le_div_iff₀ hs').1 h₁
  have ht : t ≠ 0 := by
    rintro rfl
    rw [abs_zero] at h
    linarith
  exact fiberBound_floor_mul_of_abs_le ht (by linarith)

/-- Translation count of Rapaport (2.5): a fibre of `⌊F x⌋` meets at most `2` labels
`⌊F x + c⌋`. -/
theorem fiberBound_floor_add_const (F : X → ℝ) (c : ℝ) :
    FiberBound (fun x => ⌊F x⌋) (fun x => ⌊F x + c⌋) 2 := by
  have h := fiberBound_floor_of_mem_Icc (f := fun x => ⌊F x⌋) (G := fun x => F x + c) (Λ := 1)
    fun k => ⟨k + c, fun x hx => by
      have hx' := Int.floor_eq_iff.1 hx
      constructor <;> linarith [hx'.1, hx'.2]⟩
  rwa [Nat.ceil_one] at h

/-- Translation count of Rapaport (2.5) on the line: a fibre of `⌊s x⌋` meets at most `2` labels
`⌊s (x + c)⌋`. -/
theorem fiberBound_floor_mul_add (s c : ℝ) :
    FiberBound (fun x : ℝ => ⌊s * x⌋) (fun x => ⌊s * (x + c)⌋) 2 :=
  (fiberBound_floor_add_const (fun x : ℝ => s * x) (s * c)).congr (fun _ => rfl)
    fun x => by rw [mul_add]

/-- The reverse translation count: a fibre of `⌊s (x + c)⌋` meets at most `2` labels `⌊s x⌋`. -/
theorem fiberBound_floor_mul_add_symm (s c : ℝ) :
    FiberBound (fun x : ℝ => ⌊s * (x + c)⌋) (fun x => ⌊s * x⌋) 2 :=
  (fiberBound_floor_add_const (fun x : ℝ => s * (x + c)) (-(s * c))).congr (fun _ => rfl)
    fun x => by congr 1; ring

/-- Perturbation of the argument of a floor: `|u - u'| ≤ C` gives `|⌊u⌋ - ⌊u'⌋| ≤ ⌈C⌉₊ + 1`. -/
theorem abs_floor_sub_floor_le {u u' C : ℝ} (h : |u - u'| ≤ C) :
    |⌊u⌋ - ⌊u'⌋| ≤ (⌈C⌉₊ : ℤ) + 1 := by
  have h1 := Int.floor_le u
  have h2 := Int.lt_floor_add_one u
  have h3 := Int.floor_le u'
  have h4 := Int.lt_floor_add_one u'
  have hC := Nat.le_ceil C
  rw [abs_le] at h ⊢
  constructor
  · have : ((-((⌈C⌉₊ : ℤ) + 1) : ℤ) : ℝ) ≤ ((⌊u⌋ - ⌊u'⌋ : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  · have : ((⌊u⌋ - ⌊u'⌋ : ℤ) : ℝ) ≤ (((⌈C⌉₊ : ℤ) + 1 : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this

/-- Perturbation count of Rapaport (2.7): if `|F x - G x| ≤ C` everywhere, a fibre of `⌊F x⌋`
meets at most `2 ⌈C⌉₊ + 3` labels `⌊G x⌋`. -/
theorem fiberBound_floor_perturb {F G : X → ℝ} {C : ℝ} (h : ∀ x, |F x - G x| ≤ C) :
    FiberBound (fun x => ⌊F x⌋) (fun x => ⌊G x⌋) (2 * ⌈C⌉₊ + 3) := by
  intro k
  refine ⟨Finset.Icc (k - (⌈C⌉₊ + 1)) (k + (⌈C⌉₊ + 1)), ?_, fun x hx => ?_⟩
  · rw [Int.card_Icc]
    omega
  · have hd := abs_floor_sub_floor_le (h x)
    have hx' : ⌊F x⌋ = k := hx
    rw [abs_le] at hd
    show ⌊G x⌋ ∈ Finset.Icc _ _
    rw [Finset.mem_Icc]
    constructor <;> omega

/-- Perturbation count of Rapaport (2.7) for dyadic labels: if `|F x - G x| ≤ C 2^{-i}`
everywhere, a fibre of `dyadicQuantize i ∘ F` meets at most `2 ⌈C⌉₊ + 3` labels of
`dyadicQuantize i ∘ G`. -/
theorem fiberBound_dyadicQuantize_perturb {F G : X → ℝ} {C : ℝ} {i : ℤ}
    (h : ∀ x, |F x - G x| ≤ C * 2 ^ (-i)) :
    FiberBound (dyadicQuantize i ∘ F) (dyadicQuantize i ∘ G) (2 * ⌈C⌉₊ + 3) :=
  fiberBound_floor_perturb (F := fun x => 2 ^ i * F x) (G := fun x => 2 ^ i * G x) fun x => by
    have hpos := dyadic_scale_pos i
    calc |(2 : ℝ) ^ i * F x - 2 ^ i * G x| = 2 ^ i * |F x - G x| := by
          rw [← mul_sub, abs_mul, abs_of_pos hpos]
      _ ≤ 2 ^ i * (C * 2 ^ (-i)) := mul_le_mul_of_nonneg_left (h x) hpos.le
      _ = C := by
          rw [zpow_neg]
          field_simp

/-- The children of a dyadic cell: the cell `k` at level `i` meets at most the `2^a` cells
`[2^a k, 2^a (k + 1))` at level `i + a`. -/
theorem fiberBound_dyadicQuantize_add_nat (i : ℤ) (a : ℕ) :
    FiberBound (dyadicQuantize i) (dyadicQuantize (i + a)) (2 ^ a) := by
  intro k
  refine ⟨Finset.Ico (k * (2 ^ a : ℕ)) ((k + 1) * (2 ^ a : ℕ)), ?_, fun x hx => ?_⟩
  · rw [Int.card_Ico, ← sub_mul, add_sub_cancel_left, one_mul, Int.toNat_natCast]
  · have hd : (0 : ℤ) < (2 ^ a : ℕ) := by positivity
    rw [dyadicQuantize_add_nat i a] at hx
    rw [Finset.mem_Ico, ← hx]
    exact ⟨Int.ediv_mul_le _ hd.ne', Int.lt_ediv_add_one_mul_self _ hd⟩

end Floor

end BoxLike.Rapaport
