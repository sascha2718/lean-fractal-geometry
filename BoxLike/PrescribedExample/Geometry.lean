module

/-
The geometric part of `ex:projection_double_dimensional`, tex lines 2764 to 2859, in one
statement: for every `0 < s_2 < s_1 ≤ 1` the unique `p ∈ (1/2, 1)` with
`(log 2 + H(p)) / (log 2 + J(p)) = s_2/s_1`, and a translation `t` in the cube `B` for which the
system of four maps with `a = (p/2)^{1/s_1}`, `b = ((1-p)/2)^{1/s_1}` is a proximal irreducible
box-like system with rotations, satisfies the strong separation, strong open set and projective
exponential separation conditions, has no exact overlaps, and has `dimaff = s_1`.

* `PrescribedExample.Geometry`: the conclusions about `sys P t` that hold for the selected
  translations.
* `PrescribedExample.exists_geometry_of_params`: for every `0 < b < a < 1/2` some `t ∈ B`
  satisfies `Geometry`.
* `PrescribedExample.exists_geometry`: the wrapper for `0 < s_2 < s_1 ≤ 1`.
-/
public import BoxLike.PrescribedExample.Separation

@[expose] public section

namespace BoxLike

namespace PrescribedExample

open Set

/-- The geometric conclusions of `ex:projection_double_dimensional` for the system `sys P t`:
rotations, a proximal diagonal generator, proximality and irreducibility; the invariant square
`[0, 2R]^2` with image rectangles at mutual distance at least one; strong separation and the
strong open set condition; the gap `|g_𝐢^t(0) - g_𝐣^t(0)| ≥ C c^n` for distinct words of every
length `n ≥ 1`, with `C = κ/8`, `c = b/128`, hence `Δ_n^Ψ ≥ C c^n`, projective exponential
separation and no exact overlaps; and `P(𝖠, u) = log(2 a^u + 2 b^u)` for `0 ≤ u ≤ 1`. -/
structure Geometry (P : Params) (t : Fin 8 → ℝ) : Prop where
  /-- Both orientations occur. -/
  withRotations : (sys P t).WithRotations
  /-- The tuple contains a proximal diagonal generator. -/
  hasProximalDiagonal : (sys P t).HasProximalDiagonal
  /-- The tuple is proximal. -/
  proximal : (sys P t).Proximal
  /-- The tuple is irreducible. -/
  irreducible : (sys P t).Irreducible
  /-- The four maps send `[0, 2R]^2` into itself. -/
  phi_image_square_subset : ∀ i, (sys P t).phi i '' square P ⊆ square P
  /-- The image rectangles of distinct maps are separated by gaps of at least one. -/
  one_le_dist_phi : ∀ i j, i ≠ j → ∀ z ∈ square P, ∀ z' ∈ square P,
    1 ≤ dist ((sys P t).phi i z) ((sys P t).phi j z')
  /-- The strong separation condition. -/
  strongSeparation : (sys P t).StrongSeparation
  /-- The strong open set condition. -/
  strongOpenSet : (sys P t).StrongOpenSet
  /-- `|g_𝐢^t(0) - g_𝐣^t(0)| ≥ C c^n` for distinct words of every length `n ≥ 1`. -/
  le_abs_gWord_sub : ∀ n : ℕ, 1 ≤ n → ∀ u u' : List (Fin 4 × ZMod 2), u.length = n →
    u'.length = n → u ≠ u' →
      constC P * constc P ^ n ≤ |(sys P t).gWord u 0 - (sys P t).gWord u' 0|
  /-- `Δ_n^Ψ ≥ C c^n` for every `n ≥ 1`. -/
  le_gap : ∀ n : ℕ, 1 ≤ n → ENNReal.ofReal (constC P * constc P ^ n) ≤ (sys P t).gap n
  /-- The projective exponential separation condition. -/
  projExpSeparation : (sys P t).ProjExpSeparation
  /-- The projective system has no exact overlaps. -/
  noExactOverlaps : (sys P t).NoExactOverlaps
  /-- `P(𝖠, u) = log(2 a^u + 2 b^u)` for `0 ≤ u ≤ 1`. -/
  pressure_eq : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
    (sys P t).pressure u = Real.log (2 * P.a ^ u + 2 * P.b ^ u)

/-- For all contractions `0 < b < a < 1/2` some translation `t ∈ B` satisfies the geometric
conclusions of `ex:projection_double_dimensional`. -/
theorem exists_geometry_of_params (P : Params) : ∃ t ∈ cube P, Geometry P t := by
  obtain ⟨t, ht, hgap, hΔ, hpesc, hfree⟩ := exists_translation P
  exact ⟨t, ht, withRotations P t, hasProximalDiagonal P t, proximal P t, irreducible P t,
    phi_image_square_subset ht, fun i j hij z hz z' hz' => one_le_dist_phi ht hij hz hz',
    strongSeparation ht, strongOpenSet ht, hgap, hΔ, hpesc, hfree,
    fun u hu₀ hu₁ => pressure_eq P t hu₀ hu₁⟩

/-- The construction of `ex:projection_double_dimensional` up to the measure-theoretic part:
for every `0 < s_2 < s_1 ≤ 1` there is a unique `p ∈ (1/2, 1)` with
`(log 2 + H(p)) / (log 2 + J(p)) = s_2/s_1`, and for the parameters `a = (p/2)^{1/s_1}`,
`b = ((1-p)/2)^{1/s_1}` some translation `t ∈ B` gives a system of four maps satisfying
`Geometry` with affinity dimension `s_1`. -/
theorem exists_geometry {s₁ s₂ : ℝ} (h₀ : 0 < s₂) (h₁₂ : s₂ < s₁) (h₁ : s₁ ≤ 1) :
    ∃ p : ℝ, ∃ hp : 1 / 2 < p ∧ p < 1, ratio p = s₂ / s₁ ∧
      (∀ q ∈ Ioo (1 / 2 : ℝ) 1, ratio q = s₂ / s₁ → q = p) ∧
      ∃ t ∈ cube (paramsOf s₁ p (h₀.trans h₁₂) h₁ hp.1 hp.2),
        Geometry (paramsOf s₁ p (h₀.trans h₁₂) h₁ hp.1 hp.2) t ∧
        (sys (paramsOf s₁ p (h₀.trans h₁₂) h₁ hp.1 hp.2) t).dimaff = s₁ := by
  obtain ⟨p, ⟨hp, hpr⟩, huniq⟩ := existsUnique_p h₀ h₁₂
  obtain ⟨t, ht, hg⟩ := exists_geometry_of_params (paramsOf s₁ p (h₀.trans h₁₂) h₁ hp.1 hp.2)
  exact ⟨p, hp, hpr, fun q hq hqr => huniq q ⟨hq, hqr⟩, t, ht, hg, dimaff_paramsOf t _ _ _ _⟩

end PrescribedExample

end BoxLike
