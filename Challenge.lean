/-
Comparator challenge file: the headline theorems of `FractalGeometry`, restated
with `sorry` in place of their proofs.

Everything these statements mention is defined below, over Mathlib alone. No
module of the library is imported: the trust boundary of the audit is this file
together with its import closure, and the library is what the audit is about.
`Solution.lean` is the untrusted side and may import it freely.

Run the audit from the project root with `./comparator-audit.sh`; the audited
names are listed in `comparator-config.json`.
-/
import Mathlib
namespace Challenge

open MeasureTheory
open scoped ENNReal NNReal Topology

/-! ## Frostman and Ahlfors regular measures -/

/-- `μ` is `s`-Frostman with constant `A`: a measure carried by `[0,1]` with
`μ(B̄(x,ρ)) ≤ A ρ^s` for every centre and every `0 < ρ ≤ 1`. -/
structure IsFrostman (s A : ℝ) (μ : Measure ℝ) : Prop where
  /-- The constant is at least one. -/
  one_le_const : 1 ≤ A
  /-- The measure sits on the unit interval. -/
  support : μ (Set.Icc (0:ℝ) 1)ᶜ = 0
  /-- The Frostman bound on closed balls of radius at most one. -/
  measure_closedBall_le :
    ∀ x : ℝ, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      μ (Metric.closedBall x ρ) ≤ ENNReal.ofReal (A * ρ ^ s)

/-- Two-sided regularity on the closed balls `B̄(x,r)`, at centres in the support.
Support points are those charging every ball. -/
def IsAhlforsClosed (s A : ℝ) (μ : Measure ℝ) : Prop :=
  1 ≤ A ∧ ∀ x : ℝ, (∀ ε > 0, μ (Metric.ball x ε) ≠ 0) → ∀ r : ℝ, 0 < r → r ≤ 1 →
    ENNReal.ofReal (A⁻¹ * r ^ s) ≤ μ (Metric.closedBall x r) ∧
      μ (Metric.closedBall x r) ≤ ENNReal.ofReal (A * r ^ s)

/-- The same two-sided bound on the open balls `B(x,r)`. -/
def IsAhlfors (s A : ℝ) (μ : Measure ℝ) : Prop :=
  1 ≤ A ∧ ∀ x : ℝ, (∀ ε > 0, μ (Metric.ball x ε) ≠ 0) → ∀ r : ℝ, 0 < r → r ≤ 1 →
    ENNReal.ofReal (A⁻¹ * r ^ s) ≤ μ (Metric.ball x r) ∧
      μ (Metric.ball x r) ≤ ENNReal.ofReal (A * r ^ s)

/-- The pair-distance distribution `Φ(δ) = P(|X - Y| ≤ δ)` for independent `X, Y`
with law `μ`. -/
noncomputable def Phi (μ : Measure ℝ) (δ : ℝ) : ℝ :=
  ((μ.prod μ) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}).toReal

/-! ## Self-similar systems -/

/-- A self-similar system on `[0,1]`: finitely many contracting similarities
`S_i(x) = r_i x + b_i` mapping the unit interval into itself. -/
structure System (ι : Type*) [Fintype ι] where
  /-- The contraction ratios. -/
  ratio : ι → ℝ
  /-- The translation parts. -/
  shift : ι → ℝ
  /-- Each ratio is positive. -/
  ratio_pos : ∀ i, 0 < ratio i
  /-- Each ratio is a contraction. -/
  ratio_lt_one : ∀ i, ratio i < 1
  /-- Each similarity maps the unit interval into itself. -/
  mapsTo : ∀ i, Set.MapsTo (fun x => ratio i * x + shift i) (Set.Icc 0 1) (Set.Icc 0 1)

namespace System

variable {ι : Type*} [Fintype ι] (S : System ι)

/-- The `i`-th similarity `S_i(x) = r_i x + b_i`. -/
def map (i : ι) (x : ℝ) : ℝ := S.ratio i * x + S.shift i

/-- An attractor of the system: a nonempty compact subset of `[0,1]` with
`K = ⋃ i S_i K`. -/
def IsAttractor (K : Set ℝ) : Prop :=
  IsCompact K ∧ K.Nonempty ∧ K ⊆ Set.Icc 0 1 ∧ K = ⋃ i, S.map i '' K

/-- Strong separation with gap `ρ`: the pieces `S_i K` and `S_j K` of the attractor
stay `ρ` apart for `i ≠ j`. -/
def StronglySeparated (K : Set ℝ) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ i j, i ≠ j → ∀ x ∈ K, ∀ y ∈ K, ρ ≤ |S.map i x - S.map j y|

/-- The similarity dimension: the exponent solving `∑ r_i^s = 1`. -/
def IsDimension (s : ℝ) : Prop := ∑ i, S.ratio i ^ s = 1

/-- The natural `s`-dimensional measure of the system: the self-similar probability
measure carried by the attractor, with weights `p_i = r_i^s`. -/
structure IsNatural (K : Set ℝ) (s : ℝ) (μ : Measure ℝ) : Prop where
  /-- It is a probability measure. -/
  isProbability : IsProbabilityMeasure μ
  /-- `K` is an attractor of the system. -/
  attractor : S.IsAttractor K
  /-- The measure is carried by the attractor. -/
  support : μ Kᶜ = 0
  /-- Hutchinson's identity with weights `p_i = r_i^s`. -/
  selfSimilar : μ = ∑ i, ENNReal.ofReal (S.ratio i ^ s) • μ.map (S.map i)

end System

/-! ## The middle-thirds system -/

/-- The similarity dimension `log 2 / log 3` of the middle-thirds Cantor set. -/
noncomputable def sCantor : ℝ := Real.log 2 / Real.log 3

/-- The middle-thirds system `S_0(x) = x/3`, `S_1(x) = x/3 + 2/3`. -/
noncomputable def cantorSystem : System (Fin 2) where
  ratio _ := 1/3
  shift i := if i = 0 then 0 else 2/3
  ratio_pos _ := by norm_num
  ratio_lt_one _ := by norm_num
  mapsTo i x hx := by
    obtain ⟨h0, h1⟩ := hx
    have hb : 0 ≤ (if i = 0 then (0:ℝ) else 2/3) ∧ (if i = 0 then (0:ℝ) else 2/3) ≤ 2/3 := by
      by_cases h : i = 0
      · rw [if_pos h]; constructor <;> norm_num
      · rw [if_neg h]; constructor <;> norm_num
    constructor
    · show (0:ℝ) ≤ 1/3 * x + (if i = 0 then (0:ℝ) else 2/3)
      linarith [hb.1]
    · show 1/3 * x + (if i = 0 then (0:ℝ) else 2/3) ≤ 1
      linarith [hb.2]

/-! ## The homometric digit sets -/

/-- The reflection `σ̃`, the image of `σ` under `x ↦ -x`. -/
noncomputable def reflect (σ : Measure ℝ) : Measure ℝ := σ.map (fun x : ℝ => -x)

/-- The digits of `𝒜`, enumerated. -/
def digitFunA : Fin 6 → ℤ := ![0, 1, 4, 10, 12, 17]

/-- The digits of `ℬ`, enumerated. -/
def digitFunB : Fin 6 → ℤ := ![0, 1, 8, 11, 13, 17]

/-- The common similarity dimension `log 6 / log 30` of the two digit systems. -/
noncomputable def tHom : ℝ := Real.log 6 / Real.log 30

/-- The system of six similarities `u ↦ u/30 + d_i/18` attached to a digit function. -/
noncomputable def homSystem (d : Fin 6 → ℤ) (h0 : ∀ i, 0 ≤ d i) (h17 : ∀ i, d i ≤ 17) :
    System (Fin 6) where
  ratio _ := 1/30
  shift i := (d i : ℝ) / 18
  ratio_pos _ := by norm_num
  ratio_lt_one _ := by norm_num
  mapsTo i x hx := by
    obtain ⟨hx0, hx1⟩ := hx
    have hd0 : (0:ℝ) ≤ (d i : ℝ) := by exact_mod_cast h0 i
    have hd17 : (d i : ℝ) ≤ 17 := by exact_mod_cast h17 i
    constructor
    · show (0:ℝ) ≤ 1/30 * x + (d i : ℝ)/18
      linarith
    · show 1/30 * x + (d i : ℝ)/18 ≤ 1
      linarith

/-! ## The audited statements -/

/-- **Hutchinson's theorem**: a self-similar system whose ratios solve `∑ r_i^s = 1`
has exactly one attractor carrying exactly one natural `s`-dimensional measure. -/
theorem audit_hutchinson {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    {s : ℝ} (hdim : S.IsDimension s) :
    ∃! p : Set ℝ × Measure ℝ, S.IsNatural p.1 s p.2 := sorry

/-- **Uniqueness of a self-similar probability measure on `[0,1]`**: two probability
measures carried by the unit interval satisfying Hutchinson's identity for the same
system and the same weights are equal. -/
theorem audit_self_similar_unique {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)
    {s : ℝ} (hdim : S.IsDimension s) {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ = ∑ i, ENNReal.ofReal (S.ratio i ^ s) • μ.map (S.map i))
    (hν : ν = ∑ i, ENNReal.ofReal (S.ratio i ^ s) • ν.map (S.map i))
    (hμs : μ (Set.Icc (0:ℝ) 1)ᶜ = 0) (hνs : ν (Set.Icc (0:ℝ) 1)ᶜ = 0) :
    μ = ν := sorry

/-- **Ahlfors regularity**: the natural measure of a strongly separated system is
Ahlfors regular of the similarity dimension. -/
theorem audit_ahlfors {ι : Type*} [Fintype ι] (S : System ι) {K : Set ℝ} {ρ s : ℝ}
    (hs : 0 < s) (hsep : S.StronglySeparated K ρ) (hdim : S.IsDimension s)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    ∃ A : ℝ, IsAhlforsClosed s A μ := sorry

/-- **The Frostman bound**: the natural measure of a strongly separated system
satisfies `μ(B̄(x,ρ)) ≤ A ρ^s` at every centre, not only in the support. -/
theorem audit_frostman {ι : Type*} [Fintype ι] (S : System ι) {K : Set ℝ} {ρ s : ℝ}
    (hs : 0 < s) (hsep : S.StronglySeparated K ρ)
    {μ : Measure ℝ} (hμ : S.IsNatural K s μ) :
    ∃ A : ℝ, IsFrostman s A μ := sorry

/-- **The middle-thirds Cantor measure**: the middle-thirds attractor and its natural
measure of dimension `log 2 / log 3` exist and are unique. -/
theorem audit_cantor_measure :
    ∃! p : Set ℝ × Measure ℝ, cantorSystem.IsNatural p.1 sCantor p.2 := sorry

/-- **The homometric example**: two distinct strongly separated self-similar measures,
Ahlfors regular of the same dimension `t = log 6 / log 30 ∈ (1/2,1)`, with equal signed
convolutions `σ * σ̃` and hence identical pair-distance distributions. -/
theorem audit_homometric :
    ∃ (KA KB : Set ℝ) (σA σB : Measure ℝ) (A : ℝ),
      (homSystem digitFunA (by decide) (by decide)).IsNatural KA tHom σA ∧
      (homSystem digitFunB (by decide) (by decide)).IsNatural KB tHom σB ∧
      σA ≠ σB ∧
      (homSystem digitFunA (by decide) (by decide)).StronglySeparated KA (1/45) ∧
      (homSystem digitFunB (by decide) (by decide)).StronglySeparated KB (1/45) ∧
      tHom ∈ Set.Ioo (1/2 : ℝ) 1 ∧
      IsAhlfors tHom A σA ∧ IsAhlfors tHom A σB ∧
      σA.conv (reflect σA) = σB.conv (reflect σB) ∧
      (∀ δ : ℝ, Phi σA δ = Phi σB δ) := sorry

end Challenge
