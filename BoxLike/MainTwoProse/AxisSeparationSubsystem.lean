module

/-
Exponential separation of the systems a finite diagonal subsystem induces on the coordinate
axes, from the projective exponential separation condition of the ambient system: the passage
"A composition of `k` subsystem maps acts on either coordinate axis by a map `g_𝐢` with
`|𝐢| = kn`. Distinct compositions give distinct words, and on a given axis the derivatives are
equal. Given `m ≥ n` with `Δ_m^Ψ ≥ c^m`, put `k = ⌊m/n⌋`, so that `kn ≤ m < 2kn`. By the
monotonicity of `(Δ_j^Ψ)_{j ∈ ℕ}` established in `sec:exponential_separation`, any two such
words `𝐢 ≠ 𝐣` satisfy `|g_𝐢(0) - g_𝐣(0)| ≥ Δ_{kn}^Ψ ≥ Δ_m^Ψ ≥ c^m ≥ (c^{2n})^k`. Hence, both
induced systems are exponentially separated" of the proof of `thm:main2` in
`sec:dimension_result_proof`.

* `System.gDeriv_eq_gWord_sub`: `g_𝐣' = g_𝐣(1) - g_𝐣(0)`.
* `System.subsystem_codeWord_gDeriv`: the derivative along a word of the subsystem is the
  derivative along the concatenated word of `Ψ`.
* `System.gap_mul_le_axisGap_subsystem`: `Δ_{nk}^Ψ ≤ Δ_k` for the system the subsystem induces
  on either axis.
* `System.subsystem_axisExpSeparation`: the systems the subsystem induces on both axes are
  exponentially separated, with the constant `c^{2n}`.
-/
public import BoxLike.AxisSeparation
public import BoxLike.SecondIterate
public import BoxLike.Subsystem

@[expose] public section

namespace BoxLike

open Filter
open scoped ENNReal

namespace System

variable {ι κ : Type*} (S : System ι)

/-- `g_𝐣' = g_𝐣(1) - g_𝐣(0)`, since `g_𝐣` is affine with slope `g_𝐣'`. -/
theorem gDeriv_eq_gWord_sub (u : List (ι × ZMod 2)) :
    S.gDeriv u = S.gWord u 1 - S.gWord u 0 := by
  rw [S.gWord_apply u 1]
  ring

variable {w : κ → List ι} {hw : ∀ k, w k ≠ []}

/-- The derivative of the coordinate map of the subsystem along the path of its `Σ_Z` over a
word `u` starting on the axis `c` is the derivative of `g` along the path of `Σ_Z` over the
concatenated word. -/
theorem subsystem_codeWord_gDeriv (c : ZMod 2) (u : List κ) :
    (S.subsystem w hw).gDeriv ((S.subsystem w hw).codeWord c u) =
      S.gDeriv (S.codeWord c (flatWords w u)) := by
  rw [gDeriv_eq_gWord_sub, gDeriv_eq_gWord_sub, subsystem_codeWord_gWord]

/-- `Δ_{nk}^Ψ ≤ Δ_k` for the system a subsystem of distinct diagonal words of a common length
`n > 0` induces on the axis `c` (proof of `thm:main2`): a composition of `k` subsystem maps
acts on the axis `c` by `g_𝐢` for the concatenated word `𝐢` of length `kn` in `Ψ`, distinct
`k`-sequences give distinct words, and the derivatives agree on a given axis. -/
theorem gap_mul_le_axisGap_subsystem (hdiag : ∀ k, S.oWord (w k) = 0) {n : ℕ} (hn : 0 < n)
    (hlen : ∀ k, (w k).length = n) (hinj : Function.Injective w) (c : ZMod 2) (k : ℕ) :
    S.gap (n * k) ≤ (S.subsystem w hw).axisGap c k := by
  have ho : ∀ k, (S.subsystem w hw).o k = 0 := fun k => by rw [subsystem_o]; exact hdiag k
  refine le_iInf fun u => le_iInf fun u' => le_iInf fun hu => le_iInf fun hu' =>
    le_iInf fun hne => le_iInf fun hd => ?_
  rw [← (S.subsystem w hw).codeWord_eq_axisWord ho, ← (S.subsystem w hw).codeWord_eq_axisWord ho]
    at hd ⊢
  rw [subsystem_codeWord_gWord, subsystem_codeWord_gWord]
  rw [subsystem_codeWord_gDeriv, subsystem_codeWord_gDeriv] at hd
  refine S.gap_le ?_ ?_ ?_ hd
  · rw [length_codeWord, length_flatWords hlen, hu]
  · rw [length_codeWord, length_flatWords hlen, hu']
  · intro h
    exact hne (flatWords_injective hn hlen hinj (S.codeWord_injective c h))

/-- The systems a subsystem of distinct diagonal words of a common length `n > 0` induces on
the two coordinate axes are exponentially separated when `Φ` satisfies the projective
exponential separation condition (proof of `thm:main2`): with `0 < c ≤ 1` and `Δ_m^Ψ ≥ c^m` for
infinitely many `m`, the gap of the induced system at `k = ⌊m/n⌋` is at least
`Δ_{kn}^Ψ ≥ Δ_m^Ψ ≥ c^m ≥ (c^{2n})^k`, since `kn ≤ m < 2kn` and the projective gap is
non-increasing. -/
theorem subsystem_axisExpSeparation [Nonempty ι] (hsep : S.ProjExpSeparation)
    (hdiag : ∀ k, S.oWord (w k) = 0) {n : ℕ} (hn : 0 < n) (hlen : ∀ k, (w k).length = n)
    (hinj : Function.Injective w) (c : ZMod 2) : (S.subsystem w hw).AxisExpSeparation c := by
  obtain ⟨c₀, hc₀, hfreq⟩ := S.projExpSeparation_iff_frequently.1 hsep
  -- The constant may be taken at most one.
  set r : ℝ := min c₀ 1 with hr_def
  have hr : 0 < r := lt_min hc₀ one_pos
  have hr1 : r ≤ 1 := min_le_right _ _
  have hfreq' : ∃ᶠ m : ℕ in atTop, ENNReal.ofReal (r ^ m) ≤ S.gap m :=
    hfreq.mono fun m hm =>
      (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hr.le (min_le_left _ _) m)).trans hm
  refine (S.subsystem w hw).axisExpSeparation_of_frequently (pow_pos hr (2 * n))
    (frequently_atTop.2 fun N => ?_)
  obtain ⟨m, hmN, hm⟩ := frequently_atTop.1 hfreq' (n * (N + 1))
  have hNm : N * n ≤ m := by
    rw [mul_comm]
    exact (Nat.mul_le_mul_left n (Nat.le_succ N)).trans hmN
  have hnm : n ≤ m := (Nat.le_mul_of_pos_right n (Nat.succ_pos N)).trans hmN
  refine ⟨m / n, (Nat.le_div_iff_mul_le hn).2 hNm, ?_⟩
  have hk1 : 1 ≤ m / n := (Nat.le_div_iff_mul_le hn).2 (by rwa [one_mul])
  have hkm : n * (m / n) ≤ m := Nat.mul_div_le m n
  have hmk : m ≤ 2 * n * (m / n) := by
    have h1 := Nat.lt_mul_div_succ m hn
    have h2 : n * 1 ≤ n * (m / n) := Nat.mul_le_mul_left n hk1
    nlinarith
  calc ENNReal.ofReal ((r ^ (2 * n)) ^ (m / n))
      = ENNReal.ofReal (r ^ (2 * n * (m / n))) := by rw [← pow_mul]
    _ ≤ ENNReal.ofReal (r ^ m) :=
        ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hr.le hr1 hmk)
    _ ≤ S.gap m := hm
    _ ≤ S.gap (n * (m / n)) := S.gap_anti hkm
    _ ≤ (S.subsystem w hw).axisGap c (m / n) :=
        S.gap_mul_le_axisGap_subsystem hdiag hn hlen hinj c _

end System

end BoxLike
