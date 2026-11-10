module

/-
The projective exponential separation condition implies that the projective system has no
exact overlaps: the paragraph of `sec:exponential_separation` after the definition of the
condition (tex lines 1298 to 1304). The argument: appending a symbol preserves the translation
difference of two words with equal derivatives, so `Δ_{n+1}^Ψ ≤ Δ_n^Ψ` (`System.gap_succ_le`);
if `g_𝐢 = g_𝐣` for distinct words `𝐢`, `𝐣` of any lengths, neither is a prefix of the other,
since `g_𝐢 ∘ g_𝐤 = g_𝐢` for a non-empty `𝐤` would make the contraction `g_𝐤` the identity; so
`𝐢𝐣 ≠ 𝐣𝐢` are distinct words of the common length `m = |𝐢| + |𝐣|` with `g_{𝐢𝐣} = g_{𝐣𝐢}`,
which gives `Δ_m^Ψ = 0` and hence `Δ_n^Ψ = 0` for all `n ≥ m`.

* `System.gWord_injective`: `g_𝐢` is injective.
* `System.gWord_ne_id`: `g_𝐤` is not the identity for a non-empty word `𝐤`.
* `System.not_prefix_of_gWord_eq`, `System.append_ne_append_of_gWord_eq`: distinct words with
  the same map are not prefixes of each other, and `𝐢𝐣 ≠ 𝐣𝐢`.
* `System.gap_eq_zero_of_gWord_eq`: `Δ_{|𝐢| + |𝐣|}^Ψ = 0` when `g_𝐢 = g_𝐣` for distinct words.
* `System.ProjExpSeparation.noExactOverlaps`: the statement.
-/
public import BoxLike.SecondIterate

@[expose] public section

namespace BoxLike

open scoped ENNReal

namespace System

variable {ι : Type*} (S : System ι)

/-- `g_𝐢` is injective: it is affine with the non-zero slope `g_𝐢'`
(`sec:exponential_separation`, tex line 1301). -/
theorem gWord_injective (u : List (ι × ZMod 2)) : Function.Injective (S.gWord u) := by
  intro t t' h
  rw [S.gWord_apply u t, S.gWord_apply u t'] at h
  exact mul_left_cancel₀ (S.gDeriv_ne_zero u) (add_right_cancel h)

/-- `g_𝐤` is not the identity for a non-empty word `𝐤`, since `g_𝐤` is a contraction
(`sec:exponential_separation`, tex lines 1301 to 1302): `|g_𝐤'| < 1`. -/
theorem gWord_ne_id {u : List (ι × ZMod 2)} (hu : u ≠ []) : S.gWord u ≠ id := by
  intro h
  have h0 : S.gWord u 0 = 0 := by rw [h]; rfl
  have h1 : S.gDeriv u = 1 := by
    have h1 := congrFun h 1
    rw [S.gWord_apply, h0, add_zero, mul_one] at h1
    exact h1
  have hle : ∀ v : List (ι × ZMod 2), |S.gDeriv v| ≤ 1 := fun v => by
    induction v with
    | nil => simp
    | cons p v ih =>
      rw [gDeriv_cons, abs_mul]
      calc |S.ratio p| * |S.gDeriv v| ≤ 1 * 1 :=
            mul_le_mul (S.abs_ratio_lt_one p).le ih (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
  obtain ⟨p, v, rfl⟩ := List.exists_cons_of_ne_nil hu
  rw [gDeriv_cons] at h1
  have h2 := congrArg abs h1
  rw [abs_mul, abs_one] at h2
  have hp := S.abs_ratio_lt_one p
  have hv := hle v
  nlinarith [abs_nonneg (S.ratio p), abs_nonneg (S.gDeriv v)]

/-- If `g_𝐢 = g_𝐣` for distinct words `𝐢 ≠ 𝐣`, then `𝐢` is not a prefix of `𝐣`: `𝐣 = 𝐢𝐤` with
`𝐤 ≠ ∅` would give `g_𝐢 ∘ g_𝐤 = g_𝐢`, hence `g_𝐤 = id` by the injectivity of `g_𝐢`
(`sec:exponential_separation`, tex lines 1300 to 1302). -/
theorem not_prefix_of_gWord_eq {u u' : List (ι × ZMod 2)} (hne : u ≠ u')
    (h : S.gWord u = S.gWord u') : ¬ u <+: u' := by
  rintro ⟨k, rfl⟩
  rw [gWord_append] at h
  have hk : S.gWord k = id := funext fun t => S.gWord_injective u (congrFun h t).symm
  exact S.gWord_ne_id (fun hk0 => hne (by rw [hk0, List.append_nil])) hk

/-- If `g_𝐢 = g_𝐣` for distinct words `𝐢 ≠ 𝐣`, then `𝐢𝐣 ≠ 𝐣𝐢`: the words `𝐢𝐣` and `𝐣𝐢` have
the common length `|𝐢| + |𝐣|`, and if they were equal the shorter of `𝐢`, `𝐣` would be a prefix
of the longer (`sec:exponential_separation`, tex lines 1302 to 1303). -/
theorem append_ne_append_of_gWord_eq {u u' : List (ι × ZMod 2)} (hne : u ≠ u')
    (h : S.gWord u = S.gWord u') : u ++ u' ≠ u' ++ u := by
  intro heq
  rcases le_total u.length u'.length with hle | hle
  · exact S.not_prefix_of_gWord_eq hne h
      (List.prefix_of_prefix_length_le (heq ▸ List.prefix_append u u') (List.prefix_append u' u)
        hle)
  · exact S.not_prefix_of_gWord_eq hne.symm h.symm
      (List.prefix_of_prefix_length_le (heq.symm ▸ List.prefix_append u' u)
        (List.prefix_append u u') hle)

/-- If `g_𝐢 = g_𝐣` for distinct words `𝐢 ≠ 𝐣`, then `Δ_m^Ψ = 0` for `m = |𝐢| + |𝐣|`: the
distinct words `𝐢𝐣` and `𝐣𝐢` of length `m` have equal derivatives and
`g_{𝐢𝐣} = g_𝐢 ∘ g_𝐣 = g_𝐣 ∘ g_𝐢 = g_{𝐣𝐢}` (`sec:exponential_separation`, tex line 1303). -/
theorem gap_eq_zero_of_gWord_eq {u u' : List (ι × ZMod 2)} (hne : u ≠ u')
    (h : S.gWord u = S.gWord u') : S.gap (u.length + u'.length) = 0 := by
  refine le_antisymm ?_ bot_le
  have hle := S.gap_le (n := u.length + u'.length) (u := u ++ u') (u' := u' ++ u) (by simp)
    (by simp [add_comm]) (S.append_ne_append_of_gWord_eq hne h)
    (by rw [gDeriv_append, gDeriv_append, mul_comm])
  rwa [gWord_append, gWord_append, Function.comp_apply, Function.comp_apply, h, sub_self,
    abs_zero, ENNReal.ofReal_zero] at hle

/-- The projective exponential separation condition implies that the projective system has no
exact overlaps (`sec:exponential_separation`, tex lines 1298 to 1304): if `g_𝐢 = g_𝐣` for
distinct words, then `Δ_m^Ψ = 0` for `m = |𝐢| + |𝐣|`, the gap is non-increasing, so
`Δ_n^Ψ = 0` for all `n ≥ m`, and no `c > 0` satisfies `Δ_{n_k}^Ψ ≥ c^{n_k}` along a strictly
increasing sequence. -/
theorem ProjExpSeparation.noExactOverlaps (h : S.ProjExpSeparation) : S.NoExactOverlaps := by
  intro u u' hne hg
  obtain ⟨c, hc, n, hn, hsep⟩ := h
  have hι : Nonempty ι := by
    rcases u with _ | ⟨p, u⟩
    · rcases u' with _ | ⟨q, u'⟩
      · exact absurd rfl hne
      · exact ⟨q.1⟩
    · exact ⟨p.1⟩
  have hm : S.gap (u.length + u'.length) = 0 := S.gap_eq_zero_of_gWord_eq hne hg
  have h1 := hsep (u.length + u'.length)
  have h2 : S.gap (n (u.length + u'.length)) ≤ S.gap (u.length + u'.length) :=
    S.gap_anti (hn.id_le _)
  rw [hm, nonpos_iff_eq_zero] at h2
  rw [h2] at h1
  exact (ENNReal.ofReal_pos.2 (pow_pos hc _)).not_ge h1

end System

end BoxLike
