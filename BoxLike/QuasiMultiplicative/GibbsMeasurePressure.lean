module

/-
The partition sums of the potential `𝐢 ↦ ‖A_𝐢‖^q` of a quasi-multiplicative tuple, the first
step of the proof of the existence half of Feng–Käenmäki, Proposition 1.2 (`thm:irred_eq_state`,
tex lines 2113 to 2127), after Feng–Käenmäki, *Equilibrium states of the pressure function for
products of matrices*, Discrete Contin. Dyn. Syst. 30 (2011), and Bowen's construction.
Write `ψ(𝐢) = ‖A_𝐢‖^q`, `Z_n = ∑_{|𝐢| = n} ψ(𝐢)` and `P = P(q)`. The potential is
sub-multiplicative, so `e^{nP} ≤ Z_n` by Fekete's lemma. Quasi-multiplicativity with gaps of
length at most `m` joins two words `𝐢`, `𝐣` to a word `𝐢𝐤𝐣` with `ψ(𝐢𝐤𝐣) ≥ c ψ(𝐢) ψ(𝐣)`; the
word `𝐢𝐤𝐣` determines `𝐢` and `𝐣` once the length of `𝐤` is known, so
`c Z_a Z_b ≤ ∑_{t ≤ m} Z_{a+b+t} ≤ (∑_{t ≤ m} Z_t) Z_{a+b}`, and Fekete's lemma for the
super-multiplicative sequence `Z_n / K` gives `Z_n ≤ K e^{nP}`. Padding the gap with a fixed
letter to the length `m` costs at most the factor `δ^{mq}`, where `δ^{|𝐢|} ‖M‖ ≤ ‖M A_𝐢‖`; this
gives the lower bound for the sums of `ψ(𝐱𝐮𝐲)` over the words `𝐱`, `𝐲` of fixed lengths.

* `MatrixTuple.wordsOfLength`, `MatrixTuple.mem_wordsOfLength`,
  `MatrixTuple.sum_wordsOfLength`: the finite set of the words of length `n`.
* `MatrixTuple.sum_comp_le_sum_range`: a map that is injective on the classes of a function
  with values in `{0, …, m}` has sums bounded by the sum over the `m + 1` target sets.
* `MatrixTuple.normLowerBound_le_one`, `MatrixTuple.pow_mul_norm_le_norm_mul_word`,
  `MatrixTuple.pow_mul_norm_le_norm_word_mul`: `δ ≤ 1` and `δ^{|𝐢|} ‖M‖ ≤ ‖M A_𝐢‖, ‖A_𝐢 M‖`.
* `MatrixTuple.NormQMConstants`, `MatrixTuple.NormQuasiMultiplicative.exists_normQMConstants`:
  quasi-multiplicativity for the potential `‖·‖^q`, with explicit constants.
* `MatrixTuple.normSum_zero`, `MatrixTuple.normSum_pos`, `MatrixTuple.normSum_add_le`:
  `Z_0 = 1`, `Z_n > 0` and `Z_{a+b} ≤ Z_a Z_b`.
* `MatrixTuple.exp_mul_normPressure_le_normSum`: `e^{nP} ≤ Z_n`.
* `MatrixTuple.NormQMConstants.mul_normSum_mul_le`,
  `MatrixTuple.NormQMConstants.exists_normSum_le`: `c Z_a Z_b ≤ (∑_{t ≤ m} Z_t) Z_{a+b}` and
  `Z_n ≤ K e^{nP}` with `K ≥ 1`.
* `MatrixTuple.sum_triple_le`: `∑_{𝐱, 𝐲} ψ(𝐱𝐮𝐲) ≤ Z_k ψ(𝐮) Z_l`.
* `MatrixTuple.padConst`, `MatrixTuple.NormQMConstants.le_sum_append_right`,
  `MatrixTuple.NormQMConstants.le_sum_append_left`, `MatrixTuple.NormQMConstants.le_sum_triple`:
  `κ² Z_a ψ(𝐮) Z_b ≤ ∑_{|𝐱| = m + a, |𝐲| = m + b} ψ(𝐱𝐮𝐲)`.
-/
public import BoxLike.Bowen.PartitionBounds
public import BoxLike.QuasiMultiplicative.Defs

@[expose] public section

namespace BoxLike

open Filter Topology
open scoped Matrix.Norms.L2Operator

namespace MatrixTuple

/-! ### Words of a given length -/

section Words

variable (ι : Type*) [Fintype ι]

/-- The finite set of the words of length `n`, the index set of the sums `Z_n` in the proof of
Feng–Käenmäki, Proposition 1.2 (`thm:irred_eq_state`, tex lines 2113 to 2122). -/
noncomputable def wordsOfLength (n : ℕ) : Finset (List ι) :=
  Finset.univ.map ⟨fun w : Fin n → ι => List.ofFn w, List.ofFn_injective⟩

variable {ι}

/-- The members of `wordsOfLength ι n` are the words of length `n`. -/
theorem mem_wordsOfLength {n : ℕ} {L : List ι} : L ∈ wordsOfLength ι n ↔ L.length = n := by
  constructor
  · intro h
    obtain ⟨w, -, rfl⟩ := Finset.mem_map.1 h
    exact List.length_ofFn
  · intro h
    subst h
    exact Finset.mem_map.2 ⟨fun i : Fin L.length => L[(i : ℕ)], Finset.mem_univ _,
      List.ofFn_getElem⟩

/-- A sum over the words of length `n` is the sum over `Fin n → ι`. -/
theorem sum_wordsOfLength {M : Type*} [AddCommMonoid M] (n : ℕ) (G : List ι → M) :
    ∑ L ∈ wordsOfLength ι n, G L = ∑ w : Fin n → ι, G (List.ofFn w) :=
  Finset.sum_map _ _ _

end Words

/-- The counting step of Feng–Käenmäki, Proposition 1.2 (`thm:irred_eq_state`, tex lines 2113 to
2234): if `φ` maps `a ∈ S` into `T (j a)` with `j a ≤ m`, and `φ` is injective on each class of
`j`, then `∑_{a ∈ S} F(φ a) ≤ ∑_{t ≤ m} ∑_{b ∈ T t} F(b)` for `F ≥ 0`. -/
theorem sum_comp_le_sum_range {α β : Type*} (S : Finset α) (φ : α → β) (j : α → ℕ) (m : ℕ)
    (T : ℕ → Finset β) {F : β → ℝ} (hF : ∀ b, 0 ≤ F b) (hj : ∀ a ∈ S, j a ≤ m)
    (hT : ∀ a ∈ S, φ a ∈ T (j a))
    (hinj : ∀ a ∈ S, ∀ a' ∈ S, j a = j a' → φ a = φ a' → a = a') :
    ∑ a ∈ S, F (φ a) ≤ ∑ t ∈ Finset.range (m + 1), ∑ b ∈ T t, F b := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := j) (t := Finset.range (m + 1))
    (fun a ha => Finset.mem_range.2 (Nat.lt_succ_of_le (hj a ha)))]
  refine Finset.sum_le_sum fun t _ => ?_
  have hinj' : Set.InjOn φ ↑(S.filter fun a => j a = t) := by
    intro a ha a' ha' h
    have ha1 := Finset.mem_filter.1 (Finset.mem_coe.1 ha)
    have ha2 := Finset.mem_filter.1 (Finset.mem_coe.1 ha')
    exact hinj a ha1.1 a' ha2.1 (ha1.2.trans ha2.2.symm) h
  rw [← Finset.sum_image hinj']
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun b _ _ => hF b
  intro b hb
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
  have ha' := Finset.mem_filter.1 ha
  rw [← ha'.2]
  exact hT a ha'.1

/-! ### Products with a padding word -/

section Padding

variable {ι : Type*} {A : ι → Matrix (Fin 2) (Fin 2) ℝ}

/-- `δ ≤ 1` for the constant `δ = (1 + ∑_i ‖A_i⁻¹‖)⁻¹` of `normLowerBound`. -/
theorem normLowerBound_le_one [Fintype ι] : normLowerBound A ≤ 1 := by
  have h : 0 ≤ ∑ i, ‖(A i)⁻¹‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  exact inv_le_one_of_one_le₀ (by linarith)

/-- `δ ‖M‖ ≤ ‖M A_i‖`: `‖M‖ = ‖M A_i A_i⁻¹‖ ≤ ‖M A_i‖ ‖A_i⁻¹‖` and `δ ‖A_i⁻¹‖ ≤ 1`. -/
theorem normLowerBound_mul_norm_le_norm_mul_right [Fintype ι] (hA : ∀ i, (A i).det ≠ 0)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (i : ι) : normLowerBound A * ‖M‖ ≤ ‖M * A i‖ := by
  have hinv : A i * (A i)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hA i))
  have hle : ‖M‖ ≤ ‖M * A i‖ * ‖(A i)⁻¹‖ := by
    calc ‖M‖ = ‖M * A i * (A i)⁻¹‖ := by rw [mul_assoc, hinv, mul_one]
      _ ≤ ‖M * A i‖ * ‖(A i)⁻¹‖ := Matrix.l2_opNorm_mul _ _
  have hδ := normLowerBound_pos (A := A)
  calc normLowerBound A * ‖M‖ ≤ normLowerBound A * (‖M * A i‖ * ‖(A i)⁻¹‖) :=
        mul_le_mul_of_nonneg_left hle hδ.le
    _ = (normLowerBound A * ‖(A i)⁻¹‖) * ‖M * A i‖ := by ring
    _ ≤ 1 * ‖M * A i‖ := mul_le_mul_of_nonneg_right (normLowerBound_mul_le i) (norm_nonneg _)
    _ = ‖M * A i‖ := one_mul _

/-- `δ ‖M‖ ≤ ‖A_i M‖`: `‖M‖ = ‖A_i⁻¹ A_i M‖ ≤ ‖A_i⁻¹‖ ‖A_i M‖` and `δ ‖A_i⁻¹‖ ≤ 1`. -/
theorem normLowerBound_mul_norm_le_norm_mul_left [Fintype ι] (hA : ∀ i, (A i).det ≠ 0)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (i : ι) : normLowerBound A * ‖M‖ ≤ ‖A i * M‖ := by
  have hinv : (A i)⁻¹ * A i = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hA i))
  have hle : ‖M‖ ≤ ‖(A i)⁻¹‖ * ‖A i * M‖ := by
    calc ‖M‖ = ‖(A i)⁻¹ * (A i * M)‖ := by rw [← mul_assoc, hinv, one_mul]
      _ ≤ ‖(A i)⁻¹‖ * ‖A i * M‖ := Matrix.l2_opNorm_mul _ _
  have hδ := normLowerBound_pos (A := A)
  calc normLowerBound A * ‖M‖ ≤ normLowerBound A * (‖(A i)⁻¹‖ * ‖A i * M‖) :=
        mul_le_mul_of_nonneg_left hle hδ.le
    _ = (normLowerBound A * ‖(A i)⁻¹‖) * ‖A i * M‖ := by ring
    _ ≤ 1 * ‖A i * M‖ := mul_le_mul_of_nonneg_right (normLowerBound_mul_le i) (norm_nonneg _)
    _ = ‖A i * M‖ := one_mul _

/-- `δ^{|𝐢|} ‖M‖ ≤ ‖M A_𝐢‖`: multiplying by a padding word on the right costs at most the factor
`δ^{|𝐢|}` (the padding step of Feng–Käenmäki, Proposition 1.2, `thm:irred_eq_state`). -/
theorem pow_mul_norm_le_norm_mul_word [Fintype ι] (hA : ∀ i, (A i).det ≠ 0)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (w : List ι) :
    normLowerBound A ^ w.length * ‖M‖ ≤ ‖M * word A w‖ := by
  induction w generalizing M with
  | nil => simp
  | cons i w ih =>
    rw [word_cons, ← mul_assoc, List.length_cons, pow_succ, mul_assoc]
    exact (mul_le_mul_of_nonneg_left (normLowerBound_mul_norm_le_norm_mul_right hA M i)
      (pow_nonneg normLowerBound_pos.le _)).trans (ih (M * A i))

/-- `δ^{|𝐢|} ‖M‖ ≤ ‖A_𝐢 M‖`: multiplying by a padding word on the left costs at most the factor
`δ^{|𝐢|}` (the padding step of Feng–Käenmäki, Proposition 1.2, `thm:irred_eq_state`). -/
theorem pow_mul_norm_le_norm_word_mul [Fintype ι] (hA : ∀ i, (A i).det ≠ 0)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (w : List ι) :
    normLowerBound A ^ w.length * ‖M‖ ≤ ‖word A w * M‖ := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [word_cons, mul_assoc, List.length_cons, pow_succ', mul_assoc]
    exact (mul_le_mul_of_nonneg_left ih normLowerBound_pos.le).trans
      (normLowerBound_mul_norm_le_norm_mul_left hA _ i)

end Padding

/-! ### Quasi-multiplicativity of the potential `‖·‖^q` -/

section QuasiMultiplicative

variable {ι : Type*} (A : ι → Matrix (Fin 2) (Fin 2) ℝ)

/-- Quasi-multiplicativity of the potential `ψ = ‖·‖^q` with the constants `m` and `c > 0`: any
two words `𝐮`, `𝐯` are joined by a word `𝐤` of length at most `m` with
`c ψ(𝐮) ψ(𝐯) ≤ ψ(𝐮𝐤𝐯)` (Feng–Käenmäki, Proposition 1.2, `thm:irred_eq_state`). -/
def NormQMConstants (q : ℝ) (m : ℕ) (c : ℝ) : Prop :=
  0 < c ∧ ∀ u v : List ι, ∃ k : List ι, k.length ≤ m ∧
    c * (‖word A u‖ ^ q * ‖word A v‖ ^ q) ≤ ‖word A (u ++ k ++ v)‖ ^ q

variable {A}

/-- A quasi-multiplicative norm gives quasi-multiplicativity of `‖·‖^q` for every `q ≥ 0`, with
the constant `c^q` (Feng–Käenmäki, Proposition 1.2, `thm:irred_eq_state`). -/
theorem NormQuasiMultiplicative.exists_normQMConstants (h : NormQuasiMultiplicative A) {q : ℝ}
    (hq : 0 ≤ q) : ∃ m : ℕ, ∃ c : ℝ, NormQMConstants A q m c := by
  obtain ⟨m, c, hc, h⟩ := h
  refine ⟨m, c ^ q, Real.rpow_pos_of_pos hc q, fun u v => ?_⟩
  obtain ⟨k, hk, hle⟩ := h u v
  refine ⟨k, hk, ?_⟩
  rw [← Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
    ← Real.mul_rpow hc.le (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact Real.rpow_le_rpow (mul_nonneg hc.le (mul_nonneg (norm_nonneg _) (norm_nonneg _))) hle hq

end QuasiMultiplicative

/-! ### The partition sums -/

section Partition

variable {ι : Type*} [Fintype ι] {A : ι → Matrix (Fin 2) (Fin 2) ℝ} {q : ℝ}

variable (A q) in
/-- `Z_0 = ‖I‖^q = 1`. -/
theorem normSum_zero : normSum A q 0 = 1 := by
  simp [normSum]

/-- `Z_n > 0` for an invertible tuple over a non-empty alphabet. -/
theorem normSum_pos [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) (n : ℕ) : 0 < normSum A q n :=
  Finset.sum_pos (fun _ _ => Real.rpow_pos_of_pos (norm_word_pos hA _) _) Finset.univ_nonempty

omit [Fintype ι] in
/-- `ψ(𝐮𝐯) ≤ ψ(𝐮) ψ(𝐯)` for `ψ = ‖·‖^q`, `q ≥ 0`. -/
theorem rpow_norm_word_append_le (hq : 0 ≤ q) (u v : List ι) :
    ‖word A (u ++ v)‖ ^ q ≤ ‖word A u‖ ^ q * ‖word A v‖ ^ q := by
  rw [word_append, ← Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  exact Real.rpow_le_rpow (norm_nonneg _) (Matrix.l2_opNorm_mul _ _) hq

/-- Sub-multiplicativity of the partition sums: `Z_{a+b} ≤ Z_a Z_b`. -/
theorem normSum_add_le (hq : 0 ≤ q) (a b : ℕ) :
    normSum A q (a + b) ≤ normSum A q a * normSum A q b := by
  rw [normSum, sum_ofFn_add a b fun w => ‖word A w‖ ^ q, normSum, normSum, Finset.sum_mul_sum]
  exact Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun h _ =>
    rpow_norm_word_append_le hq _ _

/-- `e^{nP} ≤ Z_n` for all `n`, with `P = P(q)` the pressure of Feng–Käenmäki (1.1): the
sequence `-log Z_n` is super-additive with `-log Z_n / n → -P` (`thm:irred_eq_state`). -/
theorem exp_mul_normPressure_le_normSum [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) (hq : 0 ≤ q)
    (n : ℕ) : Real.exp (n * normPressure A q) ≤ normSum A q n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [normSum_zero]
  have hsup : ∀ a b : ℕ, 0 < a → 0 < b →
      -Real.log (normSum A q a) + -Real.log (normSum A q b) ≤ -Real.log (normSum A q (a + b)) := by
    intro a b _ _
    rw [← neg_add, neg_le_neg_iff, ← Real.log_mul (normSum_pos hA a).ne' (normSum_pos hA b).ne']
    exact Real.log_le_log (normSum_pos hA _) (normSum_add_le hq a b)
  have ht : Tendsto (fun k : ℕ => -Real.log (normSum A q k) / k) atTop
      (𝓝 (-normPressure A q)) := by
    simpa only [neg_div] using (tendsto_normPressure hA hq).neg
  have h := le_mul_of_superadditive hsup ht hn
  rw [← Real.exp_log (normSum_pos hA n)]
  exact Real.exp_le_exp.2 (by linarith)

/-- The quasi-multiplicative lower bound for products of partition sums:
`c Z_a Z_b ≤ ∑_{t ≤ m} Z_{a+b+t} ≤ (∑_{t ≤ m} Z_t) Z_{a+b}`. The word `𝐮𝐤𝐯` of length
`a + t + b` determines `𝐮` and `𝐯` once `t = |𝐤|` is known (`thm:irred_eq_state`). -/
theorem NormQMConstants.mul_normSum_mul_le {m : ℕ} {c : ℝ} (h : NormQMConstants A q m c)
    (hq : 0 ≤ q) (a b : ℕ) :
    c * (normSum A q a * normSum A q b) ≤
      (∑ t ∈ Finset.range (m + 1), normSum A q t) * normSum A q (a + b) := by
  choose g hg using h.2
  set S := wordsOfLength ι a ×ˢ wordsOfLength ι b with hS
  have hZ : normSum A q a * normSum A q b =
      ∑ p ∈ S, ‖word A p.1‖ ^ q * ‖word A p.2‖ ^ q := by
    rw [hS, Finset.sum_product, normSum, normSum,
      ← sum_wordsOfLength a fun L => ‖word A L‖ ^ q,
      ← sum_wordsOfLength b fun L => ‖word A L‖ ^ q, Finset.sum_mul_sum]
  have hcount := sum_comp_le_sum_range S (fun p => p.1 ++ g p.1 p.2 ++ p.2)
    (fun p => (g p.1 p.2).length) m (fun t => wordsOfLength ι (a + t + b))
    (F := fun L => ‖word A L‖ ^ q) (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    (fun p _ => (hg p.1 p.2).1)
    (fun p hp => by
      obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
      rw [mem_wordsOfLength] at h1 h2 ⊢
      simp only [List.length_append, h1, h2])
    (fun p hp p' hp' hj he => by
      obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
      obtain ⟨h1', h2'⟩ := Finset.mem_product.1 hp'
      rw [mem_wordsOfLength] at h1 h2 h1' h2'
      have e1 : p.1 = p'.1 := by
        have := congrArg (List.take a) he
        rwa [List.append_assoc, List.append_assoc, List.take_left' h1,
          List.take_left' h1'] at this
      have e2 : p.2 = p'.2 := by
        have := congrArg (List.drop (a + (g p.1 p.2).length)) he
        rwa [List.drop_left' (by simp [h1]), hj, List.drop_left' (by simp [h1'])] at this
      exact Prod.ext e1 e2)
  calc c * (normSum A q a * normSum A q b)
      = ∑ p ∈ S, c * (‖word A p.1‖ ^ q * ‖word A p.2‖ ^ q) := by rw [hZ, Finset.mul_sum]
    _ ≤ ∑ p ∈ S, ‖word A (p.1 ++ g p.1 p.2 ++ p.2)‖ ^ q :=
        Finset.sum_le_sum fun p _ => (hg p.1 p.2).2
    _ ≤ ∑ t ∈ Finset.range (m + 1), ∑ L ∈ wordsOfLength ι (a + t + b), ‖word A L‖ ^ q := hcount
    _ = ∑ t ∈ Finset.range (m + 1), normSum A q (a + b + t) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [sum_wordsOfLength, normSum, Nat.add_right_comm]
    _ ≤ ∑ t ∈ Finset.range (m + 1), normSum A q t * normSum A q (a + b) :=
        Finset.sum_le_sum fun t _ => (normSum_add_le hq _ _).trans_eq (mul_comm _ _)
    _ = (∑ t ∈ Finset.range (m + 1), normSum A q t) * normSum A q (a + b) := by
        rw [Finset.sum_mul]

/-- The upper bound `Z_n ≤ K e^{nP}` for all `n`, with a constant `K ≥ 1`, for a
quasi-multiplicative tuple (`thm:irred_eq_state`): with `K_1 = c⁻¹ ∑_{t ≤ m} Z_t` the sequence
`log (Z_n / K_1)` is super-additive and `log (Z_n / K_1) / n → P`. -/
theorem NormQMConstants.exists_normSum_le [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) {m : ℕ}
    {c : ℝ} (h : NormQMConstants A q m c) (hq : 0 ≤ q) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n : ℕ, normSum A q n ≤ K * Real.exp (n * normPressure A q) := by
  set K₁ := c⁻¹ * ∑ t ∈ Finset.range (m + 1), normSum A q t with hK₁def
  have hc := h.1
  have hK₁ : 0 < K₁ := mul_pos (inv_pos.2 hc)
    (Finset.sum_pos (fun t _ => normSum_pos hA t) Finset.nonempty_range_add_one)
  have hmul : ∀ a b : ℕ, normSum A q a * normSum A q b ≤ K₁ * normSum A q (a + b) := by
    intro a b
    have := h.mul_normSum_mul_le hq a b
    rw [hK₁def, mul_assoc, le_inv_mul_iff₀ hc]
    exact this
  have hsup : ∀ a b : ℕ, 0 < a → 0 < b →
      Real.log (normSum A q a / K₁) + Real.log (normSum A q b / K₁) ≤
        Real.log (normSum A q (a + b) / K₁) := by
    intro a b _ _
    rw [← Real.log_mul (div_pos (normSum_pos hA a) hK₁).ne' (div_pos (normSum_pos hA b) hK₁).ne']
    refine Real.log_le_log (mul_pos (div_pos (normSum_pos hA a) hK₁)
      (div_pos (normSum_pos hA b) hK₁)) ?_
    rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hK₁ hK₁) hK₁]
    nlinarith [hmul a b]
  have ht : Tendsto (fun k : ℕ => Real.log (normSum A q k / K₁) / k) atTop
      (𝓝 (normPressure A q)) := by
    have := (tendsto_normPressure hA hq).sub (tendsto_const_div_atTop_nhds_zero_nat
      (Real.log K₁))
    rw [sub_zero] at this
    refine this.congr fun k => ?_
    rw [Real.log_div (normSum_pos hA k).ne' hK₁.ne', sub_div]
  refine ⟨max K₁ 1, le_max_right _ _, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [normSum_zero]
  have hle := le_mul_of_superadditive hsup ht hn
  have h1 : normSum A q n / K₁ ≤ Real.exp (n * normPressure A q) := by
    rw [← Real.exp_log (div_pos (normSum_pos hA n) hK₁)]
    exact Real.exp_le_exp.2 hle
  rw [div_le_iff₀ hK₁] at h1
  calc normSum A q n ≤ Real.exp (n * normPressure A q) * K₁ := h1
    _ ≤ max K₁ 1 * Real.exp (n * normPressure A q) := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

/-! ### Sums over the words around a fixed word -/

omit [Fintype ι] in
/-- `ψ(𝐱𝐮𝐲) ≤ ψ(𝐱) ψ(𝐮) ψ(𝐲)` for `ψ = ‖·‖^q`, `q ≥ 0`. -/
theorem rpow_norm_word_triple_le (hq : 0 ≤ q) (x u y : List ι) :
    ‖word A (x ++ u ++ y)‖ ^ q ≤ ‖word A x‖ ^ q * ‖word A u‖ ^ q * ‖word A y‖ ^ q :=
  (rpow_norm_word_append_le hq _ _).trans (mul_le_mul_of_nonneg_right
    (rpow_norm_word_append_le hq _ _) (Real.rpow_nonneg (norm_nonneg _) _))

/-- The upper bound `∑_{|𝐱| = k, |𝐲| = l} ψ(𝐱𝐮𝐲) ≤ Z_k ψ(𝐮) Z_l`, from sub-multiplicativity
(`thm:irred_eq_state`). -/
theorem sum_triple_le (hq : 0 ≤ q) (u : List ι) (k l : ℕ) :
    ∑ x : Fin k → ι, ∑ y : Fin l → ι, ‖word A (List.ofFn x ++ u ++ List.ofFn y)‖ ^ q ≤
      normSum A q k * ‖word A u‖ ^ q * normSum A q l := by
  calc ∑ x : Fin k → ι, ∑ y : Fin l → ι, ‖word A (List.ofFn x ++ u ++ List.ofFn y)‖ ^ q
      ≤ ∑ x : Fin k → ι, ∑ y : Fin l → ι, ‖word A (List.ofFn x)‖ ^ q * ‖word A u‖ ^ q *
          ‖word A (List.ofFn y)‖ ^ q :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
          rpow_norm_word_triple_le hq _ _ _
    _ = normSum A q k * ‖word A u‖ ^ q * normSum A q l := by
        rw [normSum, normSum, Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]

variable (A q) in
/-- The constant `κ = δ^{mq} c / (m + 1)` of the padded quasi-multiplicative lower bounds
(`thm:irred_eq_state`). -/
noncomputable def padConst (m : ℕ) (c : ℝ) : ℝ := (normLowerBound A ^ m) ^ q * c / (m + 1)

/-- `κ > 0`. -/
theorem padConst_pos {m : ℕ} {c : ℝ} (hc : 0 < c) : 0 < padConst A q m c :=
  div_pos (mul_pos (Real.rpow_pos_of_pos (pow_pos normLowerBound_pos _) _) hc) (by positivity)

/-- The padded lower bound on the right (`thm:irred_eq_state`):
`κ ψ(𝐮) Z_b ≤ ∑_{|𝐲| = m + b} ψ(𝐮𝐲)`. For `|𝐲'| = b` the word `𝐲 = 𝐤 𝐲' i₀^{m - |𝐤|}`, with
the gap `𝐤` of `𝐮` and `𝐲'`, has length `m + b` and `ψ(𝐮𝐲) ≥ δ^{mq} c ψ(𝐮) ψ(𝐲')`; it determines
`𝐲'` once `|𝐤|` is known. -/
theorem NormQMConstants.le_sum_append_right [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) {m : ℕ}
    {c : ℝ} (h : NormQMConstants A q m c) (hq : 0 ≤ q) (u : List ι) (b : ℕ) :
    padConst A q m c * ‖word A u‖ ^ q * normSum A q b ≤
      ∑ y : Fin (m + b) → ι, ‖word A (u ++ List.ofFn y)‖ ^ q := by
  choose g hg using h.2
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  set δ := normLowerBound A with hδdef
  have hδ : 0 < δ := normLowerBound_pos
  set pad : List ι → List ι := fun y' =>
    g u y' ++ y' ++ List.replicate (m - (g u y').length) i₀ with hpad
  have key : ∀ y' : List ι, (δ ^ m) ^ q * c * (‖word A u‖ ^ q * ‖word A y'‖ ^ q) ≤
      ‖word A (u ++ pad y')‖ ^ q := by
    intro y'
    have e : u ++ pad y' = u ++ g u y' ++ y' ++ List.replicate (m - (g u y').length) i₀ := by
      simp [hpad, List.append_assoc]
    have h1 := pow_mul_norm_le_norm_mul_word hA (word A (u ++ g u y' ++ y'))
      (List.replicate (m - (g u y').length) i₀)
    rw [List.length_replicate] at h1
    have h2 : δ ^ m ≤ δ ^ (m - (g u y').length) :=
      pow_le_pow_of_le_one hδ.le normLowerBound_le_one (Nat.sub_le _ _)
    have h3 : δ ^ m * ‖word A (u ++ g u y' ++ y')‖ ≤ ‖word A (u ++ pad y')‖ := by
      rw [e, word_append A (u ++ g u y' ++ y')]
      exact (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)).trans h1
    calc (δ ^ m) ^ q * c * (‖word A u‖ ^ q * ‖word A y'‖ ^ q)
        ≤ (δ ^ m) ^ q * ‖word A (u ++ g u y' ++ y')‖ ^ q := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (hg u y').2
            (Real.rpow_nonneg (pow_nonneg hδ.le _) _)
      _ = (δ ^ m * ‖word A (u ++ g u y' ++ y')‖) ^ q :=
          (Real.mul_rpow (pow_nonneg hδ.le _) (norm_nonneg _)).symm
      _ ≤ ‖word A (u ++ pad y')‖ ^ q :=
          Real.rpow_le_rpow (mul_nonneg (pow_nonneg hδ.le _) (norm_nonneg _)) h3 hq
  have hcount := sum_comp_le_sum_range (wordsOfLength ι b) pad (fun y' => (g u y').length) m
    (fun _ => wordsOfLength ι (m + b)) (F := fun L => ‖word A (u ++ L)‖ ^ q)
    (fun _ => Real.rpow_nonneg (norm_nonneg _) _) (fun y' _ => (hg u y').1)
    (fun y' hy' => by
      rw [mem_wordsOfLength] at hy' ⊢
      have := (hg u y').1
      simp only [hpad, List.length_append, List.length_replicate, hy']
      omega)
    (fun y' hy' y'' hy'' hj he => by
      rw [mem_wordsOfLength] at hy' hy''
      have := congrArg (fun L => List.take b (List.drop (g u y').length L)) he
      simp only [hpad, List.append_assoc] at this
      rwa [List.drop_left' rfl, List.take_left' hy', hj, List.drop_left' rfl,
        List.take_left' hy''] at this)
  have hR : ∑ t ∈ Finset.range (m + 1), ∑ L ∈ wordsOfLength ι (m + b), ‖word A (u ++ L)‖ ^ q =
      (m + 1) * ∑ y : Fin (m + b) → ι, ‖word A (u ++ List.ofFn y)‖ ^ q := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, sum_wordsOfLength]
    push_cast
    ring
  have H : (δ ^ m) ^ q * c * (‖word A u‖ ^ q * normSum A q b) ≤
      (m + 1) * ∑ y : Fin (m + b) → ι, ‖word A (u ++ List.ofFn y)‖ ^ q := by
    rw [← hR]
    refine le_trans ?_ hcount
    rw [normSum, ← sum_wordsOfLength b fun L => ‖word A L‖ ^ q, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun y' _ => key y'
  have hm : (0 : ℝ) < m + 1 := by positivity
  rw [padConst, ← hδdef, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hm]
  linarith

/-- The padded lower bound on the left (`thm:irred_eq_state`):
`κ Z_a ψ(𝐯) ≤ ∑_{|𝐱| = m + a} ψ(𝐱𝐯)`. For `|𝐱'| = a` the word `𝐱 = i₀^{m - |𝐤|} 𝐱' 𝐤`, with the
gap `𝐤` of `𝐱'` and `𝐯`, has length `m + a` and `ψ(𝐱𝐯) ≥ δ^{mq} c ψ(𝐱') ψ(𝐯)`; it determines
`𝐱'` once `|𝐤|` is known. -/
theorem NormQMConstants.le_sum_append_left [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) {m : ℕ}
    {c : ℝ} (h : NormQMConstants A q m c) (hq : 0 ≤ q) (v : List ι) (a : ℕ) :
    padConst A q m c * normSum A q a * ‖word A v‖ ^ q ≤
      ∑ x : Fin (m + a) → ι, ‖word A (List.ofFn x ++ v)‖ ^ q := by
  choose g hg using h.2
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  set δ := normLowerBound A with hδdef
  have hδ : 0 < δ := normLowerBound_pos
  set pad : List ι → List ι := fun x' =>
    List.replicate (m - (g x' v).length) i₀ ++ x' ++ g x' v with hpad
  have key : ∀ x' : List ι, (δ ^ m) ^ q * c * (‖word A x'‖ ^ q * ‖word A v‖ ^ q) ≤
      ‖word A (pad x' ++ v)‖ ^ q := by
    intro x'
    have e : pad x' ++ v = List.replicate (m - (g x' v).length) i₀ ++ (x' ++ g x' v ++ v) := by
      simp [hpad, List.append_assoc]
    have h1 := pow_mul_norm_le_norm_word_mul hA (word A (x' ++ g x' v ++ v))
      (List.replicate (m - (g x' v).length) i₀)
    rw [List.length_replicate] at h1
    have h2 : δ ^ m ≤ δ ^ (m - (g x' v).length) :=
      pow_le_pow_of_le_one hδ.le normLowerBound_le_one (Nat.sub_le _ _)
    have h3 : δ ^ m * ‖word A (x' ++ g x' v ++ v)‖ ≤ ‖word A (pad x' ++ v)‖ := by
      rw [e, word_append A (List.replicate _ i₀)]
      exact (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)).trans h1
    calc (δ ^ m) ^ q * c * (‖word A x'‖ ^ q * ‖word A v‖ ^ q)
        ≤ (δ ^ m) ^ q * ‖word A (x' ++ g x' v ++ v)‖ ^ q := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (hg x' v).2
            (Real.rpow_nonneg (pow_nonneg hδ.le _) _)
      _ = (δ ^ m * ‖word A (x' ++ g x' v ++ v)‖) ^ q :=
          (Real.mul_rpow (pow_nonneg hδ.le _) (norm_nonneg _)).symm
      _ ≤ ‖word A (pad x' ++ v)‖ ^ q :=
          Real.rpow_le_rpow (mul_nonneg (pow_nonneg hδ.le _) (norm_nonneg _)) h3 hq
  have hcount := sum_comp_le_sum_range (wordsOfLength ι a) pad
    (fun x' => m - (g x' v).length) m (fun _ => wordsOfLength ι (m + a))
    (F := fun L => ‖word A (L ++ v)‖ ^ q) (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    (fun x' _ => Nat.sub_le _ _)
    (fun x' hx' => by
      rw [mem_wordsOfLength] at hx' ⊢
      have := (hg x' v).1
      simp only [hpad, List.length_append, List.length_replicate, hx']
      omega)
    (fun x' hx' x'' hx'' hj he => by
      rw [mem_wordsOfLength] at hx' hx''
      have := congrArg (fun L => List.take a (List.drop (m - (g x' v).length) L)) he
      simp only [hpad, List.append_assoc] at this
      rwa [List.drop_left' List.length_replicate, List.take_left' hx', hj,
        List.drop_left' List.length_replicate, List.take_left' hx''] at this)
  have hR : ∑ t ∈ Finset.range (m + 1), ∑ L ∈ wordsOfLength ι (m + a), ‖word A (L ++ v)‖ ^ q =
      (m + 1) * ∑ x : Fin (m + a) → ι, ‖word A (List.ofFn x ++ v)‖ ^ q := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, sum_wordsOfLength]
    push_cast
    ring
  have H : (δ ^ m) ^ q * c * (normSum A q a * ‖word A v‖ ^ q) ≤
      (m + 1) * ∑ x : Fin (m + a) → ι, ‖word A (List.ofFn x ++ v)‖ ^ q := by
    rw [← hR]
    refine le_trans ?_ hcount
    rw [normSum, ← sum_wordsOfLength a fun L => ‖word A L‖ ^ q, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_le_sum fun x' _ => key x'
  have hm : (0 : ℝ) < m + 1 := by positivity
  rw [padConst, ← hδdef, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hm]
  linarith

/-- The two-sided padded lower bound (`thm:irred_eq_state`):
`κ² Z_a ψ(𝐮) Z_b ≤ ∑_{|𝐱| = m + a, |𝐲| = m + b} ψ(𝐱𝐮𝐲)`. -/
theorem NormQMConstants.le_sum_triple [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) {m : ℕ} {c : ℝ}
    (h : NormQMConstants A q m c) (hq : 0 ≤ q) (u : List ι) (a b : ℕ) :
    padConst A q m c ^ 2 * normSum A q a * ‖word A u‖ ^ q * normSum A q b ≤
      ∑ x : Fin (m + a) → ι, ∑ y : Fin (m + b) → ι,
        ‖word A (List.ofFn x ++ u ++ List.ofFn y)‖ ^ q := by
  have hκ := padConst_pos (A := A) (q := q) (m := m) h.1
  have hZ : 0 ≤ normSum A q b := Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
  calc padConst A q m c ^ 2 * normSum A q a * ‖word A u‖ ^ q * normSum A q b
      = padConst A q m c * normSum A q b *
          (padConst A q m c * normSum A q a * ‖word A u‖ ^ q) := by ring
    _ ≤ padConst A q m c * normSum A q b *
          ∑ x : Fin (m + a) → ι, ‖word A (List.ofFn x ++ u)‖ ^ q :=
        mul_le_mul_of_nonneg_left (h.le_sum_append_left hA hq u a) (mul_nonneg hκ.le hZ)
    _ = ∑ x : Fin (m + a) → ι,
          padConst A q m c * ‖word A (List.ofFn x ++ u)‖ ^ q * normSum A q b := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
    _ ≤ ∑ x : Fin (m + a) → ι, ∑ y : Fin (m + b) → ι,
          ‖word A (List.ofFn x ++ u ++ List.ofFn y)‖ ^ q :=
        Finset.sum_le_sum fun x _ => h.le_sum_append_right hA hq _ b

end Partition

end MatrixTuple

end BoxLike
