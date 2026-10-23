import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.LinearCocycles.Monomial
import FractalGeometry.LinearCocycles.MonomialSingularValues
import FractalGeometry.LinearCocycles.Proximal
import FractalGeometry.LinearCocycles.SingularValue
import FractalGeometry.Pressure.Rectangular.Defs
import FractalGeometry.Pressure.Rectangular.Exponents
import FractalGeometry.Pressure.Rectangular.Matrices
import FractalGeometry.Pressure.Rectangular.Pressure
import FractalGeometry.Pressure.Rectangular.Proximal
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.ParityShift
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Set

open scoped Matrix.Norms.L2Operator

universe u

section Definitions

variable {α : Type*} [MeasurableSpace α]

def IsQuasiBernoulli (μ : Measure (ℤ → α)) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ m n : ℕ, 0 < m → 0 < n → ∀ (w : Fin m → α) (w' : Fin n → α),
    C⁻¹ * (μ.real (cylinder w) * μ.real (cylinder w')) ≤ μ.real (cylinder (Fin.append w w')) ∧
      μ.real (cylinder (Fin.append w w')) ≤ C * (μ.real (cylinder w) * μ.real (cylinder w'))

def IsBernoulli [Fintype α] (μ : Measure (ℤ → α)) : Prop :=
  ∃ p : α → ℝ, (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ ∀ (k : ℤ) (n : ℕ), 0 < n → ∀ w : Fin n → α,
    μ.real (shift k ⁻¹' cylinder w) = ∏ j, p (w j)

variable {μ : Measure (ℤ → α)}

theorem IsBernoulli.measureReal_cylinder_eq_prod [Fintype α] (h : IsBernoulli μ) {n : ℕ}
    (hn : 0 < n) (w : Fin n → α) : μ.real (cylinder w) = ∏ k, μ.real (cylinder ![w k]) := by
  obtain ⟨p, -, -, hp⟩ := h
  have h0 : ∀ {m : ℕ} (v : Fin m → α), shift 0 ⁻¹' cylinder v = cylinder v := fun v =>
    Set.ext fun x => by rw [Set.mem_preimage, shift_zero]
  have h1 : ∀ i : α, μ.real (cylinder ![i]) = p i := fun i => by
    rw [← h0, hp 0 1 one_pos]
    simp
  rw [← h0 w, hp 0 n hn]
  exact Finset.prod_congr rfl fun k _ => (h1 (w k)).symm

theorem isQuasiBernoulli_of_measureReal_cylinder_eq_prod
    (h : ∀ n : ℕ, 0 < n → ∀ w : Fin n → α,
      μ.real (cylinder w) = ∏ k, μ.real (cylinder ![w k])) : IsQuasiBernoulli μ := by
  refine ⟨1, le_rfl, fun m n hm hn w w' => ?_⟩
  have e : μ.real (cylinder (Fin.append w w')) = μ.real (cylinder w) * μ.real (cylinder w') := by
    rw [h (m + n) (by omega), h m hm, h n hn, Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  rw [e]
  simp

theorem IsBernoulli.isQuasiBernoulli [Fintype α] (h : IsBernoulli μ) : IsQuasiBernoulli μ :=
  isQuasiBernoulli_of_measureReal_cylinder_eq_prod fun _ hn w =>
    h.measureReal_cylinder_eq_prod hn w

end Definitions

noncomputable def gapExp (s : ℝ) : ℝ := if s < 1 then s else 2 - s

theorem gapExp_pos {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) : 0 < gapExp s := by
  unfold gapExp
  split_ifs <;> linarith

theorem svf_eq_norm_rpow_mul_abs_det_rpow {s : ℝ} (hs2 : s ≤ 2)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    svf s A = ‖A‖ ^ gapExp s * |A.det| ^ ((s - gapExp s) / 2) := by
  unfold svf gapExp
  rcases lt_trichotomy s 1 with h | rfl | h
  · rw [ite_eq_left h.le, ite_eq_left h, sub_self, zero_div, Real.rpow_zero, mul_one]
  · norm_num
  · rw [ite_eq_right (not_le.2 h), ite_eq_left hs2, ite_eq_right (not_lt.2 h.le)]
    congr 2
    ring

theorem mul_svf_mul_le_of_norm {s : ℝ} (hs2 : s ≤ 2) {A B : Matrix (Fin 2) (Fin 2) ℝ} {K : ℝ}
    (h : K * ‖A * B‖ ^ gapExp s ≤ ‖A‖ ^ gapExp s * ‖B‖ ^ gapExp s) :
    K * svf s (A * B) ≤ svf s A * svf s B := by
  rw [svf_eq_norm_rpow_mul_abs_det_rpow hs2 (A * B), svf_eq_norm_rpow_mul_abs_det_rpow hs2 A,
    svf_eq_norm_rpow_mul_abs_det_rpow hs2 B, Matrix.det_mul, abs_mul,
    Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  have hd : 0 ≤ |A.det| ^ ((s - gapExp s) / 2) * |B.det| ^ ((s - gapExp s) / 2) :=
    mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
  calc K * (‖A * B‖ ^ gapExp s *
          (|A.det| ^ ((s - gapExp s) / 2) * |B.det| ^ ((s - gapExp s) / 2)))
      = K * ‖A * B‖ ^ gapExp s *
          (|A.det| ^ ((s - gapExp s) / 2) * |B.det| ^ ((s - gapExp s) / 2)) := by ring
    _ ≤ ‖A‖ ^ gapExp s * ‖B‖ ^ gapExp s *
          (|A.det| ^ ((s - gapExp s) / 2) * |B.det| ^ ((s - gapExp s) / 2)) :=
        mul_le_mul_of_nonneg_right h hd
    _ = _ := by ring

private theorem div_mul_div_pow_mul_le {α β γ Γ x y z : ℝ} (hα : 0 ≤ α) (hβ : 0 < β)
    (hγ : 0 ≤ γ) (hΓ : 0 < Γ) (n : ℕ) (hx : α ^ n ≤ x) (hy : γ * α ^ n ≤ y)
    (hz : z ≤ Γ * (α * β) ^ n) : γ / Γ * (α / β) ^ n * z ≤ x * y :=
  calc γ / Γ * (α / β) ^ n * z ≤ γ / Γ * (α / β) ^ n * (Γ * (α * β) ^ n) :=
        mul_le_mul_of_nonneg_left hz (by positivity)
    _ = α ^ n * (γ * α ^ n) := by
        rw [div_pow, mul_pow]
        field_simp
    _ ≤ x * y := mul_le_mul hx hy (by positivity) ((pow_nonneg hα n).trans hx)

theorem mul_norm_monomialMatrix_mul_le {a b c d : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (n : ℕ) :
    min |c| |d| / max |c| |d| * (max |a| |b| / min |a| |b|) ^ n *
        ‖monomialMatrix 0 (a ^ n) (b ^ n) * monomialMatrix 1 (c * b ^ n) (d * a ^ n)‖ ≤
      ‖monomialMatrix 0 (a ^ n) (b ^ n)‖ * ‖monomialMatrix 1 (c * b ^ n) (d * a ^ n)‖ := by
  have hab : |a| * |b| = max |a| |b| * min |a| |b| := abs_mul_abs_eq_max_mul_min a b
  have hmax : ∀ x y : ℝ, max x y ^ n ≤ max (x ^ n) (y ^ n) := fun x y => by
    rcases le_total x y with h | h
    · rw [max_eq_right h]
      exact le_max_right _ _
    · rw [max_eq_left h]
      exact le_max_left _ _
  refine div_mul_div_pow_mul_le (le_max_of_le_left (abs_nonneg a))
    (lt_min (abs_pos.2 ha) (abs_pos.2 hb)) (le_min (abs_nonneg c) (abs_nonneg d))
    (lt_max_of_lt_left (abs_pos.2 hc)) n ?_ ?_ ?_
  · rw [norm_monomialMatrix, abs_pow, abs_pow]
    exact hmax _ _
  · rw [norm_monomialMatrix, abs_mul, abs_mul, abs_pow, abs_pow]
    rcases le_total |a| |b| with h | h
    · rw [max_eq_right h]
      exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
        (pow_nonneg (abs_nonneg b) n)) (le_max_left _ _)
    · rw [max_eq_left h]
      exact le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _)
        (pow_nonneg (abs_nonneg a) n)) (le_max_right _ _)
  · have hpow : 0 ≤ (max |a| |b| * min |a| |b|) ^ n := by rw [← hab]; positivity
    have e1 : |a ^ n * (c * b ^ n)| = |c| * (max |a| |b| * min |a| |b|) ^ n := by
      rw [← hab, abs_mul, abs_mul, abs_pow, abs_pow, mul_pow]
      ring
    have e2 : |b ^ n * (d * a ^ n)| = |d| * (max |a| |b| * min |a| |b|) ^ n := by
      rw [← hab, abs_mul, abs_mul, abs_pow, abs_pow, mul_pow]
      ring
    rw [monomialMatrix_mul, ite_eq_left rfl, ite_eq_left rfl, norm_monomialMatrix, e1, e2]
    exact max_le (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hpow)

namespace RectangularIFS

section Words

variable {ι : Type u} (S : RectangularIFS ι)

theorem matWord_flatten_replicate {u : List ι} {a b : ℝ} (hu : S.matWord u = monomialMatrix 0 a b)
    (n : ℕ) : S.matWord (List.replicate n u).flatten = monomialMatrix 0 (a ^ n) (b ^ n) := by
  induction n with
  | zero =>
    ext k l
    fin_cases k <;> fin_cases l <;> simp
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, matWord_append, hu, ih, monomialMatrix_mul]
    simp [pow_succ']

theorem matWord_cons_flatten_replicate {u : List ι} {a b : ℝ}
    (hu : S.matWord u = monomialMatrix 0 a b) {j : ι} (hj : S.o j = 1) (n : ℕ) :
    S.matWord (j :: (List.replicate n u).flatten) =
      monomialMatrix 1 (S.a j * b ^ n) (S.b j * a ^ n) := by
  rw [matWord_cons, S.matWord_flatten_replicate hu, mat, hj, monomialMatrix_mul, ite_eq_right (by decide),
    ite_eq_right (by decide), add_zero]

theorem Proximal.exists_matWord_eq (hprox : S.Proximal) :
    ∃ (u : List ι) (a b : ℝ), u ≠ [] ∧ S.oWord u = 0 ∧ S.matWord u = monomialMatrix 0 a b ∧ a ≠ 0 ∧
      b ≠ 0 ∧ |a| ≠ |b| := by
  obtain ⟨u, hu0, hu⟩ := hprox
  have hmat := S.matWord_eq u
  rcases zmod_two_cases (S.oWord u) with ho | ho
  · rw [ho] at hmat
    rw [hmat] at hu
    exact ⟨u, _, _, hu0, ho, hmat, S.gDeriv_ne_zero _, S.gDeriv_ne_zero _,
      isProximalMatrix_monomialMatrix_zero.1 hu⟩
  · rw [hmat, ho] at hu
    exact absurd hu (not_isProximalMatrix_monomialMatrix_one _ _)

theorem exists_mul_svf_le {s : ℝ} (hrot : S.HasBothOrientations) (hprox : S.Proximal) (hs0 : 0 < s)
    (hs2 : s < 2) :
    ∃ (u : List ι) (j : ι) (c q : ℝ), u ≠ [] ∧ S.oWord u = 0 ∧ S.o j = 1 ∧ 0 < c ∧ 1 < q ∧
      ∀ n : ℕ, c * q ^ n * svf s (S.matWord
          ((List.replicate n u).flatten ++ j :: (List.replicate n u).flatten)) ≤
        svf s (S.matWord (List.replicate n u).flatten) *
          svf s (S.matWord (j :: (List.replicate n u).flatten)) := by
  obtain ⟨u, a, b, hu0, ho, hu, ha, hb, hne⟩ := hprox.exists_matWord_eq
  obtain ⟨j, hj⟩ := hrot.2
  have ht := gapExp_pos hs0 hs2
  have hβ : 0 < min |a| |b| := lt_min (abs_pos.2 ha) (abs_pos.2 hb)
  have hq : 1 < max |a| |b| / min |a| |b| := (one_lt_div hβ).2 (min_lt_max.2 hne)
  have hc : 0 < min |S.a j| |S.b j| / max |S.a j| |S.b j| :=
    div_pos (lt_min (abs_pos.2 (S.a_ne_zero j)) (abs_pos.2 (S.b_ne_zero j)))
      (lt_max_of_lt_left (abs_pos.2 (S.a_ne_zero j)))
  refine ⟨u, j, (min |S.a j| |S.b j| / max |S.a j| |S.b j|) ^ gapExp s,
    (max |a| |b| / min |a| |b|) ^ gapExp s, hu0, ho, hj, Real.rpow_pos_of_pos hc _,
    Real.one_lt_rpow hq ht, fun n => ?_⟩
  rw [matWord_append, S.matWord_flatten_replicate hu, S.matWord_cons_flatten_replicate hu hj]
  refine mul_svf_mul_le_of_norm hs2.le ?_
  have key := Real.rpow_le_rpow (by positivity)
    (mul_norm_monomialMatrix_mul_le ha hb (S.a_ne_zero j) (d := S.b j) n) ht.le
  rwa [Real.mul_rpow (by positivity) (norm_nonneg _), Real.mul_rpow hc.le (by positivity),
    ← Real.rpow_pow_comm (zero_lt_one.trans hq).le,
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _)] at key

end Words

section GibbsBounds

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] (S : RectangularIFS ι) {s C : ℝ}
  {μ : Measure (ℤ → ι)}

def HasGibbsBoundsWith (C s : ℝ) (μ : Measure (ℤ → ι)) : Prop :=
  1 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ w : Fin n → ι,
    C⁻¹ * (Real.exp (-(n * S.pressure s)) * svf s (S.matWord (List.ofFn w))) ≤
        μ.real (cylinder w) ∧
      μ.real (cylinder w) ≤
        C * (Real.exp (-(n * S.pressure s)) * svf s (S.matWord (List.ofFn w)))

theorem hasGibbsBounds_iff : S.HasGibbsBounds s μ ↔ ∃ C, S.HasGibbsBoundsWith C s μ := Iff.rfl

variable {S}

theorem HasGibbsBoundsWith.measureReal_cylinder_pos (h : S.HasGibbsBoundsWith C s μ) {n : ℕ}
    (hn : 0 < n) (w : Fin n → ι) : 0 < μ.real (cylinder w) :=
  lt_of_lt_of_le (mul_pos (inv_pos.2 (one_pos.trans_le h.1))
    (mul_pos (Real.exp_pos _) (S.svf_matWord_pos s _))) (h.2 n hn w).1

theorem HasGibbsBoundsWith.mul_measureReal_cylinder_append_le (h : S.HasGibbsBoundsWith C s μ)
    {l l' : List ι} (hl : l ≠ []) (hl' : l' ≠ []) {κ : ℝ} (hκ : 0 ≤ κ)
    (hsvf : κ * svf s (S.matWord (l ++ l')) ≤ svf s (S.matWord l) * svf s (S.matWord l')) :
    κ / C ^ 3 * μ.real (cylinder (Fin.append l.get l'.get)) ≤
      μ.real (cylinder l.get) * μ.real (cylinder l'.get) := by
  obtain ⟨hC, hb⟩ := h
  have hC0 : 0 < C := one_pos.trans_le hC
  have hlen : 0 < l.length := List.length_pos_of_ne_nil hl
  have hlen' : 0 < l'.length := List.length_pos_of_ne_nil hl'
  have h1 := (hb (l.length + l'.length) (by omega) (Fin.append l.get l'.get)).2
  have h2 := (hb l.length hlen l.get).1
  have h3 := (hb l'.length hlen' l'.get).1
  rw [List.ofFn_fin_append, List.ofFn_get, List.ofFn_get] at h1
  rw [List.ofFn_get] at h2 h3
  have hexp : Real.exp (-(((l.length + l'.length : ℕ) : ℝ) * S.pressure s)) =
      Real.exp (-(l.length * S.pressure s)) * Real.exp (-(l'.length * S.pressure s)) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  calc κ / C ^ 3 * μ.real (cylinder (Fin.append l.get l'.get))
      ≤ κ / C ^ 3 * (C * (Real.exp (-(((l.length + l'.length : ℕ) : ℝ) * S.pressure s)) *
          svf s (S.matWord (l ++ l')))) :=
        mul_le_mul_of_nonneg_left h1 (div_nonneg hκ (pow_pos hC0 3).le)
    _ = C⁻¹ * C⁻¹ * (Real.exp (-(((l.length + l'.length : ℕ) : ℝ) * S.pressure s)) *
          (κ * svf s (S.matWord (l ++ l')))) := by
        field_simp
    _ ≤ C⁻¹ * C⁻¹ * (Real.exp (-(((l.length + l'.length : ℕ) : ℝ) * S.pressure s)) *
          (svf s (S.matWord l) * svf s (S.matWord l'))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsvf (Real.exp_pos _).le)
          (mul_nonneg (inv_pos.2 hC0).le (inv_pos.2 hC0).le)
    _ = C⁻¹ * (Real.exp (-(l.length * S.pressure s)) * svf s (S.matWord l)) *
          (C⁻¹ * (Real.exp (-(l'.length * S.pressure s)) * svf s (S.matWord l'))) := by
        rw [hexp]
        ring
    _ ≤ μ.real (cylinder l.get) * μ.real (cylinder l'.get) :=
        mul_le_mul h2 h3 (mul_nonneg (inv_pos.2 hC0).le
          (mul_nonneg (Real.exp_pos _).le (svf_nonneg _ _))) measureReal_nonneg

theorem HasGibbsBounds.exists_mul_measureReal_cylinder_le (hrot : S.HasBothOrientations)
    (hprox : S.Proximal) (hs0 : 0 < s) (hs2 : s < 2) (h : S.HasGibbsBounds s μ) :
    ∃ (u : List ι) (j : ι) (c q : ℝ), u ≠ [] ∧ S.oWord u = 0 ∧ S.o j = 1 ∧ 0 < c ∧ 1 < q ∧
      ∀ n : ℕ, 0 < n → c * q ^ n * μ.real (cylinder (Fin.append
          (List.replicate n u).flatten.get (j :: (List.replicate n u).flatten).get)) ≤
        μ.real (cylinder (List.replicate n u).flatten.get) *
          μ.real (cylinder (j :: (List.replicate n u).flatten).get) := by
  obtain ⟨K, h⟩ := (hasGibbsBounds_iff S).1 h
  obtain ⟨u, j, c, q, hu0, ho, hj, hc, hq, hsvf⟩ := S.exists_mul_svf_le hrot hprox hs0 hs2
  have hK0 : 0 < K := one_pos.trans_le h.1
  refine ⟨u, j, c / K ^ 3, q, hu0, ho, hj, div_pos hc (pow_pos hK0 3), hq, fun n hn => ?_⟩
  have hne : (List.replicate n u).flatten ≠ [] := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [List.replicate_succ, List.flatten_cons]
    exact List.append_ne_nil_of_left_ne_nil hu0 _
  have key := h.mul_measureReal_cylinder_append_le hne (List.cons_ne_nil j _)
    (mul_nonneg hc.le (pow_nonneg (zero_le_one.trans hq.le) n)) (hsvf n)
  rwa [mul_div_right_comm] at key

theorem not_quasiBernoulli (hrot : S.HasBothOrientations) (hprox : S.Proximal) (hs0 : 0 < s)
    (hs2 : s < 2) (h : S.HasGibbsBounds s μ) : ¬ IsQuasiBernoulli μ := by
  rintro ⟨C, hC, hqb⟩
  obtain ⟨u, j, c, q, hu0, -, -, hc, hq, hfail⟩ :=
    h.exists_mul_measureReal_cylinder_le hrot hprox hs0 hs2
  obtain ⟨K, h⟩ := (hasGibbsBounds_iff S).1 h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / c) hq
  have hC0 : 0 < C := one_pos.trans_le hC
  have hlen : 0 < (List.replicate (n + 1) u).flatten.length := by
    rw [List.replicate_succ, List.flatten_cons, List.length_append]
    exact Nat.add_pos_left (List.length_pos_of_ne_nil hu0) _
  have hlen' : 0 < (j :: (List.replicate (n + 1) u).flatten).length := Nat.succ_pos _
  have hpos := h.measureReal_cylinder_pos (Nat.add_pos_left hlen _)
    (Fin.append (List.replicate (n + 1) u).flatten.get
      (j :: (List.replicate (n + 1) u).flatten).get)
  have h1 := hfail (n + 1) n.succ_pos
  have h2 := (hqb _ _ hlen hlen' (List.replicate (n + 1) u).flatten.get
    (j :: (List.replicate (n + 1) u).flatten).get).1
  rw [inv_mul_le_iff₀ hC0] at h2
  have h3 : c * q ^ (n + 1) ≤ C := le_of_mul_le_mul_right (h1.trans h2) hpos
  have h4 : q ^ n ≤ q ^ (n + 1) := pow_le_pow_right₀ hq.le n.le_succ
  rw [div_lt_iff₀ hc] at hn
  nlinarith

theorem not_isBernoulli (hrot : S.HasBothOrientations) (hprox : S.Proximal) (hs0 : 0 < s)
    (hs2 : s < 2) (h : S.HasGibbsBounds s μ) : ¬ IsBernoulli μ := fun hB =>
  not_quasiBernoulli hrot hprox hs0 hs2 h hB.isQuasiBernoulli

end GibbsBounds

end RectangularIFS

section Gibbs

variable {ι : Type u} [MeasurableSpace ι] {o : ι → ZMod 2} {φ φ' : ι × ZMod 2 → ℝ}
  {ν : Measure (ℤ → ι × ZMod 2)} {P C P' C' : ℝ} {y : ℤ → ι × ZMod 2}

def IsGibbsWith (o : ι → ZMod 2) (φ : ι × ZMod 2 → ℝ) (ν : Measure (ℤ → ι × ZMod 2))
    (P C : ℝ) : Prop :=
  0 < C ∧ ∀ y ∈ subshift o, ∀ n : ℕ, 0 < n →
    C⁻¹ * Real.exp (-(n * P) + ∑ k ∈ Finset.range n, φ (y k)) ≤
        ν.real (cylinder fun k : Fin n => y k) ∧
      ν.real (cylinder fun k : Fin n => y k) ≤
        C * Real.exp (-(n * P) + ∑ k ∈ Finset.range n, φ (y k))

theorem isGibbs_iff : IsGibbs o φ ν ↔ ∃ P C, IsGibbsWith o φ ν P C := Iff.rfl

theorem IsGibbsWith.one_le (h : IsGibbsWith o φ ν P C) (hy : y ∈ subshift o) : 1 ≤ C := by
  obtain ⟨hC, hb⟩ := h
  have h1 : C⁻¹ ≤ C :=
    le_of_mul_le_mul_right ((hb y hy 1 one_pos).1.trans (hb y hy 1 one_pos).2) (Real.exp_pos _)
  by_contra hlt
  have h2 : 1 < C⁻¹ := (one_lt_inv₀ hC).2 (not_le.1 hlt)
  linarith

end Gibbs

end FractalGeometry
