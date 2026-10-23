import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Pressure.ParityShift.HolderPotential
import FractalGeometry.Pressure.ParityShift.PeriodicWords
import FractalGeometry.Pressure.SuperadditiveBounds
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.OrientationCoding
import FractalGeometry.Symbolic.ParityShift
import FractalGeometry.Symbolic.PeriodicWords
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology Set

section Periodic

variable {ι : Type*} {o : ι → ZMod 2}

variable (o) in

theorem finite_periodicPoints [Finite ι] {p : ℕ} (hp : 0 < p) : (periodicPoints o p).Finite := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  exact Set.Finite.of_finite_image (Set.toFinite _) (bijOn_block_periodicPoints o n).injOn

variable (o) in

open Classical in

noncomputable def periodicFinset (p : ℕ) : Finset (ℤ → ι × ZMod 2) :=
  if h : (periodicPoints o p).Finite then h.toFinset else ∅

theorem mem_periodicFinset [Finite ι] {p : ℕ} (hp : 0 < p) {x : ℤ → ι × ZMod 2} :
    x ∈ periodicFinset o p ↔ x ∈ subshift o ∧ shift p x = x := by
  rw [periodicFinset, dite_eq_left (finite_periodicPoints o hp), Set.Finite.mem_toFinset]
  rfl

theorem exists_mem_periodicPoints_of_trans {n : ℕ} (g : ℕ → ι × ZMod 2)
    (hg : ∀ j, j < n → Trans o (g j) (g (j + 1))) (hc : Trans o (g n) (g 0)) :
    ∃ x, x ∈ subshift o ∧ shift ((n + 1 : ℕ) : ℤ) x = x ∧ ∀ j, j ≤ n → x j = g j := by
  set w : Fin (n + 1) → ι × ZMod 2 := fun k => g k
  have hw : IsCyclicAdmissible o w := by
    refine ⟨fun k hk => hg k (by omega), fun _ => ?_⟩
    simpa [w] using hc
  refine ⟨periodicExtension w, hw.periodicExtension_mem_subshift, shift_periodicExtension w,
    fun j hj => ?_⟩
  exact periodicExtension_natCast w ⟨j, by omega⟩

end Periodic

section Bounds

variable {ι : Type*} [Fintype ι] {o : ι → ZMod 2} {f : (ℤ → ι × ZMod 2) → ℝ} {B D : ℝ}

variable (o f) in

noncomputable def periodicPartition (p : ℕ) : ℝ :=
  ∑ x ∈ periodicFinset o p, Real.exp (birkhoffSum (shift 1) f p x)

open Classical in

theorem HasBoundedDistortion.sum_periodicFinset_cylinder_le [Nonempty ι]
    (h : HasBoundedDistortion o f B D) {y : ℤ → ι × ZMod 2} (hy : y ∈ subshift o) (m k : ℕ)
    (hmk : 0 < m + k) :
    ∑ x ∈ (periodicFinset o (m + k)).filter (· ∈ cylinder (block m y)),
        Real.exp (birkhoffSum (shift 1) f (m + k) x) ≤
      Real.exp (birkhoffSum (shift 1) f m y + D) * admissibleSumPot o f k := by
  classical
  set S := (periodicFinset o (m + k)).filter (· ∈ cylinder (block m y))
  set φ : (ℤ → ι × ZMod 2) → Fin k → ι × ZMod 2 := fun x => block k (shift m x)
  have hS : ∀ x ∈ S, x ∈ subshift o ∧ shift ((m + k : ℕ) : ℤ) x = x ∧
      x ∈ cylinder (block m y) := by
    intro x hx
    rw [Finset.mem_filter, mem_periodicFinset hmk] at hx
    exact ⟨hx.1.1, hx.1.2, hx.2⟩
  have hinj : Set.InjOn φ S := by
    intro x hx x' hx' hxx
    obtain ⟨hx1, hx2, hx3⟩ := hS x hx
    obtain ⟨hx1', hx2', hx3'⟩ := hS x' hx'
    obtain ⟨n, hn⟩ : ∃ n, m + k = n + 1 := ⟨m + k - 1, by omega⟩
    rw [hn] at hx2 hx2'
    refine eq_of_shift_eq_of_block_eq hx2 hx2' (funext fun j => ?_)
    simp only [block_apply]
    by_cases hj : (j : ℕ) < m
    · exact (hx3 ⟨j, hj⟩).trans (hx3' ⟨j, hj⟩).symm
    · have hjk : (j : ℕ) - m < k := by omega
      have e := congrFun hxx ⟨(j : ℕ) - m, hjk⟩
      simp only [φ, block_apply, shift_apply] at e
      have hc : (m : ℤ) + (((j : ℕ) - m : ℕ) : ℤ) = ((j : ℕ) : ℤ) := by
        rw [Nat.cast_sub (by omega)]; ring
      rwa [hc] at e
  have hterm : ∀ x ∈ S, Real.exp (birkhoffSum (shift 1) f (m + k) x) ≤
      Real.exp (birkhoffSum (shift 1) f m y + D) * Real.exp (cylSup o f k (φ x)) := by
    intro x hx
    obtain ⟨hx1, -, hx3⟩ := hS x hx
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    rw [birkhoffSum_add_right_apply, iterate_shift_one]
    have hd := h.distortion m y hy x hx1 fun j hj => (hx3 ⟨j, hj⟩).symm
    have hc : birkhoffSum (shift 1) f k (shift m x) ≤ cylSup o f k (φ x) :=
      (h.cylSup_bounds (shift_mem_subshift o hx1 m) (fun _ => rfl : shift m x ∈ cylinder (φ x))).1
    have := (abs_le.1 hd).1
    linarith
  calc ∑ x ∈ S, Real.exp (birkhoffSum (shift 1) f (m + k) x)
      ≤ ∑ x ∈ S, Real.exp (birkhoffSum (shift 1) f m y + D) *
          Real.exp (cylSup o f k (φ x)) := Finset.sum_le_sum hterm
    _ = Real.exp (birkhoffSum (shift 1) f m y + D) *
          ∑ v ∈ S.image φ, Real.exp (cylSup o f k v) := by
        rw [Finset.sum_image hinj, Finset.mul_sum]
    _ ≤ Real.exp (birkhoffSum (shift 1) f m y + D) * admissibleSumPot o f k := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        rw [admissibleSumPot, ← Finset.sum_filter]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => (Real.exp_pos _).le
        intro v hv
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
          isAdmissible_block (shift_mem_subshift o (hS x hx).1 m) k⟩

open Classical in

theorem HasBoundedDistortion.exp_mul_admissibleSumPot_le_sum_periodicFinset
    (h : HasBoundedDistortion o f B D) (h0 : ∃ i, o i = 0) (h1 : ∃ i, o i = 1)
    {y : ℤ → ι × ZMod 2} (hy : y ∈ subshift o) {m q : ℕ} (hm : 0 < m) (hq : 0 < q) :
    Real.exp (birkhoffSum (shift 1) f m y - (2 * B + 2 * D)) * admissibleSumPot o f q ≤
      ∑ x ∈ (periodicFinset o (m + q + 2)).filter (· ∈ cylinder (block m y)),
        Real.exp (birkhoffSum (shift 1) f (m + q + 2) x) := by
  classical
  have : Nonempty ι := ⟨h0.choose⟩
  set S := (periodicFinset o (m + q + 2)).filter (· ∈ cylinder (block m y))
  set c := birkhoffSum (shift 1) f m y - (2 * B + 2 * D)
  have key : ∀ v : Fin q → ι × ZMod 2, ∃ x : ℤ → ι × ZMod 2, IsAdmissible o v →
      x ∈ S ∧ block q (shift ((m : ℤ) + 1) x) = v ∧
        c + cylSup o f q v ≤ birkhoffSum (shift 1) f (m + q + 2) x := by
    intro v
    by_cases hv : IsAdmissible o v
    swap
    · exact ⟨y, fun h => absurd h hv⟩
    obtain ⟨z, hz, hzv⟩ := exists_mem_cylinder_of_isAdmissible hv
    obtain ⟨r, hr1, hr2⟩ := exists_trans_trans o h0 h1 (y ((m : ℤ) - 1)) (z 0)
    obtain ⟨r', hr1', hr2'⟩ := exists_trans_trans o h0 h1 (z ((q : ℤ) - 1)) (y 0)
    set g : ℕ → ι × ZMod 2 := fun j => if j < m then y j else if j = m then r
      else if j ≤ m + q then z ((j : ℤ) - (m + 1)) else r' with hg
    have hg1 : ∀ j, j < m → g j = y j := fun j hj => by simp [hg, hj]
    have hg2 : g m = r := by simp [hg]
    have hg3 : ∀ j, m < j → j ≤ m + q → g j = z ((j : ℤ) - (m + 1)) := fun j hj hj' => by
      simp [hg, show ¬ j < m by omega, show j ≠ m by omega, hj']
    have hg4 : g (m + q + 1) = r' := by
      simp [hg, show ¬ m + q + 1 < m by omega, show m + q + 1 ≠ m by omega]
    obtain ⟨x, hx1, hx2, hx3⟩ := exists_mem_periodicPoints_of_trans (n := m + q + 1) g
      (fun j hj => by
        rcases lt_trichotomy (j + 1) m with hj1 | hj1 | hj1
        · rw [hg1 j (by omega), hg1 (j + 1) hj1]
          have := hy (j : ℤ)
          push_cast
          exact this
        · rw [hg1 j (by omega), hj1, hg2]
          have e : (j : ℤ) = (m : ℤ) - 1 := by omega
          rw [e]
          exact hr1
        · rcases eq_or_lt_of_le (show m ≤ j by omega) with hj2 | hj2
          · subst hj2
            rw [hg2, hg3 (m + 1) (by omega) (by omega)]
            have e : ((m + 1 : ℕ) : ℤ) - ((m : ℤ) + 1) = 0 := by push_cast; ring
            rw [e]
            exact hr2
          · rcases lt_or_eq_of_le (show j ≤ m + q by omega) with hj3 | hj3
            · rw [hg3 j hj2 hj3.le, hg3 (j + 1) (by omega) (by omega)]
              have e : ((j + 1 : ℕ) : ℤ) - ((m : ℤ) + 1) = (j : ℤ) - ((m : ℤ) + 1) + 1 := by
                push_cast; ring
              rw [e]
              exact hz _
            · subst hj3
              rw [hg3 (m + q) hj2 le_rfl, hg4]
              have e : ((m + q : ℕ) : ℤ) - ((m : ℤ) + 1) = (q : ℤ) - 1 := by push_cast; ring
              rw [e]
              exact hr1')
      (by
        rw [hg4, hg1 0 hm]
        exact hr2')
    have hxS : x ∈ S := by
      refine Finset.mem_filter.2 ⟨(mem_periodicFinset (by omega)).2 ⟨hx1, hx2⟩, fun k => ?_⟩
      rw [hx3 k (by omega), hg1 k k.isLt]
      rfl
    have hxv : block q (shift ((m : ℤ) + 1) x) = v := by
      funext k
      rw [block_apply, shift_apply, ← hzv k]
      have e : (m : ℤ) + 1 + (k : ℕ) = ((m + 1 + k : ℕ) : ℤ) := by push_cast; ring
      rw [e, hx3 _ (by omega), hg3 _ (by omega) (by omega)]
      congr 1
      push_cast
      ring
    refine ⟨x, fun _ => ⟨hxS, hxv, ?_⟩⟩
    have hxy : x ∈ cylinder (block m y) := (Finset.mem_filter.1 hxS).2
    have hσ : shift ((m : ℤ) + 1) x ∈ subshift o := shift_mem_subshift o hx1 _
    rw [show m + q + 2 = m + (q + 1 + 1) by ring, birkhoffSum_add_right_apply,
      birkhoffSum_succ_apply', birkhoffSum_succ_apply, iterate_shift_one, iterate_shift_one,
      shift_shift, shift_shift]
    have hd := (abs_le.1 (h.distortion m y hy x hx1 fun j hj => (hxy ⟨j, hj⟩).symm)).2
    have hc := (h.cylSup_bounds hσ (by rw [cylinder_eq_preimage, Set.mem_preimage, hxv]; rfl :
      shift ((m : ℤ) + 1) x ∈ cylinder v)).2
    have hb1 := (abs_le.1 (h.abs_le_bound _ (shift_mem_subshift o hx1 m))).1
    have hb2 := (abs_le.1 (h.abs_le_bound _ (shift_mem_subshift o hx1 ((m : ℤ) + 1 + q)))).1
    simp only [c]
    linarith
  choose X hX using key
  have hinj : Set.InjOn X
      ((Finset.univ.filter fun v : Fin q → ι × ZMod 2 => IsAdmissible o v :
        Finset (Fin q → ι × ZMod 2)) : Set (Fin q → ι × ZMod 2)) := by
    intro v hv v' hv' hvv
    have h1 := (hX v (Finset.mem_filter.1 hv).2).2.1
    have h2 := (hX v' (Finset.mem_filter.1 hv').2).2.1
    rw [← h1, ← h2, hvv]
  calc Real.exp c * admissibleSumPot o f q
      = ∑ v ∈ Finset.univ.filter fun v => IsAdmissible o v,
          Real.exp (c + cylSup o f q v) := by
        rw [admissibleSumPot, ← Finset.sum_filter, Finset.mul_sum]
        exact Finset.sum_congr rfl fun v _ => (Real.exp_add _ _).symm
    _ ≤ ∑ v ∈ Finset.univ.filter fun v => IsAdmissible o v,
          Real.exp (birkhoffSum (shift 1) f (m + q + 2) (X v)) :=
        Finset.sum_le_sum fun v hv => Real.exp_le_exp.2 (hX v (Finset.mem_filter.1 hv).2).2.2
    _ = ∑ x ∈ (Finset.univ.filter fun v => IsAdmissible o v).image X,
          Real.exp (birkhoffSum (shift 1) f (m + q + 2) x) := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ x ∈ S, Real.exp (birkhoffSum (shift 1) f (m + q + 2) x) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => (Real.exp_pos _).le
        intro x hx
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hx
        exact (hX v (Finset.mem_filter.1 hv).2).1

theorem mem_subshift_of_mem_periodicFinset {p : ℕ} {x : ℤ → ι × ZMod 2}
    (hx : x ∈ periodicFinset o p) : x ∈ subshift o := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · classical
    unfold periodicFinset at hx
    split_ifs at hx with h
    · exact ((Set.Finite.mem_toFinset h).1 hx).1
    · simp at hx
  · exact ((mem_periodicFinset hp).1 hx).1

theorem HasBoundedDistortion.periodicPartition_le_admissibleSumPot [Nonempty ι]
    (h : HasBoundedDistortion o f B D) {p : ℕ} (hp : 0 < p) :
    periodicPartition o f p ≤ Real.exp D * admissibleSumPot o f p := by
  classical
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hy := tau_mem_subshift (o := o) fun _ => i
  have key := h.sum_periodicFinset_cylinder_le hy 0 p (by omega)
  simp only [zero_add, birkhoffSum_zero_apply] at key
  have hall : ∀ x ∈ periodicFinset o p, x ∈ cylinder (block 0 (tau o fun _ => i)) :=
    fun _ _ k => k.elim0
  rw [Finset.filter_true_of_mem hall] at key
  exact key

theorem HasBoundedDistortion.exp_mul_admissibleSumPot_mul_le_periodicPartition
    (h : HasBoundedDistortion o f B D) (h0 : ∃ i, o i = 0) (h1 : ∃ i, o i = 1) {m q : ℕ}
    (hm : 0 < m) (hq : 0 < q) :
    Real.exp (-(2 * B + 3 * D)) * (admissibleSumPot o f m * admissibleSumPot o f q) ≤
      periodicPartition o f (m + q + 2) := by
  classical
  have : Nonempty ι := ⟨h0.choose⟩
  set F := periodicFinset o (m + q + 2)
  set w : (ℤ → ι × ZMod 2) → ℝ := fun x => Real.exp (birkhoffSum (shift 1) f (m + q + 2) x)
  have hmaps : ∀ x ∈ F, block m x ∈ Finset.univ.filter fun u => IsAdmissible o u :=
    fun x hx => Finset.mem_filter.2 ⟨Finset.mem_univ _,
      isAdmissible_block (mem_subshift_of_mem_periodicFinset hx) m⟩
  have hfib : ∀ u ∈ Finset.univ.filter fun u : Fin m → ι × ZMod 2 => IsAdmissible o u,
      Real.exp (-(2 * B + 3 * D)) * (Real.exp (cylSup o f m u) * admissibleSumPot o f q) ≤
        ∑ x ∈ F with block m x = u, w x := by
    intro u hu
    obtain ⟨y, hy, hyu⟩ := exists_mem_cylinder_of_isAdmissible (Finset.mem_filter.1 hu).2
    have hbu : block m y = u := funext fun k => hyu k
    have hc := (h.cylSup_bounds hy hyu).2
    have key := h.exp_mul_admissibleSumPot_le_sum_periodicFinset h0 h1 hy hm hq
    have hfilt : (F.filter fun x => block m x = u) =
        F.filter (· ∈ cylinder (block m y)) := by
      refine Finset.filter_congr fun x _ => ?_
      rw [cylinder_eq_preimage, Set.mem_preimage, Set.mem_singleton_iff, hbu]
    rw [hfilt]
    refine le_trans ?_ key
    rw [← mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_)
      (h.admissibleSumPot_pos q).le
    linarith
  calc Real.exp (-(2 * B + 3 * D)) * (admissibleSumPot o f m * admissibleSumPot o f q)
      = ∑ u ∈ Finset.univ.filter fun u : Fin m → ι × ZMod 2 => IsAdmissible o u,
          Real.exp (-(2 * B + 3 * D)) *
            (Real.exp (cylSup o f m u) * admissibleSumPot o f q) := by
        rw [admissibleSumPot, ← Finset.sum_filter, Finset.sum_mul, Finset.mul_sum]
    _ ≤ ∑ u ∈ Finset.univ.filter fun u : Fin m → ι × ZMod 2 => IsAdmissible o u,
          ∑ x ∈ F with block m x = u, w x := Finset.sum_le_sum hfib
    _ = periodicPartition o f (m + q + 2) := Finset.sum_fiberwise_of_maps_to hmaps w

theorem HasBoundedDistortion.exp_mul_admissibleSumPot_mul_le
    (h : HasBoundedDistortion o f B D) (h0 : ∃ i, o i = 0) (h1 : ∃ i, o i = 1) {m q : ℕ}
    (hm : 0 < m) (hq : 0 < q) :
    Real.exp (-(2 * B + 4 * D)) * (admissibleSumPot o f m * admissibleSumPot o f q) ≤
      admissibleSumPot o f (m + q + 2) := by
  have : Nonempty ι := ⟨h0.choose⟩
  have h1' := h.exp_mul_admissibleSumPot_mul_le_periodicPartition h0 h1 hm hq
  have h2 := h.periodicPartition_le_admissibleSumPot (o := o) (f := f) (p := m + q + 2)
    (by omega)
  have e : Real.exp (-(2 * B + 3 * D)) = Real.exp D * Real.exp (-(2 * B + 4 * D)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e, mul_assoc] at h1'
  exact le_of_mul_le_mul_left (h1'.trans h2) (Real.exp_pos D)

theorem HasBoundedDistortion.exp_mul_pressureZPot_le_admissibleSumPot [Nonempty ι]
    (h : HasBoundedDistortion o f B D) (h0 : ∃ i, o i = 0) {n : ℕ} (hn : 0 < n) :
    Real.exp (n * pressureZPot o f) ≤ admissibleSumPot o f n := by
  have hL : Tendsto (fun n : ℕ => -Real.log (admissibleSumPot o f n) / n) atTop
      (𝓝 (-pressureZPot o f)) := by
    simpa only [neg_div] using (h.tendsto_pressureZPot_admissibleSumPot h0).neg
  have key := le_mul_of_superadditive (a := fun n => -Real.log (admissibleSumPot o f n))
    (fun m n _ _ => by linarith [h.subadditive_log_admissibleSumPot m n]) hL hn
  rw [← Real.le_log_iff_exp_le (h.admissibleSumPot_pos n)]
  linarith

theorem HasBoundedDistortion.exists_admissibleSumPot_le (h : HasBoundedDistortion o f B D)
    (h0 : ∃ i, o i = 0) (h1 : ∃ i, o i = 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      admissibleSumPot o f n ≤ K * Real.exp (n * pressureZPot o f) := by
  have : Nonempty ι := ⟨h0.choose⟩
  have hA := h.admissibleSumPot_pos (o := o) (f := f)
  set c : ℝ := Real.exp (-(2 * B + 4 * D)) / admissibleSumPot o f 2
  have hc : 0 < c := div_pos (Real.exp_pos _) (hA 2)
  have hsup : ∀ m q : ℕ, 0 < m → 0 < q →
      c * admissibleSumPot o f m * (c * admissibleSumPot o f q) ≤
        c * admissibleSumPot o f (m + q) := by
    intro m q hm hq
    have h2 := h.exp_mul_admissibleSumPot_mul_le h0 h1 hm hq
    have h3 := h.admissibleSumPot_add_le (m + q) 2
    have h4 : c * (admissibleSumPot o f m * admissibleSumPot o f q) ≤
        admissibleSumPot o f (m + q) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (hA 2)]
      exact h2.trans h3
    calc c * admissibleSumPot o f m * (c * admissibleSumPot o f q)
        = c * (c * (admissibleSumPot o f m * admissibleSumPot o f q)) := by ring
      _ ≤ c * admissibleSumPot o f (m + q) := mul_le_mul_of_nonneg_left h4 hc.le
  have hL : Tendsto (fun n : ℕ => Real.log (c * admissibleSumPot o f n) / n) atTop
      (𝓝 (pressureZPot o f)) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (Real.log c)).add
      (h.tendsto_pressureZPot_admissibleSumPot h0)
    rw [zero_add] at this
    refine this.congr fun n => ?_
    rw [Real.log_mul hc.ne' (hA n).ne', add_div]
  refine ⟨c⁻¹, inv_pos.2 hc, fun n hn => ?_⟩
  have key := le_mul_of_superadditive (a := fun n => Real.log (c * admissibleSumPot o f n))
    (fun m q hm hq => by
      rw [← Real.log_mul (mul_pos hc (hA m)).ne' (mul_pos hc (hA q)).ne']
      exact Real.log_le_log (mul_pos (mul_pos hc (hA m)) (mul_pos hc (hA q)))
        (hsup m q hm hq)) hL hn
  rw [Real.log_le_iff_le_exp (mul_pos hc (hA n))] at key
  calc admissibleSumPot o f n = c⁻¹ * (c * admissibleSumPot o f n) := by
        field_simp
    _ ≤ c⁻¹ * Real.exp (n * pressureZPot o f) :=
        mul_le_mul_of_nonneg_left key (inv_pos.2 hc).le

theorem HasBoundedDistortion.exp_le_periodicPartition (h : HasBoundedDistortion o f B D)
    (h0 : ∃ i, o i = 0) (h1 : ∃ i, o i = 1) {q : ℕ} (hq : 0 < q) :
    Real.exp (-(2 * B + 3 * D) + (q + 1) * pressureZPot o f) ≤ periodicPartition o f (q + 3) := by
  have : Nonempty ι := ⟨h0.choose⟩
  have key := h.exp_mul_admissibleSumPot_mul_le_periodicPartition h0 h1 one_pos hq
  rw [show 1 + q + 2 = q + 3 by ring] at key
  refine le_trans ?_ key
  have hA1 := h.exp_mul_pressureZPot_le_admissibleSumPot h0 one_pos
  have hAq := h.exp_mul_pressureZPot_le_admissibleSumPot h0 hq
  rw [Nat.cast_one, one_mul] at hA1
  calc Real.exp (-(2 * B + 3 * D) + (q + 1) * pressureZPot o f)
      = Real.exp (-(2 * B + 3 * D)) *
          (Real.exp (pressureZPot o f) * Real.exp (q * pressureZPot o f)) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-(2 * B + 3 * D)) * (admissibleSumPot o f 1 * admissibleSumPot o f q) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hA1 hAq (Real.exp_pos _).le
          (h.admissibleSumPot_pos 1).le) (Real.exp_pos _).le

open Classical in

theorem HasBoundedDistortion.exists_periodic_cylinder_bounds (h : HasBoundedDistortion o f B D)
    (h0 : ∃ i, o i = 0) (h1 : ∃ i, o i = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ y ∈ subshift o, ∀ m : ℕ, 0 < m → m ≤ N →
      C⁻¹ * Real.exp (-(m * pressureZPot o f) + birkhoffSum (shift 1) f m y) ≤
          (∑ x ∈ (periodicFinset o (N + 4)).filter (· ∈ cylinder (block m y)),
            Real.exp (birkhoffSum (shift 1) f (N + 4) x)) / periodicPartition o f (N + 4) ∧
        (∑ x ∈ (periodicFinset o (N + 4)).filter (· ∈ cylinder (block m y)),
            Real.exp (birkhoffSum (shift 1) f (N + 4) x)) / periodicPartition o f (N + 4) ≤
          C * Real.exp (-(m * pressureZPot o f) + birkhoffSum (shift 1) f m y) := by
  have : Nonempty ι := ⟨h0.choose⟩
  obtain ⟨K, hK, hAK⟩ := h.exists_admissibleSumPot_le h0 h1
  set P := pressureZPot o f
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hy₀ := tau_mem_subshift (o := o) fun _ => i
  have hB : 0 ≤ B := (abs_nonneg _).trans (h.abs_le_bound _ hy₀)
  have hD : 0 ≤ D := by
    have := h.distortion 0 _ hy₀ _ hy₀ fun _ _ => rfl
    rwa [sub_self, abs_zero] at this
  refine ⟨K * Real.exp (2 * B + 4 * D + 2 * |P|), mul_pos hK (Real.exp_pos _),
    fun N y hy m hm hmN => ?_⟩
  set S := birkhoffSum (shift 1) f m y
  set num := ∑ x ∈ (periodicFinset o (N + 4)).filter (· ∈ cylinder (block m y)),
    Real.exp (birkhoffSum (shift 1) f (N + 4) x)
  set Z := periodicPartition o f (N + 4)
  have hP1 := le_abs_self P
  have hP2 := neg_abs_le P

  have hZlow : Real.exp (-(2 * B + 3 * D) + ((N : ℝ) + 2) * P) ≤ Z := by
    have := h.exp_le_periodicPartition h0 h1 (q := N + 1) (Nat.succ_pos N)
    rw [show N + 1 + 3 = N + 4 by ring] at this
    convert this using 3
    push_cast; ring
  have hZpos : 0 < Z := (Real.exp_pos _).trans_le hZlow
  have hZupp : Z ≤ K * Real.exp (D + ((N : ℝ) + 4) * P) := by
    have h1' := h.periodicPartition_le_admissibleSumPot (o := o) (f := f) (p := N + 4)
      (by omega)
    have h2' := hAK (N + 4) (by omega)
    calc Z ≤ Real.exp D * admissibleSumPot o f (N + 4) := h1'
      _ ≤ Real.exp D * (K * Real.exp (((N + 4 : ℕ) : ℝ) * P)) :=
          mul_le_mul_of_nonneg_left h2' (Real.exp_pos _).le
      _ = K * Real.exp (D + ((N : ℝ) + 4) * P) := by
          rw [Real.exp_add]; push_cast; ring

  obtain ⟨k, hk⟩ : ∃ k, N + 4 = m + k := ⟨N + 4 - m, by omega⟩
  have hkc : ((N : ℝ) + 4) = m + k := by exact_mod_cast hk
  have hnumupp : num ≤ K * Real.exp (S + D + k * P) := by
    have h1' := h.sum_periodicFinset_cylinder_le hy m k (by omega)
    have h2' := hAK k (by omega)
    simp only [num, hk]
    calc _ ≤ Real.exp (S + D) * admissibleSumPot o f k := h1'
      _ ≤ Real.exp (S + D) * (K * Real.exp (k * P)) :=
          mul_le_mul_of_nonneg_left h2' (Real.exp_pos _).le
      _ = K * Real.exp (S + D + k * P) := by rw [Real.exp_add (S + D)]; ring
  obtain ⟨q, hq⟩ : ∃ q, N + 4 = m + q + 2 := ⟨N + 2 - m, by omega⟩
  have hqc : ((N : ℝ) + 4) = m + q + 2 := by exact_mod_cast hq
  have hnumlow : Real.exp (S - (2 * B + 2 * D) + q * P) ≤ num := by
    have h1' := h.exp_mul_admissibleSumPot_le_sum_periodicFinset h0 h1 hy hm
      (q := q) (by omega)
    have h2' := h.exp_mul_pressureZPot_le_admissibleSumPot h0 (n := q) (by omega)
    simp only [num, hq]
    calc Real.exp (S - (2 * B + 2 * D) + q * P)
        = Real.exp (S - (2 * B + 2 * D)) * Real.exp (q * P) := Real.exp_add _ _
      _ ≤ Real.exp (S - (2 * B + 2 * D)) * admissibleSumPot o f q :=
          mul_le_mul_of_nonneg_left h2' (Real.exp_pos _).le
      _ ≤ _ := h1'
  constructor
  · rw [le_div_iff₀ hZpos]
    calc (K * Real.exp (2 * B + 4 * D + 2 * |P|))⁻¹ * Real.exp (-(m * P) + S) * Z
        ≤ (K * Real.exp (2 * B + 4 * D + 2 * |P|))⁻¹ * Real.exp (-(m * P) + S) *
            (K * Real.exp (D + ((N : ℝ) + 4) * P)) :=
          mul_le_mul_of_nonneg_left hZupp (by positivity)
      _ = Real.exp (-(2 * B + 4 * D + 2 * |P|) + (-(m * P) + S) + (D + ((N : ℝ) + 4) * P)) := by
          rw [Real.exp_add (-(2 * B + 4 * D + 2 * |P|) + (-(m * P) + S)),
            Real.exp_add (-(2 * B + 4 * D + 2 * |P|)), Real.exp_neg]
          field_simp
      _ ≤ Real.exp (S - (2 * B + 2 * D) + q * P) := by
          refine Real.exp_le_exp.2 ?_
          have e : ((N : ℝ) + 4) * P = m * P + q * P + 2 * P := by rw [hqc]; ring
          rw [e]
          linarith
      _ ≤ num := hnumlow
  · rw [div_le_iff₀ hZpos]
    calc num ≤ K * Real.exp (S + D + k * P) := hnumupp
      _ ≤ K * Real.exp (2 * B + 4 * D + 2 * |P| + (-(m * P) + S) +
            (-(2 * B + 3 * D) + ((N : ℝ) + 2) * P)) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK.le
          have e : ((N : ℝ) + 2) * P = m * P + k * P - 2 * P := by
            have : ((N : ℝ) + 2) = m + k - 2 := by linarith
            rw [this]; ring
          rw [e]
          linarith
      _ = K * Real.exp (2 * B + 4 * D + 2 * |P|) * Real.exp (-(m * P) + S) *
            Real.exp (-(2 * B + 3 * D) + ((N : ℝ) + 2) * P) := by
          rw [Real.exp_add, Real.exp_add]; ring
      _ ≤ K * Real.exp (2 * B + 4 * D + 2 * |P|) * Real.exp (-(m * P) + S) * Z :=
          mul_le_mul_of_nonneg_left hZlow (by positivity)

end Bounds

end FractalGeometry
