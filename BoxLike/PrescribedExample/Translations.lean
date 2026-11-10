module

/-
The translation cube and strong separation of `ex:projection_double_dimensional`, tex lines
2956 to 2965: with `R = 2/(1 - 2a)` and `B = (0, R, 0, R, 0, 0, R, R) + [0, 1]^8`, every
`t ∈ B` makes the four maps send `[0, 2R]^2` into itself, each coordinate of an image rectangle
lies in `[0, R - 1]` or in `[R, 2R - 1]`, the four image rectangles are at mutual distance at
least one, and the strong separation condition holds.

* `PrescribedExample.R`, `PrescribedExample.two_mul_a_mul_R_add_one`: `R = 2/(1 - 2a)` and
  `2aR + 1 = R - 1`.
* `PrescribedExample.lo`, `PrescribedExample.cube`, `PrescribedExample.square`: the corner
  `(0, R, 0, R, 0, 0, R, R)`, the cube `B` and the square `[0, 2R]^2`.
* `PrescribedExample.phi_fst_mem`, `PrescribedExample.phi_snd_mem`: the coordinates of an image
  of `[0, 2R]^2` lie in the intervals `[l, l + R - 1]` given by the corner.
* `PrescribedExample.phi_image_square_subset`: `φ_i([0, 2R]^2) ⊆ [0, 2R]^2`.
* `PrescribedExample.one_le_dist_phi`, `PrescribedExample.disjoint_phi_image_square`: the image
  rectangles are separated by gaps of at least one.
* `PrescribedExample.attractor_subset_square`, `PrescribedExample.strongSeparation`,
  `PrescribedExample.strongOpenSet`: `X ⊆ [0, 2R]^2`, the strong separation condition and the
  strong open set condition for every `t ∈ B`.
-/
public import BoxLike.PrescribedExample.Pressure

@[expose] public section

namespace BoxLike

namespace PrescribedExample

open Set

variable (P : Params)

/-- The number `R = 2/(1 - 2a)` of `ex:projection_double_dimensional`. -/
noncomputable def R : ℝ := 2 / (1 - 2 * P.a)

/-- `1 - 2a > 0`, since `a < 1/2`. -/
theorem one_sub_two_mul_a_pos : 0 < 1 - 2 * P.a := by linarith [P.a_lt_half]

/-- `R > 2`. -/
theorem two_lt_R : 2 < R P := by
  have h := one_sub_two_mul_a_pos P
  rw [R, lt_div_iff₀ h]
  nlinarith [P.a_pos]

/-- `R > 0`. -/
theorem R_pos : 0 < R P := lt_trans two_pos (two_lt_R P)

/-- `2aR + 1 = R - 1` (`ex:projection_double_dimensional`). -/
theorem two_mul_a_mul_R_add_one : 2 * P.a * R P + 1 = R P - 1 := by
  have h := (one_sub_two_mul_a_pos P).ne'
  rw [R]
  field_simp
  ring

/-- The corner `(0, R, 0, R, 0, 0, R, R)` of the translation cube of
`ex:projection_double_dimensional`. The coordinate `i` of a translation is the first and the
coordinate `i + 4` the second coordinate of the translation of the map `i`. -/
noncomputable def lo : Fin 8 → ℝ := ![0, R P, 0, R P, 0, 0, R P, R P]

/-- The translation cube `B = (0, R, 0, R, 0, 0, R, R) + [0, 1]^8` of
`ex:projection_double_dimensional`. -/
noncomputable def cube : Set (Fin 8 → ℝ) := Set.pi univ fun q => Icc (lo P q) (lo P q + 1)

/-- The square `[0, 2R]^2` of `ex:projection_double_dimensional`. -/
noncomputable def square : Set (ℝ × ℝ) := Icc 0 (2 * R P) ×ˢ Icc 0 (2 * R P)

/-- Every coordinate of the corner of the cube is `0` or `R`. -/
theorem lo_eq (q : Fin 8) : lo P q = 0 ∨ lo P q = R P := by
  fin_cases q <;> simp [lo]

/-- The coordinates of the corner of the cube lie in `[0, R]`. -/
theorem lo_mem (q : Fin 8) : lo P q ∈ Icc 0 (R P) := by
  rcases lo_eq P q with h | h <;> rw [h]
  · exact ⟨le_rfl, (R_pos P).le⟩
  · exact ⟨(R_pos P).le, le_rfl⟩

/-- The square `[0, 2R]^2` is compact. -/
theorem isCompact_square : IsCompact (square P) := isCompact_Icc.prod isCompact_Icc

/-- The square `[0, 2R]^2` is non-empty. -/
theorem square_nonempty : (square P).Nonempty := by
  have h : (0 : ℝ) ∈ Icc 0 (2 * R P) := ⟨le_rfl, by linarith [R_pos P]⟩
  exact ⟨(0, 0), h, h⟩

/-- Both coordinates of a point of `[0, 2R]^2` lie in `[0, 2R]`. -/
theorem coord_mem_square {z : ℝ × ℝ} (hz : z ∈ square P) (c : ZMod 2) :
    System.coord c z ∈ Icc 0 (2 * R P) := by
  rcases zmod_two_cases c with rfl | rfl
  · exact hz.1
  · exact hz.2

variable {P} {t : Fin 8 → ℝ}

/-- The first coordinate of `φ_i(z)` for `z ∈ [0, 2R]^2` and `t ∈ B` lies in `[l, l + R - 1]`,
where `l ∈ {0, R}` is the corner of the translation interval of `t_i`
(`ex:projection_double_dimensional`). -/
theorem phi_fst_mem (ht : t ∈ cube P) (i : Fin 4) {z : ℝ × ℝ} (hz : z ∈ square P) :
    ((sys P t).phi i z).1 ∈ Icc (lo P (Fin.castAdd 4 i)) (lo P (Fin.castAdd 4 i) + R P - 1) := by
  have hc := coord_mem_square P hz (orient i)
  have hq := ht (Fin.castAdd 4 i) (mem_univ _)
  have h2 := two_mul_a_mul_R_add_one P
  have ha := P.a_pos
  simp only [System.phi, sys_a, sys_o]
  change P.a * System.coord (orient i) z + t (Fin.castAdd 4 i) ∈ _
  constructor
  · nlinarith [hc.1, hq.1]
  · nlinarith [hc.2, hq.2]

/-- The second coordinate of `φ_i(z)` for `z ∈ [0, 2R]^2` and `t ∈ B` lies in `[l, l + R - 1]`,
where `l ∈ {0, R}` is the corner of the translation interval of `t_{i+4}`; here `b < a` is
used (`ex:projection_double_dimensional`). -/
theorem phi_snd_mem (ht : t ∈ cube P) (i : Fin 4) {z : ℝ × ℝ} (hz : z ∈ square P) :
    ((sys P t).phi i z).2 ∈ Icc (lo P (Fin.natAdd 4 i)) (lo P (Fin.natAdd 4 i) + R P - 1) := by
  have hc := coord_mem_square P hz (orient i + 1)
  have hq := ht (Fin.natAdd 4 i) (mem_univ _)
  have h2 := two_mul_a_mul_R_add_one P
  have hb := P.b_pos
  have hab := P.b_lt_a
  have hR := R_pos P
  simp only [System.phi, sys_b, sys_o]
  change P.b * System.coord (orient i + 1) z + t (Fin.natAdd 4 i) ∈ _
  constructor
  · nlinarith [hc.1, hq.1]
  · nlinarith [hc.2, hq.2]

/-- For every `t ∈ B` the four maps of `ex:projection_double_dimensional` send `[0, 2R]^2` into
itself. -/
theorem phi_image_square_subset (ht : t ∈ cube P) (i : Fin 4) :
    (sys P t).phi i '' square P ⊆ square P := by
  rintro _ ⟨z, hz, rfl⟩
  have h1 := phi_fst_mem ht i hz
  have h2 := phi_snd_mem ht i hz
  have l1 := lo_mem P (Fin.castAdd 4 i)
  have l2 := lo_mem P (Fin.natAdd 4 i)
  exact ⟨⟨by linarith [h1.1, l1.1], by linarith [h1.2, l1.2]⟩,
    ⟨by linarith [h2.1, l2.1], by linarith [h2.2, l2.2]⟩⟩

/-- Two points of the intervals `[l, l + R - 1]` and `[l', l' + R - 1]` with distinct corners
`l, l' ∈ {0, R}` are at distance at least one. -/
theorem one_le_abs_sub_of_lo_ne {q q' : Fin 8} (hqq' : lo P q ≠ lo P q') {x x' : ℝ}
    (hx : x ∈ Icc (lo P q) (lo P q + R P - 1)) (hx' : x' ∈ Icc (lo P q') (lo P q' + R P - 1)) :
    1 ≤ |x - x'| := by
  rcases lo_eq P q with h | h <;> rcases lo_eq P q' with h' | h' <;>
    rw [h, h'] at hqq' <;> rw [h] at hx <;> rw [h'] at hx'
  · exact absurd rfl hqq'
  · rw [abs_sub_comm, le_abs]; left; linarith [hx.2, hx'.1]
  · rw [le_abs]; left; linarith [hx.1, hx'.2]
  · exact absurd rfl hqq'

/-- The four maps of `ex:projection_double_dimensional` occupy different pairs of translation
intervals. -/
theorem lo_ne_or_lo_ne {i j : Fin 4} (hij : i ≠ j) :
    lo P (Fin.castAdd 4 i) ≠ lo P (Fin.castAdd 4 j) ∨
      lo P (Fin.natAdd 4 i) ≠ lo P (Fin.natAdd 4 j) := by
  have hR := (R_pos P).ne'
  fin_cases i <;> fin_cases j <;> simp_all [lo, Fin.castAdd, Fin.natAdd, eq_comm]

/-- For every `t ∈ B`, the image rectangles `φ_i([0, 2R]^2)` and `φ_j([0, 2R]^2)` of distinct
maps of `ex:projection_double_dimensional` are separated by a gap of at least one. -/
theorem one_le_dist_phi (ht : t ∈ cube P) {i j : Fin 4} (hij : i ≠ j) {z z' : ℝ × ℝ}
    (hz : z ∈ square P) (hz' : z' ∈ square P) :
    1 ≤ dist ((sys P t).phi i z) ((sys P t).phi j z') := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  rcases lo_ne_or_lo_ne (P := P) hij with h | h
  · exact le_max_of_le_left
      (one_le_abs_sub_of_lo_ne h (phi_fst_mem ht i hz) (phi_fst_mem ht j hz'))
  · exact le_max_of_le_right
      (one_le_abs_sub_of_lo_ne h (phi_snd_mem ht i hz) (phi_snd_mem ht j hz'))

/-- For every `t ∈ B`, the image rectangles of distinct maps of
`ex:projection_double_dimensional` are disjoint. -/
theorem disjoint_phi_image_square (ht : t ∈ cube P) {i j : Fin 4} (hij : i ≠ j) :
    Disjoint ((sys P t).phi i '' square P) ((sys P t).phi j '' square P) := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨z, hz, rfl⟩ ⟨z', hz', h⟩
  have := one_le_dist_phi ht hij hz hz'
  rw [← h, dist_self] at this
  exact absurd this (by norm_num)

/-- For every `t ∈ B`, the self-affine set of `ex:projection_double_dimensional` lies in
`[0, 2R]^2`. -/
theorem attractor_subset_square (ht : t ∈ cube P) : (sys P t).attractor ⊆ square P :=
  (sys P t).attractor_subset_of_invariant (isCompact_square P) (square_nonempty P)
    (phi_image_square_subset ht)

/-- Every `t ∈ B` gives the strong separation condition (`ex:projection_double_dimensional`). -/
theorem strongSeparation (ht : t ∈ cube P) : (sys P t).StrongSeparation :=
  (sys P t).strongSeparation_of_invariant (isCompact_square P) (square_nonempty P)
    (phi_image_square_subset ht) fun _ _ hij => disjoint_phi_image_square ht hij

/-- Every `t ∈ B` gives the strong open set condition (`ex:projection_double_dimensional`). -/
theorem strongOpenSet (ht : t ∈ cube P) : (sys P t).StrongOpenSet :=
  (strongSeparation ht).strongOpenSet

end PrescribedExample

end BoxLike
