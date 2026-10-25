/- Adapted from this LOT tree, o078, session x0260, commit 34c7136a25cd.
   Original file: Submission/Lib/K4ExactMeasureTools/QuadraticCurves.lean -/
/-
Adapted from: here:o078
-/
import Submission.Obl.k4_scalar_grid_parameter_preparation.CurveCells

namespace Submission.Obl.k4_scalar_grid_parameter_preparation


noncomputable def integerGridExpand {d : ℕ} (r : ℤ) (Q : Finset (Fin d → ℤ)) :
    Finset (Fin d → ℤ) := by
  classical
  exact Q.biUnion (fun z => Fintype.piFinset
    (fun j => Finset.Icc (z j - r) (z j + r)))

theorem integerGridExpand_card {d : ℕ} (r : ℤ) (hr : 0 ≤ r)
    (Q : Finset (Fin d → ℤ)) :
    ((integerGridExpand r Q).card : ℝ) ≤ (Q.card : ℝ) * (4 * (r : ℝ) + 3) ^ d := by
  classical
  let box (z : Fin d → ℤ) := Fintype.piFinset
    (fun j => Finset.Icc (z j - r) (z j + r))
  have hcard (z : Fin d → ℤ) : ((box z).card : ℝ) ≤ (4 * (r : ℝ) + 3) ^ d := by
    have hh := Submission.Lib.K4IncidenceWitnesses.card_pi_grid_of_diameter
      (box z) (R := 2 * (r : ℝ)) (by positivity) (by
        intro x hx y hy j
        have hx' := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hx j)
        have hy' := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hy j)
        have hi : |x j - y j| ≤ 2 * r := abs_le.mpr ⟨by omega, by omega⟩
        exact_mod_cast hi)
    simpa only [Fintype.card_fin, show (2 : ℝ) * (2 * (r : ℝ)) + 3 = 4 * (r : ℝ) + 3 by ring]
      using hh
  calc
    _ ≤ ∑ z ∈ Q, ((box z).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := Q) (t := box))
    _ ≤ ∑ _z ∈ Q, (4 * (r : ℝ) + 3) ^ d := Finset.sum_le_sum (fun z _ => hcard z)
    _ = _ := by simp

theorem mem_integerGridExpand_of_coordinate_close {d : ℕ} {r : ℤ} {h : ℝ}
    (hh : 0 < h) (Q : Finset (Fin d → ℤ)) (x y : Fin d → ℝ)
    (hy : (fun j => ⌊y j / h⌋) ∈ Q)
    (hclose : ∀ j, |x j - y j| ≤ (r : ℝ) * h) :
    (fun j => ⌊x j / h⌋) ∈ integerGridExpand r Q := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨_, hy, Fintype.mem_piFinset.mpr ?_⟩
  intro j
  have hdiv : |x j / h - y j / h| ≤ (r : ℝ) := by
    rw [← sub_div, abs_div, abs_of_pos hh]
    exact (div_le_iff₀ hh).mpr (hclose j)
  have hlo := Int.floor_mono (show y j / h - (r : ℝ) ≤ x j / h by linarith [abs_le.mp hdiv])
  have hhi := Int.floor_mono (show x j / h ≤ y j / h + (r : ℝ) by linarith [abs_le.mp hdiv])
  exact Finset.mem_Icc.mpr (by
    simpa only [Int.floor_sub_intCast, Int.floor_add_intCast] using And.intro hlo hhi)


def quadraticCoordinates (b : Fin 5 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  ![t, b 0 + t * b 1, b 2 + t * b 3 + t ^ 2 * b 4]

noncomputable def quadraticCoordinateCode (h : ℝ) (b : Fin 5 → ℝ) (t : ℝ) : Fin 3 → ℤ :=
  fun j => ⌊quadraticCoordinates b t j / h⌋

theorem quadratic_coordinates_coefficient_error {b b₀ : Fin 5 → ℝ} {r t : ℝ}
    (hr : 0 ≤ r) (hb : ∀ j, |b j - b₀ j| ≤ r) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∀ j, |quadraticCoordinates b t j - quadraticCoordinates b₀ t j| ≤ 3 * r := by
  have ht₁ : |t| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  have ht₂ : |t ^ 2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg t)]; nlinarith only [ht.1, ht.2]
  have hprod (j : Fin 5) : |t| * |b j - b₀ j| ≤ r := by
    simpa only [one_mul] using mul_le_mul ht₁ (hb j) (abs_nonneg _) zero_le_one
  have hprod₂ (j : Fin 5) : |t ^ 2| * |b j - b₀ j| ≤ r := by
    simpa only [one_mul] using mul_le_mul ht₂ (hb j) (abs_nonneg _) zero_le_one
  intro j
  fin_cases j
  · change |t - t| ≤ 3 * r
    simp only [sub_self, abs_zero]
    positivity
  · change |(b 0 + t * b 1) - (b₀ 0 + t * b₀ 1)| ≤ 3 * r
    calc
      _ = |(b 0 - b₀ 0) + t * (b 1 - b₀ 1)| := by congr 1; ring
      _ ≤ |b 0 - b₀ 0| + |t * (b 1 - b₀ 1)| := abs_add_le _ _
      _ ≤ _ := by rw [abs_mul]; linarith only [hb 0, hprod 1, hr]
  · change |(b 2 + t * b 3 + t ^ 2 * b 4) -
        (b₀ 2 + t * b₀ 3 + t ^ 2 * b₀ 4)| ≤ 3 * r
    calc
      _ = |(b 2 - b₀ 2) + t * (b 3 - b₀ 3) + t ^ 2 * (b 4 - b₀ 4)| := by congr 1; ring
      _ ≤ |b 2 - b₀ 2| + |t * (b 3 - b₀ 3)| + |t ^ 2 * (b 4 - b₀ 4)| := abs_add_three _ _ _
      _ ≤ _ := by rw [abs_mul, abs_mul]; linarith only [hb 2, hprod 3, hprod₂ 4]

theorem quadratic_coordinates_time_lipschitz (b : Fin 5 → ℝ) {K : ℝ}
    (hK : 1 ≤ K) (hb : ∀ j, |b j| ≤ K)
    {t s : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ∀ j, |quadraticCoordinates b t j - quadraticCoordinates b s j| ≤ 9 * K * |t - s| := by
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hsum : |t + s| ≤ 2 := by rw [abs_of_nonneg (add_nonneg ht.1 hs.1)]; linarith only [ht.2, hs.2]
  have hcoeff : |b 3 + (t + s) * b 4| ≤ 3 * K := by
    calc
      _ ≤ |b 3| + |t + s| * |b 4| := by simpa only [abs_mul] using abs_add_le (b 3) ((t + s) * b 4)
      _ ≤ K + 2 * K := add_le_add (hb 3) (mul_le_mul hsum (hb 4) (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  intro j
  fin_cases j
  · change |t - s| ≤ 9 * K * |t - s|
    nlinarith only [hK, abs_nonneg (t - s)]
  · change |(b 0 + t * b 1) - (b 0 + s * b 1)| ≤ 9 * K * |t - s|
    calc
      _ = |b 1 * (t - s)| := by congr 1; ring
      _ = |b 1| * |t - s| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right ((hb 1).trans (by linarith only [hK])) (abs_nonneg _)
  · change |(b 2 + t * b 3 + t ^ 2 * b 4) - (b 2 + s * b 3 + s ^ 2 * b 4)| ≤ 9 * K * |t - s|
    calc
      _ = |(b 3 + (t + s) * b 4) * (t - s)| := by congr 1; ring
      _ = |b 3 + (t + s) * b 4| * |t - s| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (hcoeff.trans (by linarith only [hK₀])) (abs_nonneg _)

theorem quadratic_coordinate_grid_cover_linear (b : Fin 5 → ℝ) {K h : ℝ}
    (hK : 1 ≤ K) (hb : ∀ j, |b j| ≤ K) (hh : 0 < h) (hh₁ : h ≤ 1) :
    ∃ Q : Finset (Fin 3 → ℤ), (Q.card : ℝ) ≤ 5000 * K / h ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, quadraticCoordinateCode h b t ∈ Q := by
  have hK₀ : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let D : ℕ := ⌈9 * K / h⌉₊
  have hD : 1 ≤ D := Nat.ceil_pos.mpr (by positivity)
  have hscale : 9 * K ≤ (D : ℝ) * h :=
    (div_le_iff₀ hh).mp (Nat.le_ceil (9 * K / h))
  obtain ⟨Q, hQ, hcover⟩ := exists_curve_grid_cover (quadraticCoordinates b)
    (show 0 ≤ 9 * K by positivity) hh D hD hscale
    (fun t ht s hs j => quadratic_coordinates_time_lipschitz b hK hb ht hs j)
  have hQ' : (Q.card : ℝ) ≤ ((D : ℝ) + 1) * 343 := by norm_num at hQ ⊢; exact hQ
  have hceil : (D : ℝ) < 9 * (K / h) + 1 := by
    have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ 9 * K / h)
    convert h using 1
    ring
  have hKh : 1 ≤ K / h := (le_div_iff₀ hh).mpr (by simpa only [one_mul] using hh₁.trans hK)
  have hDsum : (D : ℝ) + 1 ≤ 11 * K / h := by
    have heq : 11 * K / h = 11 * (K / h) := by ring
    rw [heq]
    linarith
  refine ⟨Q, hQ'.trans ?_, hcover⟩
  calc
    ((D : ℝ) + 1) * 343 ≤ (11 * K / h) * 343 :=
      mul_le_mul_of_nonneg_right hDsum (by norm_num)
    _ = 3773 * (K / h) := by ring
    _ ≤ 5000 * (K / h) := mul_le_mul_of_nonneg_right (by norm_num) (div_nonneg hK₀.le hh.le)
    _ = _ := by ring

theorem quadratic_coordinate_block_grid_cover (b₀ : Fin 5 → ℝ) {K h : ℝ}
    (hK : 1 ≤ K) (hb₀ : ∀ j, |b₀ j| ≤ K) (hh : 0 < h) (hh₁ : h ≤ 1) :
    ∃ Q : Finset (Fin 3 → ℤ), (Q.card : ℝ) ≤
        (5000 * 111 ^ 3) * K / h ∧
      ∀ b : Fin 5 → ℝ, (∀ j, |b j - b₀ j| ≤ h) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, quadraticCoordinateCode h b t ∈ Q := by
  obtain ⟨P, hP, hcover⟩ := quadratic_coordinate_grid_cover_linear b₀ hK hb₀ hh hh₁
  refine ⟨integerGridExpand 27 P, ?_, ?_⟩
  · calc
      _ ≤ (P.card : ℝ) * (4 * (27 : ℝ) + 3) ^ 3 := integerGridExpand_card 27 (by norm_num) P
      _ ≤ (5000 * K / h) * (4 * (27 : ℝ) + 3) ^ 3 :=
        mul_le_mul_of_nonneg_right hP (by positivity)
      _ = _ := by norm_num; ring
  · intro b hb t ht
    apply mem_integerGridExpand_of_coordinate_close hh P
      (quadraticCoordinates b t) (quadraticCoordinates b₀ t) (hcover t ht)
    intro j
    have hcoord := quadratic_coordinates_coefficient_error hh.le hb ht j
    norm_num
    linarith only [hcoord, hh]

theorem quadratic_coordinate_time_cell {b : Fin 5 → ℝ} {t h : ℝ} {z : Fin 3 → ℤ}
    (hh : 0 < h) (hcode : quadraticCoordinateCode h b t = z) :
    t ∈ Set.Ico (h * (z 0 : ℝ)) (h * ((z 0 : ℝ) + 1)) := by
  have hfloor : ⌊t / h⌋ = z 0 := congrFun hcode 0
  have ht := Int.floor_eq_iff.mp hfloor
  exact ⟨by simpa only [mul_comm] using (le_div_iff₀ hh).mp ht.1,
    by simpa only [mul_comm] using (div_lt_iff₀ hh).mp ht.2⟩

theorem quadratic_coordinate_derivative_error {b b₀ : Fin 5 → ℝ} {r q K t t₀ : ℝ}
    (_hr : 0 ≤ r) (hq : 0 ≤ q) (_hK : 0 ≤ K) (hb : ∀ j, |b j - b₀ j| ≤ r)
    (hb₀ : |b₀ 4| ≤ K) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hgap : |t - t₀| ≤ q) :
    |(b 3 + 2 * t * b 4) - (b₀ 3 + 2 * t₀ * b₀ 4)| ≤ 3 * r + 2 * K * q := by
  have hprod : |t - t₀| * |b₀ 4| ≤ q * K :=
    mul_le_mul hgap hb₀ (abs_nonneg _) hq
  have hcoeff : |t| * |b 4 - b₀ 4| ≤ r := by
    simpa only [one_mul] using mul_le_mul
      (show |t| ≤ 1 by simpa only [abs_of_nonneg ht.1] using ht.2)
      (hb 4) (abs_nonneg _) zero_le_one
  calc
    _ = |(b 3 - b₀ 3) + 2 * t * (b 4 - b₀ 4) + 2 * (t - t₀) * b₀ 4| := by congr 1; ring
    _ ≤ |b 3 - b₀ 3| + |2 * t * (b 4 - b₀ 4)| + |2 * (t - t₀) * b₀ 4| := abs_add_three _ _ _
    _ ≤ _ := by
      simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
      nlinarith only [hb 3, hcoeff, hprod]

end Submission.Obl.k4_scalar_grid_parameter_preparation
