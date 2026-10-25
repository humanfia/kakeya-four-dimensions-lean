import Submission.Obl.k4_scalar_pure_multiworld_homogenization.SelectionInterface
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Format

/-!
# Polynomial format of label selections

A set of common labels inside a box of radius `R` is read off from the signs of
`3 (2R + 2)` polynomials of degree at most three, namely the mesh and hidden-bin
boundaries `n^H φ_c - m`. Hence intersecting an event with such a label selection
keeps the frozen sign format, with an additive count budget.
-/

noncomputable section

namespace Submission.Obl.k4_scalar_pure_multiworld_homogenization

open MeasureTheory Set MvPolynomial

/-- The three label coordinates as polynomials in the event fibre coordinates
`(a₀, a₁, a₂, a₃, a₄, t)`. -/
def labelPoly : Fin 3 → MvPolynomial (Fin 6) ℝ :=
  ![X 5, X 0 + X 5 * X 1, X 2 + X 5 * X 3 + X 5 ^ 2 * X 4]

/-- The incidence with event-fibre coordinates `b`. -/
def fibrePoint (i : ℕ) (b : Fin 6 → ℝ) : Incidence :=
  ((i, fun e : Fin 5 => b e.castSucc), b 5)

theorem scalarLabel_fibrePoint (n : ℝ) (H : ℕ) (i : ℕ) (b : Fin 6 → ℝ) (c : Fin 3) :
    scalarLabel n H (fibrePoint i b) c = ⌊n ^ H * eval b (labelPoly c)⌋ := by
  fin_cases c <;> simp [scalarLabel, fibrePoint, labelPoly, y, x]

theorem labelPoly_degree (c : Fin 3) : (labelPoly c).totalDegree ≤ 3 := by
  fin_cases c
  · simp only [labelPoly]
    change (X 5 : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 3
    rw [totalDegree_X]
    norm_num
  · change (X 0 + X 5 * X 1 : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 3
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · rw [totalDegree_X]; norm_num
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X, totalDegree_X]
      norm_num
  · change (X 2 + X 5 * X 3 + X 5 ^ 2 * X 4 : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 3
    refine (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans (max_le ?_ ?_)) ?_)
    · rw [totalDegree_X]; norm_num
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X, totalDegree_X]
      norm_num
    · refine (totalDegree_mul _ _).trans ?_
      have h1 : (X 5 ^ 2 : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 2 := by
        refine (totalDegree_pow _ _).trans ?_
        rw [totalDegree_X]
      rw [totalDegree_X]
      omega

/-- The boundary test `n^H φ_c - (m - R)`. -/
def boundaryPoly (n : ℝ) (H R : ℕ) (q : Fin 3 × Fin (2 * R + 2)) : MvPolynomial (Fin 6) ℝ :=
  C (n ^ H) * labelPoly q.1 - C (((q.2 : ℕ) : ℝ) - (R : ℝ))

theorem boundaryPoly_degree (n : ℝ) (H R : ℕ) (q : Fin 3 × Fin (2 * R + 2)) :
    (boundaryPoly n H R q).totalDegree ≤ 3 := by
  unfold boundaryPoly
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact labelPoly_degree q.1
  · rw [totalDegree_C]
    norm_num

theorem eval_boundaryPoly (n : ℝ) (H R : ℕ) (q : Fin 3 × Fin (2 * R + 2)) (b : Fin 6 → ℝ) :
    eval b (boundaryPoly n H R q) =
      n ^ H * eval b (labelPoly q.1) - (((q.2 : ℕ) : ℝ) - (R : ℝ)) := by
  simp [boundaryPoly]

/-- Equal boundary signs force equal labels, for labels inside the box. -/
theorem floor_eq_of_boundary_signs {n : ℝ} {H R : ℕ} {b b' : Fin 6 → ℝ} (c : Fin 3)
    (hsign : ∀ q, SignType.sign (eval b (boundaryPoly n H R q)) =
      SignType.sign (eval b' (boundaryPoly n H R q)))
    (hbox : |⌊n ^ H * eval b (labelPoly c)⌋| ≤ (R : ℤ)) :
    ⌊n ^ H * eval b' (labelPoly c)⌋ = ⌊n ^ H * eval b (labelPoly c)⌋ := by
  set m := ⌊n ^ H * eval b (labelPoly c)⌋ with hm
  have hlo := Int.floor_le (n ^ H * eval b (labelPoly c))
  have hhi := Int.lt_floor_add_one (n ^ H * eval b (labelPoly c))
  rw [← hm] at hlo hhi
  obtain ⟨hR1, hR2⟩ := abs_le.mp hbox
  have hi1 : (m + R).toNat < 2 * R + 2 := by omega
  have hi2 : (m + R + 1).toNat < 2 * R + 2 := by omega
  have hc1 : (((m + R).toNat : ℕ) : ℝ) - (R : ℝ) = (m : ℝ) := by
    have : ((m + R).toNat : ℤ) = m + R := Int.toNat_of_nonneg (by omega)
    have h' : (((m + R).toNat : ℕ) : ℝ) = (m : ℝ) + (R : ℝ) := by exact_mod_cast this
    linarith
  have hc2 : (((m + R + 1).toNat : ℕ) : ℝ) - (R : ℝ) = (m : ℝ) + 1 := by
    have : ((m + R + 1).toNat : ℤ) = m + R + 1 := Int.toNat_of_nonneg (by omega)
    have h' : (((m + R + 1).toNat : ℕ) : ℝ) = (m : ℝ) + (R : ℝ) + 1 := by exact_mod_cast this
    linarith
  have hs1 := hsign (c, ⟨(m + R).toNat, hi1⟩)
  have hs2 := hsign (c, ⟨(m + R + 1).toNat, hi2⟩)
  simp only [eval_boundaryPoly, hc1, hc2] at hs1 hs2
  rw [Int.floor_eq_iff]
  constructor
  · have h1 : 0 ≤ SignType.sign (n ^ H * eval b (labelPoly c) - m) :=
      sign_nonneg_iff.mpr (by linarith)
    rw [hs1] at h1
    have := sign_nonneg_iff.mp h1
    linarith
  · have h2 : SignType.sign (n ^ H * eval b (labelPoly c) - (m + 1)) = -1 :=
      sign_neg (by linarith)
    rw [hs2] at h2
    have := sign_eq_neg_one_iff.mp h2
    linarith

/-- A label selection inside a box has the frozen polynomial format. -/
theorem format_label_selection (n : ℝ) (H R : ℕ) (T : Set (Fin 3 → ℤ))
    (hT : ∀ l ∈ T, ∀ c, |l c| ≤ (R : ℤ)) (i : ℕ) :
    Format 6 (3 * (2 * R + 2)) 3 {b | scalarLabel n H (fibrePoint i b) ∈ T} := by
  have hB : (1 : ℝ) ≤ 3 * (2 * R + 2) := by
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    linarith
  have hcard : (Fintype.card (Fin 3 × Fin (2 * R + 2)) : ℝ) ≤ 3 * (2 * R + 2) := by
    simp
  have h := Submission.Obl.k4_scalar_true_atlas_terminal_lists.Format.of_invariant
    (n := 6) (D := 3) hB (m := Fintype.card (Fin 3 × Fin (2 * R + 2))) hcard
    (fun q => boundaryPoly n H R ((Fintype.equivFin _).symm q))
    (fun q => boundaryPoly_degree n H R _)
    {b | scalarLabel n H (fibrePoint i b) ∈ T}
  apply h
  intro b b' hsign
  have hsign' : ∀ q, SignType.sign (eval b (boundaryPoly n H R q)) =
      SignType.sign (eval b' (boundaryPoly n H R q)) := by
    intro q
    simpa using hsign (Fintype.equivFin _ q)
  have key : ∀ (u v : Fin 6 → ℝ), (∀ q, SignType.sign (eval u (boundaryPoly n H R q)) =
      SignType.sign (eval v (boundaryPoly n H R q))) →
      scalarLabel n H (fibrePoint i u) ∈ T → scalarLabel n H (fibrePoint i v) ∈ T := by
    intro u v huv hu
    have heq : scalarLabel n H (fibrePoint i v) = scalarLabel n H (fibrePoint i u) := by
      funext c
      rw [scalarLabel_fibrePoint, scalarLabel_fibrePoint]
      apply floor_eq_of_boundary_signs c huv
      rw [← scalarLabel_fibrePoint]
      exact hT _ hu c
    rw [heq]
    exact hu
  exact ⟨key b b' hsign', key b' b (fun q => (hsign' q).symm)⟩

end Submission.Obl.k4_scalar_pure_multiworld_homogenization
