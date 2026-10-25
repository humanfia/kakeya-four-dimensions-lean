import Submission.Obl.k4_matching_homogeneous_records.RawConstruction

namespace Submission.Obl.k4_matching_homogeneous_records

lemma cofinal_rawRecords {D J : ℕ} {d : ℝ} {β : ℕ → ℝ}
    (hD : 1 ≤ D) (hDJ : D ≤ J)
    (hz : ∃ i, 1 ≤ i ∧ i ≤ D ∧ β i = 0)
    (hgap : ∀ η : ℝ, 0 < η → ∀ R : ℝ, 2 ≤ R → ∃ N : ℝ, R ≤ N ∧ Gap J d β η N)
    (q : ℕ) (hq : 1 ≤ q) :
    ∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 2 ≤ R → ∃ N : ℝ, R ≤ N ∧ RawRecords J d β q ε N := by
  intro ε hε R hR
  let M : ℕ := (q + 1) * (J + 1) + 1
  let C : ℝ := 2 * ((4 * (J + 2) + 5 : ℕ) : ℝ) ^ ((q + 1) * (J + 1))
  let η : ℝ := ε / (2 * (M : ℝ))
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by dsimp [M]; omega)
  have hMp : (0 : ℝ) < M := by linarith
  have hη : 0 < η := by dsimp [η]; positivity
  have hMη : (M : ℝ) * η = ε / 2 := by dsimp [η]; field_simp
  have hηε : η ≤ ε := by nlinarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨N, hRN, hgapN⟩ := hgap η hη (max R (C ^ (2 / ε))) (hR.trans (le_max_left _ _))
  have hN : 1 ≤ N := by linarith [le_max_left R (C ^ (2 / ε))]
  have hNp : 0 < N := by linarith
  have hCN : C ≤ N ^ (ε / 2) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hC (2 / ε))
      ((le_max_right R (C ^ (2 / ε))).trans hRN) (show 0 ≤ ε / 2 by positivity)
    rw [← Real.rpow_mul hC] at h
    have he : (2 / ε) * (ε / 2) = 1 := by field_simp
    simpa only [he, Real.rpow_one] using h
  have hbudget : C * N ^ (d + radius J β 1 + (M : ℝ) * η) ≤
      N ^ (d + radius J β 1 + ε) := by
    calc
      _ ≤ N ^ (ε / 2) * N ^ (d + radius J β 1 + (M : ℝ) * η) :=
        mul_le_mul_of_nonneg_right hCN (Real.rpow_nonneg hNp.le _)
      _ = _ := by
        rw [← Real.rpow_add hNp, hMη]
        congr 1
        ring
  exact ⟨N, (le_max_left R (C ^ (2 / ε))).trans hRN,
    rawRecords_of_gap hD hDJ hz hN hq hη.le hηε hbudget hgapN⟩

end Submission.Obl.k4_matching_homogeneous_records
