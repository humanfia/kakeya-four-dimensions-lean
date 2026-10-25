/- Adapted from this LOT tree, o078, session x0260, commit 34c7136a25cd.
   Original file: Submission/Lib/K4ExactMeasureTools/CurveCells.lean -/
/- Finite grid covers of bounded-speed curves.
Adapted from: here:o078
-/

import Mathlib
import Submission.Lib.K4IncidenceWitnesses

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

/-- A coordinate-Lipschitz curve visits only linearly many grid cells.
The finite cover includes every time, including both interval endpoints. -/
theorem exists_curve_grid_cover {d : ℕ} (F : ℝ → Fin d → ℝ) {L h : ℝ}
    (hL : 0 ≤ L) (hh : 0 < h) (D : ℕ) (hD : 1 ≤ D) (hscale : L ≤ (D : ℝ) * h)
    (hLip : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ j,
      |F t j - F s j| ≤ L * |t - s|) :
    ∃ Q : Finset (Fin d → ℤ), (Q.card : ℝ) ≤ ((D : ℝ) + 1) * 7 ^ d ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, (fun j => ⌊F t j / h⌋) ∈ Q := by
  classical
  have hD₀ : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  let tcen (i : Fin (D + 1)) : ℝ := (i : ℕ) / (D : ℝ)
  let boxes (i : Fin (D + 1)) : Finset (Fin d → ℤ) :=
    Fintype.piFinset (fun j => Finset.Icc (⌊F (tcen i) j / h⌋ - 1) (⌊F (tcen i) j / h⌋ + 1))
  let Q := Finset.univ.biUnion boxes
  have hcard (i : Fin (D + 1)) : ((boxes i).card : ℝ) ≤ 7 ^ d := by
    have h := Submission.Lib.K4IncidenceWitnesses.card_pi_grid_of_diameter
      (boxes i) (R := 2) (by norm_num) (by
        intro p hp q hq j
        have hp' := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hp j)
        have hq' := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hq j)
        have hi : |p j - q j| ≤ (2 : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
        exact_mod_cast hi)
    simpa only [Fintype.card_fin, show (2 : ℝ) * 2 + 3 = 7 by norm_num] using h
  refine ⟨Q, ?_, ?_⟩
  · calc
      (Q.card : ℝ) ≤ ∑ i, ((boxes i).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := Finset.univ) (t := boxes))
      _ ≤ ∑ _ : Fin (D + 1), (7 : ℝ) ^ d := Finset.sum_le_sum (fun i _ => hcard i)
      _ = ((D : ℝ) + 1) * 7 ^ d := by simp
  · intro t ht
    let n : ℕ := ⌊(D : ℝ) * t⌋₊
    have hnD : n ≤ D := Nat.floor_le_of_le (by nlinarith [ht.2] : (D : ℝ) * t ≤ D)
    let i : Fin (D + 1) := ⟨n, by omega⟩
    have hfloor : (n : ℝ) ≤ (D : ℝ) * t := Nat.floor_le (mul_nonneg hD₀.le ht.1)
    have hfloor' : (D : ℝ) * t < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    have htcen : tcen i ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (Nat.cast_nonneg n) hD₀.le
      · exact (div_le_one hD₀).mpr (Nat.cast_le.mpr hnD)
    have hmul : tcen i * (D : ℝ) = n := by dsimp [tcen, i]; field_simp
    have hnear : |t - tcen i| ≤ 1 / (D : ℝ) := by
      have hnonneg : 0 ≤ t - tcen i := by nlinarith
      rw [abs_of_nonneg hnonneg]
      apply (le_div_iff₀ hD₀).mpr
      nlinarith
    have hcoord (j : Fin d) : |F t j - F (tcen i) j| ≤ h := by
      calc
        _ ≤ L * |t - tcen i| := hLip t ht _ htcen j
        _ ≤ L * (1 / (D : ℝ)) := mul_le_mul_of_nonneg_left hnear hL
        _ ≤ h := by
          rw [mul_one_div]
          exact (div_le_iff₀ hD₀).mpr (by simpa only [mul_comm] using hscale)
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, Fintype.mem_piFinset.mpr ?_⟩
    intro j
    apply Finset.mem_Icc.mpr
    have hdiv : |F t j / h - F (tcen i) j / h| ≤ 1 := by
      rw [← sub_div, abs_div, abs_of_pos hh]
      exact (div_le_one hh).mpr (hcoord j)
    have hlo := Int.floor_mono (by linarith [abs_le.mp hdiv] : F (tcen i) j / h - 1 ≤ F t j / h)
    have hhi := Int.floor_mono (by linarith [abs_le.mp hdiv] : F t j / h ≤ F (tcen i) j / h + 1)
    simpa only [Int.floor_sub_one, Int.floor_add_one] using And.intro hlo hhi

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
