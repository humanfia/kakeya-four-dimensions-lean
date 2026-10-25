import Submission.Obl.k4_plank_projected_multiplicity.DirectionCap
import Submission.Obl.k4_plank_projected_multiplicity.PlankMultiplicity

namespace Submission.Obl.k4_plank_projected_multiplicity

open Filter Finset
open Submission.Lib.K4PlankGeometry (cellCode)

noncomputable section

/-- A separated slope family has power-small incidence mass in highly occupied projected cells. -/
theorem high_projected_cell_tail (hplank : PlankEstimate) {a R : ℝ}
    (ha : 0 < a) (hR : 1 ≤ R) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      ∀ {ι : Type*} [Fintype ι] (b : ι → E2) (s : ι → E3),
      (∀ i, ‖b i‖ ≤ 1 ∧ ‖planarPart (s i)‖ ≤ 1) →
      (∀ i, |s i 2| ≤ R) →
      (∀ i j, i ≠ j → (D : ℝ)⁻¹ ≤ ‖s i - s j‖) →
      (∑ i : ι, ((highCellMarks
        (fun p => cellCode D (b p.1) (planarPart (s p.1)) p.2)
        ((D : ℝ) ^ (1 + a)) i).card : ℝ)) ≤
          (Fintype.card ι : ℝ) * (D : ℝ) ^ (1 - τ) := by
  classical
  obtain ⟨η, hη, C, hC, hbound⟩ := plank_high_multiplicity hplank (ε := a / 2) (by positivity)
  have hlarge : ∀ᶠ D : ℕ in atTop, 4000000 * C * R ≤ (D : ℝ) ^ (a / 2) :=
    ((tendsto_rpow_atTop (show 0 < a / 2 by positivity)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  have htwo : ∀ᶠ D : ℕ in atTop, 2 ≤ (D : ℝ) ^ (η / 2) :=
    ((tendsto_rpow_atTop (show 0 < η / 2 by positivity)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp (hlarge.and (htwo.and (eventually_ge_atTop 1)))
  refine ⟨η / 2, by positivity, D₀, ?_⟩
  intro D hD ι _ b s hbu hs hsep
  rcases hD₀ D hD with ⟨hlargeD, htwoD, hD₁⟩
  have hDp : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD₁)
  have hRp : 0 < R := zero_lt_one.trans_le hR
  let A : ℝ := 2000000 * R * (D : ℝ)
  have hM : 2 * (C * A * (D : ℝ) ^ (a / 2)) ≤ (D : ℝ) ^ (1 + a) := by
    calc
      2 * (C * A * (D : ℝ) ^ (a / 2)) =
          (4000000 * C * R) * (D : ℝ) ^ (1 + a / 2) := by
        rw [Real.rpow_add hDp, Real.rpow_one]
        dsimp [A]
        ring
      _ ≤ (D : ℝ) ^ (a / 2) * (D : ℝ) ^ (1 + a / 2) :=
        mul_le_mul_of_nonneg_right hlargeD (Real.rpow_pos_of_pos hDp _).le
      _ = (D : ℝ) ^ (1 + a) := by rw [← Real.rpow_add hDp]; congr 1; ring
  have hh := hbound D hD₁ b (fun i => planarPart (s i)) A (by dsimp [A]; positivity) hbu
    (fulltime_plank_cap_of_separated_slopes D hD₁ hR b s hs hsep)
    (highCellMarks (fun p => cellCode D (b p.1) (planarPart (s p.1)) p.2)
      ((D : ℝ) ^ (1 + a))) ((D : ℝ) ^ (1 + a)) hM (highCellMarks_fiber _ _)
  calc
    _ ≤ 2 * (Fintype.card ι : ℝ) * (D : ℝ) ^ (1 - η) := hh
    _ = (Fintype.card ι : ℝ) * (2 * (D : ℝ) ^ (1 - η)) := by ring
    _ ≤ (Fintype.card ι : ℝ) * ((D : ℝ) ^ (η / 2) * (D : ℝ) ^ (1 - η)) := by
      gcongr
    _ = (Fintype.card ι : ℝ) * (D : ℝ) ^ (1 - η / 2) := by
      rw [← Real.rpow_add hDp]
      congr 2
      ring

end

end Submission.Obl.k4_plank_projected_multiplicity
