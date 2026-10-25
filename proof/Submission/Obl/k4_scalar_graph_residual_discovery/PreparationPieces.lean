/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file PreparationPieces.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.PreparationScaleGrid
import Submission.Obl.k4_scalar_graph_residual_discovery.CoefficientZoom

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice

noncomputable section

/-- Construct the higher-jet piece map at EVERY real scale while using
only C*J+1 original preparation levels. Its coefficients have the global
diameter bound, including trajectories outside the retained world. -/
theorem exists_prepared_coefficient_pieces {N H a : ℝ} (hN : 1 < N)
    (M J C : ℕ) (hM : 1 ≤ M) (hJ : 1 ≤ J)
    (hcost : N ^ (1 / (M : ℝ)) ≤ H) (ha : 0 ≤ a) :
    ∃ u : ℝ → ℝ,
      (∀ r, u r ∈ preparationScaleGrid M J C a) ∧
      (∀ r, ∃ m : ℕ, u r = (m : ℝ) / (M : ℝ)) ∧
      (∀ r, Measurable (fun l : ScalarLine => cell (N ^ (-u r)) l.2)) ∧
      ∀ r : ℝ, N ^ (-(C : ℝ)) ≤ r → r ≤ 1 →
        a ≤ u r ∧ u r ≤ a + (C : ℝ) + 1 / (M : ℝ) ∧
          N ^ (-u r) ≤ N ^ (-a) * r ∧
            N ^ (-a) * r ≤ (H * N ^ (1 / (J : ℝ))) * N ^ (-u r) ∧
              ∀ (q : Fin 5 → ℤ) (l l' : ScalarLine),
                cell (N ^ (-u r)) l.2 = cell (N ^ (-u r)) l'.2 →
                  ‖Zoom.coeff (N ^ (-a)) q l - Zoom.coeff (N ^ (-a)) q l'‖ ≤ r := by
  classical
  choose u humem humesh hulo huhi huwidth huratio using fun r : Icc (N ^ (-(C : ℝ))) 1 =>
    exists_prepared_relative_scale hN M J C hM hJ hcost ha r.property.1 r.property.2
  let f : ℝ → ℝ := fun r =>
    if hr : r ∈ Icc (N ^ (-(C : ℝ))) 1 then u ⟨r, hr⟩ else upperGridExponent M a
  have hmem (r : ℝ) : f r ∈ preparationScaleGrid M J C a := by
    dsimp only [f]
    split_ifs with hr
    · exact humem ⟨r, hr⟩
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_insert_self _ _, by simp only [add_zero]⟩
  refine ⟨f, hmem, fun r => preparationScaleGrid_on_mesh (hmem r),
    fun r => measurable_cell _ measurable_snd, ?_⟩
  intro r hr hr₁
  let v : Icc (N ^ (-(C : ℝ))) 1 := ⟨r, hr, hr₁⟩
  have heq : f r = u v := dite_eq_left ⟨hr, hr₁⟩
  rw [heq]
  refine ⟨hulo v, huhi v, huwidth v, huratio v, ?_⟩
  intro q l l' hbin
  have hN₀ : 0 < N := by linarith
  have hr₀ : 0 < r := (Real.rpow_pos_of_pos hN₀ _).trans_le hr
  apply (pi_norm_le_iff_of_nonneg hr₀.le).mpr
  intro e
  exact Zoom.coeff_piece_diameter (Real.rpow_pos_of_pos hN₀ _)
    (Real.rpow_pos_of_pos hN₀ _) (huwidth v) q hbin e

end

end Submission.Obl.k4_scalar_graph_residual_discovery
