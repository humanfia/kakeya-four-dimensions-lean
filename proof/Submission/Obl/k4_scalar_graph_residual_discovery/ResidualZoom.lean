/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file ResidualZoom.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.CoefficientZoom
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalRows

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice

namespace Zoom

noncomputable section

def residual (ρ : ℝ) (q : Fin 5 → ℤ) (F : ℝ → ℝ) (l : ScalarLine) (t : ℝ) : ℝ :=
  coeff ρ q l 1 + 2 * t * coeff ρ q l 2 - F t * coeff ρ q l 4

def rowResidual (ρ : ℝ) (q : Fin 5 → ℤ) (G : Fin 2 → ℝ) (t : ℝ) : ℝ :=
  (G 0 + G 1 * (center ρ q).2 1 -
    ((center ρ q).2 3 + 2 * t * (center ρ q).2 4)) / ρ

def stateResidual (ρ b : ℝ) (q : Fin 5 → ℤ)
    (G : (Fin 3 → ℤ) → Fin 2 → ℝ) (w : Fin 3 → ℤ) : ℝ :=
  rowResidual ρ q (G w) (leftCorner b w 0)

theorem measurable_residual (ρ : ℝ) (q : Fin 5 → ℤ) {F : ℝ → ℝ} (hF : Measurable F) :
    Measurable (fun z : ScalarIncidence => residual ρ q F z.1 z.2) := by
  dsimp only [residual, coeff]
  fun_prop

theorem residual_sub_rowResidual (ρ : ℝ) (q : Fin 5 → ℤ) (F : ℝ → ℝ)
    (l : ScalarLine) (t : ℝ) (G : Fin 2 → ℝ) :
    residual ρ q F l t - rowResidual ρ q G t =
      ((G 1 - F t) * (l.2 1 - (center ρ q).2 1) +
        (l.2 3 + 2 * t * l.2 4 - G 0 - G 1 * l.2 1)) / ρ := by
  dsimp [residual, rowResidual, coeff, order, center]
  ring

/-- The original graph error and the time-only row approximation make
the normalized residual nearly constant on each original fine state/world. -/
theorem residual_near_rowResidual {ρ : ℝ} (hρ : 0 < ρ) (q : Fin 5 → ℤ)
    (F : ℝ → ℝ) (l : ScalarLine) (t : ℝ) (G : Fin 2 → ℝ) {δ ε : ℝ}
    (hcoeff : cell ρ l.2 = q) (hrow : |G 1 - F t| ≤ δ)
    (hgraph : |l.2 3 + 2 * t * l.2 4 - G 0 - G 1 * l.2 1| ≤ ε) :
    |residual ρ q F l t - rowResidual ρ q G t| ≤ δ + ε / ρ := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hrow
  have hv := coeff_abs_le_one hρ hcoeff 4
  change |(l.2 1 - (center ρ q).2 1) / ρ| ≤ 1 at hv
  rw [abs_div, abs_of_pos hρ] at hv
  have hv' : |l.2 1 - (center ρ q).2 1| ≤ ρ := by
    simpa only [one_mul] using (div_le_iff₀ hρ).mp hv
  rw [residual_sub_rowResidual, abs_div, abs_of_pos hρ]
  calc
    _ ≤ (δ * ρ + ε) / ρ := div_le_div_of_nonneg_right
      ((abs_add_le _ _).trans (add_le_add
        (by rw [abs_mul]; exact mul_le_mul hrow hv' (abs_nonneg _) hδ) hgraph)) hρ.le
    _ = _ := by field_simp

theorem rowResidual_time_variation {ρ : ℝ} (hρ : 0 < ρ) (q : Fin 5 → ℤ)
    (G : Fin 2 → ℝ) {t u H b : ℝ} (hH : |(center ρ q).2 4| ≤ H) (hgap : |t - u| ≤ b) :
    |rowResidual ρ q G t - rowResidual ρ q G u| ≤ 2 * H * b / ρ := by
  have hid : rowResidual ρ q G t - rowResidual ρ q G u =
      (-(2 * (center ρ q).2 4 * (t - u))) / ρ := by dsimp only [rowResidual]; ring
  rw [hid, abs_div, abs_of_pos hρ, abs_neg, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_left hH (by norm_num)) hgap (abs_nonneg _)
      (by have h := (abs_nonneg _).trans hH; positivity)) hρ.le

theorem residual_near_original_state {ρ b : ℝ} (hρ : 0 < ρ) (hb : 0 < b)
    (q : Fin 5 → ℤ) (F : ℝ → ℝ) (G : (Fin 3 → ℤ) → Fin 2 → ℝ)
    (z : ScalarIncidence) (w : Fin 3 → ℤ) {H δ ε : ℝ}
    (hcoeff : cell ρ z.1.2 = q) (hstate : cell b (scalarPosition z) = w)
    (hH : |(center ρ q).2 4| ≤ H) (hrow : |G w 1 - F z.2| ≤ δ)
    (hgraph : |z.1.2 3 + 2 * z.2 * z.1.2 4 - G w 0 - G w 1 * z.1.2 1| ≤ ε) :
    |residual ρ q F z.1 z.2 - stateResidual ρ b q G w| ≤ δ + ε / ρ + 2 * H * b / ρ := by
  have hgap : |z.2 - leftCorner b w 0| ≤ b := by
    have h := (norm_le_pi_norm
      (scalarPosition z - leftCorner b (cell b (scalarPosition z))) 0).trans
        (norm_sub_leftCorner_le hb (scalarPosition z))
    change |z.2 - leftCorner b (cell b (scalarPosition z)) 0| ≤ b at h
    simpa only [hstate] using h
  exact (abs_sub_le _ (rowResidual ρ q (G w) z.2) _).trans
    (add_le_add (residual_near_rowResidual hρ q F z.1 z.2 (G w) hcoeff hrow hgraph)
      (rowResidual_time_variation hρ q (G w) hH hgap))

theorem residual_coeff_difference {c c' : Fin 5 → ℝ} {t u F F' H L r : ℝ}
    (hdiff : ∀ e, |c e - c' e| ≤ r) (hunit : ∀ e, |c' e| ≤ 1)
    (ht : |t| ≤ 1) (hgap : |t - u| ≤ r) (hF : |F| ≤ H) (hFF : |F - F'| ≤ L * r) :
    |(c 1 + 2 * t * c 2 - F * c 4) - (c' 1 + 2 * u * c' 2 - F' * c' 4)| ≤
      (5 + H + L) * r := by
  have hr : 0 ≤ r := (abs_nonneg _).trans hgap
  have hH : 0 ≤ H := (abs_nonneg _).trans hF
  have hLr : 0 ≤ L * r := (abs_nonneg _).trans hFF
  have hquad : |2 * t * c 2 - 2 * u * c' 2| ≤ 4 * r := by
    have hid : 2 * t * c 2 - 2 * u * c' 2 =
        2 * t * (c 2 - c' 2) + 2 * (t - u) * c' 2 := by ring
    rw [hid]
    have hfirst : |2 * t * (c 2 - c' 2)| ≤ 2 * r := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have h := mul_le_mul (mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 2))
        (hdiff 2) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2 * 1)
      simpa only [mul_one] using h
    have hsecond : |2 * (t - u) * c' 2| ≤ 2 * r := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have h := mul_le_mul (mul_le_mul_of_nonneg_left hgap (by norm_num : (0 : ℝ) ≤ 2))
        (hunit 2) (abs_nonneg _) (mul_nonneg (by norm_num) hr)
      simpa only [mul_one] using h
    exact (abs_add_le _ _).trans (by linarith)
  have hprod : |F * c 4 - F' * c' 4| ≤ H * r + L * r := by
    have hid : F * c 4 - F' * c' 4 = F * (c 4 - c' 4) + (F - F') * c' 4 := by ring
    rw [hid]
    have hfirst : |F * (c 4 - c' 4)| ≤ H * r := by
      rw [abs_mul]
      exact mul_le_mul hF (hdiff 4) (abs_nonneg _) hH
    have hsecond : |(F - F') * c' 4| ≤ L * r := by
      rw [abs_mul]
      simpa only [mul_one] using mul_le_mul hFF (hunit 4) (abs_nonneg _) hLr
    exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)
  have hid : (c 1 + 2 * t * c 2 - F * c 4) - (c' 1 + 2 * u * c' 2 - F' * c' 4) =
      (c 1 - c' 1) + (2 * t * c 2 - 2 * u * c' 2) - (F * c 4 - F' * c' 4) := by ring
  rw [hid]
  calc
    _ ≤ |c 1 - c' 1| + |2 * t * c 2 - 2 * u * c' 2| + |F * c 4 - F' * c' 4| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ r + 4 * r + (H * r + L * r) := add_le_add (add_le_add (hdiff 1) hquad) hprod
    _ = _ := by ring

/-- Within one fine original parameter box and one zoom time cell, residual
variation is bounded before the final residual common choice is applied. -/
theorem residual_piece_variation {ρ β r : ℝ} (hρ : 0 < ρ) (hβ : 0 < β)
    (hscale : β ≤ ρ * r) (q : Fin 5 → ℤ) (F : ℝ → ℝ)
    (l l' : ScalarLine) {t u H L : ℝ} (hcoarse : cell ρ l'.2 = q)
    (hbin : cell β l.2 = cell β l'.2) (ht : |t| ≤ 1) (hgap : |t - u| ≤ r)
    (hF : |F t| ≤ H) (hFF : |F t - F u| ≤ L * r) :
    |residual ρ q F l t - residual ρ q F l' u| ≤ (5 + H + L) * r :=
  residual_coeff_difference (fun e => coeff_piece_diameter hρ hβ hscale q hbin e)
    (coeff_abs_le_one hρ hcoarse) ht hgap hF hFF

end

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
