-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.ParameterZoom, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/ParameterZoom.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/ParameterZoom.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/ParameterZoom.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory
open scoped BigOperators

noncomputable section

/-- Subtract the central original quadratic/affine coefficient curves,
then divide every spatial coordinate by the same parameter width. -/
def zoomCoefficients (ρ : ℝ) (center c : Fin 7 → ℝ) : Fin 7 → ℝ :=
  fun i => (c i - center i) / ρ

theorem measurable_zoomCoefficients {Λ : Type*} [MeasurableSpace Λ]
    (ρ : ℝ) (center : Fin 7 → ℝ) {c : Λ → Fin 7 → ℝ} (hc : Measurable c) :
    Measurable (fun l => zoomCoefficients ρ center (c l)) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (((measurable_pi_apply i).comp hc).sub_const (center i)).div_const ρ

theorem zx_zoom (ρ : ℝ) (center c : Fin 7 → ℝ) (t : ℝ) :
    zx (zoomCoefficients ρ center c) t = (zx c t - zx center t) / ρ := by
  simp only [zx, zoomCoefficients, div_eq_mul_inv]
  ring

theorem zy_zoom (ρ : ℝ) (center c : Fin 7 → ℝ) (t : ℝ) :
    zy (zoomCoefficients ρ center c) t =
      fun i => (zy c t i - zy center t i) / ρ := by
  funext i
  fin_cases i <;> simp [zy, zoomCoefficients, div_eq_mul_inv] <;> ring

theorem zv_zoom (ρ : ℝ) (center c : Fin 7 → ℝ) :
    zv (zoomCoefficients ρ center c) = fun i => (zv c i - zv center i) / ρ := by
  funext i
  fin_cases i <;> rfl

theorem zR_zoom (ρ : ℝ) (center c : Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ) (t : ℝ) :
    zR F (zoomCoefficients ρ center c) t = (zR F c t - zR F center t) / ρ := by
  simp [zR, zv, zoomCoefficients, dotProduct, Fin.sum_univ_two, div_eq_mul_inv]
  ring

theorem zoom_coefficients_bound (ρ : ℝ) (hρ : 0 < ρ) (center c : Fin 7 → ℝ)
    (h : ∀ i, |c i - center i| ≤ ρ) : ‖zoomCoefficients ρ center c‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  change |(c i - center i) / ρ| ≤ 1
  rw [abs_div, abs_of_pos hρ, div_le_one hρ]
  exact h i

/-- An actual original coefficient bin, viewed in its original zoom,
has the coefficient diameter needed by the jet theorem. -/
theorem zoom_piece_diameter (ρ r : ℝ) (hρ : 0 < ρ) (hr : 0 < r)
    (center c c' : Fin 7 → ℝ)
    (hbin : ∀ i, ⌊c i / (ρ * r)⌋ = ⌊c' i / (ρ * r)⌋) :
    ‖zoomCoefficients ρ center c - zoomCoefficients ρ center c'‖ ≤ r := by
  apply (pi_norm_le_iff_of_nonneg hr.le).mpr
  intro i
  have hgap : |c i - c' i| ≤ ρ * r := by
    have h := (Int.abs_sub_lt_one_of_floor_eq_floor (hbin i)).le
    simpa only [← sub_div, abs_div, abs_of_pos (mul_pos hρ hr),
      div_le_iff₀ (mul_pos hρ hr), one_mul] using h
  change |(c i - center i) / ρ - (c' i - center i) / ρ| ≤ r
  rw [← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hρ, div_le_iff₀ hρ]
  simpa only [mul_comm] using hgap

/-- Exact residual identity in the parameter zoom. Its error term is
the ORIGINAL line--field error, before dividing by the parameter width. -/
theorem zoom_residual_decomposition (ρ : ℝ) (hρ : ρ ≠ 0)
    (center c : Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ)
    (g₀ : ℝ) (g : Fin 2 → ℝ) (t : ℝ) :
    ρ * zR F (zoomCoefficients ρ center c) t =
      (g₀ + g ⬝ᵥ zv center - (center 1 + 2 * center 2 * t)) +
      (g - F t) ⬝ᵥ (zv c - zv center) +
      (c 1 + 2 * c 2 * t - g₀ - g ⬝ᵥ zv c) := by
  simp [zR, zv, zoomCoefficients, dotProduct, Fin.sum_univ_two]
  field_simp
  ring

theorem zoom_residual_near_original_state (ρ : ℝ) (hρ : ρ ≠ 0)
    (center c : Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ)
    (g₀ : ℝ) (g : Fin 2 → ℝ) (t η V E : ℝ)
    (hη : 0 ≤ η) (hV : 0 ≤ V)
    (hrow : ∀ i, |g i - F t i| ≤ η)
    (hvel : ∀ i, |zv c i - zv center i| ≤ V)
    (hgraph : |c 1 + 2 * c 2 * t - g₀ - g ⬝ᵥ zv c| ≤ E) :
    |ρ * zR F (zoomCoefficients ρ center c) t -
      (g₀ + g ⬝ᵥ zv center - (center 1 + 2 * center 2 * t))| ≤ E + 2 * η * V := by
  have hterm (i : Fin 2) : |(g i - F t i) * (zv c i - zv center i)| ≤ η * V := by
    rw [abs_mul]
    exact mul_le_mul (hrow i) (hvel i) (abs_nonneg _) hη
  have hdot : |(g - F t) ⬝ᵥ (zv c - zv center)| ≤ 2 * η * V := by
    rw [dotProduct, Fin.sum_univ_two]
    simp only [Pi.sub_apply]
    exact (abs_add_le _ _).trans ((add_le_add (hterm 0) (hterm 1)).trans_eq (by ring))
  rw [zoom_residual_decomposition ρ hρ]
  rw [show (g₀ + g ⬝ᵥ zv center - (center 1 + 2 * center 2 * t)) +
      (g - F t) ⬝ᵥ (zv c - zv center) +
      (c 1 + 2 * c 2 * t - g₀ - g ⬝ᵥ zv c) -
      (g₀ + g ⬝ᵥ zv center - (center 1 + 2 * center 2 * t)) =
      (g - F t) ⬝ᵥ (zv c - zv center) +
        (c 1 + 2 * c 2 * t - g₀ - g ⬝ᵥ zv c) by ring]
  exact (abs_add_le _ _).trans ((add_le_add hdot hgraph).trans_eq (by ring))

/-- The residual is almost constant on one original physical state
and one parameter world. Both errors are paid before normalization. -/
theorem zoom_residual_original_state_range (ρ : ℝ) (hρ : 0 < ρ)
    (center c c' : Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ)
    (g₀ : ℝ) (g : Fin 2 → ℝ) (t t' η V E : ℝ)
    (hη : 0 ≤ η) (hV : 0 ≤ V)
    (hrow : ∀ i, |g i - F t i| ≤ η) (hrow' : ∀ i, |g i - F t' i| ≤ η)
    (hvel : ∀ i, |zv c i - zv center i| ≤ V)
    (hvel' : ∀ i, |zv c' i - zv center i| ≤ V)
    (hgraph : |c 1 + 2 * c 2 * t - g₀ - g ⬝ᵥ zv c| ≤ E)
    (hgraph' : |c' 1 + 2 * c' 2 * t' - g₀ - g ⬝ᵥ zv c'| ≤ E) :
    |zR F (zoomCoefficients ρ center c) t - zR F (zoomCoefficients ρ center c') t'| ≤
      (2 * (E + 2 * η * V) + 2 * |center 2| * |t - t'|) / ρ := by
  have h := zoom_residual_near_original_state ρ hρ.ne' center c F g₀ g t η V E
    hη hV hrow hvel hgraph
  have h' := zoom_residual_near_original_state ρ hρ.ne' center c' F g₀ g t' η V E
    hη hV hrow' hvel' hgraph'
  let a := g₀ + g ⬝ᵥ zv center - (center 1 + 2 * center 2 * t)
  let a' := g₀ + g ⬝ᵥ zv center - (center 1 + 2 * center 2 * t')
  have ha : |a - a'| = 2 * |center 2| * |t - t'| := by
    rw [show a - a' = -(2 * center 2 * (t - t')) by dsimp [a, a']; ring]
    simp only [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (le_div_iff₀ hρ).mpr
  have hs (x y : ℝ) : |x - y| * ρ = |ρ * x - ρ * y| := by
    rw [← mul_sub, abs_mul, abs_of_pos hρ]
    ring
  rw [hs]
  have h1 := abs_sub_le (ρ * zR F (zoomCoefficients ρ center c) t) a
    (ρ * zR F (zoomCoefficients ρ center c') t')
  have h2 := abs_sub_le a a' (ρ * zR F (zoomCoefficients ρ center c') t')
  have h'': |a' - ρ * zR F (zoomCoefficients ρ center c') t'| ≤ E + 2 * η * V := by
    rw [abs_sub_comm]
    exact h'
  change |ρ * zR F (zoomCoefficients ρ center c) t - a| ≤ E + 2 * η * V at h
  linarith

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
