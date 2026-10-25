-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.QuarterDirectional, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/QuarterDirectional.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/QuarterDirectional.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit b13a9e17a6c8;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/QuarterDirectional.lean. Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/QuarterDirectional.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.FirstDirectional

/-! # First directional tests at every original point of a quarter core -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

open Metric Set MeasureTheory MvPolynomial
open scoped ContDiff

noncomputable section

/-- An original long ordinary-time witness inside the SAME quarter core
controls the first directional derivative at ANY original core point.
The interval and holomorphic-domain conditions are DERIVED by the actual
rescaling h=1/(2*norm(direction)). -/
theorem quarter_core_constant_fit_first_jet (D : ℕ) :
    ∃ K C : ℝ, 0 < K ∧ 1 ≤ C ∧
    ∀ (Δ U V W : MvPolynomial (Fin 3) ℂ), Δ.totalDegree ≤ D → U.totalDegree ≤ D →
      V.totalDegree ≤ D → W.totalDegree ≤ D →
      ∀ (s F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : EuclideanSpace ℝ (Fin 3) → ℝ),
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, (s z) ^ 2 = eval (fun i => z i) Δ) →
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
        eval (fun i => z i) W * F z = eval (fun i => z i) U + eval (fun i => z i) V * s z) →
      ContDiffOn ℂ ∞ F (ball 0 4) →
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ < 4 → F (DenseJet.realSlice x) = (f x : ℂ)) →
      ∀ (u v : EuclideanSpace ℝ (Fin 3)), ‖u‖ ≤ 1 / 4 → 1 ≤ ‖v‖ →
      eval (fun i => (DenseJet.realSlice u) i) W ≠ 0 →
      ∀ (T : Set ℝ) (θ ε intercept : ℝ), MeasurableSet T → 0 < θ → θ ≤ 1 →
        0 ≤ ε → ENNReal.ofReal θ ≤ volume T →
        (∀ t ∈ T, ‖u + t • v‖ ≤ 1 / 4) →
        (∀ t ∈ T, |f (u + t • v) - intercept| ≤ ε) →
        |fderiv ℝ f u v| ≤ 2 * K * ‖v‖ * θ ^ (-C) * ε := by
  obtain ⟨K, C, hK, hC, hfirst⟩ := quadratic_fit_first_jet_norming D
  refine ⟨K, C, hK, hC, ?_⟩
  intro Δ U V W hΔ hU hV hW s F f hroot hrep hF hmatch u v hu hv hWu
    T θ ε intercept hT hθ hθ1 hε hvol hcore hfit
  have hvpos : 0 < ‖v‖ := zero_lt_one.trans_le hv
  let h : ℝ := (2 * ‖v‖)⁻¹
  have hh : 0 < h := by dsimp only [h]; positivity
  have hhnorm : h * ‖v‖ = 1 / 2 := by dsimp only [h]; field_simp
  have hscaled : ‖h • v‖ = 1 / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh, hhnorm]
  have huv : ‖u‖ + 4 * ‖h • v‖ < 4 := by rw [hscaled]; linarith
  have htime (t : ℝ) (ht : t ∈ T) : |t| * ‖v‖ ≤ 1 / 2 := by
    calc
      |t| * ‖v‖ = ‖t • v‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = ‖(u + t • v) - u‖ := by congr 1; abel
      _ ≤ ‖u + t • v‖ + ‖u‖ := norm_sub_le _ _
      _ ≤ 1 / 2 := by linarith [hcore t ht]
  let S : Set ℝ := (fun t : ℝ => h * t) ⁻¹' T
  have hS : MeasurableSet S := hT.preimage (measurable_const_mul h)
  have hSsub : S ⊆ Icc (-1 : ℝ) 1 := by
    intro t ht
    have ht' := htime (h * t) ht
    rw [abs_mul, abs_of_pos hh] at ht'
    have heq : h * |t| * ‖v‖ = (h * ‖v‖) * |t| := by ring
    rw [heq, hhnorm] at ht'
    exact abs_le.mp (by linarith : |t| ≤ 1)
  have hSvol : ENNReal.ofReal θ ≤ volume S := by
    rw [Real.volume_preimage_mul_left hh.ne', abs_of_pos (inv_pos.mpr hh)]
    have hinv : 1 ≤ h⁻¹ := by dsimp only [h]; rw [inv_inv]; linarith
    have hcoef : (1 : ENNReal) ≤ ENNReal.ofReal h⁻¹ := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hinv
    apply hvol.trans
    simpa only [one_mul] using mul_le_mul' hcoef (le_refl (volume T))
  have hhfit : ∀ t ∈ S,
      |f (u + t • (h • v)) - (intercept + 0 * t + 0 * t ^ 2)| ≤ ε := by
    intro t ht
    simpa only [zero_mul, add_zero, smul_smul, mul_comm t h] using hfit (h * t) ht
  have hder := hfirst Δ U V W hΔ hU hV hW s F f hroot hrep hF hmatch
    u (h • v) intercept 0 0 huv hWu S θ ε hS hSsub hθ hθ1 hε hSvol hhfit
  rw [map_smul, smul_eq_mul, sub_zero, abs_mul, abs_of_pos hh] at hder
  have hd : |fderiv ℝ f u v| ≤ K * θ ^ (-C) * ε / h :=
    (le_div_iff₀ hh).mpr (by nlinarith)
  exact hd.trans_eq (by dsimp only [h]; rw [div_inv_eq_mul]; ring)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
