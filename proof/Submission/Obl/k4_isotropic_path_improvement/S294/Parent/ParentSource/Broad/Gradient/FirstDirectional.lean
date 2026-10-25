-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.FirstDirectional, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/FirstDirectional.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/FirstDirectional.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit b13a9e17a6c8;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/FirstDirectional.lean. Existing source attributions are preserved below.

-- Adapted from this LOT tree, o204, session x0747, commit7ddecf81.
-- Original file: Submission/Obl/k4_uniform_sampled_isotropic_branches/FirstDirectional.lean; existing source attributions retained.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Restoration.Analytic.LinePolynomialError
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Restoration.Analytic.DenseJet.Line
import Submission.Obl.k4_algebraic_sheet_remez

/-!
# First directional tests from long native quadratic witnesses

The first derivative of a local graph prediction is compared to the
actual native quadratic trajectory derivative. The accepted algebraic
Remez theorem supplies the norming input.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

noncomputable section

open Metric Set MvPolynomial MeasureTheory
open scoped ContDiff ENNReal

/-- A long quadratic tube witness controls the FIRST derivative of the
graph error. Its time coefficient is retained rather than discarded.
The line restriction construction follows the owned
`Analytic/QuadraticFitNorming.lean` (adapted from LOT o143/x0487);
the new conclusion is the first-order comparison needed for support. -/
theorem quadratic_fit_first_jet_norming (D : ℕ) :
    ∃ K C : ℝ, 0 < K ∧ 1 ≤ C ∧
    ∀ (Δ U V W : MvPolynomial (Fin 3) ℂ), Δ.totalDegree ≤ D → U.totalDegree ≤ D →
      V.totalDegree ≤ D → W.totalDegree ≤ D →
      ∀ (s F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : EuclideanSpace ℝ (Fin 3) → ℝ),
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, (s z) ^ 2 = eval (fun i => z i) Δ) →
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
        eval (fun i => z i) W * F z = eval (fun i => z i) U + eval (fun i => z i) V * s z) →
      ContDiffOn ℂ ∞ F (ball 0 4) →
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ < 4 → F (DenseJet.realSlice x) = (f x : ℂ)) →
      ∀ (u v : EuclideanSpace ℝ (Fin 3)) (α β γ : ℝ), ‖u‖ + 4 * ‖v‖ < 4 →
      eval (fun i => (DenseJet.realSlice u) i) W ≠ 0 →
      ∀ (S : Set ℝ) (θ ε : ℝ), MeasurableSet S → S ⊆ Icc (-1) 1 → 0 < θ → θ ≤ 1 →
        0 ≤ ε → ENNReal.ofReal θ ≤ volume S →
        (∀ t ∈ S, |f (u + t • v) - (α + β * t + γ * t ^ 2)| ≤ ε) →
        |fderiv ℝ f u v - β| ≤ K * θ ^ (-C) * ε := by
  have hR : DenseJet.SheetRemezAssertion := Submission.k4_algebraic_sheet_remez
  obtain ⟨K, C, hK, hC, hline⟩ := DenseJet.Line.line_jet_bound hR (8 * (D + 2) + 2)
  refine ⟨K, C, hK, hC, ?_⟩
  intro Δ U V W hΔ hU hV hW s F f hroot hrep hF hmatch u v α β γ huv hWa
    S θ ε hS hSsub hθ hθ1 hε hvol hbound
  have hf : ContDiffOn ℝ ∞ f (ball 0 4) := by
    have hcomp : ContDiffOn ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 3) =>
        F (DenseJet.realSlice x)) (ball 0 4) :=
      (hF.restrict_scalars ℝ).comp DenseJet.realSlice.contDiff.contDiffOn (by
        intro x hx
        simpa only [mem_ball, dist_zero_right, DenseJet.norm_realSlice_apply] using hx)
    have hre := Complex.reCLM.contDiff.comp_contDiffOn hcomp
    apply hre.congr
    intro x hx
    simp [hmatch x (by simpa only [mem_ball, dist_zero_right] using hx)]
  let Q : MvPolynomial (Fin 1) ℂ := MvPolynomial.C (α : ℂ) +
    MvPolynomial.C (β : ℂ) * X 0 + MvPolynomial.C (γ : ℂ) * (X 0) ^ 2
  have hQ : Q.totalDegree ≤ 2 := by
    have hlinear : (MvPolynomial.C (β : ℂ) * (X 0 : MvPolynomial (Fin 1) ℂ)).totalDegree ≤ 1 :=
      (totalDegree_mul _ _).trans (by simp)
    have hsquare : ((X 0 : MvPolynomial (Fin 1) ℂ) ^ 2).totalDegree ≤ 2 :=
      (totalDegree_pow _ _).trans (by simp)
    exact (totalDegree_add _ _).trans (max_le
      ((totalDegree_add _ _).trans (max_le (by simp) (hlinear.trans (by omega))))
      ((totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hsquare)))
  have hpt : ∀ ζ : ℂ, ‖ζ‖ < 4 → ‖DenseJet.realSlice u + ζ • DenseJet.realSlice v‖ < 4 := by
    intro ζ hζ
    calc
      _ ≤ ‖DenseJet.realSlice u‖ + ‖ζ‖ * ‖DenseJet.realSlice v‖ := by
        simpa only [norm_smul] using norm_add_le (DenseJet.realSlice u) (ζ • DenseJet.realSlice v)
      _ ≤ ‖u‖ + 4 * ‖v‖ := by
        rw [DenseJet.norm_realSlice_apply, DenseJet.norm_realSlice_apply]
        gcongr
      _ < 4 := huv
  have hmap : MapsTo (fun z : EuclideanSpace ℂ (Fin 1) =>
      DenseJet.realSlice u + z 0 • DenseJet.realSlice v) (ball 0 4) (ball 0 4) := by
    intro z hz
    rw [mem_ball, dist_zero_right] at hz ⊢
    exact hpt (z 0) ((PiLp.norm_apply_le z 0).trans_lt hz)
  have hrel := hasSheetRelation_polynomial_line_error D 2 Δ U V W hΔ hU hV hW
    (ball 0 4) s F hroot hrep (DenseJet.realSlice u) (DenseJet.realSlice v) Q hQ hWa hmap
  let G : ℂ → ℂ := fun ζ => F (DenseJet.realSlice u + ζ • DenseJet.realSlice v) -
    ((α : ℂ) + (β : ℂ) * ζ + (γ : ℂ) * ζ ^ 2)
  let g : ℝ → ℝ := fun t => f (u + t • v) - (α + β * t + γ * t ^ 2)
  have hrelG : k4_algebraic_real_jet_comparison.HasSheetRelation 1 (8 * (D + 2) + 2)
      (fun z : EuclideanSpace ℂ (Fin 1) => G (z 0)) := by
    simpa only [Q, G, map_add, map_mul, eval_C, eval_X, map_pow] using hrel
  have hG : ContDiffOn ℂ ∞ G (ball 0 4) := by
    have hlin : ContDiff ℂ ∞ (fun ζ : ℂ => DenseJet.realSlice u + ζ • DenseJet.realSlice v) := by fun_prop
    have hmaps : MapsTo (fun ζ : ℂ => DenseJet.realSlice u + ζ • DenseJet.realSlice v)
        (ball 0 4) (ball 0 4) := by
      intro ζ hζ
      simpa only [mem_ball, dist_zero_right] using
        hpt ζ (by simpa only [mem_ball, dist_zero_right] using hζ)
    exact (hF.comp hlin.contDiffOn hmaps).sub (by fun_prop)
  have hGg : ∀ t : ℝ, |t| < 4 → G t = (g t : ℂ) := by
    intro t ht
    have heq : DenseJet.realSlice u + (t : ℂ) • DenseJet.realSlice v =
        DenseJet.realSlice (u + t • v) := by
      ext i
      simp [DenseJet.realSlice_apply]
    have hnorm : ‖u + t • v‖ < 4 := by
      rw [← DenseJet.norm_realSlice_apply, ← heq]
      exact hpt t (by simpa using ht)
    simp only [G, g, heq, hmatch _ hnorm]
    push_cast
    rfl
  have hnormed := hline G g hrelG hG hGg S θ ε hS hSsub hθ hθ1 hε hvol hbound
    1 (by norm_num) 0 (by norm_num)
  have hu4 : u ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 4 := by
    rw [mem_ball, dist_zero_right]
    nlinarith [norm_nonneg v]
  have hψ : ContDiffAt ℝ (1 : ℕ) (fun t : ℝ => f (u + t • v)) 0 := by
    have hfu : ContDiffAt ℝ (1 : ℕ) f u :=
      (hf.contDiffAt (isOpen_ball.mem_nhds hu4)).of_le (by simp)
    have hfu' : ContDiffAt ℝ (1 : ℕ) f (u + (0 : ℝ) • v) := by simpa using hfu
    exact hfu'.comp 0 (show ContDiffAt ℝ (1 : ℕ) (fun t : ℝ => u + t • v) 0 from by fun_prop)
  have hfit : ContDiffAt ℝ (1 : ℕ) (fun t : ℝ => α + β * t + γ * t ^ 2) 0 := by fun_prop
  have hpoly : iteratedDeriv 1 (fun t : ℝ => α + β * t + γ * t ^ 2) 0 = β := by
    rw [iteratedDeriv_one]
    have hid : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id 0
    have hlinear : HasDerivAt (fun t : ℝ => α + β * t) β 0 := by
      simpa using (hid.const_mul β).const_add α
    have hsquare : HasDerivAt (fun t : ℝ => γ * t ^ 2) 0 0 := by
      simpa using (hid.pow 2).const_mul γ
    simpa only [Pi.add_def, add_zero] using (hlinear.add hsquare).deriv
  have hfirst : iteratedDeriv 1 (fun t : ℝ => f (u + t • v)) 0 = fderiv ℝ f u v := by
    rw [iteratedDeriv_one]
    have hfu := (hf.contDiffAt (isOpen_ball.mem_nhds hu4)).differentiableAt (by simp)
    have hfu' : HasFDerivAt f (fderiv ℝ f u) (u + (0 : ℝ) • v) := by
      simpa using hfu.hasFDerivAt
    have hline : HasDerivAt (fun t : ℝ => u + t • v) v 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u)
    exact (hfu'.comp_hasDerivAt 0 hline).deriv
  have hg : g = (fun t : ℝ => f (u + t • v)) - (fun t : ℝ => α + β * t + γ * t ^ 2) := rfl
  rw [hg, iteratedDeriv_sub hψ hfit] at hnormed
  simpa only [Pi.sub_apply, hfirst, hpoly] using hnormed

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
