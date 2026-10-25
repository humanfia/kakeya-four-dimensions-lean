-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.OriginalRowRenewal, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/OriginalRowRenewal.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/OriginalRowRenewal.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit b13a9e17a6c8;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/OriginalRowRenewal.lean. Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/OriginalRowRenewal.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.QuarterDirectional
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.RenewalCells
import Submission.Lib.K4PlankGeometry

/-! # Original long rows give whole-core renewal on the actual base cells -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Metric MvPolynomial
open scoped ContDiff

noncomputable section

/-- Long ordinary-time witnesses in the SAME original quarter entry,
tested with the SAME original cell laws as the velocity strip caps, give
whole-core gradient and oscillation bounds. The actual floor code supplies
the freeze geometry and its power radius absorbs the relative Hessian.
Only cells meeting E need a positive original broad test floor. -/
theorem original_quarter_row_gradient_renewal (drep : ℕ) :
    ∃ K₀ C₀ : ℝ, 0 < K₀ ∧ 1 ≤ C₀ ∧
    ∀ {D J : ℕ}, ValueJetBound D J →
    ∀ (Δ U V W : MvPolynomial (Fin 3) ℂ), Δ.totalDegree ≤ drep →
      U.totalDegree ≤ drep → V.totalDegree ≤ drep → W.totalDegree ≤ drep →
    ∀ (s F : EuclideanSpace ℂ (Fin 3) → ℂ) (g : EuclideanSpace ℝ (Fin 3) → ℝ),
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, (s z) ^ 2 = eval (fun j => z j) Δ) →
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
        eval (fun j => z j) W * F z = eval (fun j => z j) U + eval (fun j => z j) V * s z) →
      ContDiffOn ℂ ∞ F (ball 0 4) →
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ < 4 → F (Analytic.DenseJet.realSlice x) = (g x : ℂ)) →
      ContDiffOn ℝ 2 g (ball 0 4) →
      (∀ j : Fin 3, exf D (gradientComponent g j)) →
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ₀ : Measure Ω) (μ : (Fin 3 → ℤ) → Measure Ω)
      (vel : Ω → EuclideanSpace ℝ (Fin 2)), Measurable vel →
    ∀ (tests : (Fin 3 → ℤ) → Set Ω) (Z : Ω → EuclideanSpace ℝ (Fin 3))
      (E : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet E →
      E ⊆ closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 4) →
    ∀ (K A B δ β θ ε : ℝ) (q : ℕ), 2 ≤ K → 2 ≤ A → A ≤ K →
      0 ≤ B → B ≤ K → 0 < δ → (K ^ q)⁻¹ ≤ δ → 0 < β →
      0 < θ → θ ≤ 1 → 0 ≤ ε →
      ENNReal.ofReal (β / A) ≤ μ₀ univ →
      (∀ U : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet U →
        μ₀ (Z ⁻¹' U) ≤ ENNReal.ofReal β * volume U) →
      (∀ᵐ p ∂μ₀, Z p ∈ E) →
    ∀ threshold : (Fin 3 → ℤ) → ENNReal,
      (∀ i, ∀ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 → ∀ c : ℝ,
        μ i (vel ⁻¹' Submission.Lib.K4VelocityStrips.affineStrip n c δ) ≤ threshold i) →
      (∀ x ∈ E, threshold (renewalCellCode K J q x) <
        μ (renewalCellCode K J q x) (tests (renewalCellCode K J q x))) →
      (∀ i p, p ∈ tests i → renewalCellCode K J q (Z p) = i) →
      (∀ i p, p ∈ tests i → ‖vel p‖ ≤ B) →
      (∀ i p, p ∈ tests i → ‖Z p‖ ≤ 1 / 4) →
      (∀ i p, p ∈ tests i → eval (fun j => (Analytic.DenseJet.realSlice (Z p)) j) W ≠ 0) →
      (∀ i p, p ∈ tests i → ∃ T : Set ℝ, ∃ intercept : ℝ,
        MeasurableSet T ∧ ENNReal.ofReal θ ≤ volume T ∧
        (∀ t ∈ T, ‖Z p + t • spacetimeDirection (vel p)‖ ≤ 1 / 4) ∧
        ∀ t ∈ T, |g (Z p + t • spacetimeDirection (vel p)) - intercept| ≤ ε) →
      (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
        ‖fderiv ℝ g x‖ ≤ 6 * A ^ J * (1 + (B + 2) / δ) *
          (2 * K₀ * (1 + 2 * B) * θ ^ (-C₀) * ε)) ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
        |g y - g x| ≤ 12 * A ^ J * (1 + (B + 2) / δ) *
          (2 * K₀ * (1 + 2 * B) * θ ^ (-C₀) * ε) := by
  obtain ⟨K₀, C₀, hK₀, hC₀, hfirst⟩ := Analytic.quarter_core_constant_fit_first_jet drep
  refine ⟨K₀, C₀, hK₀, hC₀, ?_⟩
  intro D J hjets Δ U V W hΔ hU hV hW s F g hroot hrep hF hreal hg hgext
    Ω _ μ₀ μ vel hvel tests Z E hE hEball K A B δ β θ ε q hK hA hAK
    hB hBK hδ hδfloor hβ hθ hθ1 hε hmass₀ hcap hsupp threshold hstrip hmass
    hcode hspeed hcore hden hrows
  let ι := {i : Fin 3 → ℤ // ∃ x ∈ E, renewalCellCode K J q x = i}
  have htest (i : ι) (p : Ω) (hp : p ∈ tests i.1) :
      |fderiv ℝ g (Z p) (spacetimeDirection (vel p))| ≤
        2 * K₀ * (1 + 2 * B) * θ ^ (-C₀) * ε := by
    have hdir : 1 ≤ ‖spacetimeDirection (vel p)‖ := by
      have hh := PiLp.norm_apply_le (spacetimeDirection (vel p)) 0
      simpa [spacetimeDirection] using hh
    have hdirupper : ‖spacetimeDirection (vel p)‖ ≤ 1 + 2 * B := by
      have hs := Submission.Lib.K4PlankGeometry.rawDirection_norm_sq (vel p)
      change ‖spacetimeDirection (vel p)‖ ^ 2 = 1 + ‖vel p‖ ^ 2 at hs
      have hv := hspeed i.1 p hp
      have hn := norm_nonneg (spacetimeDirection (vel p))
      have hvn := norm_nonneg (vel p)
      have hsq := pow_le_pow_left₀ hvn hv 2
      nlinarith [sq_nonneg B]
    obtain ⟨T, intercept, hT, hvol, hTcore, hfit⟩ := hrows i.1 p hp
    exact (hfirst Δ U V W hΔ hU hV hW s F g hroot hrep hF hreal
      (Z p) (spacetimeDirection (vel p)) (hcore i.1 p hp) hdir (hden i.1 p hp)
      T θ ε intercept hT hθ hθ1 hε hvol hTcore hfit).trans
        (by gcongr)
  obtain ⟨hr, habsorb⟩ := renewalCellRadius_absorbs hK hA hAK hB hBK hδ hδfloor
  apply original_entry_gradient_renewal hjets μ₀ (fun i : ι => μ i.1) vel hvel
    (fun i : ι => tests i.1) Z g hg hgext E hE
    (hEball.trans (closedBall_subset_closedBall (by norm_num : (1 / 4 : ℝ) ≤ 1)))
    hA hβ (by positivity) hr.le hδ hB hmass₀ hcap hsupp
    (fun i : ι => threshold i.1) (fun i => hstrip i.1) ?_
    (fun i => hspeed i.1) ?_ htest ?_ habsorb
  · intro i
    obtain ⟨x, hx, hxi⟩ := i.2
    simpa only [hxi] using hmass x hx
  · intro i p hp
    rw [mem_ball, dist_zero_right]
    linarith [hcore i.1 p hp]
  · intro x hx
    refine ⟨⟨renewalCellCode K J q x, x, hx, rfl⟩, ?_⟩
    intro p hp
    exact renewalCellCode_diameter hK J q (hcode _ p hp)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
