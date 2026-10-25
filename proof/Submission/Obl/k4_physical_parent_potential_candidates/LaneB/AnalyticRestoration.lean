import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.PowerBounds

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

open Set MeasureTheory MvPolynomial FubiniJets FubiniHessian QuadraticTube
open scoped ENNReal

noncomputable section

namespace MeasureNorming

attribute [local irreducible] conicPower detPower radiusPower conditioningPower
  denominatorPower framePower restorationPower

/-- Palette-free quantitative restoration for a normalized algebraic graph.
The directions may vary at every point. A single quadratic is obtained on a
ball carrying a fixed-power fraction of the unchanged base measure. -/
theorem analytic_normalized_restoration {D J : ℕ} (hjet : DenseJetBound D J) :
    ∃ M C : ℕ, 1 ≤ M ∧ M ≤ C ∧
    ∀ {A : ℝ}, 2 ≤ A → ∀ {g : Base → ℝ},
    ContDiffOn ℝ 6 g (Metric.ball (0:Base) 3) →
    (∀ n : ℕ, n ≤ 4 → ∀ x ∈ Metric.closedBall (0:Base) 1, ‖iteratedFDeriv ℝ n g x‖ ≤ A) →
    (∀ (c : ℝ) (L : Base →L[ℝ] ℝ),
      ∃ u ∈ Metric.closedBall (0:Base) 1, 1 ≤ |g u-c-L u|) →
    (∀ i j, HasRealExtension D (fun x => hessian g x i j)) →
    (∀ i j k, HasRealExtension D (fun x => clearedCubicError g x i j k)) →
    ∀ {μ : Measure Base}, μ univ ≠ 0 → μ univ ≠ ⊤ →
    (∀ E : Set Base, MeasurableSet E → μ E ≤ ENNReal.ofReal A*μ univ*volume E) →
    μ (Metric.closedBall (0:Base) (1/2))ᶜ = 0 →
    ∀ {η ε : ℝ}, 0 ≤ η → 0 ≤ ε → η*A^C ≤ 1 → ε*A^C ≤ 1 →
    (∀ᵐ x ∂μ, ∃ p : Fin 7 → Base,
      (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ A) ∧
      (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
        A⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)|) ∧
      (∀ i, |iteratedFDeriv ℝ 2 g x (fun _ => p i)| ≤ η)) →
    (∀ᵐ x ∂μ, ∀ i j k, |clearedCubicError g x i j k| ≤ ε) →
    ∃ c ∈ Metric.closedBall (0:Base) (1/2), ∃ Q : Poly,
      Q.totalDegree ≤ 2 ∧ (∀ e, |Q.coeff e| ≤ A^C) ∧
      μ univ ≤ ENNReal.ofReal (A^C)*μ (Metric.ball c (A^M)⁻¹) ∧
      ∀ u ∈ Metric.closedBall c (2*(A^M)⁻¹), ∀ w : ℝ, A^C*|w-g u| ≤ 1 →
        |ev Q u w| ≤ A^C*(ε+|w-g u|) ∧
        (A^C)⁻¹ ≤ ev (pderiv (3:Fin 4) Q) u w ∧
        ev (pderiv (3:Fin 4) Q) u w ≤ A^C ∧
        |ev (pderiv (3:Fin 4) (pderiv (3:Fin 4) Q)) u w| ≤ A^C := by
  obtain ⟨Dc, hDc, hregular⟩ := regular_hessian_mass
  let M := radiusPower J Dc
  let C := restorationPower J Dc
  refine ⟨M+1, C, by omega,
    by simp only [M, C, restorationPower]; omega, ?_⟩
  intro A hA g hg hb hnon hextH hextN μ hμ0 hμfin hdom hsupport η ε hη hε hsmallη hsmallε hdirs hNae
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hp := patch_power_bounds hA J Dc
  let r := powerRadius A J Dc
  let ν := powerDet A J Dc
  let G := {x : Base | x ∈ Metric.closedBall (0:Base) (1/2) ∧ ν ≤ |(hessian g x).det|}
  have hηR : η*(A^conicPower J)^(4*Dc+1) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hp.conic_error hη).trans hsmallη
  have hG : MeasurableSet G ∧ μ univ/2 ≤ μ G := by
    have hh := hregular hjet hg hextH hnon hμ0 hμfin hA hp.conic_mono hη hdom hsupport
      (fun x hx => hb 2 (by decide) x
        (Metric.closedBall_subset_closedBall (by norm_num : (1:ℝ)/2 ≤ 1) hx))
      hp.conic_floor hp.conic_upper hηR hdirs
    simpa only [hp.determinant_eq] using hh
  obtain ⟨c, hcG, hmass⟩ := heavy_regular_ball μ G hG.1 (fun x hx => hx.1)
    hμ0 hμfin hG.2 hA (M+1)
  have hpow : (2*A)^J ≤ A^(2*J) := by
    have hh : 2*A ≤ A^2 := by nlinarith
    convert pow_le_pow_left₀ (by positivity : 0 ≤ 2*A) hh J using 1 <;> ring
  have hNorm (i j k : Fin 3) (n : ℕ) (hn : n ≤ 2) (x : Base)
      (hx : x ∈ Metric.closedBall (0:Base) 1) :
      ‖iteratedFDeriv ℝ n (fun y => clearedCubicError g y i j k) x‖ ≤ A^(2*J)*ε := by
    have hs := FubiniZoom.cleared_smooth Metric.isOpen_ball hg i j k
    have hh := dense_bound_of_ae hjet (hextN i j k)
      (hs.continuousOn.mono (Metric.closedBall_subset_ball (by norm_num : (1:ℝ)/2 < 3)))
      hμ0 hμfin hA hε hdom hsupport (hNae.mono (fun x hx => hx i j k)) n
      (hn.trans (by decide : 2 ≤ 6)) x
      (Metric.closedBall_subset_closedBall (by norm_num : (1:ℝ) ≤ 2) hx)
    exact hh.trans (mul_le_mul_of_nonneg_right hpow hε)
  have hN (x : Base) (hx : x ∈ Metric.closedBall (0:Base) 1) (i j k : Fin 3) :
      C2Bound (fun y => clearedCubicError g y i j k) (A^(2*J)*ε) x := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hNorm i j k 0 (by decide) x hx
    · intro p
      exact coordinate_jet_bound (hNorm i j k 1 (by decide) x hx) ![p]
    · intro p l
      exact coordinate_jet_bound (hNorm i j k 2 (by decide) x hx) ![p,l]
  have hsmall : 3000000*(patchFrame A r ν)^9*
      (6*(2000*(patchBudget A r ν)^4)^5*(A^(2*J)*ε)) ≤ 1 := by
    convert (mul_le_mul_of_nonneg_right hp.smallness hε).trans
      (by simpa only [mul_comm] using hsmallε) using 1 <;> ring
  obtain ⟨Q, hdeg, hcoeff, hest⟩ := ball_tube_certificate hg hA1 hp.radius_pos hp.radius_le_one
    hp.det_pos (by positivity : 0 ≤ A^(2*J)*ε) hb hN hp.radius_small hp.det_stable hcG.1 hcG.2 hsmall
  refine ⟨c, hcG.1, Q, hdeg, fun e => (hcoeff e).trans hp.coefficient, ?_, ?_⟩
  · apply hmass.trans
    exact mul_le_mul (ENNReal.ofReal_le_ofReal hp.mass) (measure_mono (fun x hx => hx.2)) bot_le bot_le
  · intro u hu w hw
    have hradius : 2*(A^(M+1))⁻¹ ≤ r := by
      change 2*(A^(M+1))⁻¹ ≤ (A^M)⁻¹
      calc 2*(A^(M+1))⁻¹ = (A^M)⁻¹*(2/A) := by rw [pow_succ,mul_inv]; ring
        _ ≤ (A^M)⁻¹*1 := mul_le_mul_of_nonneg_left
          ((div_le_one hA0).mpr hA) (by positivity)
        _ = _ := mul_one _
    have hu' : u ∈ Metric.closedBall c r := Metric.closedBall_subset_closedBall hradius hu
    have hwidth : 4*(patchFrame A r ν)^3*|w-g u| ≤ 1 :=
      (mul_le_mul_of_nonneg_right hp.tube (abs_nonneg _)).trans hw
    obtain ⟨hv, hl, hupp, hc⟩ := hest u hu' w hwidth
    refine ⟨hv.trans ?_, ?_, hupp.trans hp.upper_derivative, hc.trans hp.curvature⟩
    · calc
        _ = (patchError A r ν*A^(2*J))*ε+4*(patchFrame A r ν)^2*|w-g u| := by ring
        _ ≤ A^C*ε+A^C*|w-g u| := add_le_add
          (mul_le_mul_of_nonneg_right hp.value hε)
          (mul_le_mul_of_nonneg_right hp.vertical_value (abs_nonneg _))
        _ = _ := by ring
    · apply le_trans ?_ hl
      simpa only [one_div] using one_div_le_one_div_of_le
        (by have hh := patchFrame_one_le hA1 hp.radius_pos hp.det_pos; linarith : 0 < 2*patchFrame A r ν)
        hp.lower_derivative

end MeasureNorming

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
