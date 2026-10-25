import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.BaseReturn
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.LocalCertificate

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

open Set MvPolynomial FubiniJets FubiniHessian QuadraticTube

noncomputable section

namespace MeasureNorming

theorem patchFrame_one_le {A r ν : ℝ} (hA : 1 ≤ A) (hr : 0 < r) (hν : 0 < ν) :
    1 ≤ patchFrame A r ν := by
  have hp : 0 ≤ 2/(r^6*ν) := by positivity
  have hK : 1 ≤ patchBudget A r ν := by dsimp [patchBudget]; linarith
  have hKc : 1 ≤ 2000*(patchBudget A r ν)^4 := by
    have hh := one_le_pow₀ hK (n := 4)
    linarith
  exact (frameBudget_bounds hKc).1

/-- A regular Hessian ball carries an actual quadratic certificate in its
original base coordinates, valid throughout a controlled vertical tube. -/
theorem ball_tube_certificate
    {g : Base → ℝ} (hg : ContDiffOn ℝ 6 g (Metric.ball (0:Base) 3))
    {A r ν ε : ℝ} (hA : 1 ≤ A) (hr : 0 < r) (hr1 : r ≤ 1) (hν : 0 < ν) (hε : 0 ≤ ε)
    (hb : ∀ n : ℕ, n ≤ 4 → ∀ x ∈ Metric.closedBall (0:Base) 1,
      ‖iteratedFDeriv ℝ n g x‖ ≤ A)
    (hN : ∀ x ∈ Metric.closedBall (0:Base) 1, ∀ i j k,
      C2Bound (fun y => clearedCubicError g y i j k) ε x)
    (hsmallr : 4*r ≤ 1/2) (hsmallν : 1152*A^3*r ≤ ν/2)
    {c : Base} (hc : c ∈ Metric.closedBall (0:Base) (1/2)) (hdet : ν ≤ |(hessian g c).det|)
    (hsmall : 3000000*(patchFrame A r ν)^9*(6*(2000*(patchBudget A r ν)^4)^5*ε) ≤ 1) :
    ∃ Q : Poly, Q.totalDegree ≤ 2 ∧
      (∀ e, |Q.coeff e| ≤ 95904*(patchFrame A r ν)^4*(r⁻¹)^2) ∧
      ∀ u ∈ Metric.closedBall c r, ∀ w : ℝ, 4*(patchFrame A r ν)^3*|w-g u| ≤ 1 →
        |ev Q u w| ≤ patchError A r ν*ε+4*(patchFrame A r ν)^2*|w-g u| ∧
        (2*patchFrame A r ν)⁻¹ ≤ ev (pderiv (3:Fin 4) Q) u w ∧
        ev (pderiv (3:Fin 4) Q) u w ≤ 4*patchFrame A r ν ∧
        |ev (pderiv (3:Fin 4) (pderiv (3:Fin 4) Q)) u w| ≤ 2*(patchFrame A r ν)^2 := by
  obtain ⟨Q, hd, hcQ, hest⟩ := local_graph_certificate hg hA hr hr1 hν hε hb hN hsmallr hsmallν hc hdet hsmall
  have ht := return_tube_certificate hc hr hr1 (patchFrame_one_le hA hr hν)
    (by positivity : 0 ≤ 74*(patchFrame A r ν)^4) Q hd hcQ hest
  refine ⟨returnBase c r Q, ht.1, ?_, ht.2.2⟩
  intro e
  convert ht.2.1 e using 1 <;> ring

end MeasureNorming

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
