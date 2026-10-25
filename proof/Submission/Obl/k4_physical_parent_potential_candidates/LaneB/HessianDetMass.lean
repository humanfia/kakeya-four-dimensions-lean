import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.MeasureNorming
import Submission.Obl.k4_approximate_conic_taylor_decomposition.RestoredDirections

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

open Set MeasureTheory FubiniJets FubiniHessian
open Submission.Obl.k4_real_conic_restoration (quad coeff coeff_le entry_le_coeff)
open scoped ENNReal

noncomputable section

namespace MeasureNorming

/-- The determinant floor forced by the per-event conics holds on a set
carrying at least half the original measure. The conditioning R is separate
from the measure density A, so both remain explicit polynomial budgets. -/
theorem regular_hessian_mass :
    ∃ Dc : ℕ, 1 ≤ Dc ∧ ∀ {D J : ℕ}, DenseJetBound D J →
    ∀ {g : Base → ℝ}, ContDiffOn ℝ 6 g (Metric.ball (0:Base) 3) →
    (∀ i j, HasRealExtension D (fun x => hessian g x i j)) →
    (∀ (c : ℝ) (L : Base →L[ℝ] ℝ),
      ∃ u ∈ Metric.closedBall (0:Base) 1, 1 ≤ |g u-c-L u|) →
    ∀ {μ : Measure Base}, μ univ ≠ 0 → μ univ ≠ ⊤ →
    ∀ {A R η : ℝ}, 2 ≤ A → A ≤ R → 0 ≤ η →
    (∀ E : Set Base, MeasurableSet E → μ E ≤ ENNReal.ofReal A*μ univ*volume E) →
    μ (Metric.closedBall (0:Base) (1/2))ᶜ = 0 →
    (∀ x ∈ Metric.closedBall (0:Base) (1/2), ‖iteratedFDeriv ℝ 2 g x‖ ≤ A) →
    (R^4)⁻¹ ≤ (100*(2*A)^J)⁻¹ → 9*A ≤ R^4 → η*R^(4*Dc+1) ≤ 1 →
    (∀ᵐ x ∂μ, ∃ p : Fin 7 → Base,
      (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ A) ∧
      (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
        A⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)|) ∧
      (∀ i, |iteratedFDeriv ℝ 2 g x (fun _ => p i)| ≤ η)) →
    MeasurableSet {x : Base | x ∈ Metric.closedBall (0:Base) (1/2) ∧
      (R^(4*Dc))⁻¹ ≤ |(hessian g x).det|} ∧
    μ univ/2 ≤ μ {x : Base | x ∈ Metric.closedBall (0:Base) (1/2) ∧
      (R^(4*Dc))⁻¹ ≤ |(hessian g x).det|} := by
  obtain ⟨Dc, hDc, hrestore⟩ :=
    Submission.Obl.k4_approximate_conic_taylor_decomposition.Backup.conditioned_conic_restoration
  refine ⟨Dc, hDc, ?_⟩
  intro D J hjet g hg hext hnon μ hμ0 hμfin A R η hA hAR hη hdom hsupport hHnorm
    hfloor hupper hsmall hdirs
  have hA0 : 0 < A := by linarith
  have hR2 : 2 ≤ R := hA.trans hAR
  have hR1 : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  let G := {x : Base | x ∈ Metric.closedBall (0:Base) (1/2) ∧
    (R^(4*Dc))⁻¹ ≤ |(hessian g x).det|}
  let Hbig := {x : Base | x ∈ Metric.closedBall (0:Base) (1/2) ∧
    ∃ i j, (100*(2*A)^J)⁻¹ < |hessian g x i j|}
  have hcont (i j : Fin 3) : ContinuousOn (fun x => hessian g x i j)
      (Metric.closedBall (0:Base) (1/2)) :=
    (contDiffOn_jet Metric.isOpen_ball hg (M := 0) (by norm_num) ![i,j]).continuousOn.mono
      (Metric.closedBall_subset_ball (by norm_num : (1:ℝ)/2 < 3))
  have hdetcont : ContinuousOn (fun x => (hessian g x).det)
      (Metric.closedBall (0:Base) (1/2)) := by
    simp only [Matrix.det_fin_three]
    fun_prop
  have hGm : MeasurableSet G :=
    (hdetcont.abs.preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_Ici).measurableSet
  have hgood : Hbig ≤ᵐ[μ] G := by
    filter_upwards [hdirs] with x hxdir
    intro hx
    obtain ⟨p, hp, htr, htest⟩ := hxdir
    have hx3 : x ∈ Metric.ball (0:Base) 3 :=
      Metric.closedBall_subset_ball (by norm_num : (1:ℝ)/2 < 3) hx.1
    have hsym := hessian_symmetric Metric.isOpen_ball hg hx3
    have hpR : ∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ R := fun i => ⟨(hp i).1, (hp i).2.trans hAR⟩
    have htrR (i j k : Fin 7) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
        R⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)| := by
      have hRA : R⁻¹ ≤ A⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le hA0 hAR
      exact hRA.trans (htr i j k hij hik hjk)
    have hentry (i j : Fin 3) : |hessian g x i j| ≤ A :=
      coordinate_jet_bound (hHnorm x hx.1) ![i,j]
    have hcoefup : coeff (hessian g x) ≤ R^4 := (coeff_le hentry).trans hupper
    have hcoeflo : (R^4)⁻¹ ≤ coeff (hessian g x) := by
      obtain ⟨i,j,hij⟩ := hx.2
      exact hfloor.trans ((hij.le).trans (entry_le_coeff _ i j))
    have hquad (i : Fin 7) : |quad (hessian g x) (fun j => p i j)| ≤ R*η := by
      rw [hessian_diagonal_eq]
      exact (htest i).trans (le_mul_of_one_le_left hη hR1)
    obtain ⟨hd, -⟩ := hrestore R η hR2 hη p (hessian g x) hpR htrR hsym
      hcoeflo hcoefup hquad hsmall
    exact ⟨hx.1, hd⟩
  have hmass := (large_hessian_mass hjet hg hext hnon hμ0 hμfin hA hdom hsupport).2
  exact ⟨hGm, hmass.trans (measure_mono_ae hgood)⟩

end MeasureNorming

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
