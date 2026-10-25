import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.HessianDetMass
import Submission.Obl.k4_physical_parent_potential_candidates.FubiniC2Bounds
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.Analytic.QuantitativeLocalization

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

open Set MeasureTheory FubiniJets FubiniHessian
open scoped ENNReal

noncomputable section

namespace MeasureNorming

/-- First coordinate-jet bounds give a full derivative bound with the
explicit dimension factor three. -/
theorem norm_fderiv_of_coordinate_bounds (f : Base → ℝ) (x : Base) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ i, |jet f 1 ![i] x| ≤ K) : ‖fderiv ℝ f x‖ ≤ 3*K := by
  have hcoeff (i : Fin 3) : |fderiv ℝ f x (basis i)| ≤ K := by
    have hh := hb i
    simpa only [jet, iteratedFDeriv_one_apply, Fin.isValue, Matrix.cons_val_zero] using hh
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  rw [Real.norm_eq_abs, ← Submission.Obl.k4_seven_direction_local_degree_restoration.linear_coordinates]
  calc
    _ ≤ ∑ i : Fin 3, |fderiv ℝ f x (EuclideanSpace.basisFun (Fin 3) ℝ i)*u i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, K*‖u‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (hcoeff i) (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u i)
        (abs_nonneg _) hK
    _ = _ := by simp; ring

/-- The Hessian determinant is Lipschitz on the unit ball, with a fixed
cubic loss in the graph's normalized jet budget. -/
theorem hessian_det_lipschitz
    {g : Base → ℝ} (hg : ContDiffOn ℝ 6 g (Metric.ball (0:Base) 3))
    {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ n : ℕ, 2 ≤ n → n ≤ 4 → ∀ x ∈ Metric.closedBall (0:Base) 1,
      ‖iteratedFDeriv ℝ n g x‖ ≤ A)
    {x y : Base} (hx : x ∈ Metric.closedBall (0:Base) 1)
    (hy : y ∈ Metric.closedBall (0:Base) 1) :
    |(hessian g y).det-(hessian g x).det| ≤ 288*A^3*‖y-x‖ := by
  have hd : ContDiffOn ℝ 2 (fun z => (hessian g z).det) (Metric.ball (0:Base) 3) :=
    det_contDiffOn (fun i j => contDiffOn_jet Metric.isOpen_ball hg (by norm_num) ![i,j])
  have hdiff (z : Base) (hz : z ∈ Metric.closedBall (0:Base) 1) :
      DifferentiableAt ℝ (fun z => (hessian g z).det) z :=
    (hd.contDiffAt (Metric.isOpen_ball.mem_nhds
      (Metric.closedBall_subset_ball (by norm_num : (1:ℝ) < 3) hz))).differentiableAt (by norm_num)
  have hder (z : Base) (hz : z ∈ Metric.closedBall (0:Base) 1) :
      ‖fderiv ℝ (fun z => (hessian g z).det) z‖ ≤ 288*A^3 := by
    have hh := hessian_det_C2_bound Metric.isOpen_ball hg
      (Metric.closedBall_subset_ball (by norm_num : (1:ℝ) < 3) hz) (fun n hn hn' => hb n hn hn' z hz)
    convert norm_fderiv_of_coordinate_bounds _ z (by positivity : 0 ≤ 96*A^3) hh.first using 1 <;> ring
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
    hdiff hder (convex_closedBall (0:Base) 1) hx hy

/-- A regular Hessian at a retained centre stays regular on a quantitative
ball around it; the ball lies inside the original unit ball. -/
theorem regular_hessian_ball
    {g : Base → ℝ} (hg : ContDiffOn ℝ 6 g (Metric.ball (0:Base) 3))
    {A r ν : ℝ} (hA : 0 ≤ A) (hr : 0 ≤ r)
    (hb : ∀ n : ℕ, 2 ≤ n → n ≤ 4 → ∀ x ∈ Metric.closedBall (0:Base) 1,
      ‖iteratedFDeriv ℝ n g x‖ ≤ A)
    (hsmallr : 4*r ≤ 1/2) (hsmallν : 1152*A^3*r ≤ ν/2)
    {c : Base} (hc : c ∈ Metric.closedBall (0:Base) (1/2)) (hdet : ν ≤ |(hessian g c).det|) :
    ∀ x ∈ Metric.closedBall c (4*r), x ∈ Metric.closedBall (0:Base) 1 ∧
      ν/2 ≤ |(hessian g x).det| := by
  intro x hx
  have hdist : ‖x-c‖ ≤ 4*r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
  have hcn : ‖c‖ ≤ 1/2 := by simpa using hc
  have hxn : ‖x‖ ≤ 1 := by
    have hh : ‖x‖ ≤ ‖x-c‖+‖c‖ := by
      calc ‖x‖ = ‖(x-c)+c‖ := by congr 1; abel
           _ ≤ _ := norm_add_le _ _
    linarith
  have hx1 : x ∈ Metric.closedBall (0:Base) 1 := by simpa using hxn
  have hc1 : c ∈ Metric.closedBall (0:Base) 1 :=
    Metric.closedBall_subset_closedBall (by norm_num : (1:ℝ)/2 ≤ 1) hc
  have hd := hessian_det_lipschitz hg hA hb hc1 hx1
  have hdiff : |(hessian g x).det-(hessian g c).det| ≤ ν/2 := by
    apply hd.trans
    calc
      _ ≤ 288*A^3*(4*r) := mul_le_mul_of_nonneg_left hdist (by positivity)
      _ = 1152*A^3*r := by ring
      _ ≤ _ := hsmallν
  refine ⟨hx1, ?_⟩
  have hh := abs_sub (hessian g c).det (hessian g x).det
  have he : (hessian g c).det-((hessian g c).det-(hessian g x).det) = (hessian g x).det := by ring
  have hh' := abs_sub ((hessian g c).det-(hessian g x).det) (-(hessian g x).det)
  have htri : |(hessian g c).det| ≤ |(hessian g c).det-(hessian g x).det|+|(hessian g x).det| := by
    convert abs_add_le ((hessian g c).det-(hessian g x).det) (hessian g x).det using 1 <;> congr 1 <;> ring
  rw [abs_sub_comm] at hdiff
  linarith

/-- Localize a positive regular set without changing its reference measure.
The chosen centre itself belongs to the regular set. -/
theorem heavy_regular_ball
    (μ : Measure Base) (G : Set Base) (hGm : MeasurableSet G)
    (hGsub : G ⊆ Metric.closedBall (0:Base) (1/2))
    (hμ0 : μ univ ≠ 0) (hμfin : μ univ ≠ ⊤) (hGmass : μ univ/2 ≤ μ G)
    {A : ℝ} (hA : 2 ≤ A) (M : ℕ) :
    ∃ c ∈ G, μ univ ≤ ENNReal.ofReal (2*A^(3*M+14))*
      μ {x | x ∈ G ∧ x ∈ Metric.ball c (A^M)⁻¹} := by
  have hne : G.Nonempty := by
    by_contra h
    have he := Set.not_nonempty_iff_eq_empty.mp h
    rw [he, measure_empty] at hGmass
    have hhalf : μ univ/2 ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hμ0, by norm_num⟩
    exact hhalf (le_antisymm hGmass bot_le)
  obtain ⟨c, hc, hm⟩ := power_bounded_image_mass_localization μ id G hne hA 0 M
    (fun x hx => by
      have hh := hGsub hx
      rw [Metric.mem_closedBall, dist_zero_right] at hh
      simpa only [id_eq, pow_zero, Metric.mem_ball, dist_zero_right] using lt_of_le_of_lt hh (by norm_num : (1:ℝ)/2 < 1))
    (ne_top_of_le_ne_top hμfin (measure_mono (subset_univ G)))
  refine ⟨c, hc, ?_⟩
  have hh := mul_le_mul_of_nonneg_left (hGmass.trans hm) (by positivity : (0:ENNReal) ≤ 2)
  have hmul (b : ℝ) : (2:ENNReal)*ENNReal.ofReal b = ENNReal.ofReal (2*b) := by
    simpa using (ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2) (q := b)).symm
  rw [ENNReal.mul_div_cancel (by norm_num : (2:ENNReal) ≠ 0) (by norm_num : (2:ENNReal) ≠ ⊤),
    ← mul_assoc, hmul] at hh
  simpa only [id_eq, zero_add] using hh

end MeasureNorming

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
