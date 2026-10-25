import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.QuadraticTube
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.ZoomJets
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.TransportBounds

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

open Set MvPolynomial FubiniJets FubiniHessian QuadraticTube

noncomputable section

namespace MeasureNorming

def returnBase (c : Base) (r : ℝ) (Q : Poly) : Poly :=
  transportPolynomial (fun i => -(c i)/r) (r⁻¹ • (1:Matrix (Fin 3) (Fin 3) ℝ)) 1 Q

def inverseBase (c : Base) (r : ℝ) (u : Base) : Base := r⁻¹ • (u-c)

theorem coordinateMap_returnBase (c : Base) (r : ℝ) (u : Base) (w : ℝ) :
    coordinateMap (fun i => -(c i)/r) (r⁻¹ • (1:Matrix (Fin 3) (Fin 3) ℝ)) 1 (point u w) =
      point (inverseBase c r u) w := by
  have he (v : Base) (w : ℝ) : point v w = ![v 0,v 1,v 2,w] := by
    funext i
    fin_cases i <;> rfl
  rw [he, he]
  funext i
  fin_cases i <;>
    simp [coordinateMap, inverseBase, Matrix.smul_apply, Matrix.one_apply,
      Fin.sum_univ_three] <;> ring

theorem eval_returnBase (c : Base) (r : ℝ) (Q : Poly) (u : Base) (w : ℝ) :
    ev (returnBase c r Q) u w = ev Q (inverseBase c r u) w := by
  unfold returnBase ev
  rw [eval_transportPolynomial, coordinateMap_returnBase]

theorem pderiv_returnBase (c : Base) (r : ℝ) (Q : Poly) :
    pderiv (3:Fin 4) (returnBase c r Q) = returnBase c r (pderiv (3:Fin 4) Q) := by
  simp [returnBase, pderiv_transportPolynomial]

theorem degree_returnBase (c : Base) (r : ℝ) (Q : Poly) :
    (returnBase c r Q).totalDegree ≤ Q.totalDegree := totalDegree_transportPolynomial_le _ _ _ _

theorem coeff_returnBase {c : Base} (hc : c ∈ Metric.closedBall (0:Base) (1/2))
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (Q : Poly) {Z : ℝ} (hZ : 0 ≤ Z)
    (hdeg : Q.totalDegree ≤ 2) (hcoeff : ∀ e, |Q.coeff e| ≤ Z) (e : Fin 4 →₀ ℕ) :
    |(returnBase c r Q).coeff e| ≤ 1296*Z*(r⁻¹)^2 := by
  have hR : 1 ≤ r⁻¹ := (one_le_inv₀ hr).mpr hr1
  have hcn : ‖c‖ ≤ 1/2 := by simpa using hc
  apply transportPolynomial_coeff_bound _ _ _ _ hR hZ ?_ ?_ ?_ hdeg hcoeff e
  · intro i
    rw [abs_div, abs_neg, abs_of_pos hr]
    calc
      _ ≤ 1/r := div_le_div_of_nonneg_right ((PiLp.norm_apply_le c i).trans (by linarith)) hr.le
      _ = _ := one_div _
  · intro i j
    by_cases hij : i=j
    · simp [Matrix.smul_apply, Matrix.one_apply, hij, abs_of_pos (inv_pos.mpr hr)]
    · simp [Matrix.smul_apply, Matrix.one_apply, hij, inv_nonneg.mpr hr.le]
  · simpa using hR

theorem inverseBase_mem {c u : Base} {r : ℝ} (hr : 0 < r)
    (hu : u ∈ Metric.closedBall c r) : inverseBase c r u ∈ Metric.closedBall (0:Base) 1 := by
  have hd : ‖u-c‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hu
  rw [Metric.mem_closedBall, dist_zero_right, inverseBase, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hr)]
  calc
    _ ≤ r⁻¹*r := mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hr.le)
    _ = 1 := inv_mul_cancel₀ hr.ne'

theorem map_inverseBase (c : Base) {r : ℝ} (hr : r ≠ 0) (u : Base) :
    FubiniZoom.map c r (inverseBase c r u) = u := by
  rw [FubiniZoom.map, inverseBase, smul_smul, mul_inv_cancel₀ hr, one_smul]
  abel

/-- Return a quadratic graph certificate from a unit zoom to its original
base ball, retaining signed derivative regularity throughout a vertical tube. -/
theorem return_tube_certificate
    {g : Base → ℝ} {c : Base} (hc : c ∈ Metric.closedBall (0:Base) (1/2))
    {r A Z E : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hA : 1 ≤ A) (hZ : 0 ≤ Z)
    (Q : Poly) (hdeg : Q.totalDegree ≤ 2) (hcoeff : ∀ e, |Q.coeff e| ≤ Z)
    (hgraph : ∀ x ∈ Metric.closedBall (0:Base) 1,
      |ev Q x (FubiniZoom.pull g c r x)| ≤ E ∧
      A⁻¹ ≤ ev (pderiv (3:Fin 4) Q) x (FubiniZoom.pull g c r x) ∧
      ev (pderiv (3:Fin 4) Q) x (FubiniZoom.pull g c r x) ≤ 3*A ∧
      |ev (pderiv (3:Fin 4) (pderiv (3:Fin 4) Q)) x (FubiniZoom.pull g c r x)| ≤ 2*A^2) :
    (returnBase c r Q).totalDegree ≤ 2 ∧
    (∀ e, |(returnBase c r Q).coeff e| ≤ 1296*Z*(r⁻¹)^2) ∧
    ∀ u ∈ Metric.closedBall c r, ∀ w : ℝ, 4*A^3*|w-g u| ≤ 1 →
      |ev (returnBase c r Q) u w| ≤ E+4*A^2*|w-g u| ∧
      (2*A)⁻¹ ≤ ev (pderiv (3:Fin 4) (returnBase c r Q)) u w ∧
      ev (pderiv (3:Fin 4) (returnBase c r Q)) u w ≤ 4*A ∧
      |ev (pderiv (3:Fin 4) (pderiv (3:Fin 4) (returnBase c r Q))) u w| ≤ 2*A^2 := by
  refine ⟨(degree_returnBase c r Q).trans hdeg, coeff_returnBase hc hr hr1 Q hZ hdeg hcoeff, ?_⟩
  intro u hu w hw
  have hh := hgraph (inverseBase c r u) (inverseBase_mem hr hu)
  have he : FubiniZoom.pull g c r (inverseBase c r u) = g u := by
    unfold FubiniZoom.pull
    rw [map_inverseBase c hr.ne' u]
  rw [he] at hh
  have ht := QuadraticTube.estimates Q hdeg (inverseBase c r u) (g u) w hA
    hh.1 hh.2.1 hh.2.2.1 hh.2.2.2 hw
  simpa only [pderiv_returnBase, eval_returnBase] using ht

end MeasureNorming

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
