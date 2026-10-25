import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.ZoomJets
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.HessianPatch

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

open Set MvPolynomial FubiniJets FubiniHessian

noncomputable section

namespace MeasureNorming

def patchBudget (A r ν : ℝ) : ℝ := 2+A+2/(r^6*ν)

def patchFrame (A r ν : ℝ) : ℝ := frameBudget (2000*(patchBudget A r ν)^4)

def patchError (A r ν : ℝ) : ℝ :=
  18000000*(patchFrame A r ν)^8*(2000*(patchBudget A r ν)^4)^5

/-- The checked Fubini integration on an actual regular Hessian ball.
Only ordinary graph jets and the C²-small cleared tensor are supplied. -/
theorem local_graph_certificate
    {g : Base → ℝ} (hg : ContDiffOn ℝ 6 g (Metric.ball (0:Base) 3))
    {A r ν ε : ℝ} (hA : 1 ≤ A) (hr : 0 < r) (hr1 : r ≤ 1) (hν : 0 < ν) (hε : 0 ≤ ε)
    (hb : ∀ n : ℕ, n ≤ 4 → ∀ x ∈ Metric.closedBall (0:Base) 1,
      ‖iteratedFDeriv ℝ n g x‖ ≤ A)
    (hN : ∀ x ∈ Metric.closedBall (0:Base) 1, ∀ i j k,
      C2Bound (fun y => clearedCubicError g y i j k) ε x)
    (hsmallr : 4*r ≤ 1/2) (hsmallν : 1152*A^3*r ≤ ν/2)
    {c : Base} (hc : c ∈ Metric.closedBall (0:Base) (1/2)) (hdet : ν ≤ |(hessian g c).det|)
    (hsmall : 3000000*(patchFrame A r ν)^9*(6*(2000*(patchBudget A r ν)^4)^5*ε) ≤ 1) :
    ∃ Q : MvPolynomial (Fin 4) ℝ,
      Q.totalDegree ≤ 2 ∧ (∀ e, |Q.coeff e| ≤ 74*(patchFrame A r ν)^4) ∧
      ∀ x ∈ Metric.closedBall (0:Base) 1,
        |eval (Fin.snoc (fun i => x i) (FubiniZoom.pull g c r x)) Q| ≤ patchError A r ν*ε ∧
        (patchFrame A r ν)⁻¹ ≤
          eval (Fin.snoc (fun i => x i) (FubiniZoom.pull g c r x)) (pderiv (3:Fin 4) Q) ∧
        eval (Fin.snoc (fun i => x i) (FubiniZoom.pull g c r x)) (pderiv (3:Fin 4) Q) ≤
          3*patchFrame A r ν ∧
        |eval (Fin.snoc (fun i => x i) (FubiniZoom.pull g c r x))
          (pderiv (3:Fin 4) (pderiv (3:Fin 4) Q))| ≤ 2*(patchFrame A r ν)^2 := by
  have hA0 : 0 ≤ A := by linarith
  let K := patchBudget A r ν
  have hprod0 : 0 < r^6*ν := mul_pos (pow_pos hr 6) hν
  have hKr : 2/(r^6*ν) ≤ K := by dsimp [K, patchBudget]; linarith
  have hKA : A ≤ K := by
    dsimp [K, patchBudget]
    have hh : 0 ≤ 2/(r^6*ν) := by positivity
    linarith
  have hK : 1 ≤ K := hA.trans hKA
  have hK0 : 0 ≤ K := by linarith
  have hregK : K⁻¹ ≤ r^6*ν/2 := by
    have hh := one_div_le_one_div_of_le (div_pos (by norm_num : (0:ℝ) < 2) hprod0) hKr
    calc
      _ ≤ (2/(r^6*ν))⁻¹ := by simpa only [one_div] using hh
      _ = _ := by field_simp
  have hpatch := regular_hessian_ball hg hA0 hr.le
    (fun n _ hn x hx => hb n hn x hx) hsmallr hsmallν hc hdet
  have hzoom4 (x : Base) (hx : ‖x‖ ≤ 3) :
      FubiniZoom.map c r x ∈ Metric.closedBall c (4*r) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp only [FubiniZoom.map, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith
  have hz1 (x : Base) (hx : ‖x‖ ≤ 3) : FubiniZoom.map c r x ∈ Metric.closedBall (0:Base) 1 :=
    (hpatch _ (hzoom4 x hx)).1
  have hz3 (x : Base) (hx : ‖x‖ ≤ 3) : FubiniZoom.map c r x ∈ Metric.ball (0:Base) 3 :=
    Metric.closedBall_subset_ball (by norm_num : (1:ℝ) < 3) (hz1 x hx)
  have hdom3 : MapsTo (FubiniZoom.map c r) (Metric.ball (0:Base) 3) (Metric.ball (0:Base) 3) := by
    intro x hx
    exact hz3 x (by simpa using (Metric.mem_ball.mp hx).le)
  have hgs := FubiniZoom.contDiffOn_pull hg c r hdom3
  have hlow (x : Base) (hx : ‖x‖ ≤ 3) :
      r^6*ν/2 ≤ |(hessian (FubiniZoom.pull g c r) x).det| := by
    rw [FubiniZoom.det_hessian_pull Metric.isOpen_ball hg c r x (hz3 x hx), abs_mul,
      abs_of_pos (pow_pos hr 6)]
    convert mul_le_mul_of_nonneg_left (hpatch _ (hzoom4 x hx)).2 (pow_nonneg hr.le 6) using 1 <;> ring
  have hreg : ∀ x ∈ Metric.ball (0:Base) 3, (hessian (FubiniZoom.pull g c r) x).det ≠ 0 := by
    intro x hx
    apply abs_pos.mp
    exact (div_pos hprod0 (by norm_num : (0:ℝ) < 2)).trans_le
      (hlow x (by simpa using (Metric.mem_ball.mp hx).le))
  have hunit (x : Base) (hx : x ∈ Metric.closedBall (0:Base) 1) : ‖x‖ ≤ 3 := by
    have hh : ‖x‖ ≤ 1 := by simpa using hx
    linarith
  have hbzoom (n : ℕ) (hn : n ≤ 4) (x : Base) (hx : x ∈ Metric.closedBall (0:Base) 1) :
      ‖iteratedFDeriv ℝ n (FubiniZoom.pull g c r) x‖ ≤ K :=
    (FubiniZoom.norm_pull_bound Metric.isOpen_ball hg (by exact_mod_cast hn.trans (by decide : 4 ≤ 6))
      c hr.le hr1 x (hz3 x (hunit x hx)) (hb n hn _ (hz1 x (hunit x hx)))).trans hKA
  have hNzoom (x : Base) (hx : x ∈ Metric.closedBall (0:Base) 1) :=
    FubiniZoom.cleared_pull_C2_bound Metric.isOpen_ball hg c hr.le hr1 x (hz3 x (hunit x hx))
      (hN _ (hz1 x (hunit x hx)))
  have hconst (x : Base) : C2Bound (fun _ : Base => (1:ℝ)) K x := by
    refine ⟨by simpa using hK, ?_, ?_⟩
    · intro i
      simpa only [jet, iteratedFDeriv_const_of_ne (by decide : 1 ≠ 0), Pi.zero_apply,
        ContinuousMultilinearMap.zero_apply, abs_zero] using hK0
    · intro i j
      simpa only [jet, iteratedFDeriv_const_of_ne (by decide : 2 ≠ 0), Pi.zero_apply,
        ContinuousMultilinearMap.zero_apply, abs_zero] using hK0
  apply restoration_of_conditioned_implicit_numerator Metric.isOpen_ball hgs
    (Metric.closedBall_subset_ball (by norm_num : (1:ℝ) < 3)) hreg contDiffOn_const
    (fun x hx i j k => ?_) hK hε hbzoom
    (fun x hx => hregK.trans (hlow x (hunit x hx)))
    (fun _ _ => by simpa using inv_le_one_of_one_le₀ hK)
    (fun x _ => hconst x)
    (fun x hx i j k => (hNzoom x hx i j k).value)
    (fun x hx p i j k => (hNzoom x hx i j k).first p)
    (fun x hx p l i j k => (hNzoom x hx i j k).second p l) hsmall
  rw [clearedCubicError_eq Metric.isOpen_ball hgs hreg hx]
  ring

end MeasureNorming

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
