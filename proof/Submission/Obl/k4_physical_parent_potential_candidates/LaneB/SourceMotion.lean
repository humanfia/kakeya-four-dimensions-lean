import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.SourceSevenInputs

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set Metric

noncomputable section

namespace SourceNormalization

/-- The actual source frame and its isotropic zoom have the expected
physical clock speed, with no use of hidden line coefficients. -/
theorem eventBase_speed (T j : ℕ) (c u : P2) {K lam B : ℝ}
    (hK : 2 ≤ K) (hlam : 0 < lam) (b cz : Fin 3 → ℝ)
    (l : Ln) (hvel : ‖v l‖ ≤ K) (t s : ℝ) :
    ‖eventBase T j c u (8*K) b cz lam B (l,t)-
      eventBase T j c u (8*K) b cz lam B (l,s)‖ ≤ lam/((2:ℝ)^T)⁻¹*|t-s| := by
  have hK0 : 0 < K := by linarith
  have hh : 0 < ((2:ℝ)^T)⁻¹ := by positivity
  have hscale : 0 < scale T (8*K) := scale_pos T (by positivity)
  have hdir := (norm_lift_velocity (v l)).trans
    (show 1+2*‖v l‖ ≤ 8*K by linarith only [hvel,hK])
  unfold eventBase
  rw [Analytic.normalizedBase_graphPoint,add_sub_cancel_left,
    lineDir_source_matrix,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_pos (div_pos hlam hscale)]
  calc
    _ ≤ |t-s| *(lam/scale T (8*K)*(8*K)) := by gcongr
    _ = _ := by dsimp only [scale]; field_simp

/-- A retained anchor in the inner ball stays in the doubled certified
ball throughout any time window whose base displacement is at most `r`. -/
theorem eventBase_stays_double_ball (T j : ℕ) (c u : P2) {K lam B theta r : ℝ}
    (hK : 2 ≤ K) (hlam : 0 < lam) (b cz : Fin 3 → ℝ)
    (e : Ev) (hvel : ‖v e.1‖ ≤ K) (cq : P3)
    (hanchor : eventBase T j c u (8*K) b cz lam B e ∈ ball cq r)
    (hstep : lam*theta ≤ r) (t : ℝ)
    (htime : |t-e.2| ≤ theta*((2:ℝ)^T)⁻¹) :
    eventBase T j c u (8*K) b cz lam B (e.1,t) ∈ closedBall cq (2*r) := by
  have hh : 0 < ((2:ℝ)^T)⁻¹ := by positivity
  have hspeed := eventBase_speed T j c u (B := B) hK hlam b cz e.1 hvel t e.2
  have hdist : ‖eventBase T j c u (8*K) b cz lam B (e.1,t)-
      eventBase T j c u (8*K) b cz lam B e‖ ≤ r := by
    calc
      _ ≤ lam/((2:ℝ)^T)⁻¹*|t-e.2| := hspeed
      _ ≤ lam/((2:ℝ)^T)⁻¹*(theta*((2:ℝ)^T)⁻¹) := by gcongr
      _ = lam*theta := by field_simp
      _ ≤ r := hstep
  rw [mem_closedBall,dist_eq_norm]
  rw [mem_ball,dist_eq_norm] at hanchor
  have htri := norm_add_le
    (eventBase T j c u (8*K) b cz lam B (e.1,t)-
      eventBase T j c u (8*K) b cz lam B e)
    (eventBase T j c u (8*K) b cz lam B e-cq)
  rw [sub_add_sub_cancel] at htri
  linarith only [htri,hdist,hanchor]

end SourceNormalization

end

end Submission.Obl.k4_physical_parent_potential_candidates
