import Submission.Obl.k4_algebraic_sheet_bound.RootBarrier
import Submission.Obl.k4_algebraic_sheet_bound.ExceptionalSet
import Submission.Obl.k4_algebraic_sheet_bound.PolynomialCircle

namespace Submission.Obl.k4_algebraic_sheet_bound

open Set Metric Filter Polynomial
open scoped Topology

/-- Holomorphic chosen roots remain bounded at `1` near a limiting polynomial relation whose
leading coefficient does not vanish at the normalization point `0`.  Higher degree terms in
nearby relations may vanish in the limit. -/
theorem eventually_bound_of_polynomial_limit {A : Type*} [TopologicalSpace A]
    {u : ℕ → A} {p : A} (hu : Tendsto u atTop (𝓝 p))
    (H : A → ℂ → ℂ → ℂ)
    (hH : Continuous (fun z : A × (ℂ × ℂ) => H z.1 z.2.1 z.2.2))
    (Q : Polynomial (Polynomial ℂ))
    (hlim : ∀ t w : ℂ, H p t w = (Q.map (Polynomial.evalRingHom t)).eval w)
    (hlead : Q.leadingCoeff.eval 0 ≠ 0)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ j, DifferentiableOn ℂ (f j) (ball 0 2))
    (hroot : ∀ j, ∀ t ∈ ball (0 : ℂ) 2, H (u j) t (f j t) = 0)
    (hbase : ∀ j, ‖f j 0‖ ≤ 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ j in atTop, ‖f j 1‖ ≤ R := by
  have hQ : Q.leadingCoeff ≠ 0 := by
    intro h
    exact hlead (by simp [h])
  have hF : {t : ℂ | Q.leadingCoeff.eval t = 0}.Finite :=
    Polynomial.finite_setOfPred_isRoot hQ
  obtain ⟨r, K, hr1, hr2, hK, hconn, h0, hcircle, hsub, hdisj⟩ :=
    exists_compact_connected_circle_avoiding hF hlead
  have hKlead : ∀ t ∈ K, Q.leadingCoeff.eval t ≠ 0 := by
    intro t ht hzero
    exact Set.disjoint_left.mp hdisj ht hzero
  obtain ⟨R, hR, hfree⟩ := exists_root_free_circle Q hK hKlead
  have hcomp : IsCompact (K ×ˢ sphere (0 : ℂ) R) :=
    hK.prod (isCompact_sphere 0 R)
  have hnear : ∀ᶠ q in 𝓝 p, ∀ tw ∈ K ×ˢ sphere (0 : ℂ) R,
      H q tw.1 tw.2 ≠ 0 := by
    apply hcomp.eventually_forall_of_forall_eventually
    intro tw htw
    apply (hH.continuousAt.eventually_ne ?_)
    rw [hlim]
    exact hfree tw.1 htw.1 tw.2 (by simpa only [mem_sphere, dist_zero_right] using htw.2)
  refine ⟨R, by linarith, ?_⟩
  filter_upwards [hu.eventually hnear] with j hj
  have hfreej : ∀ t ∈ K, ∀ w : ℂ, ‖w‖ = R → H (u j) t w ≠ 0 := by
    intro t ht w hw
    exact hj (t, w) ⟨ht, by simpa only [mem_sphere, dist_zero_right] using hw⟩
  have hdiff : DiffContOnCl ℂ (f j) (ball 0 r) :=
    ⟨(hf j).mono (ball_subset_ball hr2.le),
      ((hf j).continuousOn).mono (by
        rw [closure_ball (0 : ℂ) (show r ≠ 0 by linarith)]
        exact closedBall_subset_ball hr2)⟩
  exact norm_le_on_disk_of_root_free_circle hconn (by linarith) hcircle
    ((hf j).continuousOn.mono hsub) (fun t ht => hroot j t (hsub ht))
    hfreej h0 ((hbase j).trans_lt hR) hdiff (by simp; linarith)

end Submission.Obl.k4_algebraic_sheet_bound
