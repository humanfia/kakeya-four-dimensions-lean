import Submission.Obl.k4_pair_anchor_jet_bins.Interface

namespace Submission.Obl.k4_pair_anchor_jet_bins.DiscIdentities
open MvPolynomial Submission.Lib.K4QuadraticSheets
lemma degree_map_le (P : Test) : (P.map (algebraMap ℝ ℂ)).totalDegree ≤ P.totalDegree := by
  classical
  exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)
lemma eval_map_real {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    eval (fun i => (x i : ℂ)) (P.map (algebraMap ℝ ℂ)) = (eval x P : ℂ) :=
  (map_eval (algebraMap ℝ ℂ) x P).symm
lemma qc_map_real (P : Test) : qc (P.map (algebraMap ℝ ℂ)) =
    (eval (0 : Fin 4 → ℝ) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P)) : ℂ) := by
  unfold qc
  rw [pderiv_map, pderiv_map]
  change eval (fun _ => (0 : ℂ)) ((pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P)).map
    (algebraMap ℝ ℂ)) = (eval (fun _ => (0 : ℝ)) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P)) : ℂ)
  exact eval_map_real _ (fun _ => 0)

lemma eval₂_disc (P : Test) (z : Fin 3 → ℂ) :
    eval z ((disc P).map (algebraMap ℝ ℂ)) =
      eval (Fin.snoc z 0) (((pderiv (3 : Fin 4) P) ^ 2 -
        2 * pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P) * P).map (algebraMap ℝ ℂ)) := by
  rw [disc, ← eval₂_eq_eval_map]
  change eval₂Hom (algebraMap ℝ ℂ) z (eval₂Hom C _ _) = _
  rw [map_eval₂Hom]
  have hc : (eval₂Hom (algebraMap ℝ ℂ) z).comp C = algebraMap ℝ ℂ := by ext; simp
  rw [hc, ← eval₂_eq_eval_map]
  change eval₂ (algebraMap ℝ ℂ) (fun i => eval₂Hom (algebraMap ℝ ℂ) z (Fin.lastCases 0 X i)) _ = _
  apply congrArg (fun y : Fin 4 → ℂ => eval₂ (algebraMap ℝ ℂ) y _)
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change eval₂ (algebraMap ℝ ℂ) z
      (Fin.lastCases (0 : MvPolynomial (Fin 3) ℝ) X (Fin.last 3)) =
      (Fin.snoc z 0 : Fin 4 → ℂ) (Fin.last 3)
    simp only [Fin.lastCases_last, Fin.snoc_last, eval₂_zero]
  · simp only [Fin.lastCases_castSucc, Fin.snoc_castSucc, eval₂Hom_X']
lemma eval_disc_eq_qdisc (P : Test) (hP : P.totalDegree ≤ 2) (z : Fin 3 → ℂ) :
    eval z ((disc P).map (algebraMap ℝ ℂ)) = qdisc (P.map (algebraMap ℝ ℂ)) z := by
  rw [eval₂_disc]
  simp only [map_sub, map_pow, map_mul, map_ofNat, ← pderiv_map]
  have heval : eval (Fin.snoc z 0)
      (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (P.map (algebraMap ℝ ℂ)))) =
      qc (P.map (algebraMap ℝ ℂ)) := by
    simpa only [show Fin.last 3 = (3 : Fin 4) from rfl] using
      eval_pderiv2_eq_qc (P.map (algebraMap ℝ ℂ)) ((degree_map_le P).trans hP) (Fin.snoc z 0)
  rw [heval]
  rfl
end Submission.Obl.k4_pair_anchor_jet_bins.DiscIdentities
