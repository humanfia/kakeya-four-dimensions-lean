-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/ObservationCell.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.ObservationIntercept
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.CrudeLipschitz

/-!
# Intercepts are nearly constant on a fine observation cell

Two points `z, z'` of retained trajectories whose base coordinates differ by at most `ϱ` in
`ℓ¹` and whose hidden coordinates differ by at most `η` have own intercepts within

  `2 εfit + Lip_F ϱ + (D + Lip_∂ ϱ) η`,

where `D` bounds the hidden derivative `∂₃ R_b` at both points (the chart gives `κ B`),
`Lip_F` is a box Lipschitz constant of `F = R_b - P` and `Lip_∂` one of `∂₃ R_b`
(`abs_eval_sub_eval_le_box`).  Pass through the auxiliary point `z̃` with the base of `z'` and
the hidden coordinate of `z`: from `z` to `z̃` only base coordinates move (crude Lipschitz),
from `z̃` to `z'` only the hidden one (exact two-point identity for the quadratic `R_b`, with
the hidden derivative at `z̃` controlled through `Lip_∂`).
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Broad

open MvPolynomial
open Submission.Lib.K4ChartLifting

noncomputable section

/-- The auxiliary point: base of `z'`, hidden coordinate of `z`. -/
def mixPoint (z z' : Fin 4 → ℝ) : Fin 4 → ℝ := Function.update z' 3 (z 3)

lemma mixPoint_base (z z' : Fin 4 → ℝ) (i : Fin 4) (hi : i ≠ 3) : mixPoint z z' i = z' i := by
  simp [mixPoint, Function.update_of_ne hi]

lemma mixPoint_hidden (z z' : Fin 4 → ℝ) : mixPoint z z' 3 = z 3 := by simp [mixPoint]

/-- Sum of coordinate differences between `z` and the auxiliary point: only base coordinates. -/
lemma sum_abs_sub_mixPoint (z z' : Fin 4 → ℝ) :
    ∑ i, |z i - mixPoint z z' i| =
      |z 0 - z' 0| + |z 1 - z' 1| + |z 2 - z' 2| := by
  rw [Fin.sum_univ_four]
  simp [mixPoint, Function.update_of_ne]

/-- **Intercept continuity on an observation cell.** -/
theorem intercept_close_of_cell {Rb : MvPolynomial (Fin 4) ℝ} (hR : Rb.totalDegree ≤ 2)
    (P : MvPolynomial (Fin 3) ℝ) (cpt : Ln → ℝ) {εfit D Bx ϱ η : ℝ} (hBx : 1 ≤ Bx)
    {l l' : Ln} {t t' : ℝ}
    (hfit : |MvPolynomial.eval (xp l t) Rb - MvPolynomial.eval (fun i => xp l t i.castSucc) P -
      cpt l| ≤ εfit)
    (hfit' : |MvPolynomial.eval (xp l' t') Rb -
      MvPolynomial.eval (fun i => xp l' t' i.castSucc) P - cpt l'| ≤ εfit)
    (hbox : ∀ i, |xp l t i| ≤ Bx) (hbox' : ∀ i, |xp l' t' i| ≤ Bx)
    (hbase : |xp l t 0 - xp l' t' 0| + |xp l t 1 - xp l' t' 1| + |xp l t 2 - xp l' t' 2| ≤ ϱ)
    (hhidden : |xp l t 3 - xp l' t' 3| ≤ η)
    (hder : |MvPolynomial.eval (xp l t) (pderiv 3 Rb)| ≤ D)
    (hder' : |MvPolynomial.eval (xp l' t') (pderiv 3 Rb)| ≤ D) :
    |cpt l - cpt l'| ≤ 2 * εfit +
      ((Rb - liftBase P).totalDegree * coeffL1 (Rb - liftBase P) *
        Bx ^ (Rb - liftBase P).totalDegree) * ϱ +
      (D + ((pderiv 3 Rb).totalDegree * coeffL1 (pderiv 3 Rb) *
        Bx ^ (pderiv 3 Rb).totalDegree) * ϱ) * η := by
  set z := xp l t with hz
  set z' := xp l' t' with hz'
  set zt := mixPoint z z' with hzt
  set F : MvPolynomial (Fin 4) ℝ := Rb - liftBase P with hF
  set LipF := (F.totalDegree : ℝ) * coeffL1 F * Bx ^ F.totalDegree with hLipF
  set LipD := ((pderiv 3 Rb).totalDegree : ℝ) * coeffL1 (pderiv 3 Rb) *
    Bx ^ (pderiv 3 Rb).totalDegree with hLipD
  have hboxt : ∀ i, |zt i| ≤ Bx := by
    intro i
    by_cases hi : i = 3
    · subst hi; rw [hzt, mixPoint_hidden]; exact hbox 3
    · rw [hzt, mixPoint_base z z' i hi]; exact hbox' i
  have hFeval : ∀ w : Fin 4 → ℝ, MvPolynomial.eval w F =
      MvPolynomial.eval w Rb - MvPolynomial.eval (fun i => w i.castSucc) P := by
    intro w; simp [hF, eval_liftBase]
  -- base move: crude Lipschitz for `F`
  have h1 : |MvPolynomial.eval z F - MvPolynomial.eval zt F| ≤ LipF * ϱ := by
    have := abs_eval_sub_eval_le_box F hBx z zt hbox hboxt
    rw [sum_abs_sub_mixPoint] at this
    refine this.trans ?_
    have hL : 0 ≤ LipF := by rw [hLipF]; unfold coeffL1; positivity
    exact mul_le_mul_of_nonneg_left hbase hL
  -- hidden move: two-point identity, the hidden derivative at `zt` via crude Lipschitz
  have hdert : |MvPolynomial.eval zt (pderiv 3 Rb)| ≤ D + LipD * ϱ := by
    have := abs_eval_sub_eval_le_box (pderiv 3 Rb) hBx z zt hbox hboxt
    rw [sum_abs_sub_mixPoint] at this
    have hL : 0 ≤ LipD := by rw [hLipD]; unfold coeffL1; positivity
    calc |MvPolynomial.eval zt (pderiv 3 Rb)|
        ≤ |MvPolynomial.eval z (pderiv 3 Rb)| +
          |MvPolynomial.eval z (pderiv 3 Rb) - MvPolynomial.eval zt (pderiv 3 Rb)| := by
          have := abs_sub_abs_le_abs_sub (MvPolynomial.eval zt (pderiv 3 Rb))
            (MvPolynomial.eval z (pderiv 3 Rb))
          rw [abs_sub_comm (MvPolynomial.eval z (pderiv 3 Rb))] at *
          linarith
      _ ≤ D + LipD * ϱ := add_le_add hder (this.trans (mul_le_mul_of_nonneg_left hbase hL))
  have hzzt : ∀ i : Fin 4, i ≠ 3 → zt i = z' i := fun i hi => mixPoint_base z z' i hi
  have h2 : |MvPolynomial.eval zt Rb - MvPolynomial.eval z' Rb| ≤ (D + LipD * ϱ) * η := by
    have hD' : |MvPolynomial.eval z' (pderiv 3 Rb)| ≤ D + LipD * ϱ := by
      have hL : 0 ≤ LipD * ϱ := by
        have : 0 ≤ ϱ := le_trans (by positivity) hbase
        have hL0 : 0 ≤ LipD := by rw [hLipD]; unfold coeffL1; positivity
        positivity
      linarith
    have := abs_eval_sub_le_of_hidden hR zt z' hzzt hdert hD'
    rw [hzt, mixPoint_hidden] at this
    exact this.trans (mul_le_mul_of_nonneg_left hhidden (le_trans (abs_nonneg _) hdert))
  -- the base coordinates of `zt` and `z'` agree, so `P` agrees
  have hPt : MvPolynomial.eval (fun i => zt i.castSucc) P =
      MvPolynomial.eval (fun i => z' i.castSucc) P := by
    have hfun : (fun i : Fin 3 => zt i.castSucc) = (fun i => z' i.castSucc) := by
      funext i
      exact hzzt _ (by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega)
    rw [hfun]
  -- assemble
  have hc : cpt l - cpt l' =
      -(MvPolynomial.eval z Rb - MvPolynomial.eval (fun i => z i.castSucc) P - cpt l) +
      (MvPolynomial.eval z' Rb - MvPolynomial.eval (fun i => z' i.castSucc) P - cpt l') +
      (MvPolynomial.eval z F - MvPolynomial.eval zt F) +
      (MvPolynomial.eval zt Rb - MvPolynomial.eval z' Rb) := by
    rw [hFeval z, hFeval zt, hPt]
    ring
  rw [hc]
  calc |-(MvPolynomial.eval z Rb - MvPolynomial.eval (fun i => z i.castSucc) P - cpt l) +
        (MvPolynomial.eval z' Rb - MvPolynomial.eval (fun i => z' i.castSucc) P - cpt l') +
        (MvPolynomial.eval z F - MvPolynomial.eval zt F) +
        (MvPolynomial.eval zt Rb - MvPolynomial.eval z' Rb)|
      ≤ εfit + εfit + LipF * ϱ + (D + LipD * ϱ) * η := by
        refine (abs_add_le _ _).trans (add_le_add ?_ h2)
        refine (abs_add_le _ _).trans (add_le_add ?_ h1)
        refine (abs_add_le _ _).trans (add_le_add ?_ hfit')
        rw [abs_neg]; exact hfit
    _ = _ := by rw [hLipF, hLipD]; ring

end

end Submission.Obl.k4_physical_parent_potential_candidates.Broad
