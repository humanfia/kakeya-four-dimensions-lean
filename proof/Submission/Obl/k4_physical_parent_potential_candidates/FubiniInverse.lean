import Submission.Obl.k4_physical_parent_potential_candidates.FubiniLogDet

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Matrix Set
open scoped BigOperators

noncomputable section

/-- Entrywise smoothness of matrix inversion on a regular three-dimensional patch. -/
theorem contDiffOn_inverse_entries_three
    {H : FubiniBase → Matrix (Fin 3) (Fin 3) ℝ} {U : Set FubiniBase} {n : WithTop ℕ∞}
    (hH : ∀ i j, ContDiffOn ℝ n (fun x => H x i j) U)
    (hdet : ∀ x ∈ U, (H x).det ≠ 0) :
    ∀ i j, ContDiffOn ℝ n (fun x => (H x)⁻¹ i j) U := by
  have hdetSmooth : ContDiffOn ℝ n (fun x => (H x).det) U := by
    simp only [Matrix.det_fin_three]
    fun_prop
  have hadj : ∀ i j, ContDiffOn ℝ n (fun x => (H x).adjugate i j) U := by
    intro i j
    simp only [Matrix.adjugate_fin_three]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  intro i j
  simpa only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv, Pi.inv_apply, Pi.mul_apply] using
    (hdetSmooth.inv hdet).mul (hadj i j)

/-- The inverse derivative follows from differentiating the genuine
identity H H^-1=1, rather than introducing a formal matrix inverse jet. -/
theorem hasDerivAt_inverse_entries_three
    {H : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {H' : Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ}
    (hH : ∀ i j, HasDerivAt (fun s => H s i j) (H' i j) t) (hdet : (H t).det ≠ 0) :
    ∀ i j, HasDerivAt (fun s => (H s)⁻¹ i j) (-((H t)⁻¹*H'*(H t)⁻¹) i j) t := by
  have hdetd := hasDerivAt_det_three hH
  have hadj : ∀ i j, DifferentiableAt ℝ (fun s => (H s).adjugate i j) t := by
    have hHd : ∀ i j, DifferentiableAt ℝ (fun s => H s i j) t := fun i j => (hH i j).differentiableAt
    intro i j
    simp only [Matrix.adjugate_fin_three]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hGd : ∀ i j, DifferentiableAt ℝ (fun s => (H s)⁻¹ i j) t := by
    intro i j
    have hh := (hdetd.differentiableAt.inv hdet).mul (hadj i j)
    convert hh using 1
    funext s
    simp [Matrix.inv_def, Ring.inverse_eq_inv]
  let G' : Matrix (Fin 3) (Fin 3) ℝ := fun i j => deriv (fun s => (H s)⁻¹ i j) t
  have hG : ∀ i j, HasDerivAt (fun s => (H s)⁻¹ i j) (G' i j) t := fun i j => (hGd i j).hasDerivAt
  have hnear : ∀ᶠ s in nhds t, (H s).det ≠ 0 := hdetd.continuousAt.eventually_ne hdet
  have hprod (i j : Fin 3) :
      ∑ k : Fin 3, (H' i k*(H t)⁻¹ k j+H t i k*G' k j) = 0 := by
    have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => (hH i k).mul (hG k j))
    have heq : (fun s => ∑ k : Fin 3, H s i k*(H s)⁻¹ k j) =ᶠ[nhds t]
        (fun _ => (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) := by
      filter_upwards [hnear] with s hs
      exact congrFun (congrFun (Matrix.mul_nonsing_inv (H s) (isUnit_iff_ne_zero.mpr hs)) i) j
    have hz := (hasDerivAt_const t ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j)).congr_of_eventuallyEq heq
    exact hh.unique hz
  have hmat : H'*(H t)⁻¹+H t*G' = 0 := by
    ext i j
    simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply, ← Finset.sum_add_distrib] using hprod i j
  have hG'eq : G' = -((H t)⁻¹*H'*(H t)⁻¹) := by
    calc
      G' = (H t)⁻¹*(H t*G') := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul (H t) (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mul]
      _ = (H t)⁻¹* (-(H'*(H t)⁻¹)) := congrArg (fun M => (H t)⁻¹*M) (eq_neg_of_add_eq_zero_right hmat)
      _ = _ := by rw [Matrix.mul_neg, Matrix.mul_assoc]
  intro i j
  have hh := hG i j
  rw [hG'eq] at hh
  simpa only [Matrix.neg_apply, Matrix.neg_mul] using hh

end

end Submission.Obl.k4_physical_parent_potential_candidates
