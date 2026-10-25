import Submission.Obl.k4_physical_parent_potential_candidates.FubiniJets

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Matrix Set
open scoped BigOperators

noncomputable section

/-- Jacobi's determinant derivative for a three-by-three matrix curve. -/
theorem hasDerivAt_det_three
    {H : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {H' : Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ}
    (hH : ∀ i j, HasDerivAt (fun s => H s i j) (H' i j) t) :
    HasDerivAt (fun s => (H s).det)
      (∑ i : Fin 3, ∑ j : Fin 3, (H t).adjugate j i*H' i j) t := by
  have hh := ((((((hH 0 0).mul (hH 1 1)).mul (hH 2 2)).sub
    (((hH 0 0).mul (hH 1 2)).mul (hH 2 1))).sub
    (((hH 0 1).mul (hH 1 0)).mul (hH 2 2))).add
    (((hH 0 1).mul (hH 1 2)).mul (hH 2 0))).add
    (((hH 0 2).mul (hH 1 0)).mul (hH 2 1)) |>.sub
    (((hH 0 2).mul (hH 1 1)).mul (hH 2 0))
  convert hh using 1
  · funext s
    simp only [Matrix.det_fin_three, Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
  · simp [Fin.sum_univ_three, Matrix.adjugate_fin_three, Pi.mul_apply]
    ring

/-- The canonical one-form is the logarithmic derivative of the Hessian
volume, so its coordinate derivatives commute. -/
theorem hasDerivAt_log_det_three
    {H : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {H' : Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ}
    (hH : ∀ i j, HasDerivAt (fun s => H s i j) (H' i j) t) (hdet : (H t).det ≠ 0) :
    HasDerivAt (fun s => Real.log (H s).det)
      (∑ i : Fin 3, ∑ j : Fin 3, (H t)⁻¹ j i*H' i j) t := by
  have hh := (hasDerivAt_det_three hH).log hdet
  convert hh using 1
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv,
    Fin.sum_univ_three]
  ring

def fubiniLogPotential (H : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := Real.log H.det/5

def fubiniDensity (H : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := Real.exp (-fubiniLogPotential H)

theorem fubiniDensity_pos (H : Matrix (Fin 3) (Fin 3) ℝ) : 0 < fubiniDensity H :=
  Real.exp_pos _

theorem hasDerivAt_fubiniLogPotential
    {H : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {H' : Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ}
    (hH : ∀ i j, HasDerivAt (fun s => H s i j) (H' i j) t) (hdet : (H t).det ≠ 0) :
    HasDerivAt (fun s => fubiniLogPotential (H s))
      ((∑ i : Fin 3, ∑ j : Fin 3, (H t)⁻¹ j i*H' i j)/5) t :=
  (hasDerivAt_log_det_three hH hdet).div_const 5

theorem hasDerivAt_fubiniDensity
    {H : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {H' : Matrix (Fin 3) (Fin 3) ℝ} {t : ℝ}
    (hH : ∀ i j, HasDerivAt (fun s => H s i j) (H' i j) t) (hdet : (H t).det ≠ 0) :
    HasDerivAt (fun s => fubiniDensity (H s))
      (-fubiniDensity (H t)*((∑ i : Fin 3, ∑ j : Fin 3, (H t)⁻¹ j i*H' i j)/5)) t := by
  convert ((hasDerivAt_fubiniLogPotential hH hdet).neg).exp using 1 <;>
    dsimp [fubiniDensity] <;> ring

/-- The logarithmic potential inherits exactly the available smoothness
of the Hessian entries on every regular patch. -/
theorem contDiffOn_fubiniLogPotential
    {H : FubiniBase → Matrix (Fin 3) (Fin 3) ℝ} {U : Set FubiniBase} {n : WithTop ℕ∞}
    (hH : ∀ i j, ContDiffOn ℝ n (fun x => H x i j) U)
    (hdet : ∀ x ∈ U, (H x).det ≠ 0) :
    ContDiffOn ℝ n (fun x => fubiniLogPotential (H x)) U := by
  have hh := ((((((hH 0 0).mul (hH 1 1)).mul (hH 2 2)).sub
    (((hH 0 0).mul (hH 1 2)).mul (hH 2 1))).sub
    (((hH 0 1).mul (hH 1 0)).mul (hH 2 2))).add
    (((hH 0 1).mul (hH 1 2)).mul (hH 2 0))).add
    (((hH 0 2).mul (hH 1 0)).mul (hH 2 1)) |>.sub
    (((hH 0 2).mul (hH 1 1)).mul (hH 2 0))
  have hdetSmooth : ContDiffOn ℝ n (fun x => (H x).det) U := by
    convert hh using 1
    funext x
    simp only [Matrix.det_fin_three, Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
  exact (hdetSmooth.log hdet).div_const 5

end

end Submission.Obl.k4_physical_parent_potential_candidates
