import Submission.Obl.k4_physical_parent_potential_candidates.FubiniCleared
import Submission.Obl.k4_physical_parent_potential_candidates.FubiniProductJets

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set FubiniJets FubiniProductJets

noncomputable section

namespace FubiniHessian

/-- Differentiate an actual quadratic implicit equation three times.
The affine b and quadratic c parts are specified by their vanishing higher
jets; the potential is allowed to have arbitrary higher degree. -/
theorem implicit_cubic_identity
    {f b c Pot : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 3 f U) (hb : ContDiffOn ℝ 3 b U) (hc : ContDiffOn ℝ 3 c U)
    (a : ℝ) (heq : ∀ y ∈ U, Pot y = a*(f y*f y)+b y*f y+c y)
    {x : FubiniBase} (hx : x ∈ U)
    (hB2 : ∀ i j, jet b 2 ![i,j] x = 0)
    (hB3 : ∀ i j k, jet b 3 ![i,j,k] x = 0)
    (hC3 : ∀ i j k, jet c 3 ![i,j,k] x = 0)
    (i j k : Fin 3) :
    jet Pot 3 ![i,j,k] x =
      (2*a*f x+b x)*cubic f x i j k+
      fubiniCubic (hessian f x) (fun l => 2*a*jet f 1 ![l] x+jet b 1 ![l] x) i j k := by
  have haf : ContDiffOn ℝ 3 (fun y => a*(f y*f y)) U := contDiffOn_const.mul (hf.mul hf)
  have hbf : ContDiffOn ℝ 3 (fun y => b y*f y) U := hb.mul hf
  rw [jet_eq_of_eqOn hU heq hx,
    jet_add hU (haf.add hbf) hc hx 3 (by norm_num),
    jet_add hU haf hbf hx 3 (by norm_num),
    jet_const_mul hU (hf.mul hf) hx a 3 (by norm_num),
    third_mul hU hf hf hx, third_mul hU hb hf hx]
  simp only [hB2, hB3, hC3, zero_mul, add_zero]
  dsimp only [cubic, hessian, fubiniCubic]
  ring

/-- The cleared cubic of the defining potential equals a scalar multiple
of the canonical cubic error of the actual implicit graph. -/
theorem implicit_cleared_potential_identity
    {f b c Pot : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hb : ContDiffOn ℝ 3 b U) (hc : ContDiffOn ℝ 3 c U)
    (hdet : ∀ y ∈ U, (hessian f y).det ≠ 0)
    (a : ℝ) (heq : ∀ y ∈ U, Pot y = a*(f y*f y)+b y*f y+c y)
    {x : FubiniBase} (hx : x ∈ U)
    (hB2 : ∀ i j, jet b 2 ![i,j] x = 0)
    (hB3 : ∀ i j k, jet b 3 ![i,j,k] x = 0)
    (hC3 : ∀ i j k, jet c 3 ![i,j,k] x = 0)
    (i j k : Fin 3) :
    ConicTensor.cleared (hessian f x) (fun l m n => jet Pot 3 ![l,m,n] x) i j k =
      5*(2*a*f x+b x)*(hessian f x).det*cubicError f x i j k := by
  apply cleared_potential_eq_error hU hf hdet hx _
    (fun l => 2*a*jet f 1 ![l] x+jet b 1 ![l] x) (2*a*f x+b x)
  intro l m n
  exact implicit_cubic_identity hU (hf.of_le (by norm_num)) hb hc a heq hx hB2 hB3 hC3 l m n

end FubiniHessian

end

end Submission.Obl.k4_physical_parent_potential_candidates
