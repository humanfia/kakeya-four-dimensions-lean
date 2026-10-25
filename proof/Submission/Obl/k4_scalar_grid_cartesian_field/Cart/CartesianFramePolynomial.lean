-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/CartesianFramePolynomial.lean;
-- only the namespace was renamed into o230's.
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.CartesianFrame
import Submission.Lib.K4PolynomialPotential.AffineCurl
import Submission.Lib.K4ScalarSwitching.PolynomialDegree

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart

open Set MvPolynomial
open Submission.Lib.K4PolynomialPotential
open Submission.Lib.K4ScalarSwitching.PolynomialDegree

noncomputable def cartesianFrameOrigin (t0 y0 vr vc : ℝ) : Fin 2 → ℝ :=
  cartesianFrameCoordinates t0 y0 vr vc 0 0

noncomputable def cartesianFrameMatrix (vr vc : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![vc/(vc-vr),-1/(vc-vr)], ![-vr/(vc-vr),1/(vc-vr)]]

theorem cartesianFrameCoordinates_affine (t0 y0 vr vc t y : ℝ) :
    cartesianFrameCoordinates t0 y0 vr vc t y=
      fun i => cartesianFrameOrigin t0 y0 vr vc i+
        cartesianFrameMatrix vr vc i 0*t+cartesianFrameMatrix vr vc i 1*y := by
  ext i
  fin_cases i <;> simp [cartesianFrameCoordinates,cartesianFrameOrigin,cartesianFrameMatrix] <;> ring

/-- The actual polynomial in physical `(t,y)` coordinates, obtained
through the accepted affine polynomial substitution. -/
noncomputable def cartesianFramePolynomial (t0 y0 vr vc : ℝ)
    (P : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 2) ℝ :=
  scalarAffineHom (cartesianFrameOrigin t0 y0 vr vc) (cartesianFrameMatrix vr vc) P

theorem eval_cartesianFramePolynomial (t0 y0 vr vc t y : ℝ)
    (P : MvPolynomial (Fin 2) ℝ) :
    eval ![t,y] (cartesianFramePolynomial t0 y0 vr vc P)=
      eval (cartesianFrameCoordinates t0 y0 vr vc t y) P := by
  rw [cartesianFramePolynomial,eval_scalarAffineHom,cartesianFrameCoordinates_affine]
  rfl

theorem cartesianFramePolynomial_degree (t0 y0 vr vc : ℝ)
    (P : MvPolynomial (Fin 2) ℝ) :
    (cartesianFramePolynomial t0 y0 vr vc P).totalDegree ≤ P.totalDegree := by
  unfold cartesianFramePolynomial scalarAffineHom
  apply degree_aeval_le
  intro i
  apply degree_add_le
  · apply degree_add_le
    · simp
    · exact (degree_C_mul_le _ _).trans (by simp)
  · exact (degree_C_mul_le _ _).trans (by simp)

/-- The coordinate conditioning is paid inside the interpolation box;
evaluating the transported field changes neither its norm budget nor
its degree bound. -/
theorem cartesianFramePolynomial_norm (t0 y0 vr vc K R B H : ℝ)
    (hK : 1 ≤ K) (hR : 0 ≤ R) (hvr : |vr| ≤ K) (hvc : |vc| ≤ K)
    (hsep : 1/K ≤ |vc-vr|) (hbox : 2*K^2*R ≤ B)
    (P : MvPolynomial (Fin 2) ℝ)
    (hnorm : ∀ z ∈ Icc (fun _ : Fin 2 => -B) (fun _ => B), |eval z P| ≤ H)
    (t y : ℝ) (ht : |t-t0| ≤ R) (hy : |y-y0| ≤ R) :
    |eval ![t,y] (cartesianFramePolynomial t0 y0 vr vc P)| ≤ H := by
  rw [eval_cartesianFramePolynomial]
  have hcoord := cartesianFrame_coordinate_bound t0 y0 vr vc t y K R hK hR hvr hvc hsep ht hy
  apply hnorm
  constructor <;> intro i
  · exact (abs_le.mp ((hcoord i).trans hbox)).1
  · exact (abs_le.mp ((hcoord i).trans hbox)).2

theorem cartesianFramePolynomial_fit (t0 y0 vr vc t y G E : ℝ)
    (P : MvPolynomial (Fin 2) ℝ)
    (hfit : |G-eval (cartesianFrameCoordinates t0 y0 vr vc t y) P| ≤ E) :
    |G-eval ![t,y] (cartesianFramePolynomial t0 y0 vr vc P)| ≤ E := by
  rwa [eval_cartesianFramePolynomial]

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart
