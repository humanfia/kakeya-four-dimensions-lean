import Submission.Obl.k4_physical_parent_potential_candidates.MixedPointwiseConic
import Submission.Obl.k4_physical_parent_potential_candidates.FubiniInput

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set FubiniJets FubiniHessian
open Submission.Obl.k4_approximate_conic_taylor_decomposition
open Submission.Obl.k4_real_conic_restoration (quad)

noncomputable section

namespace FubiniHessian

theorem hessian_entry_eq (f : FubiniBase → ℝ) (x : FubiniBase) (i j : Fin 3) :
    hessian f x i j = iteratedFDeriv ℝ 2 f x ![basis i,basis j] := by
  unfold hessian jet
  congr 1
  funext k
  fin_cases k <;> rfl

theorem hessian_diagonal_eq (f : FubiniBase → ℝ) (x p : FubiniBase) :
    quad (hessian f x) (fun i => p i) = iteratedFDeriv ℝ 2 f x (fun _ => p) := by
  calc
    _ = ∑ i : Fin 3, ∑ j : Fin 3, iteratedFDeriv ℝ 2 f x ![basis i,basis j]*p i*p j := by
      unfold quad
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hessian_entry_eq]
      ring
    _ = iteratedFDeriv ℝ 2 f x ![p,p] :=
      Submission.Obl.k4_seven_direction_local_degree_restoration.bilinear_coordinates _ p p
    _ = _ := by congr 1; funext i; fin_cases i <;> rfl

theorem basis_eq_e3 (i : Fin 3) : basis i = e3 i := by
  ext j
  simp [basis, e3, EuclideanSpace.basisFun_apply]

theorem cubic_entry_eq (f : FubiniBase → ℝ) (x : FubiniBase) (i j k : Fin 3) :
    cubic f x i j k = iteratedFDeriv ℝ 3 f x ![e3 i,e3 j,e3 k] := by
  unfold cubic jet
  congr 1
  funext a
  fin_cases a <;> exact basis_eq_e3 _

/-- The mixed seven-direction estimate directly for the Hessian of one
smooth graph and the cubic derivative of its small physical potential. -/
theorem pointwise_potential_cleared_bound :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ (A MH MF ηq ηc : ℝ),
      2 ≤ A → 0 ≤ MH → 0 ≤ MF → 0 ≤ ηq → 0 ≤ ηc →
      ∀ (p : Fin 7 → FubiniBase) (g Pot : FubiniBase → ℝ) (U : Set FubiniBase),
      IsOpen U → ContDiffOn ℝ 6 g U → ContDiffOn ℝ 6 Pot U →
      ∀ x ∈ U,
      (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ A) →
      (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
        A⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)|) →
      ‖iteratedFDeriv ℝ 2 g x‖ ≤ MH → ‖iteratedFDeriv ℝ 3 Pot x‖ ≤ MF →
      (∀ i, |iteratedFDeriv ℝ 2 g x (fun _ => p i)| ≤ ηq) →
      (∀ i, |iteratedFDeriv ℝ 3 Pot x (fun _ => p i)| ≤ ηc) →
      ∀ i j k, |ConicTensor.cleared (hessian g x) (cubic Pot x) i j k| ≤
        A^J*(MH^3*ηc+MF*MH^2*ηq) := by
  obtain ⟨J, hJ, hnorm⟩ := PointwiseConic.mixed_multilinear_bound
  refine ⟨J, hJ, ?_⟩
  intro A MH MF ηq ηc hA hMH hMF hηq hηc p g Pot U hU hg hPot x hx hp htr hg2 hPot3 hquad htest
  have hs : IsSymmML (iteratedFDeriv ℝ 3 Pot x) := by
    intro σ m
    exact iteratedFDeriv_comp_perm hU hPot 3 (by norm_num) x hx σ m
  have hb := hnorm A MH MF ηq ηc hA hMH hMF hηq hηc p (hessian g x)
    (iteratedFDeriv ℝ 3 Pot x) hp htr (hessian_symmetric hU hg hx)
    (fun i j => coordinate_jet_bound hg2 ![i,j]) hs hPot3
    (fun i => by rw [hessian_diagonal_eq]; exact hquad i) htest
  have he : (fun i j k => iteratedFDeriv ℝ 3 Pot x ![e3 i,e3 j,e3 k]) = cubic Pot x := by
    funext i j k
    exact (cubic_entry_eq Pot x i j k).symm
  rw [he] at hb
  exact hb

end FubiniHessian

end

end Submission.Obl.k4_physical_parent_potential_candidates
