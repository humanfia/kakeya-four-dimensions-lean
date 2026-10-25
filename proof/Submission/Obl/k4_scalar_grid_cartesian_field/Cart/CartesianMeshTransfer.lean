-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/CartesianMeshTransfer.lean;
-- only the namespace was renamed into o230's.
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.PolynomialVariation

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart

open Set MvPolynomial
open Submission.Lib.K4PolynomialPotential
open Submission.Obl.k4_scalar_grid_cartesian_field.Cart.Switching
open Submission.Obl.k4_eligibility_sign_description

/-- Rescaling the existing square variation estimate gives a constant
uniform over every centered square of radius at least one. -/
theorem exists_box_square_variation_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 2) ℝ), P.totalDegree ≤ D →
      ∀ B H : ℝ, 1 ≤ B → 0 ≤ H →
        (∀ z ∈ Icc (fun _ : Fin 2 => -B) (fun _ => B), |eval z P| ≤ H) →
        ∀ x ∈ Icc (fun _ : Fin 2 => -B) (fun _ => B), ∀ y ∈ Icc (fun _ : Fin 2 => -B) (fun _ => B),
          |eval y P-eval x P| ≤ C*H*(|y 0-x 0|+|y 1-x 1|) := by
  obtain ⟨C,hC,hvar⟩ := Switching.exists_symmetric_square_variation_constant D
  refine ⟨C,hC,?_⟩
  intro P hP B H hB hH hb x hx y hy
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  let Q : MvPolynomial (Fin 2) ℝ := aeval (fun i => MvPolynomial.C B*X i) P
  have hQ : Q.totalDegree ≤ D := by
    apply (degree_aeval_le P _ ?_).trans hP
    intro i
    exact (degree_C_mul_le _ _).trans (by simp)
  have heval (z : Fin 2 → ℝ) : eval z Q=eval (fun i => B*z i) P := by
    dsimp only [Q]
    rw [eval_substitution]
    simp only [map_mul,eval_C,eval_X]
  have hQb : ∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval z Q| ≤ H := by
    intro z hz
    rw [heval]
    apply hb
    constructor <;> intro i
    · have hi : (-1 : ℝ) ≤ z i := hz.1 i
      change -B ≤ B*z i
      nlinarith
    · have hi : z i ≤ (1 : ℝ) := hz.2 i
      change B*z i ≤ B
      nlinarith
  have hnorm (z : Fin 2 → ℝ) (hz : z ∈ Icc (fun _ : Fin 2 => -B) (fun _ => B)) :
      (fun i => z i/B) ∈ Icc (-1 : Fin 2 → ℝ) 1 := by
    constructor <;> intro i
    · change (-1 : ℝ) ≤ z i/B
      exact (le_div_iff₀ hBpos).2 (by simpa using hz.1 i)
    · change z i/B ≤ (1 : ℝ)
      exact (div_le_iff₀ hBpos).2 (by simpa using hz.2 i)
  have hback (z : Fin 2 → ℝ) : eval (fun i => z i/B) Q=eval z P := by
    rw [heval]
    apply congrArg (fun f : Fin 2 → ℝ => eval f P)
    ext i
    field_simp
  have h := hvar Q hQ H hH hQb _ (hnorm x hx) _ (hnorm y hy)
  rw [hback,hback] at h
  have hd (i : Fin 2) : |y i/B-x i/B|=|y i-x i|/B := by
    rw [← sub_div,abs_div,abs_of_pos hBpos]
  simp only [hd] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (add_le_add (div_le_self (abs_nonneg _) hB) (div_le_self (abs_nonneg _) hB))
    (mul_nonneg hC.le hH))

/-- Moving the evaluation point from its mesh center to the actual
Cartesian source point preserves the same source set and works for all
components simultaneously. -/
theorem exists_cartesian_mesh_fit_transfer_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι Ω : Type*} (A : Set Ω)
      (P : ι → MvPolynomial (Fin 2) ℝ) (G : ι → Ω → ℝ)
      (center actual : Ω → Fin 2 → ℝ) (B H E δ : ℝ),
      1 ≤ B → 0 ≤ H →
      (∀ i, (P i).totalDegree ≤ D) →
      (∀ i, ∀ z ∈ Icc (fun _ : Fin 2 => -B) (fun _ => B), |eval z (P i)| ≤ H) →
      (∀ ω ∈ A, center ω ∈ Icc (fun _ : Fin 2 => -B) (fun _ => B)) →
      (∀ ω ∈ A, actual ω ∈ Icc (fun _ : Fin 2 => -B) (fun _ => B)) →
      (∀ ω ∈ A, |actual ω 0-center ω 0|+|actual ω 1-center ω 1| ≤ δ) →
      (∀ ω ∈ A, ∀ i, |G i ω-eval (center ω) (P i)| ≤ E) →
      ∀ ω ∈ A, ∀ i, |G i ω-eval (actual ω) (P i)| ≤ E+C*H*δ := by
  obtain ⟨C,hC,hvar⟩ := exists_box_square_variation_constant D
  refine ⟨C,hC,?_⟩
  intro ι Ω A P G center actual B H E δ hB hH hdegree hnorm hcenter hactual hdist hfit ω hω i
  have h := hvar (P i) (hdegree i) B H hB hH (hnorm i)
    (center ω) (hcenter ω hω) (actual ω) (hactual ω hω)
  have hmove : |eval (center ω) (P i)-eval (actual ω) (P i)| ≤ C*H*δ := by
    rw [abs_sub_comm]
    exact h.trans (mul_le_mul_of_nonneg_left (hdist ω hω) (mul_nonneg hC.le hH))
  exact (abs_sub_le (G i ω) (eval (center ω) (P i)) (eval (actual ω) (P i))).trans
    (add_le_add (hfit ω hω i) hmove)

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart
