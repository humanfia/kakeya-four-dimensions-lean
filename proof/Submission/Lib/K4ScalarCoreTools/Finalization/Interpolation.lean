/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarFinalization/Interpolation.lean at 34bf057964440b5ed25e8d148b45315a2683e87d.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original interpolation/recovery: o062/x0212, Extrapolation.lean; inherited and checked on x0511.
The scalar-line classification uses accepted K4HiddenQuadratic Taylor and K4PolynomialPotential.
-/

import Submission.Lib.K4HiddenQuadratic
import Submission.Lib.K4PolynomialPotential.TrajectoryFits

namespace Submission.Lib.K4ScalarCoreTools.Finalization

open Set MeasureTheory MvPolynomial

def Quadratic (f : ℝ → ℝ) : Prop := ∃ A B C : ℝ, ∀ t : ℝ, f t = A * t ^ 2 + B * t + C

theorem abs_sub_le_one {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : |x - y| ≤ 1 := by
  exact abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩

theorem quadratic_interpolation (f : ℝ → ℝ) (hf : Quadratic f) (a q t : ℝ) :
    q ^ 2 * f t =
      2 * (t - a - q / 2) * (t - a - q) * f a -
      4 * (t - a) * (t - a - q) * f (a + q / 2) +
      2 * (t - a) * (t - a - q / 2) * f (a + q) := by
  obtain ⟨A, B, C, h⟩ := hf
  simp only [h]
  ring

/-- A quadratic bounded at the ends and midpoint of a short block is bounded
throughout unit time, at the explicit loss `8 / q^2`. -/
theorem quadratic_extrapolate (f : ℝ → ℝ) (hf : Quadratic f)
    {a q E : ℝ} (hq : 0 < q) (ha : 0 ≤ a) (haq : a + q ≤ 1)
    (h₀ : |f a| ≤ E) (h₁ : |f (a + q / 2)| ≤ E) (h₂ : |f (a + q)| ≤ E)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |f t| ≤ 8 * E / q ^ 2 := by
  have hE : 0 ≤ E := (abs_nonneg _).trans h₀
  have hta : |t - a| ≤ 1 := abs_sub_le_one ht ⟨ha, by linarith⟩
  have htm : |t - a - q / 2| ≤ 1 := by
    simpa only [sub_sub] using abs_sub_le_one ht
      (show a + q / 2 ∈ Icc (0 : ℝ) 1 from ⟨by linarith, by linarith⟩)
  have htb : |t - a - q| ≤ 1 := by
    simpa only [sub_sub] using abs_sub_le_one ht
      (show a + q ∈ Icc (0 : ℝ) 1 from ⟨by linarith, haq⟩)
  have hpair₀ : |t - a - q / 2| * |t - a - q| ≤ 1 :=
    (mul_le_mul htm htb (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hpair₁ : |t - a| * |t - a - q| ≤ 1 :=
    (mul_le_mul hta htb (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hpair₂ : |t - a| * |t - a - q / 2| ≤ 1 :=
    (mul_le_mul hta htm (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  apply (le_div_iff₀ (sq_pos_of_pos hq)).2
  calc
    |f t| * q ^ 2 = |q ^ 2 * f t| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg q), mul_comm]
    _ = |2 * (t - a - q / 2) * (t - a - q) * f a -
        4 * (t - a) * (t - a - q) * f (a + q / 2) +
        2 * (t - a) * (t - a - q / 2) * f (a + q)| := by
      rw [quadratic_interpolation f hf]
    _ ≤ |2 * (t - a - q / 2) * (t - a - q) * f a| +
        |4 * (t - a) * (t - a - q) * f (a + q / 2)| +
        |2 * (t - a) * (t - a - q / 2) * f (a + q)| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ = 2 * (|t - a - q / 2| * |t - a - q| * |f a|) +
        4 * (|t - a| * |t - a - q| * |f (a + q / 2)|) +
        2 * (|t - a| * |t - a - q / 2| * |f (a + q)|) := by
      simp only [abs_mul]
      norm_num
      ring
    _ ≤ 2 * (1 * E) + 4 * (1 * E) + 2 * (1 * E) := by
      gcongr
    _ = 8 * E := by ring

theorem quadratic_along_scalar_trajectory (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) (b v : ℝ) :
    Quadratic (fun t => eval ![t, b + t * v] P) := by
  let p := Submission.Lib.K4PolynomialPotential.scalarLineHom b v P
  have hp : p.natDegree ≤ 2 :=
    (Submission.Lib.K4PolynomialPotential.natDegree_scalarLineHom_le P b v).trans hP
  refine ⟨p.derivative.derivative.eval 0 / 2, p.derivative.eval 0, p.eval 0, fun t => ?_⟩
  have h := Submission.Lib.K4HiddenQuadratic.eval_add_of_natDegree_le_two p hp 0 t
  calc
    eval ![t, b + t * v] P = p.eval t :=
      (Submission.Lib.K4PolynomialPotential.eval_scalarLineHom P b v t).symm
    _ = p.eval 0 + t * p.derivative.eval 0 + t ^ 2 / 2 * p.derivative.derivative.eval 0 := by
      simpa only [zero_add] using h
    _ = p.derivative.derivative.eval 0 / 2 * t ^ 2 + p.derivative.eval 0 * t + p.eval 0 := by ring

theorem quadratic_scalar_residual (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) (b₀ b₁ b₂ b₃ b₄ : ℝ) :
    Quadratic (fun t => b₂ + t * b₃ + t ^ 2 * b₄ -
      MvPolynomial.eval ![t, b₀ + t * b₁] P) := by
  obtain ⟨A, B, C, h⟩ := quadratic_along_scalar_trajectory P hP b₀ b₁
  refine ⟨b₄ - A, b₃ - B, b₂ - C, fun t => ?_⟩
  dsimp only
  have ht := h t
  dsimp only at ht
  rw [ht]
  ring

end Submission.Lib.K4ScalarCoreTools.Finalization
