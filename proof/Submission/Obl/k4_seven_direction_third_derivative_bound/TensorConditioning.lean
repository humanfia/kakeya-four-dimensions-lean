/-
Adapted from: here:root
Original proofs by session x0001, root branch x0001-cubiclib, commit f6ada26.
Source: Submission/Lib/K4CubicTests/TensorConditioning.lean.
This helper has not entered lib; only the cubic two-copy argument is used here.
-/
import Submission.Obl.k4_seven_direction_third_derivative_bound.FrameConditioning

namespace Submission.Obl.k4_seven_direction_third_derivative_bound

section Trilinear

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Expansion of a trilinear form in a finite basis. -/
theorem trilinear_basis_expansion (b : Module.Basis (Fin 3) ℝ E)
    (T : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x y z : E) :
    T x y z = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      (b.repr x i * b.repr y j * b.repr z k) * T (b i) (b j) (b k) := by
  classical
  calc
    T x y z = T (∑ i : Fin 3, b.repr x i • b i)
        (∑ j : Fin 3, b.repr y j • b j) (∑ k : Fin 3, b.repr z k • b k) := by
      rw [b.sum_repr, b.sum_repr, b.sum_repr]
    _ = _ := by
      simp only [Fin.sum_univ_three, map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul]
      ring

private theorem triple_sum_abs_bound (f : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (B : ℝ) (hf : ∀ i j k, |f i j k| ≤ B) :
    |∑ i, ∑ j, ∑ k, f i j k| ≤ 27 * B := by
  have hsum (g : Fin 3 → ℝ) (C : ℝ) (hg : ∀ i, |g i| ≤ C) : |∑ i, g i| ≤ 3 * C := by
    calc
      _ ≤ ∑ i, |g i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 3, C := Finset.sum_le_sum fun i _ => hg i
      _ = _ := by simp
  have hinner (i j : Fin 3) := hsum (f i j) B (hf i j)
  have hmid (i : Fin 3) := hsum (fun j => ∑ k, f i j k) (3 * B) (hinner i)
  convert hsum (fun i => ∑ j, ∑ k, f i j k) (3 * (3 * B)) hmid using 1 <;> ring

/-- Bounds on the coordinates of three vectors and on the basis coefficients
bound their trilinear test, with an explicit constant. -/
theorem trilinear_abs_le_of_basis_coefficients (b : Module.Basis (Fin 3) ℝ E)
    (T : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x y z : E)
    (H M : ℝ) (hH : 0 ≤ H) (_hM : 0 ≤ M)
    (hx : ∀ i, |b.repr x i| ≤ H) (hy : ∀ i, |b.repr y i| ≤ H)
    (hz : ∀ i, |b.repr z i| ≤ H)
    (hT : ∀ i j k, |T (b i) (b j) (b k)| ≤ M) :
    |T x y z| ≤ 27 * H ^ 3 * M := by
  rw [trilinear_basis_expansion b T]
  have hterm (i j k : Fin 3) :
      |(b.repr x i * b.repr y j * b.repr z k) * T (b i) (b j) (b k)| ≤ H ^ 3 * M := by
    simp only [abs_mul]
    calc
      _ ≤ (H * H * H) * M := mul_le_mul
        (mul_le_mul (mul_le_mul (hx i) (hy j) (abs_nonneg _) hH) (hz k)
          (abs_nonneg _) (mul_nonneg hH hH)) (hT i j k)
        (abs_nonneg _) (by positivity)
      _ = _ := by ring
  convert triple_sum_abs_bound _ (H ^ 3 * M) hterm using 1 <;> ring

end Trilinear

/-- The cubic two-copy test bound measured in the standard coordinates,
with all conditioning losses written explicitly. -/
theorem cubic_standard_coefficients_le_of_frame_determinants
    (b : Module.Basis (Fin 3) ℝ (Fin 3 → ℝ))
    (T : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (h01 : ∀ x y z, T x y z = T y x z)
    (h12 : ∀ x y z, T x y z = T x z y)
    (v : Fin 3 → ℝ) (A κ ε : ℝ) (hA : 0 < A) (hκ : 0 < κ) (hε : 0 ≤ ε)
    (hb : ∀ i j, |b i j| ≤ A) (hvcoord : ∀ j, |v j| ≤ A)
    (hdet : κ ≤ |(basisRows b).det|)
    (hdet1 : κ ≤ |((basisRows b).updateRow 1 v).det|)
    (hdet2 : κ ≤ |((basisRows b).updateRow 2 v).det|)
    (hB : ∀ i j : Fin 3, |T (b i) (b i) (b j)| ≤ ε)
    (hv : |T v v (b 0)| ≤ ε) :
    ∀ i j k : Fin 3, |T (Pi.single i 1) (Pi.single j 1) (Pi.single k 1)| ≤
      27 * (6 * A ^ 2 / κ) ^ 3 * (4 * (6 * A ^ 3 / κ) ^ 4 * ε) := by
  have hbasis := cubic_coefficients_le_of_frame_determinants b T h01 h12 v A κ ε hA hκ hε
    hb hvcoord hdet hdet1 hdet2 hB hv
  have hcoords (i j : Fin 3) : |b.repr (Pi.single i 1) j| ≤ 6 * A ^ 2 / κ := by
    have he (k : Fin 3) : |((Pi.single i (1 : ℝ) : Fin 3 → ℝ)) k| ≤ 1 := by
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    simpa using basis_repr_abs_le_of_det b A 1 κ hA.le hκ hb hdet (Pi.single i 1) he j
  intro i j k
  exact trilinear_abs_le_of_basis_coefficients b T _ _ _ _ _ (by positivity) (by positivity)
    (hcoords i) (hcoords j) (hcoords k) hbasis

end Submission.Obl.k4_seven_direction_third_derivative_bound
