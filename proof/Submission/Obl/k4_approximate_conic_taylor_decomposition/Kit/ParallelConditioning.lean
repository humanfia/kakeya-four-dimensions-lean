/-
Copied with the namespace renamed from o144 (k4_seven_direction_local_degree_restoration),
branch x0492, commit 9cac1f6, file Submission/Obl/k4_seven_direction_local_degree_restoration/Kit/ParallelConditioning.lean.
That file's own header follows.
-/
/-
Copied with the namespace renamed from root session x0001's library bundle
K4CubicTests (root.git branch x0001-cubiclib, commit d9813f5,
Submission/Lib/K4CubicTests/ParallelConditioning.lean), not yet admitted to lib.
That file's own header follows.
-/
/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit.ScalarConditioning
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit.WedgeConditioning

namespace Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit

/-- Four approximate parallelism tests determine a linear field up to a scalar
multiple of an invertible field. All losses are explicit polynomial products
of the bounds on a projective frame and its inverse. -/
theorem matrix_near_proportional_of_frame_cross_tests
    (A B P : Matrix (Fin 3) (Fin 3) ℝ) (hBdet : IsUnit B.det) (hPdet : IsUnit P.det)
    (α : Fin 3 → ℝ) (R S T U V ε : ℝ)
    (hR : 1 ≤ R) (hS : 0 ≤ S) (hT : 0 ≤ T) (hU : 0 ≤ U) (hV : 0 ≤ V) (hε : 0 ≤ ε)
    (hα : ∀ i, |α i| ≤ R) (hlow : ∀ i, 1 ≤ R * |α i|)
    (hPinv : ∀ i j, |P⁻¹ i j| ≤ S) (hBinv : ∀ i j, |B⁻¹ i j| ≤ T)
    (hB : ∀ i j, |B i j| ≤ U) (hP : ∀ i j, |P i j| ≤ V)
    (hbasis : ∀ i j k : Fin 3,
      |crossCoordinate (Matrix.mulVec B (fun l => P l i))
        (Matrix.mulVec A (fun l => P l i)) j k| ≤ ε)
    (hextra : ∀ j k : Fin 3,
      |crossCoordinate (Matrix.mulVec B (Matrix.mulVec P α))
        (Matrix.mulVec A (Matrix.mulVec P α)) j k| ≤ ε) :
    ∃ r : ℝ, ∀ i j : Fin 3, |(A - r • B) i j| ≤
      27 * U * V * S * (5 * R ^ 4 * (9 * (3 * S * T) ^ 2 * ε)) := by
  classical
  let D : Matrix (Fin 3) (Fin 3) ℝ := P⁻¹ * B⁻¹
  let N : Matrix (Fin 3) (Fin 3) ℝ := D * A * P
  let δ : ℝ := 9 * (3 * S * T) ^ 2 * ε
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hD (i j : Fin 3) : |D i j| ≤ 3 * S * T :=
    matrix_mul_three_entry_abs_le P⁻¹ B⁻¹ S T hS hPinv hBinv i j
  have hDBP : D * B * P = 1 := by
    calc
      _ = P⁻¹ * (B⁻¹ * B) * P := by dsimp [D]; simp only [mul_assoc]
      _ = 1 := by rw [Matrix.nonsing_inv_mul B hBdet]; simpa using Matrix.nonsing_inv_mul P hPdet
  have hBPD : B * P * D = 1 := by
    calc
      _ = B * (P * P⁻¹) * B⁻¹ := by dsimp [D]; simp only [mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv P hPdet]; simpa using Matrix.mul_nonsing_inv B hBdet
  have hfirst (x : Fin 3 → ℝ) :
      Matrix.mulVec D (Matrix.mulVec B (Matrix.mulVec P x)) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hDBP, Matrix.one_mulVec]
  have hsecond (x : Fin 3 → ℝ) :
      Matrix.mulVec D (Matrix.mulVec A (Matrix.mulVec P x)) = Matrix.mulVec N x := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hnormalized (x : Fin 3 → ℝ)
      (hx : ∀ j k : Fin 3, |crossCoordinate (Matrix.mulVec B (Matrix.mulVec P x))
        (Matrix.mulVec A (Matrix.mulVec P x)) j k| ≤ ε) (j k : Fin 3) :
      |crossCoordinate x (Matrix.mulVec N x) j k| ≤ δ := by
    simpa only [hfirst x, hsecond x] using crossCoordinate_mulVec_abs_le D
      (Matrix.mulVec B (Matrix.mulVec P x)) (Matrix.mulVec A (Matrix.mulVec P x))
      (3 * S * T) ε (by positivity) hε hD hx j k
  have hcol (i : Fin 3) : P.col i = fun l => P l i := by
    funext l
    rfl
  have hbasis' (i j k : Fin 3) :
      |crossCoordinate (Pi.single i 1) (Matrix.mulVec N (Pi.single i 1)) j k| ≤ δ := by
    apply hnormalized
    intro j k
    simpa only [Matrix.mulVec_single_one, hcol i] using hbasis i j k
  have hoff (i j : Fin 3) (hij : i ≠ j) : |N i j| ≤ δ := by
    simpa [crossCoordinate, Matrix.mulVec_single_one, Matrix.col_apply,
      Pi.single_apply, hij, Ne.symm hij] using hbasis' j i j
  have hcross (j k : Fin 3) :
      |α k * Matrix.mulVec N α j - α j * Matrix.mulVec N α k| ≤ δ :=
    hnormalized α hextra j k
  have hnear := matrix_near_scalar_of_projective_frame_tests N α R δ hR hδ hα hlow hoff hcross
  let r : ℝ := N 0 0
  let E : Matrix (Fin 3) (Fin 3) ℝ := N - r • 1
  let η : ℝ := 5 * R ^ 4 * δ
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hE (i j : Fin 3) : |E i j| ≤ η := by
    simpa [E, r, η, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul] using hnear i j
  have hrecoverA : B * P * N * P⁻¹ = A := by
    calc
      _ = (B * P * D) * A * (P * P⁻¹) := by dsimp [N]; simp only [mul_assoc]
      _ = A := by rw [hBPD, Matrix.mul_nonsing_inv P hPdet]; simp
  have hrecoverB : B * P * (r • (1 : Matrix (Fin 3) (Fin 3) ℝ)) * P⁻¹ = r • B := by
    simp only [mul_smul_comm, smul_mul_assoc, mul_one, mul_assoc,
      Matrix.mul_nonsing_inv P hPdet]
  have hrecover : B * P * E * P⁻¹ = A - r • B := by
    dsimp [E]
    rw [mul_sub, sub_mul, hrecoverA, hrecoverB]
  have hBP (i j : Fin 3) : |(B * P) i j| ≤ 3 * U * V :=
    matrix_mul_three_entry_abs_le B P U V hU hB hP i j
  have hBPE (i j : Fin 3) : |(B * P * E) i j| ≤ 3 * (3 * U * V) * η :=
    matrix_mul_three_entry_abs_le (B * P) E (3 * U * V) η (by positivity) hBP hE i j
  refine ⟨r, ?_⟩
  intro i j
  rw [← hrecover]
  convert matrix_mul_three_entry_abs_le (B * P * E) P⁻¹ (3 * (3 * U * V) * η) S
    (by positivity) hBPE hPinv i j using 1 <;> dsimp [η, δ] <;> ring

end Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit
