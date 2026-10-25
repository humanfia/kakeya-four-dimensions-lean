/-
Copied with the namespace renamed from o144 (k4_seven_direction_local_degree_restoration),
branch x0492, commit 9cac1f6, file Submission/Obl/k4_seven_direction_local_degree_restoration/Kit/ProjectiveFrame.lean.
That file's own header follows.
-/
/-
Copied with the namespace renamed from root session x0001's library bundle
K4CubicTests (root.git branch x0001-cubiclib, commit d9813f5,
Submission/Lib/K4CubicTests/ProjectiveFrame.lean), not yet admitted to lib.
That file's own header follows.
-/
/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit.FrameConditioning

namespace Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit

/-- A quantitative projective frame constructed from the first four directions.
The constants come directly from three-dimensional Cramer's rule. -/
theorem exists_conditioned_projective_frame (p : Fin 7 → Fin 3 → ℝ)
    (A κ : ℝ) (hA : 0 < A) (hκ : 0 < κ) (hcoord : ∀ i j, |p i j| ≤ A)
    (hp : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      κ ≤ |Matrix.det (Matrix.of ![p i, p j, p k])|) :
    ∃ (P : Matrix (Fin 3) (Fin 3) ℝ) (α : Fin 3 → ℝ),
      IsUnit P.det ∧ (∀ i j, |P i j| ≤ A) ∧ (∀ i j, |P⁻¹ i j| ≤ 2 * A ^ 2 / κ) ∧
      1 ≤ 6 * A ^ 3 / κ ∧ (∀ i, |α i| ≤ 6 * A ^ 3 / κ) ∧
      (∀ i, 1 ≤ (6 * A ^ 3 / κ) * |α i|) ∧
      (∀ i : Fin 3, p (Fin.castLE (by decide : 3 ≤ 7) i) = fun l => P l i) ∧
      p 3 = Matrix.mulVec P α := by
  classical
  have hdet0 : Matrix.det (Matrix.of ![p 0, p 1, p 2]) ≠ 0 :=
    abs_pos.mp (hκ.trans_le (hp 0 1 2 (by decide) (by decide) (by decide)))
  have hlin : LinearIndependent ℝ ![p 0, p 1, p 2] := by
    have h := Matrix.linearIndependent_rows_of_det_ne_zero hdet0
    convert h using 1
    funext i j
    rfl
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ (Fin 3 → ℝ) := by simp
  let b : Module.Basis (Fin 3) ℝ (Fin 3 → ℝ) := basisOfLinearIndependentOfCardEqFinrank hlin hcard
  have hb (i : Fin 3) : b i = ![p 0, p 1, p 2] i :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hlin hcard) i
  have hRows : basisRows b = Matrix.of ![p 0, p 1, p 2] := by
    ext i j
    simpa only [basisRows, Matrix.of_apply] using congrFun (hb i) j
  have hdetb : κ ≤ |(basisRows b).det| := by
    rw [hRows]
    exact hp 0 1 2 (by decide) (by decide) (by decide)
  have hbc (i j : Fin 3) : |b i j| ≤ A := by
    rw [hb i]
    fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;>
      apply hcoord
  let P := (basisRows b).transpose
  let α : Fin 3 → ℝ := fun i => b.repr (p 3) i
  have hPc (i j : Fin 3) : |P i j| ≤ A := hbc j i
  have hdetP : κ ≤ |P.det| := by simpa [P] using hdetb
  have huP : IsUnit P.det := isUnit_iff_ne_zero.mpr (abs_pos.mp (hκ.trans_le hdetP))
  have hPinv (i j : Fin 3) : |P⁻¹ i j| ≤ 2 * A ^ 2 / κ :=
    matrix_inverse_three_abs_le P A κ hA.le hκ hPc hdetP i j
  have hR : 1 ≤ 6 * A ^ 3 / κ := by
    apply (le_div_iff₀ hκ).mpr
    simpa using hdetb.trans (matrix_det_three_abs_le (basisRows b) A hA.le hbc)
  have hα (i : Fin 3) : |α i| ≤ 6 * A ^ 3 / κ := by
    convert basis_repr_abs_le_of_det b A A κ hA.le hκ hbc hdetb (p 3) (hcoord 3) i using 1 <;> ring
  have hreplace (i : Fin 3) : κ ≤ |((basisRows b).updateRow i (p 3)).det| := by
    fin_cases i
    · change κ ≤ |((basisRows b).updateRow (0 : Fin 3) (p 3)).det|
      have he : (basisRows b).updateRow 0 (p 3) = Matrix.of ![p 3, p 1, p 2] := by
        ext j k
        fin_cases j <;> simp [basisRows, hb, Matrix.updateRow_apply]
      rw [he]
      exact hp 3 1 2 (by decide) (by decide) (by decide)
    · change κ ≤ |((basisRows b).updateRow (1 : Fin 3) (p 3)).det|
      have he : (basisRows b).updateRow 1 (p 3) = Matrix.of ![p 0, p 3, p 2] := by
        ext j k
        fin_cases j <;> simp [basisRows, hb, Matrix.updateRow_apply]
      rw [he]
      exact hp 0 3 2 (by decide) (by decide) (by decide)
    · change κ ≤ |((basisRows b).updateRow (2 : Fin 3) (p 3)).det|
      have he : (basisRows b).updateRow 2 (p 3) = Matrix.of ![p 0, p 1, p 3] := by
        ext j k
        fin_cases j <;> simp [basisRows, hb, Matrix.updateRow_apply]
      rw [he]
      exact hp 0 1 3 (by decide) (by decide) (by decide)
  have hlow (i : Fin 3) : 1 ≤ (6 * A ^ 3 / κ) * |α i| := by
    have h := basis_repr_abs_ge_of_replaced_det b A κ hA hbc (p 3) i (hreplace i)
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hκ).mpr
    simpa [α, mul_comm] using h
  refine ⟨P, α, huP, hPc, hPinv, hR, hα, hlow, ?_, ?_⟩
  · intro i
    funext l
    fin_cases i <;> simp [P, basisRows, hb]
  · funext l
    simpa [P, α, basisRows, Matrix.mulVec, dotProduct, smul_eq_mul, mul_comm] using
      (congrFun (b.sum_repr (p 3)) l).symm

end Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit
