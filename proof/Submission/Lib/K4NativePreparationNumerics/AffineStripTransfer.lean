/-
Adapted from: here:o204
Original file: Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/AffineStripTransfer.lean.
Any earlier attribution is retained below.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! An original velocity strip cap transfers to a new affine frame with
only the inverse-frame norm loss. The normal and intercept are constructed,
so no nondegeneracy or target-frame breadth is assumed. -/

namespace Submission.Lib.K4NativePreparationNumerics

open Set
open scoped RealInnerProductSpace

theorem affine_velocity_strip_pullback
    (L R : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
    {C width radius : ℝ} (hC : 0 ≤ C) (hwidth : 0 ≤ width)
    (hR : ∀ v, ‖R v‖ ≤ C * ‖v‖) (hLR : ∀ v, L (R v) = v)
    (hscale : width * C ≤ radius)
    (n shift center : EuclideanSpace ℝ (Fin 2)) (hn : ‖n‖ = 1) :
    ∃ normal : EuclideanSpace ℝ (Fin 2), ∃ offset : ℝ, ‖normal‖ = 1 ∧
      {v | |inner ℝ n (L v + shift - center)| ≤ width} ⊆
        {v | |inner ℝ v normal - offset| ≤ radius} := by
  let d := ‖L.adjoint n‖
  have hinner : inner ℝ (L.adjoint n) (R n) = 1 := by
    rw [ContinuousLinearMap.adjoint_inner_left, hLR]
    rw [real_inner_self_eq_norm_sq, hn]
    norm_num
  have hden : 1 ≤ d * C := by
    have h := abs_real_inner_le_norm (L.adjoint n) (R n)
    rw [hinner, abs_one] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa only [hn, mul_one] using hR n
  have hd : 0 < d := by
    have hd0 : 0 ≤ d := norm_nonneg _
    by_contra h
    have hz : d = 0 := le_antisymm (le_of_not_gt h) hd0
    rw [hz, zero_mul] at hden
    norm_num at hden
  let normal := d⁻¹ • L.adjoint n
  let offset := inner ℝ n (center - shift) / d
  refine ⟨normal, offset, ?_, ?_⟩
  · change ‖d⁻¹ • L.adjoint n‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
    exact inv_mul_cancel₀ hd.ne'
  · intro v hv
    have heq : inner ℝ v normal - offset = inner ℝ n (L v + shift - center) / d := by
      dsimp only [normal, offset]
      simp only [inner_smul_right, inner_add_right, inner_sub_right,
        ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
      ring
    change |inner ℝ v normal - offset| ≤ radius
    rw [heq, abs_div, abs_of_pos hd]
    apply (div_le_iff₀ hd).mpr
    have hwidth' : width ≤ radius * d := by
      calc
        width = width * 1 := by ring
        _ ≤ width * (d * C) := mul_le_mul_of_nonneg_left hden hwidth
        _ = (width * C) * d := by ring
        _ ≤ radius * d := mul_le_mul_of_nonneg_right hscale hd.le
    exact hv.trans hwidth'

end Submission.Lib.K4NativePreparationNumerics
