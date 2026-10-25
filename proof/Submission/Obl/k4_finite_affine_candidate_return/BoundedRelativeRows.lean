-- Adapted from this LOT tree, o232 `k4_finite_positive_prepared_models`, session x0807,
-- branch x0807 at commit 96b53fe05c6301b6463738f96ea23d9c511248b2.
-- Source: Submission/Obl/k4_finite_positive_prepared_models/BoundedRelativeRows.lean (namespace renamed to `Submission.Obl.k4_finite_affine_candidate_return`).
import Submission.Lib.K4XInterface.Charts

namespace Submission.Obl.k4_finite_affine_candidate_return

open Submission.Lib.K4XInterface

noncomputable section

/-- A large row of an affine relative frame pulls a bounded parent
velocity coordinate back to a narrow unit-normal strip. The strip is
centered at an ACTUAL child velocity, so its bias uses only the child
velocity bound, never an absolute frame-center budget. -/
theorem strip_of_bounded_affine_row
    {Y : Type*} (V : Set Y) (hne : V.Nonempty)
    (old parent : Y → EuclideanSpace ℝ (Fin 2))
    (M : Matrix (Fin 2) (Fin 2) ℝ) (offset : EuclideanSpace ℝ (Fin 2))
    (Kold Kparent : ℝ)
    (hold : ∀ y ∈ V, ‖old y‖ ≤ Kold)
    (hparent : ∀ y ∈ V, ∀ e, |parent y e| ≤ Kparent)
    (hrel : ∀ y ∈ V, parent y = offset + Matrix.toEuclideanLin M (old y))
    (e : Fin 2) (hrow : 0 < ‖WithLp.toLp 2 (fun f => M e f)‖) :
    ∃ (a : Fin 2 → ℝ) (bias : ℝ), (∑ f, (a f) ^ 2) = 1 ∧ |bias| ≤ Kold ∧
      ∀ y ∈ V, |(∑ f, a f * old y f) - bias| ≤
        2 * Kparent / ‖WithLp.toLp 2 (fun f => M e f)‖ := by
  obtain ⟨y₀, hy₀⟩ := hne
  let row : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun f => M e f)
  let unit : EuclideanSpace ℝ (Fin 2) := ‖row‖⁻¹ • row
  have hnunit : ‖unit‖ = 1 := by
    dsimp only [unit]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact inv_mul_cancel₀ hrow.ne'
  let a : Fin 2 → ℝ := fun f => unit f
  let bias := inner ℝ unit (old y₀)
  have hinner (w : EuclideanSpace ℝ (Fin 2)) : (∑ f, a f * w f) = inner ℝ unit w := by
    simp only [a, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
    ring
  have hroweval (y : Y) (hy : y ∈ V) : inner ℝ row (old y) = parent y e - offset e := by
    have heq : inner ℝ row (old y) = (Matrix.toEuclideanLin M (old y)) e := by
      simp only [row, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
        toEuclideanLin_apply_fin2]
      ring
    rw [heq]
    have h := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w e) (hrel y hy)
    simp only [PiLp.add_apply] at h
    linarith
  refine ⟨a, bias, ?_, ?_, fun y hy => ?_⟩
  · have h := norm_sq_fin2 unit
    rw [hnunit, one_pow] at h
    simpa only [a, Fin.sum_univ_two] using h.symm
  · exact (abs_real_inner_le_norm _ _).trans
      (by simpa only [bias, hnunit, one_mul] using hold y₀ hy₀)
  · rw [hinner]
    change |inner ℝ unit (old y) - inner ℝ unit (old y₀)| ≤ _
    rw [← inner_sub_right]
    change |inner ℝ (‖row‖⁻¹ • row) (old y - old y₀)| ≤ _
    rw [inner_smul_left]
    simp only [conj_trivial, inner_sub_right, hroweval y hy, hroweval y₀ hy₀]
    rw [show parent y e - offset e - (parent y₀ e - offset e) =
      parent y e - parent y₀ e by ring, abs_mul, abs_of_pos (inv_pos.mpr hrow)]
    have hd : |parent y e - parent y₀ e| ≤ 2 * Kparent :=
      (abs_sub _ _).trans ((add_le_add (hparent y hy e) (hparent y₀ hy₀ e)).trans_eq (by ring))
    exact (mul_le_mul_of_nonneg_left hd (by positivity)).trans_eq (by ring)

/-- In the no-candidate branch, a substantial child cannot be confined to
any allowed narrow strip. Bounded parent coordinates then bound every row
of the actual relative velocity matrix. This avoids an extra angular
pruning to prove the relative frame's UPPER bound. -/
theorem relative_rows_le_of_no_strip
    {Y : Type*} (V : Set Y) (hne : V.Nonempty)
    (old parent : Y → EuclideanSpace ℝ (Fin 2))
    (M : Matrix (Fin 2) (Fin 2) ℝ) (offset : EuclideanSpace ℝ (Fin 2))
    (Kold Kparent width : ℝ) (hKparent : 0 ≤ Kparent) (hwidth : 0 < width)
    (hold : ∀ y ∈ V, ‖old y‖ ≤ Kold)
    (hparent : ∀ y ∈ V, ∀ e, |parent y e| ≤ Kparent)
    (hrel : ∀ y ∈ V, parent y = offset + Matrix.toEuclideanLin M (old y))
    (hno : ∀ (a : Fin 2 → ℝ) (bias : ℝ), (∑ f, (a f) ^ 2) = 1 → |bias| ≤ Kold →
      ¬(∀ y ∈ V, |(∑ f, a f * old y f) - bias| ≤ width)) :
    ∀ e : Fin 2, ‖WithLp.toLp 2 (fun f => M e f)‖ ≤ 2 * Kparent / width := by
  intro e
  by_contra hn
  have hlarge : 2 * Kparent / width < ‖WithLp.toLp 2 (fun f => M e f)‖ := lt_of_not_ge hn
  have hrow : 0 < ‖WithLp.toLp 2 (fun f => M e f)‖ := (by positivity : 0 ≤ 2 * Kparent / width).trans_lt hlarge
  obtain ⟨a, bias, ha, hb, hstrip⟩ := strip_of_bounded_affine_row V hne old parent M offset
    Kold Kparent hold hparent hrel e hrow
  apply hno a bias ha hb
  intro y hy
  apply (hstrip y hy).trans
  apply (div_le_iff₀ hrow).mpr
  have h := (div_lt_iff₀ hwidth).mp hlarge
  linarith

end

end Submission.Obl.k4_finite_affine_candidate_return
