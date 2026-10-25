/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/PacketCancellation.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.TimeConditioning

/-! Exact cancellation of the original full assignment budget and the spatial
Jacobian in the balanced-packet construction. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF
namespace PacketCancellation

open MeasureTheory Set
open Submission.Obl.k4_dyadic_crop_affine_laws.Framework

/-- A child assignment has its original prior mass divided by the full parent
assignment mass; the selected incidence event is absent from this formula. -/
theorem conditional_assignment_mass {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) [IsFiniteMeasure ν] (A : Set X) (e : X ≃ᵐ Y)
    (B : Set Y) (hB : MeasurableSet B) :
    (conditionedPrior ν A e B).toReal =
      (ν (A ∩ e ⁻¹' B)).toReal / (ν A).toReal := by
  rw [conditionedPrior, Measure.smul_apply, e.measurableEmbedding.map_apply,
    Measure.restrict_apply (e.measurable hB)]
  simp only [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv]
  rw [inter_comm, mul_comm]

/-- The actual saturation ratio of a child and the calibrated parent ratio
give the original child's mass-to-area ratio. The absolute primed exponent
is replaced by a difference of primed exponents. -/
theorem ratio_bounds {N aC JC aA JA fL F₁ Fb α ε : ℝ}
    (hN : 0 < N) (haC : 0 < aC) (hJC : 0 < JC) (hJA : 0 < JA)
    (hparent : N ^ (α - ε) ≤ JC / aC ∧ JC / aC ≤ N ^ (α + ε))
    (hchild : N ^ (-Fb - ε) ≤ (aA / aC) / (JA / JC) ∧
      (aA / aC) / (JA / JC) ≤ N ^ (-Fb + ε))
    (hterminal : F₁ = fL - α) :
    N ^ (-fL + F₁ - Fb - 2 * ε) ≤ aA / JA ∧
      aA / JA ≤ N ^ (-fL + F₁ - Fb + 2 * ε) := by
  have hratio : 0 < JC / aC := div_pos hJC haC
  have heq : aA / JA = ((aA / aC) / (JA / JC)) / (JC / aC) := by
    field_simp
  have hlo : N ^ (-fL + F₁ - Fb - 2 * ε) * N ^ (α + ε) =
      N ^ (-Fb - ε) := by
    rw [← Real.rpow_add hN, hterminal]
    congr 1
    ring
  have hhi : N ^ (-fL + F₁ - Fb + 2 * ε) * N ^ (α - ε) =
      N ^ (-Fb + ε) := by
    rw [← Real.rpow_add hN, hterminal]
    congr 1
    ring
  rw [heq]
  constructor
  · apply (le_div_iff₀ hratio).mpr
    calc
      N ^ (-fL + F₁ - Fb - 2 * ε) * (JC / aC) ≤
          N ^ (-fL + F₁ - Fb - 2 * ε) * N ^ (α + ε) :=
        mul_le_mul_of_nonneg_left hparent.2 (Real.rpow_nonneg hN.le _)
      _ ≤ (aA / aC) / (JA / JC) := hlo.le.trans hchild.1
  · apply (div_le_iff₀ hratio).mpr
    calc
      (aA / aC) / (JA / JC) ≤
          N ^ (-fL + F₁ - Fb + 2 * ε) * N ^ (α - ε) :=
        hchild.2.trans hhi.symm.le
      _ ≤ N ^ (-fL + F₁ - Fb + 2 * ε) * (JC / aC) :=
        mul_le_mul_of_nonneg_left hparent.1 (Real.rpow_nonneg hN.le _)

/-- Approximate linearity of the old endpoint and the primed relative profile
turn the cancellation into the two-sided balance bound at depth `b`. Neither
absolute primed exponent is bounded. -/
theorem balanced_ratio_bounds {N aC JC aA JA fL F₁ Fb α ε d b : ℝ}
    (hN : 1 ≤ N) (haC : 0 < aC) (hJC : 0 < JC) (hJA : 0 < JA)
    (hparent : N ^ (α - ε) ≤ JC / aC ∧ JC / aC ≤ N ^ (α + ε))
    (hchild : N ^ (-Fb - ε) ≤ (aA / aC) / (JA / JC) ∧
      (aA / aC) / (JA / JC) ≤ N ^ (-Fb + ε))
    (hterminal : F₁ = fL - α)
    (hold : |fL - d| ≤ ε) (hrelative : |F₁ - Fb - d * (1 - b)| ≤ ε) :
    N ^ (-d * b - 4 * ε) ≤ aA / JA ∧ aA / JA ≤ N ^ (-d * b + 4 * ε) := by
  have h := ratio_bounds (by linarith) haC hJC hJA hparent hchild hterminal
  rw [abs_le] at hold hrelative
  constructor
  · refine (Real.rpow_le_rpow_of_exponent_le hN ?_).trans h.1
    nlinarith [hold.1, hrelative.1]
  · refine h.2.trans (Real.rpow_le_rpow_of_exponent_le hN ?_)
    nlinarith [hold.2, hrelative.2]

/-- The preceding cancellation for the actual original prior, conditional
child assignment and composed spatial frame. -/
theorem original_assignment_balance (ν : Measure Trajectory) [IsFiniteMeasure ν]
    (A : Set Trajectory) (e : Trajectory ≃ᵐ Trajectory)
    (B : Set Trajectory) (hB : MeasurableSet B) (Q R : Frame)
    {N fL F₁ Fb α ε d b : ℝ} (hN : 1 ≤ N)
    (ha : 0 < (ν A).toReal) (hQ : Q.det ≠ 0) (hR : R.det ≠ 0)
    (hparent : N ^ (α - ε) ≤ |Q.det| / (ν A).toReal ∧
      |Q.det| / (ν A).toReal ≤ N ^ (α + ε))
    (hchild : N ^ (-Fb - ε) ≤ (conditionedPrior ν A e B).toReal / |R.det| ∧
      (conditionedPrior ν A e B).toReal / |R.det| ≤ N ^ (-Fb + ε))
    (hterminal : F₁ = fL - α)
    (hold : |fL - d| ≤ ε) (hrelative : |F₁ - Fb - d * (1 - b)| ≤ ε) :
    N ^ (-d * b - 4 * ε) ≤ (ν (A ∩ e ⁻¹' B)).toReal / |(Q * R).det| ∧
      (ν (A ∩ e ⁻¹' B)).toReal / |(Q * R).det| ≤ N ^ (-d * b + 4 * ε) := by
  have hdet : |(Q * R).det| / |Q.det| = |R.det| := by
    rw [Matrix.det_mul, abs_mul, mul_div_cancel_left₀ _ (abs_ne_zero.mpr hQ)]
  apply balanced_ratio_bounds hN ha (abs_pos.mpr hQ)
    (abs_pos.mpr (by rw [Matrix.det_mul]; exact mul_ne_zero hQ hR)) hparent
    (by simpa only [hdet, ← conditional_assignment_mass ν A e B hB] using hchild)
    hterminal hold hrelative

/-- A vanishing outer balance error gives uniform prescribed power windows
only after taking the outer index late and then the inner sample late. The
assertion keeps these two limits in their original order. -/
theorem two_limit_balance (N : ℕ → ℕ → ℝ) (C : ℕ → ℕ → ℕ)
    (ratio : (i k : ℕ) → Fin (C i k) → ℝ) (error : ℕ → ℝ)
    (hN : ∀ i k, 1 ≤ N i k)
    (he : Filter.Tendsto error Filter.atTop (nhds 0))
    (hbound : ∀ i, ∀ δ : ℝ, 0 < δ → ∀ᶠ k in Filter.atTop,
      ∀ b, N i k ^ (-error i - δ) ≤ ratio i k b ∧
        ratio i k b ≤ N i k ^ (error i + δ)) :
    ∀ χ : ℝ, 0 < χ → ∀ᶠ i in Filter.atTop, ∀ᶠ k in Filter.atTop,
      ∀ b, N i k ^ (-χ) ≤ ratio i k b ∧ ratio i k b ≤ N i k ^ χ := by
  intro χ hχ
  filter_upwards [he.eventually (gt_mem_nhds (half_pos hχ))] with i hi
  filter_upwards [hbound i (χ / 2) (half_pos hχ)] with k hk b
  exact ⟨(Real.rpow_le_rpow_of_exponent_le (hN i k) (by linarith)).trans (hk b).1,
    (hk b).2.trans (Real.rpow_le_rpow_of_exponent_le (hN i k) (by linarith))⟩

end PacketCancellation
end Submission.Obl.k4_balanced_native_packet_transport.CPF
