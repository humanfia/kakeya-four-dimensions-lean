-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.SmallPowers.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
namespace WangZahlLot.Obl.wz_slab_local_linearity

lemma exists_small_rpow {a B : ℝ} (ha : 0 < a) (hB : 0 < B) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ρ ^ a ≤ B := by
  refine ⟨B ^ (1 / a), Real.rpow_pos_of_pos hB _, ?_⟩
  intro ρ hρ hρ₀
  calc ρ ^ a ≤ (B ^ (1 / a)) ^ a := Real.rpow_le_rpow hρ.le hρ₀ ha.le
    _ = B := by rw [← Real.rpow_mul hB.le, one_div_mul_cancel ha.ne', Real.rpow_one]

/-- Every fixed positive constant is absorbed by a strict gap in power exponents
at sufficiently small positive scales. -/
lemma exists_small_monomial {a b C : ℝ} (hab : b < a) (hC : 0 < C) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → C * ρ ^ a ≤ ρ ^ b := by
  obtain ⟨ρ₀, hρ₀, hs⟩ := exists_small_rpow (sub_pos.mpr hab) (one_div_pos.mpr hC)
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ hρ hρsmall
  have hp : C * ρ ^ (a - b) ≤ 1 := by
    have hh := (le_div_iff₀ hC).mp (hs ρ hρ hρsmall)
    simpa only [mul_comm] using hh
  have he : ρ ^ b * ρ ^ (a - b) = ρ ^ a := by
    rw [← Real.rpow_add hρ]
    congr 1
    ring
  calc C * ρ ^ a = ρ ^ b * (C * ρ ^ (a - b)) := by rw [← he]; ring
    _ ≤ ρ ^ b * 1 := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hρ.le _)
    _ = ρ ^ b := mul_one _

end WangZahlLot.Obl.wz_slab_local_linearity
