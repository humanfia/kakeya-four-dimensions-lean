-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.WeightedCards.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.BalancedPruning
import Submission.WZ.Obl.wz_multiscale_finite_tower.ClosedRegularization

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open WangZahlLot.Obl.wz_tower_balanced_refinement (Balanced leafFiber)

lemma weighted_card_retention {α : Type*} (A B : Finset α) (w : α → ℝ)
    {R H : ℝ} (hR : 0 ≤ R) (hH : 0 ≤ H) (hB : B.Nonempty)
    (hw : ∀ b ∈ B, 0 ≤ w b) (hcomp : ∀ a ∈ A, ∀ b ∈ B, w a ≤ R * w b)
    (hcard : H * A.card ≤ B.card) : H * (∑ a ∈ A, w a) ≤ R * ∑ b ∈ B, w b := by
  have hBpos : (0 : ℝ) < B.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hB)
  have hh : (B.card : ℝ) * (∑ a ∈ A, w a) ≤
      (A.card : ℝ) * (R * ∑ b ∈ B, w b) := by
    calc
      _ = ∑ b ∈ B, ∑ a ∈ A, w a := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ b ∈ B, ∑ a ∈ A, R * w b :=
        Finset.sum_le_sum fun b hb => Finset.sum_le_sum fun a ha => hcomp a ha b hb
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, mul_assoc]
  apply le_of_mul_le_mul_left (a := (B.card : ℝ)) _ hBpos
  calc
    (B.card : ℝ) * (H * ∑ a ∈ A, w a) = H * (B.card * ∑ a ∈ A, w a) := by ring
    _ ≤ H * (A.card * (R * ∑ b ∈ B, w b)) := mul_le_mul_of_nonneg_left hh hH
    _ = (H * A.card) * (R * ∑ b ∈ B, w b) := by ring
    _ ≤ B.card * (R * ∑ b ∈ B, w b) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg hR (Finset.sum_nonneg hw))

lemma weighted_card_comparison {α : Type*} (A B : Finset α) (w : α → ℝ)
    {R C : ℝ} (hR : 0 ≤ R) (hC : 0 < C) (hB : B.Nonempty)
    (hw : ∀ b ∈ B, 0 ≤ w b) (hcomp : ∀ a ∈ A, ∀ b ∈ B, w a ≤ R * w b)
    (hcard : (A.card : ℝ) ≤ C * B.card) :
    (∑ a ∈ A, w a) ≤ (C * R) * ∑ b ∈ B, w b := by
  have hh := weighted_card_retention A B w hR (inv_nonneg.mpr hC.le) hB hw hcomp
    (show C⁻¹ * A.card ≤ B.card by rwa [← div_eq_inv_mul, div_le_iff₀ hC, mul_comm])
  have hh' := mul_le_mul_of_nonneg_left hh hC.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul] using hh'

lemma card_preimage_eq_sum {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (p : α → β) (A : Finset β) :
    ((Finset.univ.filter fun i => p i ∈ A).card : ℝ) =
      ∑ b ∈ A, ((Finset.univ.filter fun i => p i = b).card : ℝ) := by
  classical
  have hh := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter fun i => p i ∈ A) (t := A) (f := p)
    (fun i hi => (Finset.mem_filter.mp hi).2)
  have he (b) (hb : b ∈ A) :
      (Finset.univ.filter fun i => p i ∈ A).filter (fun i => p i = b) =
        Finset.univ.filter (fun i => p i = b) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨by simpa only [h] using hb, h⟩
  rw [Finset.sum_congr rfl (fun b hb => congrArg Finset.card (he b hb))] at hh
  exact_mod_cast hh

end WangZahlLot.Obl.wz_multiscale_finite_tower
