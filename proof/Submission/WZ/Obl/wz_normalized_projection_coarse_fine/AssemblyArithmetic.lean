-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.AssemblyArithmetic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.Budgets
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.MassRefinement

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open MeasureTheory
open scoped ENNReal

lemma relative_scale_bound {δ ρ τ ε : ℝ} (hδ : 0 < δ) (hτ : 0 < τ)
    (hcoarse : δ ^ (1 - ε ^ 2) ≤ ρ) (hwidth : ρ * τ ≤ 26 * δ)
    (hsmall : 26 * δ ^ (ε ^ 2 / 2) ≤ 1) : τ ≤ δ ^ (ε ^ 2 / 2) := by
  have hp : δ ^ (1 - ε ^ 2) * τ ≤ 26 * δ :=
    (mul_le_mul_of_nonneg_right hcoarse hτ.le).trans hwidth
  have he : δ ^ (1 - ε ^ 2) * (26 * δ ^ (ε ^ 2)) = 26 * δ := by
    rw [mul_left_comm, ← Real.rpow_add hδ, sub_add_cancel, Real.rpow_one]
  have ht : τ ≤ 26 * δ ^ (ε ^ 2) :=
    (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hδ _)).mp (hp.trans_eq he.symm)
  calc
    τ ≤ 26 * δ ^ (ε ^ 2) := ht
    _ = (26 * δ ^ (ε ^ 2 / 2)) * δ ^ (ε ^ 2 / 2) := by
      rw [mul_assoc, ← Real.rpow_add hδ]
      congr 2
      ring
    _ ≤ 1 * δ ^ (ε ^ 2 / 2) := mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = _ := one_mul _

lemma residual_weight_bound {n : ℕ} {δ ε η : ℝ} (hδ : 0 < δ)
    (w : Fin n → ℝ≥0∞) (hw : ∀ i, w i ≤ ENNReal.ofReal (56 * δ ^ 2))
    (R : Finset (Fin n))
    (hR : (R.card : ℝ) ≤ (6 * 81 ^ 3 / δ) * (δ ^ (1 + ε ^ 2) * (n : ℝ)))
    (hsmall : (112 * (6 * 81 ^ 3)) * δ ^ (ε ^ 2) ≤ δ ^ η) :
    (∑ i ∈ R, w i) ≤ ENNReal.ofReal (δ ^ η * n * δ ^ 2) / 2 := by
  have hreal : (R.card : ℝ) * (56 * δ ^ 2) ≤ (δ ^ η * n * δ ^ 2) / 2 := by
    calc
      _ ≤ ((6 * 81 ^ 3 / δ) * (δ ^ (1 + ε ^ 2) * n)) * (56 * δ ^ 2) :=
        mul_le_mul_of_nonneg_right hR (by positivity)
      _ = ((112 * (6 * 81 ^ 3)) * δ ^ (ε ^ 2)) * (n * δ ^ 2) / 2 := by
        rw [Real.rpow_add hδ, Real.rpow_one]
        field_simp
        <;> ring
      _ ≤ δ ^ η * (n * δ ^ 2) / 2 := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ∑ _i ∈ R, ENNReal.ofReal (56 * δ ^ 2) := Finset.sum_le_sum (fun i _ => hw i)
    _ = ENNReal.ofReal ((R.card : ℝ) * (56 * δ ^ 2)) := by
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((δ ^ η * n * δ ^ 2) / 2) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := by rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]; norm_num

lemma cast_mass_budget {δ u η : ℝ} (hδ : 0 < δ) {L n : ℕ}
    (h : 4 * (L + 1 : ℝ) * δ ^ u ≤ δ ^ η) :
    (4 * (L + 1 : ℝ≥0∞)) * ENNReal.ofReal (δ ^ u * n * δ ^ 2) ≤
      ENNReal.ofReal (δ ^ η * n * δ ^ 2) := by
  have he : (4 * (L + 1 : ℝ≥0∞)) = ENNReal.ofReal (4 * (L + 1 : ℝ)) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      ENNReal.ofReal_add (Nat.cast_nonneg _) (by norm_num)]
    norm_num
  rw [he, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hh := mul_le_mul_of_nonneg_right h (show 0 ≤ (n : ℝ) * δ ^ 2 by positivity)
  nlinarith

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
