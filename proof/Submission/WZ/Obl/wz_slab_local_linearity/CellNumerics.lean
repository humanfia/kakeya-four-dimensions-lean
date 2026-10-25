-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.CellNumerics.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.CellAssembly
import Submission.WZ.Obl.wz_slab_local_linearity.SmallPowers

namespace WangZahlLot.Obl.wz_slab_local_linearity.CellProofs

lemma cell_denominator_bound {M : ℕ} {s A t κ : ℝ}
    (hs : 0 < s) (hA : 0 ≤ A) (ht : 0 ≤ t) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hM : (M : ℝ) ≤ 2 / s) :
    cellCountDenominator M (4 / s) (A * t) κ ≤
      415872 * A ^ 4 * t ^ 4 / (s ^ 5 * κ ^ 2) := by
  have hfac : 16 / κ + 3 ≤ 19 / κ := by
    apply (le_div_iff₀ hκ).mpr
    have he : (16 / κ + 3) * κ = 16 + 3 * κ := by field_simp
    rw [he]
    linarith
  calc cellCountDenominator M (4 / s) (A * t) κ
      = ((4 / s) * ((A * t) * (16 / κ + 3))) ^ 2 *
          (M * (M * (3 * (A * t)))) * (M * (3 * (A * t))) := rfl
    _ ≤ ((4 / s) * ((A * t) * (19 / κ))) ^ 2 *
          ((2 / s) * ((2 / s) * (3 * (A * t)))) * ((2 / s) * (3 * (A * t))) := by
        gcongr
    _ = 415872 * A ^ 4 * t ^ 4 / (s ^ 5 * κ ^ 2) := by field_simp; ring

lemma cell_rich_bound {M : ℕ} {s A t κ : ℝ}
    (hs : 0 < s) (hA : 0 ≤ A) (ht : 0 ≤ t) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hM : (M : ℝ) ≤ 2 / s) :
    (3 * (A * t)) * M * (3 * (A * t)) * (1 + 16 / κ) ≤
      306 * A ^ 2 * t ^ 2 / (s * κ) := by
  have hfac : 1 + 16 / κ ≤ 17 / κ := by
    apply (le_div_iff₀ hκ).mpr
    have he : (1 + 16 / κ) * κ = κ + 16 := by field_simp
    rw [he]
    linarith
  calc (3 * (A * t)) * M * (3 * (A * t)) * (1 + 16 / κ)
      ≤ (3 * (A * t)) * (2 / s) * (3 * (A * t)) * (17 / κ) := by gcongr
    _ = 306 * A ^ 2 * t ^ 2 / (s * κ) := by field_simp; ring

lemma cell_fourth_moment_lower {M : ℕ} {s P Q : ℝ} (hMpos : 0 < M)
    (hs : 0 < s) (hQ : 0 ≤ Q) (hQP : Q ≤ P) (hM : (M : ℝ) ≤ 2 / s) :
    (Q * s / 4) ^ 4 ≤ (P / (2 * M)) ^ 4 := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hMs : (M : ℝ) * s ≤ 2 := (le_div_iff₀ hs).mp hM
  have hQM := mul_le_mul_of_nonneg_left hMs hQ
  have he : Q * s / 4 ≤ P / (2 * M) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * M)]
    nlinarith
  exact pow_le_pow_left₀ (by positivity) he 4

end WangZahlLot.Obl.wz_slab_local_linearity.CellProofs
