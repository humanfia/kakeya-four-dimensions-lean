-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.PacketNumerics.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.Budget

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

lemma regularization_losses {D n M F : ℝ} {K : ℕ} (hD : 0 < D) (hK : 0 < K)
    (hreg : 224 * (K : ℝ) ≤ D) (hM : 0 ≤ M)
    (hn : F ≤ D ^ (3 : ℕ) * n)
    (hret : ((1 / D ^ 2) / (224 * K)) * n ≤ M) :
    F ≤ D ^ (6 : ℕ) * M ∧ 1 / D ^ (3 : ℕ) ≤ (1 / D ^ (2 : ℕ)) / (4 * K) := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hh : n ≤ D ^ (2 : ℕ) * (224 * K) * M := by
    have he : ((1 / D ^ 2) / (224 * K)) * n = n / (D ^ 2 * (224 * K)) := by ring
    rw [he] at hret
    have hh := (div_le_iff₀ (by positivity)).mp hret
    nlinarith only [hh]
  constructor
  · have hbig : n ≤ D ^ (3 : ℕ) * M := by
      exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_right hreg (by positivity : 0 ≤ D ^ 2 * M)])
    have hh := mul_le_mul_of_nonneg_left hbig (by positivity : 0 ≤ D ^ 3)
    nlinarith only [hn, hh]
  · apply (le_div_iff₀ (by positivity : 0 < 4 * (K : ℝ))).mpr
    field_simp
    linarith

lemma parent_selection_losses {D F Fmax N M P : ℝ} (hD : 0 < D) (hFmax : 0 < Fmax)
    (hsize : F ≤ D ^ (6 : ℕ) * M) (hbudget : Fmax * N ≤ D ^ (5 : ℕ) * F)
    (hparent : M ≤ Fmax * P) : N ≤ D ^ (11 : ℕ) * P := by
  apply (mul_le_mul_iff_right₀ hFmax).mp
  have h1 := mul_le_mul_of_nonneg_left hsize (by positivity : 0 ≤ D ^ 5)
  have h2 := mul_le_mul_of_nonneg_left hparent (by positivity : 0 ≤ D ^ 11)
  nlinarith only [hbudget, h1, h2]

lemma slab_coefficient_budget {D : ℝ} {K : ℕ} (hD : 1 ≤ D)
    (hbudget : (10 : ℝ) ^ (16 : ℕ) * (K + 1 : ℕ) ≤ D) :
    D * D ^ (11 : ℕ) * (384 + 1280 * K * (49152 * D)) ≤ D ^ (14 : ℕ) := by
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hh : 384 + 1280 * (K : ℝ) * (49152 * D) ≤ D ^ (2 : ℕ) := by
    push_cast at hbudget
    have hm := mul_le_mul_of_nonneg_right hbudget hDpos.le
    nlinarith [Nat.cast_nonneg (α := ℝ) K]
  have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ D ^ 12)
  nlinarith only [hm]

lemma hull_density_budget {D a b : ℝ} {K : ℕ} (hD : 0 < D) (ha : 0 < a) (hb : 0 < b)
    (hbudget : (10 : ℝ) ^ (16 : ℕ) * (K + 1 : ℕ) ≤ D) :
    a * b / D ^ (19 : ℕ) ≤ (1 / D ^ (3 : ℕ)) ^ (2 : ℕ) * a * b /
      ((10 : ℝ) ^ (15 : ℕ) * D ^ (12 : ℕ) * (K + 1 : ℕ)) := by
  have hk : (0 : ℝ) < (K + 1 : ℕ) := by positivity
  have hbudget' : (10 : ℝ) ^ (15 : ℕ) * (K + 1 : ℕ) ≤ D := by nlinarith
  field_simp
  exact hbudget'

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
