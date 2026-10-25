-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.MassGain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_seed_of_balanced_robust_clusters.Counting
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Definitions

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open MeasureTheory LeanEval.Analysis.WangZahlKakeya
open wz_clustered_cover_volume_gain (A)

/-- A nearly disjoint shading already gives the volume alternative. The slab
count prevents the normalization `n * δ` from becoming too small. -/
theorem volume_gain_of_mass_fraction {δ η σ ω α b : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 ≤ η) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hbudget : b + α + 2 * η ≤ ω)
    {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hA : A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y)
    (hmass : ENNReal.ofReal (δ ^ b) * ∑ i, volume (Y i) ≤ volume (⋃ i, Y i)) :
    ENNReal.ofReal ((1 / 8 : ℝ) * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤
      volume (⋃ i, Y i) := by
  have hnδ : 0 < (n : ℝ) * δ := mul_pos (Nat.cast_pos.mpr hA.1) hδ
  have hpow : 0 < δ ^ η := Real.rpow_pos_of_pos hδ η
  have hpow1 : δ ^ η ≤ 1 := Real.rpow_le_one hδ.le hδ1 hη
  have hslab := wz_seed_of_balanced_robust_clusters.slab_count_lower hδ
    (Real.rpow_nonneg hδ.le (-η)) hA.1 (fun i => (hA.2.1 i).1)
    hA.2.2.2.2.2 (fun i => (hA.2.1 i).2.1)
  have hcard : δ ^ η ≤ 8 * ((n : ℝ) * δ) := by
    calc
      δ ^ η = δ ^ η * 1 := by ring
      _ ≤ δ ^ η * (8 * δ ^ (-η) * (n : ℝ) * δ) :=
        mul_le_mul_of_nonneg_left hslab hpow.le
      _ = 8 * ((n : ℝ) * δ) := by
        rw [Real.rpow_neg hδ.le]
        field_simp
  have hcardpow : δ ^ η ≤ 8 * ((n : ℝ) * δ) ^ σ := by
    by_cases hsmall : (n : ℝ) * δ ≤ 1
    · calc
        δ ^ η ≤ 8 * ((n : ℝ) * δ) := hcard
        _ = 8 * ((n : ℝ) * δ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ ≤ 8 * ((n : ℝ) * δ) ^ σ :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_ge hnδ hsmall hσ1) (by norm_num)
    · have hlarge : 1 ≤ ((n : ℝ) * δ) ^ σ :=
        Real.one_le_rpow (le_of_lt (lt_of_not_ge hsmall)) hσ
      linarith
  have hcancel : δ ^ η * ((n : ℝ) * δ) ^ (-σ) ≤ 8 := by
    rw [Real.rpow_neg hnδ.le]
    exact (mul_inv_le_iff₀ (Real.rpow_pos_of_pos hnδ σ)).mpr hcardpow
  have hscalar :
      (1 / 8 : ℝ) * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ) ≤
        δ ^ (b + η) * n * δ ^ 2 := by
    calc
      _ ≤ (1 / 8 : ℝ) * δ ^ (b + 2 * η) * (n * δ ^ 2) * (n * δ) ^ (-σ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)) (by norm_num))
            (by positivity)) (Real.rpow_nonneg hnδ.le _)
      _ = (δ ^ (b + η) * n * δ ^ 2) * (δ ^ η * (n * δ) ^ (-σ) / 8) := by
        rw [show b + 2 * η = (b + η) + η by ring, Real.rpow_add hδ]
        ring
      _ ≤ δ ^ (b + η) * n * δ ^ 2 := by
        apply mul_le_of_le_one_right (by positivity)
        linarith
  apply (ENNReal.ofReal_le_ofReal hscalar).trans
  calc
    ENNReal.ofReal (δ ^ (b + η) * n * δ ^ 2) =
        ENNReal.ofReal (δ ^ b) * ENNReal.ofReal (δ ^ η * n * δ ^ 2) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), Real.rpow_add hδ]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (δ ^ b) * ∑ i, volume (Y i) :=
      mul_le_mul_right hA.2.2.2.1 _
    _ ≤ volume (⋃ i, Y i) := hmass

end WangZahlLot.Obl.wz_broad_grains_initialization
