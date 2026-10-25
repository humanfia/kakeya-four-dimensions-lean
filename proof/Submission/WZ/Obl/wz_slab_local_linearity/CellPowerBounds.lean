-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.CellPowerBounds.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.CellNumerics
import Submission.WZ.Obl.wz_slab_local_linearity.PowerIdentities

namespace WangZahlLot.Obl.wz_slab_local_linearity.CellProofs

lemma cell_denominator_rpow_bound {ρ σ η A : ℝ} {M : ℕ}
    (hρ : 0 < ρ) (hA : 0 ≤ A) (hκ1 : ρ ^ η ≤ 1) (hM : (M : ℝ) ≤ 2 / Real.sqrt ρ) :
    cellCountDenominator M (4 / Real.sqrt ρ) (A * ρ ^ (-(1 - σ) / 2 - η)) (ρ ^ η) ≤
      (415872 * A ^ 4) * ρ ^ (-(9 : ℝ) / 2 + 2 * σ - 6 * η) := by
  have hh := cell_denominator_bound (t := ρ ^ (-(1 - σ) / 2 - η)) (Real.sqrt_pos.mpr hρ) hA (Real.rpow_nonneg hρ.le _)
    (Real.rpow_pos_of_pos hρ _) hκ1 hM
  calc _ ≤ 415872 * A ^ 4 * (ρ ^ (-(1 - σ) / 2 - η)) ^ 4 /
        ((Real.sqrt ρ) ^ 5 * (ρ ^ η) ^ 2) := hh
    _ = (415872 * A ^ 4) * ρ ^ (-(9 : ℝ) / 2 + 2 * σ - 6 * η) := by
      rw [mul_div_assoc, cell_denominator_power hρ]

lemma cell_rich_rpow_bound {ρ σ η A : ℝ} {M : ℕ}
    (hρ : 0 < ρ) (hA : 0 ≤ A) (hκ1 : ρ ^ η ≤ 1) (hM : (M : ℝ) ≤ 2 / Real.sqrt ρ) :
    (3 * (A * ρ ^ (-(1 - σ) / 2 - η))) * M *
        (3 * (A * ρ ^ (-(1 - σ) / 2 - η))) * (1 + 16 / ρ ^ η) ≤
      (306 * A ^ 2) * ρ ^ (-(3 : ℝ) / 2 + σ - 3 * η) := by
  have hh := cell_rich_bound (t := ρ ^ (-(1 - σ) / 2 - η)) (Real.sqrt_pos.mpr hρ) hA (Real.rpow_nonneg hρ.le _)
    (Real.rpow_pos_of_pos hρ _) hκ1 hM
  calc _ ≤ 306 * A ^ 2 * (ρ ^ (-(1 - σ) / 2 - η)) ^ 2 / (Real.sqrt ρ * ρ ^ η) := hh
    _ = (306 * A ^ 2) * ρ ^ (-(3 : ℝ) / 2 + σ - 3 * η) := by
      rw [mul_div_assoc, cell_rich_power hρ]

lemma cell_fourth_rpow_lower {ρ σ η P : ℝ} {M : ℕ} (hρ : 0 < ρ)
    (hMpos : 0 < M) (hM : (M : ℝ) ≤ 2 / Real.sqrt ρ)
    (hP : ρ ^ (-2 + σ / 2 + η) ≤ P) :
    ρ ^ (-6 + 2 * σ + 4 * η) / 256 ≤ (P / (2 * M)) ^ 4 := by
  have hh := cell_fourth_moment_lower hMpos (Real.sqrt_pos.mpr hρ)
    (Real.rpow_nonneg hρ.le _) hP hM
  rwa [cell_fourth_power hρ] at hh

lemma cell_triple_threshold_upper {ρ τ η : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ) :
    2 * ((100 / ρ ^ η) ^ 3 * (Real.sqrt ρ / 1000) ^ (τ - 3)) ≤
      2000000000000000 * ρ ^ (τ / 2 - 3 / 2 - 3 * η) := by
  rw [cell_multiplicity_power hρ]
  calc 2 * ((1000000 * ρ ^ (-3 * η)) * (Real.sqrt ρ / 1000) ^ (τ - 3))
      ≤ 2 * ((1000000 * ρ ^ (-3 * η)) * (1000000000 * ρ ^ (τ / 2 - 3 / 2))) := by
        gcongr
        exact cell_delta_power_upper hρ hτ
    _ = 2000000000000000 * (ρ ^ (-3 * η) * ρ ^ (τ / 2 - 3 / 2)) := by ring
    _ = 2000000000000000 * ρ ^ (τ / 2 - 3 / 2 - 3 * η) := by
        rw [← Real.rpow_add hρ]
        congr 2
        ring

/-- The power comparison that supplies the required number of dot-product triples. -/
lemma cell_triple_budget {ρ σ η τ A P : ℝ} {M : ℕ}
    (hρ : 0 < ρ) (hA : 0 ≤ A) (hτ : 0 < τ) (hκ1 : ρ ^ η ≤ 1)
    (hMpos : 0 < M) (hM : (M : ℝ) ≤ 2 / Real.sqrt ρ)
    (hP : ρ ^ (-2 + σ / 2 + η) ≤ P)
    (hbudget : (256 * 415872 * 2000000000000000 * A ^ 4) *
      ρ ^ (-6 + 2 * σ + τ / 2 - 9 * η) ≤ ρ ^ (-6 + 2 * σ + 4 * η)) :
    cellCountDenominator M (4 / Real.sqrt ρ) (A * ρ ^ (-(1 - σ) / 2 - η)) (ρ ^ η) *
      (2 * ((100 / ρ ^ η) ^ 3 * (Real.sqrt ρ / 1000) ^ (τ - 3))) ≤
        (P / (2 * M)) ^ 4 := by
  apply le_trans _ (cell_fourth_rpow_lower hρ hMpos hM hP)
  have hd := cell_denominator_rpow_bound (σ := σ) hρ hA hκ1 hM
  have ht := cell_triple_threshold_upper (η := η) hρ hτ
  calc _ ≤ ((415872 * A ^ 4) * ρ ^ (-(9 : ℝ) / 2 + 2 * σ - 6 * η)) *
        (2000000000000000 * ρ ^ (τ / 2 - 3 / 2 - 3 * η)) :=
      mul_le_mul hd ht (by positivity) (by positivity)
    _ = ((256 * 415872 * 2000000000000000 * A ^ 4) *
        ρ ^ (-6 + 2 * σ + τ / 2 - 9 * η)) / 256 := by
      rw [mul_mul_mul_comm, ← Real.rpow_add hρ]
      have he : -(9 : ℝ) / 2 + 2 * σ - 6 * η + (τ / 2 - 3 / 2 - 3 * η) =
          -6 + 2 * σ + τ / 2 - 9 * η := by ring
      rw [he]
      ring
    _ ≤ ρ ^ (-6 + 2 * σ + 4 * η) / 256 := div_le_div_of_nonneg_right hbudget (by norm_num)

lemma cell_rich_budget {ρ σ η A P : ℝ} {M : ℕ}
    (hρ : 0 < ρ) (hA : 0 ≤ A) (hκ1 : ρ ^ η ≤ 1)
    (hM : (M : ℝ) ≤ 2 / Real.sqrt ρ) (hP : ρ ^ (-2 + σ / 2 + η) ≤ P)
    (hbudget : (4896 * A ^ 2) * ρ ^ (-(3 : ℝ) / 2 + σ - 3 * η) ≤
      ρ ^ (-(3 : ℝ) / 2 + σ / 2 + η)) :
    (3 * (A * ρ ^ (-(1 - σ) / 2 - η))) * M *
      (3 * (A * ρ ^ (-(1 - σ) / 2 - η))) * (1 + 16 / ρ ^ η) <
        P / (2 * (4 / Real.sqrt ρ)) := by
  have hleft := cell_rich_rpow_bound (σ := σ) hρ hA hκ1 hM
  have hp : 0 < ρ ^ (-(3 : ℝ) / 2 + σ / 2 + η) := Real.rpow_pos_of_pos hρ _
  have he : ρ ^ (-2 + σ / 2 + η) * Real.sqrt ρ = ρ ^ (-(3 : ℝ) / 2 + σ / 2 + η) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hρ]
    congr 1
    ring
  have hright : ρ ^ (-(3 : ℝ) / 2 + σ / 2 + η) / 8 ≤ P / (2 * (4 / Real.sqrt ρ)) := by
    have hprod := mul_le_mul_of_nonneg_right hP (Real.sqrt_nonneg ρ)
    rw [he] at hprod
    have hd : P / (2 * (4 / Real.sqrt ρ)) = P * Real.sqrt ρ / 8 := by field_simp; ring
    rw [hd]
    exact div_le_div_of_nonneg_right hprod (by norm_num)
  calc _ ≤ (306 * A ^ 2) * ρ ^ (-(3 : ℝ) / 2 + σ - 3 * η) := hleft
    _ ≤ ρ ^ (-(3 : ℝ) / 2 + σ / 2 + η) / 16 := by nlinarith [hbudget]
    _ < ρ ^ (-(3 : ℝ) / 2 + σ / 2 + η) / 8 := by linarith
    _ ≤ P / (2 * (4 / Real.sqrt ρ)) := hright

end WangZahlLot.Obl.wz_slab_local_linearity.CellProofs
