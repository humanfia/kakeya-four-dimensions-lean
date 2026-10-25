-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.QuarterCells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.HeightCells

namespace WangZahlLot.Obl.wz_slab_local_linearity

open Set MeasureTheory
open scoped ENNReal

def quarterHeightCells (ρ : ℝ) (K : Finset ℤ) : Set ℝ :=
  ⋃ k ∈ K, Ico (ρ * (k : ℝ)) (ρ * (k : ℝ) + ρ / 4)

lemma quarterHeightCells_subset {ρ : ℝ} (hρ : 0 ≤ ρ) (K : Finset ℤ) :
    quarterHeightCells ρ K ⊆ heightCells ρ K := by
  rintro z hz
  obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.mp hz
  refine mem_iUnion₂.mpr ⟨k, hk, hzk.1, ?_⟩
  have hh := hzk.2
  change z < ρ * ((k : ℝ) + 1)
  linarith

lemma volume_quarterHeightCells {ρ : ℝ} (hρ : 0 ≤ ρ) (K : Finset ℤ) :
    volume (quarterHeightCells ρ K) = ENNReal.ofReal ((K.card : ℝ) * ρ / 4) := by
  have hsub (k : ℤ) : Ico (ρ * (k : ℝ)) (ρ * (k : ℝ) + ρ / 4) ⊆ heightCell ρ k := by
    intro z hz
    exact ⟨hz.1, by change z < ρ * ((k : ℝ) + 1); linarith [hz.2]⟩
  rw [quarterHeightCells, measure_biUnion_finset
    (fun i _ j _ hij => (heightCell_disjoint hρ hij).mono (hsub i) (hsub j))
    (fun _ _ => measurableSet_Ico)]
  simp only [Real.volume_Ico, add_sub_cancel_left, Finset.sum_const, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  ring

/-- Extend a `ρ/8` approximation with slope at most two to lower quarter cells. -/
lemma quarter_height_extraction {ρ a b : ℝ} {K : Finset ℤ} {f : ℝ → ℝ} {Z : Set ℝ}
    (hρ : 0 < ρ) (hZ : heightCells ρ K ⊆ Z) (hb : |b| ≤ 2)
    (hf : ∀ x ∈ Z, ∀ y ∈ Z, |f x - f y| ≤ |x - y|)
    (hanchor : ∀ (k : ℤ), k ∈ K → |f (ρ * k) - (a + b * (ρ * k))| ≤ ρ / 8) :
    ∃ Zl : Set ℝ, Zl ⊆ Z ∧ ENNReal.ofReal ((K.card : ℝ) * ρ / 4) ≤ volume Zl ∧
      ∀ z ∈ Zl, |f z - (a + b * z)| ≤ ρ := by
  refine ⟨quarterHeightCells ρ K, (quarterHeightCells_subset hρ.le K).trans hZ,
    (volume_quarterHeightCells hρ.le K).symm.le, ?_⟩
  intro z hz
  have hzZ := hZ (quarterHeightCells_subset hρ.le K hz)
  obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.mp hz
  have hkZ : ρ * (k : ℝ) ∈ Z := by
    apply hZ
    refine mem_iUnion₂.mpr ⟨k, hk, le_rfl, ?_⟩
    change ρ * (k : ℝ) < ρ * ((k : ℝ) + 1)
    nlinarith
  have hdist : |z - ρ * (k : ℝ)| ≤ ρ / 4 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hzk.1)]
    linarith [hzk.2]
  have hfl : |f z - f (ρ * (k : ℝ))| ≤ ρ / 4 := (hf z hzZ _ hkZ).trans hdist
  have hbl : |b * (ρ * (k : ℝ) - z)| ≤ ρ / 2 := by
    rw [abs_mul, abs_sub_comm]
    nlinarith [mul_le_mul hb hdist (abs_nonneg (z - ρ * (k : ℝ))) (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    |f z - (a + b * z)| =
      |(f z - f (ρ * (k : ℝ))) + (f (ρ * (k : ℝ)) - (a + b * (ρ * (k : ℝ)))) +
        b * (ρ * (k : ℝ) - z)| := by congr 1; ring
    _ ≤ |f z - f (ρ * (k : ℝ))| + |f (ρ * (k : ℝ)) - (a + b * (ρ * (k : ℝ)))| +
        |b * (ρ * (k : ℝ) - z)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ρ := by linarith [hanchor k hk]

lemma quarter_cell_measure_budget {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ρ ^ ((1 : ℝ) / 2 + ε) ≤ ρ ^ ((ε - 1) / 2) * ρ / 4 := by
  refine ⟨(1 / 4 : ℝ) ^ (2 / ε), Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
  intro ρ hρ hρ₀
  have hh : ρ ^ (ε / 2) ≤ 1 / 4 := by
    calc
      ρ ^ (ε / 2) ≤ ((1 / 4 : ℝ) ^ (2 / ε)) ^ (ε / 2) :=
        Real.rpow_le_rpow hρ.le hρ₀ (by positivity)
      _ = 1 / 4 := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
        have hmul : 2 / ε * (ε / 2) = 1 := by field_simp
        rw [hmul, Real.rpow_one]
  have hr : ρ ^ ((ε - 1) / 2) * ρ = ρ ^ ((ε + 1) / 2) := by
    calc
      ρ ^ ((ε - 1) / 2) * ρ = ρ ^ ((ε - 1) / 2) * ρ ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = ρ ^ ((ε - 1) / 2 + 1) := (Real.rpow_add hρ _ _).symm
      _ = ρ ^ ((ε + 1) / 2) := by congr 1; ring
  rw [hr]
  calc
    ρ ^ ((1 : ℝ) / 2 + ε) = ρ ^ ((ε + 1) / 2) * ρ ^ (ε / 2) := by
      rw [← Real.rpow_add hρ]
      congr 1
      ring
    _ ≤ ρ ^ ((ε + 1) / 2) * (1 / 4) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hρ.le _)
    _ = ρ ^ ((ε + 1) / 2) / 4 := by ring

end WangZahlLot.Obl.wz_slab_local_linearity
