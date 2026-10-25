-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.SmallIteration.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_iteration.CoarseProof
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.ProjectionMeasure

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open MeasureTheory
open WangZahlLot.Obl.wz_normalized_projection_iteration

/-- The coarse/fine comparison at one prescribed comparison exponent. -/
def ComparisonAt (ε : ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1 / 100 : ℝ) →
    ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space)
      (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space),
      Family η δ n x v Y → (∀ i, (1 / 2 : ℝ) ≤ |v i 2|) →
      Frostman η δ n x v → ∀ f : ℝ → ℝ, Slope f → |f 0| ≤ 1 →
      ∃ ρ : ℝ, δ ^ (1 - ε ^ 2) < ρ ∧ ρ < 1 ∧
      ∃ Z : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space,
        (∀ i, MeasurableSet (Z i)) ∧ (∀ i, Z i ⊆ Y i) ∧
        ENNReal.ofReal (δ ^ κ * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Z i) ∧
        ENNReal.ofReal ((δ / ρ) ^ ε) *
          volume (Metric.thickening ρ (Projection f (⋃ i, Z i))) ≤
            volume (Projection f (⋃ i, Z i))

/-- The elementary fiber bound supplies a base exponent without any coarse/fine hypothesis. -/
theorem elementary_projection_estimate : Estimate 2 := by
  refine ⟨1 / 2, by norm_num, 1 / 100, by norm_num, ?_⟩
  intro δ hδ hd hsmall n x v Y hH htr hF f hf hf0
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr hH.1
  have hcoef : 6 * δ ≤ δ ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    have hs := Real.sq_sqrt hδ.le
    have hmul := mul_nonneg hδ.le (show 0 ≤ 1 - 36 * δ by linarith)
    nlinarith [Real.sqrt_nonneg δ]
  have hfiber : ∑ i, volume (Y i) ≤
      ENNReal.ofReal (6 * δ * n) * volume (Projection f (⋃ i, Y i)) := by
    calc
      _ ≤ ∑ _i : Fin n, ENNReal.ofReal (6 * δ) * volume (Projection f (⋃ i, Y i)) := by
        apply Finset.sum_le_sum
        intro i hi
        apply (volume_le_projection_volume hf.1.continuous.measurable hδ
          (hH.2.1 i) (htr i) (hH.2.2.2.2.2.1 i)).trans
        apply mul_le_mul' le_rfl
        exact measure_mono (Set.image_mono (Set.subset_iUnion Y i))
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin,
          ENNReal.ofReal_mul (show 0 ≤ 6 * δ by positivity), ENNReal.ofReal_natCast]
        ring
  have hc : 0 < ENNReal.ofReal (6 * δ * n) := ENNReal.ofReal_pos.mpr (by positivity)
  apply (ENNReal.mul_le_mul_iff_right hc.ne' ENNReal.ofReal_ne_top).mp
  apply le_trans _ hfiber
  apply le_trans _ hH.2.2.2.2.2.2
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef hn.le) (sq_nonneg δ)
  simpa only [Real.rpow_two] using hm

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
