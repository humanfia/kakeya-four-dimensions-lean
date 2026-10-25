-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.CompactRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.Geometry

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

lemma continuous_projection {f : ℝ → ℝ} (hf : Continuous f) : Continuous (projection f) := by
  unfold projection
  fun_prop

/-- A finite family of bounded measurable shadings has a compact refinement retaining
at least half of its total mass. -/
theorem exists_compact_refinement {n : ℕ} (Y : Fin n → Set Space)
    (hY : ∀ i, MeasurableSet (Y i)) (hfinite : ∀ i, volume (Y i) ≠ ⊤) :
    ∃ Z : Fin n → Set Space, (∀ i, IsCompact (Z i)) ∧ (∀ i, Z i ⊆ Y i) ∧
      (1 / 2 : ℝ≥0∞) * ∑ i, volume (Y i) ≤ ∑ i, volume (Z i) := by
  classical
  have hex (i : Fin n) : ∃ K : Set Space, IsCompact K ∧ K ⊆ Y i ∧
      (1 / 2 : ℝ≥0∞) * volume (Y i) ≤ volume K := by
    by_cases hzero : volume (Y i) = 0
    · exact ⟨∅, isCompact_empty, empty_subset _, by simp [hzero]⟩
    have hhalf : volume (Y i) / 2 < volume (Y i) := ENNReal.half_lt_self hzero (hfinite i)
    obtain ⟨K, hKY, hK, hvol⟩ := (hY i).exists_lt_isCompact_of_ne_top (hfinite i) hhalf
    refine ⟨K, hK, hKY, ?_⟩
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hvol.le
  choose Z hZ hZY hmass using hex
  refine ⟨Z, hZ, hZY, ?_⟩
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => hmass i

theorem exists_compact_shading_refinement {n : ℕ} (x v : Fin n → Space)
    (Y : Fin n → Set Space) {δ : ℝ} (hY : ∀ i, MeasurableSet (Y i))
    (hYtube : ∀ i, Y i ⊆ Tube δ (x i) (v i))
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball 0 1) :
    ∃ Z : Fin n → Set Space, (∀ i, IsCompact (Z i)) ∧ (∀ i, Z i ⊆ Y i) ∧
      (1 / 2 : ℝ≥0∞) * ∑ i, volume (Y i) ≤ ∑ i, volume (Z i) := by
  apply exists_compact_refinement Y hY
  intro i
  exact ne_top_of_le_ne_top measure_ball_lt_top.ne
    (measure_mono ((hYtube i).trans (hball i)))

lemma isCompact_projection_iUnion {n : ℕ} {f : ℝ → ℝ} (hf : Continuous f)
    {Z : Fin n → Set Space} (hZ : ∀ i, IsCompact (Z i)) :
    IsCompact (projection f '' (⋃ i, Z i)) :=
  (isCompact_iUnion hZ).image (continuous_projection hf)

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
