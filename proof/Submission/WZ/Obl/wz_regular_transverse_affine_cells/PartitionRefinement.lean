-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.PartitionRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Regularize

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open MeasureTheory Set
open scoped ENNReal

open Classical in
/-- If each input shading meets at most `M` partition cells, enforcing a fixed
whole-body density in each surviving cell costs at most `M` thresholds per body. -/
lemma bounded_partition_density_refinement {X ι κ : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (U Y : ι → Set X) (hYm : ∀ i, MeasurableSet (Y i))
    (F : Finset κ) (B : κ → Set X) (hB : ∀ ℓ ∈ F, MeasurableSet (B ℓ))
    (M : ℕ) (hcount : ∀ i, (F.filter fun ℓ => (Y i ∩ B ℓ).Nonempty).card ≤ M)
    (τ : ℝ≥0∞) :
    ∃ H : ι → Set X, (∀ i, MeasurableSet (H i)) ∧ (∀ i, H i ⊆ Y i) ∧
      (∑ i, μ (Y i)) ≤ (∑ i, μ (H i)) + (M : ℝ≥0∞) * τ * ∑ i, μ (U i) ∧
      ∀ i ℓ, ℓ ∈ F → (H i ∩ B ℓ).Nonempty → τ * μ (U i) ≤ μ (H i ∩ B ℓ) := by
  classical
  let J : ι → Finset κ := fun i => F.filter fun ℓ => (Y i ∩ B ℓ).Nonempty
  have hJsub : ∀ i, J i ⊆ F := fun _ => Finset.filter_subset _ _
  choose H hHm hHY hmass hreg using fun i =>
    finite_density_pruning μ B (fun _ => τ * μ (U i)) (J i)
      (fun ℓ hℓ => hB ℓ (hJsub i hℓ)) (hYm i)
  have hbudget (i : ι) : (∑ ℓ ∈ J i, τ * μ (U i)) ≤ (M : ℝ≥0∞) * τ * μ (U i) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [mul_assoc]
    apply mul_le_mul_left
    exact_mod_cast hcount i
  refine ⟨H, hHm, hHY, ?_, ?_⟩
  · calc (∑ i, μ (Y i)) ≤ ∑ i, (μ (H i) + (M : ℝ≥0∞) * τ * μ (U i)) := by
          apply Finset.sum_le_sum
          intro i _
          exact (hmass i).trans (add_le_add le_rfl (hbudget i))
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  · intro i ℓ hℓ hmeet
    apply hreg i ℓ _ hmeet
    refine Finset.mem_filter.mpr ⟨hℓ, ?_⟩
    exact hmeet.mono (inter_subset_inter_left _ (hHY i))

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
