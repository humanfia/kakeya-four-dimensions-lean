-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.CombinedRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.CoupledRegularity
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.AngularPartition

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_balanced_cluster_cover

/-- One complete regularity/angular refinement step. It splits off a regular,
pointwise transverse core, and sends the remaining retained mass into disjoint
thin slab cells containing the whole corresponding bodies. -/
lemma regular_transverse_or_slabs {n : ℕ} (hn : 0 < n)
    (P Y : Fin n → Set E) (u c : Fin n → E)
    (hPm : ∀ i, MeasurableSet (P i)) (hPc : ∀ i, Convex ℝ (P i))
    (hPne : ∀ i, (P i).Nonempty) (hu : ∀ i, ‖u i‖ = 1)
    (hYm : ∀ i, MeasurableSet (Y i)) (hYP : ∀ i, Y i ⊆ P i)
    {a θ h : ℝ} (hPbound : ∀ i, P i ⊆ closedBall 0 1)
    (ha : 0 < a) (haθ : a ≤ θ) (hh : 0 ≤ h)
    (hthin : ∀ i q, q ∈ P i → |inner ℝ (u i) (q - c i)| ≤ a)
    {K : ℕ} (hK : (1 / 2 : ℝ) ^ K < 2 * a) :
    ∃ (H Q : Fin n → Set E) (F : Finset Angular.Label) (V : Angular.Label → Set E),
      (∀ i, MeasurableSet (H i)) ∧ (∀ i, MeasurableSet (Q i)) ∧
      (∀ i, H i ⊆ Y i) ∧ (∀ i, Q i ⊆ Y i) ∧
      Disjoint (⋃ i, H i) (⋃ i, Q i) ∧
      (∀ p, (∃ i, p ∈ H i) →
        ∃ i j, p ∈ H i ∧ p ∈ H j ∧ θ < min ‖u i - u j‖ ‖u i + u j‖) ∧
      (∀ i, (H i).Nonempty → ENNReal.ofReal h * volume (P i) ≤ volume (H i)) ∧
      (∀ i p, p ∈ H i → ∀ r : ℝ, a ≤ r → r ≤ 1 →
        ENNReal.ofReal h * volume (P i ∩ ball p r) ≤ volume (H i ∩ ball p r)) ∧
      (∀ ℓ, MeasurableSet (V ℓ)) ∧ Pairwise (fun ℓ ℓ' => Disjoint (V ℓ) (V ℓ')) ∧
      (∀ i, Q i ⊆ ⋃ ℓ ∈ F, V ℓ) ∧
      (∀ i ℓ, ℓ ∈ F → (Q i ∩ V ℓ).Nonempty →
        ENNReal.ofReal h * volume (P i) ≤ volume (Q i ∩ V ℓ)) ∧
      (∀ i ℓ, (Q i ∩ V ℓ).Nonempty → ‖W θ ℓ.1‖ = 1 ∧
        P i ⊆ slab (innerSL ℝ (W θ ℓ.1)) (θ * ℓ.2) (9 * θ)) ∧
      (∑ i, volume (Y i)) ≤ (∑ i, volume (H i)) + (∑ i, volume (Q i)) +
        (ENNReal.ofReal (512 * h) * (1 + 1000 * (K + 1 : ℕ) : ℝ≥0∞) +
          2304 * ENNReal.ofReal h) * ∑ i, volume (P i) := by
  obtain ⟨H, B, hHm, hBm, hHY, hBY, hHB, hHbr, hBnar, hmass, hdensity, hregular⟩ :=
    regular_broad_core (fun i j => θ < min ‖u i - u j‖ ‖u i + u j‖)
      P Y hPm hPc hYm hYP hPbound ha hh hK
  have hBangle : ∀ p i j, p ∈ B i → p ∈ B j → min ‖u i - u j‖ ‖u i + u j‖ ≤ θ := by
    intro p i j hi hj
    exact le_of_not_gt (hBnar p i j hi hj)
  obtain ⟨F, V, Q, hVm, hVdisj, hQm, hQB, hcover, hQmass, hQdensity, hwhole⟩ :=
    Angular.slab_refinement hn (ha.trans_le haθ) haθ P B u c hPne hu hPbound hthin hBm
      (fun i => (hBY i).trans (hYP i)) hBangle (ENNReal.ofReal h)
  refine ⟨H, Q, F, V, hHm, hQm, hHY, fun i => (hQB i).trans (hBY i),
    hHB.mono_right (iUnion_mono hQB), hHbr, hdensity, hregular, hVm, hVdisj,
    hcover, hQdensity, hwhole, ?_⟩
  calc (∑ i, volume (Y i)) ≤ (∑ i, volume (H i)) + (∑ i, volume (B i)) +
        ENNReal.ofReal (512 * h) * (1 + 1000 * (K + 1 : ℕ) : ℝ≥0∞) * ∑ i, volume (P i) := hmass
    _ ≤ (∑ i, volume (H i)) + ((∑ i, volume (Q i)) +
        2304 * ENNReal.ofReal h * ∑ i, volume (P i)) +
        ENNReal.ofReal (512 * h) * (1 + 1000 * (K + 1 : ℕ) : ℝ≥0∞) * ∑ i, volume (P i) :=
      add_le_add (add_le_add le_rfl hQmass) le_rfl
    _ = _ := by ring

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
