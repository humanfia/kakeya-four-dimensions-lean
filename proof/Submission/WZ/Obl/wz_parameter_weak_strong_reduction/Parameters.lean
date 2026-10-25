-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_parameter_weak_strong_reduction.Parameters.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_parameter_weak_strong_reduction

open Filter Set
open scoped Topology

/-- Any fixed constant is bounded by a negative power on a sufficiently small
positive interval. -/
theorem exists_power_cutoff (C a : ℝ) (ha : 0 < a) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → C ≤ δ ^ (-a) := by
  have he : ∀ᶠ δ : ℝ in 𝓝[>] 0, C ≤ δ ^ (-a) :=
    (tendsto_rpow_neg_nhdsGT_zero (by linarith : -a < 0)).eventually_ge_atTop C
  obtain ⟨d, hd, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  change 0 < d at hd
  refine ⟨d / 2, by linarith, ?_⟩
  intro δ hδ hδd
  exact hbound ⟨hδ, by linarith⟩

end WangZahlLot.Obl.wz_parameter_weak_strong_reduction
