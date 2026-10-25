/- Adapted from this LOT tree, obligation o100, session x0340, commit fb1668b,
   Submission/Obl/k4_scalar_marked_profile_selection/PureAtomRecords.lean. -/
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.AtomRecords
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.PureRecords

namespace Submission.Obl.k4_marked_scalar_grid_selection.Scalar

open MeasureTheory Set
open scoped ENNReal

/-- At unit slope depth, the same record supports the pure observation. The
bounded old slope code provides the additional finite overlap factor. -/
theorem atom_supported_on_pure_record {H J : ℕ} (hJ : 0 < J) {σ a K R : ℝ}
    (hσ : 0 < σ) (hσ₁ : σ ≤ 1) (hmesh : 1 ≤ (J : ℝ) * σ) (ha : σ ≤ a)
    (hK : 0 ≤ K) (hR : 10 * (K + 1) ≤ R)
    (b : Fin H → Fin 5 → ℝ) (hb : ∀ j i, |b j i| ≤ K)
    (j : Fin H) (z : Fin J) :
    ∀ᵐ p ∂atom σ J b j z, pureWidthObservation a p ∈
      pureRecordSupport σ K R (atomRecord σ a 1 b j z) := by
  have hsupport := atom_supported_on_record hJ hσ hmesh ha (by norm_num : (0 : ℝ) < 1)
    hσ₁ (by norm_num : (1 : ℝ) ≤ 1) hK hR b hb j z
  have hfloor := Submission.Obl.k4_matching_homogeneous_records.floor_sub_bound (b j 1) 0
  simp only [Int.floor_zero, Int.cast_sub, Int.cast_zero, sub_zero] at hfloor
  have hcode : |((atomRecord σ a 1 b j z).2.2.2 : ℝ)| ≤ K + 1 := by
    simpa only [atomRecord, div_one, Int.floor_zero, sub_zero, Int.cast_sub,
      Int.cast_zero] using hfloor.trans (by linarith [hb j 1])
  filter_upwards [hsupport] with p hp
  refine ⟨hcode, hp.1, hp.2.1⟩

end Submission.Obl.k4_marked_scalar_grid_selection.Scalar
