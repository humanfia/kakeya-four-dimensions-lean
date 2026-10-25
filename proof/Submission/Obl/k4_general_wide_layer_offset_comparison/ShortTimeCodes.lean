import Submission.Obl.k4_general_wide_layer_offset_comparison.ShortDomainFiber
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.NestedWitnesses

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ShortTimeCodes.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- Closed true blocks read their exact short-domain time code almost
surely. Accepted o259 removes all dyadic endpoints using only the original
prior-times-Lebesgue domination, so this deletion has zero original mass. -/
theorem Basic.ae_short_time_code (hbase : p.Basic) (k : ℕ) (r m : ℝ) :
    ∀ᵐ ω ∂p.μ k, ∀ Q : Fin (p.n k r), ω.2 ∈ block (p.T k r) (p.j k r Q) →
      (p.shortComparisonCode k r m ω).2.1 = ((p.j k r Q : ℕ) : ℤ) := by
  letI := (hbase k).2.1
  have haway := Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ae_time_away_from_endpoints
    (p.μ k) (p.ν k) (ENNReal.ofReal (p.K k)) (hbase k).2.2.2.1 (p.T k r)
  filter_upwards [haway] with ω hω
  intro Q ht
  have hD : 0 < (2 : ℝ) ^ p.T k r := by positivity
  have hstrict : ω.2 < ((((p.j k r Q : ℕ) : ℝ) + 1) / (2 : ℝ) ^ p.T k r) := by
    apply lt_of_le_of_ne ht.2
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using hω (((p.j k r Q : ℕ) : ℤ) + 1)
  change ⌊ω.2 / (2 : ℝ) ^ (-(p.T k r : ℤ))⌋ = ((p.j k r Q : ℕ) : ℤ)
  rw [zpow_neg, zpow_natCast, div_inv_eq_mul]
  apply Int.floor_eq_iff.mpr
  constructor
  · simpa only [Int.cast_natCast] using (div_le_iff₀ hD).mp ht.1
  · simpa only [Int.cast_natCast] using (lt_div_iff₀ hD).mp hstrict

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
