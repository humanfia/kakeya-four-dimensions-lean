-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.ProjectionInterval.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CoverCounting
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Parameters

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

/-- An interval containing a sufficiently large projection gives the gain
alternative. The image can be a single fiber of the original hypergraph. -/
theorem projectionGain_of_bounded_subset {δ η ε ρ B N : ℝ} {Q : Set Triple} {S : Set ℝ}
    (hδρ : δ ≤ ρ) (hlength : δ ^ (-η) * ρ ≤ 2 * B)
    (hcount : CoverLower ρ S N) (hpower : ((2 * B) / ρ) ^ (1 - ε) ≤ N)
    (hSD : S ⊆ DotSet Q) (hbound : ∀ s ∈ S, |s| ≤ B) :
    ProjectionGain δ η ε Q := by
  refine ⟨ρ, -B, 2 * B, hδρ, hlength, ?_⟩
  apply (hcount.weaken hpower).mono_set
  intro s hs
  have habs := abs_le.mp (hbound s hs)
  exact ⟨⟨habs.1, by linarith [habs.2]⟩, hSD hs⟩

theorem projectionGain_of_bounded_negative {δ η ε ρ B N : ℝ} {Q : Set Triple} {S : Set ℝ}
    (hδρ : δ ≤ ρ) (hlength : δ ^ (-η) * ρ ≤ 2 * B)
    (hcount : CoverLower ρ S N) (hpower : ((2 * B) / ρ) ^ (1 - ε) ≤ N)
    (hSD : ∀ s ∈ S, -s ∈ DotSet Q) (hbound : ∀ s ∈ S, |s| ≤ B) :
    ProjectionGain δ η ε Q := by
  apply projectionGain_of_bounded_subset hδρ hlength hcount.neg_image hpower
  · rintro x ⟨y, hy, rfl⟩
    exact hSD y hy
  · rintro x ⟨y, hy, rfl⟩
    simpa only [abs_neg] using hbound y hy

end WangZahlLot.Obl.wz_separated_projection_dichotomy
