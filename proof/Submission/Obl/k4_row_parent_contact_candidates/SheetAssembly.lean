import Submission.Obl.k4_row_parent_contact_candidates.SheetPrinciple
import Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation.RowAffineRefinement

/-! Identify the portable original-law affine preparation with the row-parent
record used by the contact renewal. Both use the accepted prepared-model types. -/

namespace Submission.Obl.k4_row_parent_contact_candidates

open scoped Submission.Obl.k4_row_parent_contact_candidates.ZoomInput

open MeasureTheory Set Filter
open PreparedModel

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- The portable preparation record has the same original row-parent fields. -/
def RowParent.toCoarse {p : Parameters} {a : PreparedModel α} {k : ℕ} {r E M : ℝ}
    (RP : RowParent p a k r E M) : AffinePreparation.CoarseRowParent p a k r E M where
  Q := RP.Q
  B := RP.B
  lam := RP.lam
  G := RP.G
  measurable_G := RP.measurable_G
  G_sub := RP.G_sub
  mass := RP.mass
  B_le := RP.B_le
  lam_le := RP.lam_le
  row := RP.row

/-- Return the refined original-law record to the contact renewal interface. -/
def rowParentOfCoarse {p : Parameters} {a : PreparedModel α} {k : ℕ} {r E M : ℝ}
    (RP : AffinePreparation.CoarseRowParent p a k r E M) : RowParent p a k r E M where
  Q := RP.Q
  B := RP.B
  lam := RP.lam
  G := RP.G
  measurable_G := RP.measurable_G
  G_sub := RP.G_sub
  mass := RP.mass
  B_le := RP.B_le
  lam_le := RP.lam_le
  row := RP.row

/-- The actual native partition and affine palette supply the remaining
sheet input, with its mass charged to the original prior and current law. -/
theorem rowSheetPrinciple : RowSheetPrinciple := by
  intro α _ p hp a ha r e hr hrU he M hM1 hM hfreq
  have hfreq' : ∃ᶠ k in atTop,
      ∃ RP : AffinePreparation.CoarseRowParent p a k r (M k * p.N k ^ (-e)) (M k),
        RP.lam ≠ 0 ∧ |RP.lam⁻¹| ≤ M k := by
    refine hfreq.mono ?_
    rintro k ⟨RP, hlam, hinv⟩
    exact ⟨RP.toCoarse, hlam, hinv⟩
  obtain ⟨M', hM'1, hM'sub, hfreq'⟩ :=
    AffinePreparation.frequently_row_affine_refinement p hp a ha.1 ha.2.1 ha.2.2.1
      hr hrU.le he M hM1 hM hfreq'
  refine ⟨e, he, M', hM'1, hM'sub, ?_⟩
  refine hfreq'.mono ?_
  rintro k ⟨RP, L, hlam, hinv, hfit⟩
  exact ⟨rowParentOfCoarse RP, L, hlam, hinv, hfit⟩

end

end Submission.Obl.k4_row_parent_contact_candidates
