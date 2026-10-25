import Submission.Obl.k4_row_parent_contact_candidates.SkewSelection
import Submission.Obl.k4_row_parent_contact_candidates.RowCalibration
import Submission.Obl.k4_row_parent_contact_candidates.Wrapper

/-! The remaining geometric input is a dense affine sheet on nondegenerate
row parents. Calibration, contact renewal and candidate return are already
contained in RowCalibration. -/

namespace Submission.Obl.k4_row_parent_contact_candidates

open scoped Submission.Obl.k4_row_parent_contact_candidates.ZoomInput

open MeasureTheory Set Filter MvPolynomial
open PreparedModel
open Submission.Lib.K4ContactNormalization (point affineBase)

noncomputable section

/-- A dense row parent with subpower inverse skew admits a full-time affine
hidden predictor after a further subpower restriction. -/
def RowSheetPrinciple : Prop :=
  ∀ {α : Type} [MeasurableSpace α] {p : Parameters}, p.Valid →
    ∀ {a : PreparedModel α}, a.Valid p →
    ∀ {r e : ℝ}, 0 < r → r < p.U → 0 < e →
    ∀ M : ℕ → ℝ, (∀ k, 1 ≤ M k) → Subpower p.N M →
    (∃ᶠ k in atTop, ∃ RP : RowParent p a k r (M k * p.N k ^ (-e)) (M k),
      RP.lam ≠ 0 ∧ |RP.lam⁻¹| ≤ M k) →
    ∃ e' : ℝ, 0 < e' ∧ ∃ M' : ℕ → ℝ, (∀ k, 1 ≤ M' k) ∧ Subpower p.N M' ∧
      ∃ᶠ k in atTop, ∃ RP : RowParent p a k r (M' k * p.N k ^ (-e')) (M' k),
        ∃ L : Fin 4 → ℝ, RP.lam ≠ 0 ∧ |RP.lam⁻¹| ≤ M' k ∧
          ∀ z ∈ RP.G, ∀ t ∈ a.block k r RP.Q,
            |eval (point (a.b k z.1) t) (affineBase L) - point (a.b k z.1) t 3| ≤
              M' k * width p k r

/-- The original row-parent implication follows from affine preparation. -/
theorem rowParentsPrinciple_of_sheets (hsheets : RowSheetPrinciple) : RowParentsPrinciple := by
  intro α _ p hp a ha hCMP r e hr hrU he M hM1 hM hfreq
  by_contra hnot
  obtain ⟨M₁, hM₁1, hM₁, hfreq₁⟩ :=
    nondegenerate_rowParents_of_not_result hp ha hnot hr hrU he M hM1 hM hfreq
  obtain ⟨e', he', M₂, hM₂1, hM₂, hfreq₂⟩ :=
    hsheets hp ha hr hrU he M₁ hM₁1 hM₁ hfreq₁
  exact hnot (result_of_rowParents_affine hp ha hCMP hr hrU he' M₂ hM₂1 hM₂ hfreq₂)

end

end Submission.Obl.k4_row_parent_contact_candidates
