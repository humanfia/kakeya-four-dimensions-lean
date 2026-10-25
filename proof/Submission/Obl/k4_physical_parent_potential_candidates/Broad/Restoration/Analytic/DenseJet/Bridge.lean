-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/Analytic/DenseJet/Bridge.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/Analytic/DenseJet/Bridge.lean (session x0945).
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (with x0491's contributions), branch x0487,
-- commit 36234c36, file Submission/Obl/k4_isotropic_discovery_of_local_restoration/DenseJet/Bridge.lean
-- (namespace renamed; the attributions that file carries are kept below).
import Mathlib
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.SampledBranch
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.DenseJet.Assertion
import Submission.Obl.k4_algebraic_sheet_remez

/-!
# The dense jet assertion of the sampled-branch interface

`DenseJetAssertion` (with `HasRealExtension` asking for a `ContDiffOn ℂ ⊤` extension)
follows from the sheet Remez assertion, the frozen statement of o172.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

open Submission.Obl.k4_physical_parent_potential_candidates.Analytic.DenseJet

theorem HasRealExtension.toSmooth {D : ℕ} {f : Base → ℝ} (h : HasRealExtension D f) :
    HasSmoothRealExtension D f := by
  obtain ⟨F, P, hP, hdeg, hF, hroot, hfF⟩ := h
  exact ⟨F, P, hP, hdeg, hF.of_le le_top, hroot, hfF⟩

theorem DenseJetBound.of_smooth {D J : ℕ} (h : DenseJetBoundSmooth D J) : DenseJetBound D J :=
  fun A hA f hf => h A hA f hf.toSmooth

/-- The sampled-branch jet interface from the frozen o172 statement. -/
theorem denseJetAssertion_of_sheetRemez (hR : SheetRemezAssertion) : DenseJetAssertion := by
  intro D
  obtain ⟨J, hJ, hjet⟩ := denseJetBoundSmooth_of_sheetRemez hR D
  exact ⟨J, hJ, DenseJetBound.of_smooth hjet⟩

/-- The sampled-branch jet interface, from the accepted o172. -/
theorem denseJetAssertion : DenseJetAssertion :=
  denseJetAssertion_of_sheetRemez Submission.k4_algebraic_sheet_remez

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
