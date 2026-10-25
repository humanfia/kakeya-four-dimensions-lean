-- Part of an offer for o106 assembled by x0678 (o064). Adapted from this LOT tree, o064's
-- repository, origin/x0447 at f61522e4 (x0447's file Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/RawRestoration/DenseJet/Bridge.lean);
-- only the namespace changed. See that file for the sources it in turn adapts.
-- Adapted from this LOT tree o143/x0542, commit f027eb90,
-- Submission/Obl/k4_isotropic_discovery_of_local_restoration/DenseJet/Bridge.lean.
import Mathlib
import Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration.SampledBranch
import Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration.DenseJet.Assertion
import Submission.Obl.k4_algebraic_sheet_remez

/-!
# The dense jet assertion of the sampled-branch interface

`DenseJetAssertion` (with `HasRealExtension` asking for a `ContDiffOn ℂ ⊤` extension)
follows from the sheet Remez assertion, the frozen statement of o172.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration

open Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration.DenseJet

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

end Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration
