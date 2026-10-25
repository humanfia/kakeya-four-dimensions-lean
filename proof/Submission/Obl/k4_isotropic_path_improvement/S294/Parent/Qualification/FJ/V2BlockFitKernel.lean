-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FJ.V2BlockFitKernel, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FJ/V2BlockFitKernel.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FJ/V2BlockFitKernel.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FJ/V2BlockFitKernel.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2BlockFit
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2RangeFit
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarUniformLocalFit
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarUniformRangeLocalFit

set_option autoImplicit false

/-!
# The planar kernel discharges `LocalFitStatement` and `RangeFitStatement`

`LocalFitStatement` is exactly the statement of x0662's `uniform_original_scalar_affine_fit`
(o078, branch `x0662` at `f2bac599`, adapted in `FJ/ScalarUniformLocalFit.lean`), and
`RangeFitStatement` that of x0260's `uniform_original_scalar_affine_fit_between_powers_all_labels`
(o078, branch `x0260` at `206ab988`, adapted in `FJ/ScalarUniformRangeLocalFit.lean`) for
trajectory types in `Type`; `V2NormalizedFitAt` is x0260's `OriginalScalarNormalizedFitAt`.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2

open Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

theorem localFitStatement_holds (Λ : Type*) [MeasurableSpace Λ] : LocalFitStatement Λ :=
  fun N K hN hNt hK hsub _ _ _ hc hd0 hd hτ =>
    uniform_original_scalar_affine_fit (Λ := Λ) N K hN hNt hK hsub hc hd0 hd hτ

theorem rangeFitStatement_holds : RangeFitStatement :=
  fun N K hN hNt hK hsub _ _ _ _ ha hab hd0 hd hτ =>
    uniform_original_scalar_affine_fit_between_powers_all_labels.{0} N K hN hNt hK hsub
      ha hab hd0 hd hτ

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2
