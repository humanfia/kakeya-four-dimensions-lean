-- Part of an offer for o106 assembled by x0678 (o064). Adapted from this LOT tree, o064's
-- repository, origin/x0447 at f61522e4 (x0447's file Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/IsotropicFromWeak.lean);
-- only the namespace changed. See that file for the sources it in turn adapts.
import Submission.Obl.k4_isotropic_path_improvement.Repair.AcceptedAnalytical
import Submission.Obl.k4_isotropic_path_improvement.Repair.SubpowerWeakDiscoveryRepair

namespace Submission.Obl.k4_isotropic_path_improvement.Repair.IsotropicFromWeak

/-- The geometric engine is the remaining input to the isotropic branch. -/
theorem isotropic_of_power_weak (hWeak : SubpowerWeakDiscoveryRepair.WeakUniformDiscovery) :
    O106Repair.O106 :=
  O106Repair117.o106_of_repair
    (SubpowerWeakDiscoveryRepair.frozen_repaired_discovery_of_weak hWeak)
    AcceptedAnalytical.analytical_conversion

end Submission.Obl.k4_isotropic_path_improvement.Repair.IsotropicFromWeak
