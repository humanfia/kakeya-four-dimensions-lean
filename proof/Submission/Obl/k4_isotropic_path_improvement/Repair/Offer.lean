import Submission.Obl.k4_isotropic_path_improvement.Repair.RawStagedWeakInterface
import Submission.Obl.k4_isotropic_path_improvement.Repair.RawPowerWeakDiscoveryBridge
import Submission.Obl.k4_isotropic_path_improvement.Repair.IsotropicFromWeak

/-!
# Core of an offer for o106 (x0678, o064)

o106's exact frozen statement (`O106Repair.O106`) from o265's exact frozen statement
(`RawStagedWeakInterface.StagedWeakAssertion`, x0447: definitionally o265's frozen type), using
accepted o144, o172, o173 and the repaired glue (no re-split of o106 needed). Once o265 is
accepted, the offer's main file applies `o106_of_265` to `Submission.k4_staged_weak_breadth_discovery`.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.Repair.Offer

open Submission.Obl.k4_isotropic_path_improvement.Repair

/-- From the power-mass weak discovery (with accepted o173). -/
theorem o106_of_weak (hweak : SubpowerWeakDiscoveryRepair.WeakUniformDiscovery) :
    O106Repair.O106 :=
  IsotropicFromWeak.isotropic_of_power_weak hweak

/-- From o265's exact frozen statement. -/
theorem o106_of_265 (h : RawStagedWeakInterface.StagedWeakAssertion) : O106Repair.O106 :=
  o106_of_weak (RawPowerWeakDiscoveryBridge.weak_uniform_of_raw
    (RawStagedWeakInterface.power_weak_of_staged h))

end Submission.Obl.k4_isotropic_path_improvement.Repair.Offer
