-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeScaleDataMono, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeScaleData

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

noncomputable section

/-- A smaller path exponent uses the same numerical native choices
and all their already established mass bounds. -/
def NativeScaleData.restrict_sigma
    {q : NativeScaleDesign} {N sigma sigma' Kcensus stripWidth theta : ℝ} {T fine steps : ℕ}
    (native : NativeScaleData q N sigma T fine steps Kcensus stripWidth theta)
    (hN : 1 ≤ N) (hsigma : sigma' ≤ sigma) :
    NativeScaleData q N sigma' T fine steps Kcensus stripWidth theta :=
  { native with
    pre_charge := fun kappa hk hkn => native.pre_charge kappa hk
      (hkn.trans (Real.rpow_le_rpow_of_exponent_le hN hsigma))
    terminal_charge := fun kappa hk hkn => native.terminal_charge kappa hk
      (hkn.trans (Real.rpow_le_rpow_of_exponent_le hN hsigma))
    support_charge := fun kappa hk hkn => native.support_charge kappa hk
      (hkn.trans (Real.rpow_le_rpow_of_exponent_le hN hsigma)) }

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
