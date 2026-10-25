-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.GradientCoefficientPower, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/GradientCoefficientPower.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit adc5136f,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/GradientCoefficientPower.lean.
All earlier source attributions below are retained. -/
-- From this LOT tree, o265 session x0943, branch origin/x0943, Broad/Source/GradientCoefficientPower.lean.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.CoreLipschitz

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

noncomputable section

/-- The genuine whole-core gradient coefficient is a fixed envelope
power whenever strip width and row retention have envelope-power floors.
Its universal norming constants are chosen before all source types. -/
theorem coreGradientCoeff_le_power
    {K width theta : ℝ} (q w t J : ℕ) (hK : 2 ≤ K)
    (hconstant : 96*coreRowK₀ ≤ K) (hwidth : 0 < width)
    (hwidthK : (K^w)⁻¹ ≤ width) (htheta : 0 < theta) (hthetaK : (K^t)⁻¹ ≤ theta) :
    coreGradientCoeff (2*K^(q+7)) width theta J ≤
      K^((q+8)*J+w+t*⌈coreRowC₀⌉₊+1) := by
  have hK1 : 1 ≤ K := by linarith
  have hK0 : 0 ≤ K := zero_le_one.trans hK1
  have hRow : 0 < coreRowK₀ := coreRow_spec.1
  have hC0 : 0 ≤ coreRowC₀ := zero_le_one.trans coreRow_spec.2.1
  have hthetaPower : theta^(-coreRowC₀) ≤ K^(t*⌈coreRowC₀⌉₊) := by
    calc
      _ ≤ ((K^t)⁻¹)^(-coreRowC₀) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hthetaK (neg_nonpos.mpr hC0)
      _ = (K^t)^coreRowC₀ := by
        rw [Real.inv_rpow (by positivity),Real.rpow_neg (by positivity),inv_inv]
      _ ≤ (K^t)^(⌈coreRowC₀⌉₊:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hK1) (Nat.le_ceil _)
      _ = _ := by rw [Real.rpow_natCast,←pow_mul]
  have hwidthInv : width⁻¹ ≤ K^w := by
    have hh := (inv_le_inv₀ hwidth (by positivity : 0 < (K^w)⁻¹)).mpr hwidthK
    simpa only [inv_inv] using hh
  have hwidthPower : 1+(1/2+2)/width ≤ 4*K^w := by
    have hOne : 1 ≤ K^w := one_le_pow₀ hK1
    rw [div_eq_mul_inv]
    nlinarith
  have hA : 2*K^(q+7) ≤ K^(q+8) := by
    calc
      _ ≤ K*K^(q+7) := mul_le_mul_of_nonneg_right hK (pow_nonneg hK0 _)
      _ = _ := by rw [show q+8=q+7+1 by omega,pow_succ]; ring
  have hAJ : (2*K^(q+7))^J ≤ K^((q+8)*J) := by
    simpa only [←pow_mul] using pow_le_pow_left₀ (by positivity : 0 ≤ 2*K^(q+7)) hA J
  calc
    _ = 6*(2*K^(q+7))^J*(1+(1/2+2)/width)*
        (4*coreRowK₀*theta^(-coreRowC₀)) := by unfold coreGradientCoeff; ring
    _ ≤ 6*K^((q+8)*J)*(4*K^w)*(4*coreRowK₀*K^(t*⌈coreRowC₀⌉₊)) := by gcongr
    _ = (96*coreRowK₀)*K^((q+8)*J)*K^w*K^(t*⌈coreRowC₀⌉₊) := by ring
    _ ≤ K*K^((q+8)*J)*K^w*K^(t*⌈coreRowC₀⌉₊) := by gcongr
    _ = _ := by simp only [pow_add,pow_one]; ring

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
