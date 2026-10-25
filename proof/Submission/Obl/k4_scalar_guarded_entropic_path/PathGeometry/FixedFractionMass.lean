/-
Adapted from this LOT tree, obligation o093, session x0535, commit 21cac614,
Submission/Obl/k4_scalar_critical_path_terminal/FixedFractionMass.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.SelectedPaths

/-! Any fixed positive fraction of the common path probability retains
inverse-subpower mass in the unchanged original worlds. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures.RefinementChain

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

theorem fixedFactor_subpower {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (C : ℝ) (hC : 0 ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, chain.referenceFactor k * C ≤ N z k ^ ε := by
  have h := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    (fun k => (by linarith [hz.1.1 k])) hz.1.2.1 (chain.referenceFactor_one_le hz)
    (chain.referenceFactor_subpower hz) 1 (a := 0) (b := ε) hε (A := C) hC
  filter_upwards [h] with k hk
  simpa only [pow_one, Real.rpow_zero, mul_one, one_mul, mul_comm] using hk.le

theorem selectedWorldLaw_mass_subpower_of_fixed_fraction {p z : Code}
    (chain : RefinementChain p z) (hz : Exact z)
    (G : (k : ℕ) → Set (Fin (W z k) × State))
    (c : ℝ) (hc : 0 < c)
    (hG : ∀ᶠ k in atTop, ENNReal.ofReal c ≤ normalizedWorldMixture z k (G k))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ENNReal.ofReal (N z k ^ (-ε)) ≤
      ∑ g, ENNReal.ofReal (ω p (chain.sample k) g) *
        chain.selectedWorldLaw k (G k) g univ := by
  filter_upwards [hG, chain.fixedFactor_subpower hz c⁻¹ (inv_nonneg.mpr hc.le) ε hε]
    with k hk hR
  have hN : 0 ≤ N z k := by linarith [hz.1.1 k]
  have hRpos : 0 < chain.referenceFactor k :=
    zero_lt_one.trans_le (chain.referenceFactor_one_le hz k)
  rw [chain.selectedWorldLaw_mass hz k (G k)]
  calc
    _ = ENNReal.ofReal ((N z k ^ ε)⁻¹) := by rw [Real.rpow_neg hN]
    _ ≤ ENNReal.ofReal ((chain.referenceFactor k * c⁻¹)⁻¹) :=
      ENNReal.ofReal_le_ofReal (inv_anti₀ (mul_pos hRpos (inv_pos.mpr hc)) hR)
    _ = ENNReal.ofReal ((chain.referenceFactor k)⁻¹) * ENNReal.ofReal c := by
      rw [mul_inv, inv_inv, ENNReal.ofReal_mul (inv_nonneg.mpr hRpos.le)]
    _ = chain.originalLaw k univ * ENNReal.ofReal c := by
      rw [chain.originalLaw_mass_ofReal_inverseReference hz k]
    _ ≤ _ := mul_le_mul' le_rfl hk

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures.RefinementChain
