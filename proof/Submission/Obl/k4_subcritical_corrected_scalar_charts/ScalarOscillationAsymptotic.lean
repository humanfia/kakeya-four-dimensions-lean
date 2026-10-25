/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/ScalarOscillationAsymptotic.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeScalarOscillation
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeResolution

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory Filter
open Submission.Obl.k4_profile_density_bounds

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The scalar coefficient ceiling is a fixed power of the coarse scale,
independent of the endpoint's raw coefficient exponent. -/
theorem Prepared.eventually_scalar_coefficient_ceiling (h : cfg.Prepared) {s₀ η : ℝ}
    (hs₀ : 0 < s₀) (hη : η ≤ s₀ / 4) :
    ∀ᶠ k in atTop,
      (512 * cfg.K k ^ 5 + 32 * cfg.N k ^ η) / cfg.N k ^ (-s₀) + 2 * cfg.N k ^ η ≤
        cfg.N k ^ (2 * s₀) := by
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [h.scale k]
  have hpow := eventually_subpower_pow_le hN1 h.subpower.1 h.subpower.2
    5 (show 0 < s₀ / 4 by positivity)
  have hc := eventually_const_mul_rpow_lt h.scale_limit (show 5 * s₀ / 4 < 2 * s₀ by linarith) 546
  filter_upwards [hpow, hc] with k hK hc
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have he : cfg.N k ^ η ≤ cfg.N k ^ (s₀ / 4) :=
    Real.rpow_le_rpow_of_exponent_le (hN1 k) hη
  have hAi : (cfg.N k ^ (-s₀))⁻¹ = cfg.N k ^ s₀ := by
    rw [Real.rpow_neg hN.le, inv_inv]
  have ht : 2 * cfg.N k ^ (s₀ / 4) ≤ 2 * cfg.N k ^ (s₀ / 4) * cfg.N k ^ s₀ :=
    le_mul_of_one_le_right (by positivity) (Real.one_le_rpow (hN1 k) hs₀.le)
  calc
    _ ≤ (512 * cfg.N k ^ (s₀ / 4) + 32 * cfg.N k ^ (s₀ / 4)) /
        cfg.N k ^ (-s₀) + 2 * cfg.N k ^ (s₀ / 4) := by gcongr
    _ = 544 * cfg.N k ^ (s₀ / 4) * cfg.N k ^ s₀ + 2 * cfg.N k ^ (s₀ / 4) := by
      rw [div_eq_mul_inv, hAi]
      ring
    _ ≤ 544 * cfg.N k ^ (s₀ / 4) * cfg.N k ^ s₀ +
        2 * cfg.N k ^ (s₀ / 4) * cfg.N k ^ s₀ := add_le_add le_rfl ht
    _ = 546 * cfg.N k ^ (5 * s₀ / 4) := by
      rw [show 544 * cfg.N k ^ (s₀ / 4) * cfg.N k ^ s₀ +
          2 * cfg.N k ^ (s₀ / 4) * cfg.N k ^ s₀ =
          546 * (cfg.N k ^ (s₀ / 4) * cfg.N k ^ s₀) by ring,
        ← Real.rpow_add hN]
      congr 1
      congr 1
      ring
    _ ≤ _ := hc.le

/-- Within a scalar mesh cell, a corrected genuine native entry moves by at
most one terminal signal width. A free native constant coefficient is harmless. -/
theorem Prepared.eventually_native_scalar_oscillation (h : cfg.Prepared) {s₀ s η : ℝ}
    (hs₀ : 0 < s₀) (hη : η ≤ s₀ / 4) (hgap : s - s₀ < 18 * s₀) :
    ∀ᶠ k in atTop, ∀ (a : cfg.NativeLevel k s) (i : Fin (cfg.n k s))
      (H : Fin 6 → ℝ) (β : Fin 3 → ℝ) (pc qc v : ℝ),
      |pc| ≤ 3 * cfg.K k → |v| ≤ 3 * cfg.K k → |β 2| ≤ cfg.N k ^ η →
      (∀ t ∈ Icc (0 : ℝ) 1,
        ∀ p ∈ Icc pc (pc + cfg.N k ^ (-(2 * cfg.κ * s₀))),
        ∀ q ∈ Icc qc (qc + cfg.N k ^ (-(2 * cfg.κ * s₀))),
          |parameterPredictor H t p q| ≤ cfg.N k ^ η) →
      ∀ t t' R R' : ℝ, t ∈ Icc (0 : ℝ) 1 → t' ∈ Icc (0 : ℝ) 1 → |R| ≤ 4 → |R'| ≤ 4 →
      |t - t'| ≤ 2 * cfg.N k ^ (-(20 * s₀)) →
      |R - R'| ≤ 2 * cfg.N k ^ (-(20 * s₀)) →
      |nativeScalarEntry H β (a.L i) (cfg.N k ^ (-(2 * cfg.κ * s₀))) (cfg.N k ^ (-s₀)) pc qc v t R -
        nativeScalarEntry H β (a.L i) (cfg.N k ^ (-(2 * cfg.κ * s₀))) (cfg.N k ^ (-s₀)) pc qc v t' R'| ≤
          cfg.N k ^ (-(s - s₀)) := by
  have hsmall := eventually_const_mul_rpow_lt h.scale_limit
    (show -(18 * s₀) < -(s - s₀) by linarith) 8
  filter_upwards [h.eventually_scalar_coefficient_ceiling hs₀ hη, hsmall] with k hcoef hsmall
  intro a i H β pc qc v hpc hv hβ hnorm t t' R R' ht ht' hR hR' hdt hdR
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hN1 : 1 ≤ cfg.N k := by linarith [h.scale k]
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hD : 0 < cfg.N k ^ (-(2 * cfg.κ * s₀)) := Real.rpow_pos_of_pos hN _
  have hD1 : cfg.N k ^ (-(2 * cfg.κ * s₀)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by nlinarith [h.rate_pos])
  have hA : 0 < cfg.N k ^ (-s₀) := Real.rpow_pos_of_pos hN _
  have hc := nativeScalarEntry_uniform_nonconstant_bound H β (a.L i)
    hK hD hD1 hA (by positivity : 0 ≤ cfg.N k ^ η) (a.slope i) hpc hv hβ hnorm
  have hh := nativeScalarEntry_oscillation H β (a.L i)
    (cfg.N k ^ (-(2 * cfg.κ * s₀))) (cfg.N k ^ (-s₀)) pc qc v
    (by positivity : 0 ≤ cfg.N k ^ (2 * s₀))
    (hc.1.trans hcoef) (hc.2.1.trans hcoef) (hc.2.2.trans hcoef) ht ht' hR hR'
  refine hh.trans ?_
  calc
    _ ≤ 2 * cfg.N k ^ (2 * s₀) *
        (2 * cfg.N k ^ (-(20 * s₀)) + 2 * cfg.N k ^ (-(20 * s₀))) := by gcongr
    _ = 8 * cfg.N k ^ (-(18 * s₀)) := by
      rw [show 2 * cfg.N k ^ (2 * s₀) *
          (2 * cfg.N k ^ (-(20 * s₀)) + 2 * cfg.N k ^ (-(20 * s₀))) =
          8 * (cfg.N k ^ (2 * s₀) * cfg.N k ^ (-(20 * s₀))) by ring,
        ← Real.rpow_add hN]
      congr 1
      congr 1
      ring
    _ ≤ _ := hsmall.le

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
