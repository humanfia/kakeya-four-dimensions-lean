/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeResolution.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeOriginalCaps
import Submission.Obl.k4_profile_density_bounds.Asymptotics

/-! Resolve the genuine native frame by a fixed fine physical mesh. The
accepted subpower estimates are applied to the original N and K. -/

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory Filter
open Submission.Obl.k4_critical_intercept_concentration.Data
open Submission.Obl.k4_profile_density_bounds

noncomputable section

/-- The apparent product of slopes in the last row cancels in the actual
atlas frame. Its row sum is controlled by the native transverse h² scale. -/
theorem atlas_matrix_row_bound {h K δ : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hK : 1 ≤ K) (hδ : 0 ≤ δ) (c : Fin 5 → ℝ) (hc : ∀ e, |c e| ≤ K)
    (e : Fin 3) :
    (∑ j, |nativeFrameMatrix h (c 1) (-c 3 - c 4 * c 1) (c 4) e j| * δ) ≤
      3 * K * δ / h ^ 2 := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hh2 : 0 < h ^ 2 := sq_pos_of_pos hh
  have hratio : δ / h ≤ δ / h ^ 2 := by
    apply (div_le_div_iff₀ hh hh2).mpr
    nlinarith [mul_nonneg hδ (show 0 ≤ h * (1 - h) by positivity)]
  have h3 : δ / h ^ 2 ≤ 3 * K * δ / h ^ 2 := by
    gcongr
    nlinarith
  fin_cases e
  · simpa [nativeFrameMatrix, Fin.sum_univ_three, abs_of_pos hh,
      abs_inv, inv_mul_eq_div] using hratio.trans h3
  · rw [Fin.sum_univ_three]
    change |-(c 1) / h| * δ + |h⁻¹| * δ + |(0 : ℝ)| * δ ≤ _
    simp only [abs_div, abs_neg, abs_of_pos hh, abs_zero, zero_mul, add_zero, abs_inv]
    calc
      |c 1| / h * δ + h⁻¹ * δ = (|c 1| + 1) * (δ / h) := by ring
      _ ≤ (K + 1) * (δ / h ^ 2) := by gcongr; exact hc 1
      _ ≤ 3 * K * δ / h ^ 2 := by
        have hsum : K + 1 ≤ 3 * K := by linarith
        calc
          _ ≤ (3 * K) * (δ / h ^ 2) := mul_le_mul_of_nonneg_right hsum (by positivity)
          _ = _ := by ring
  · rw [Fin.sum_univ_three]
    change |(-c 3 - c 4 * c 1 + c 4 * c 1) / h ^ 2| * δ +
      |-c 4 / h ^ 2| * δ + |(h ^ 2)⁻¹| * δ ≤ _
    rw [show -c 3 - c 4 * c 1 + c 4 * c 1 = -c 3 by ring]
    rw [abs_div, abs_div, abs_neg, abs_neg, abs_inv, abs_of_pos hh2]
    calc
      |c 3| / h ^ 2 * δ + |c 4| / h ^ 2 * δ + (h ^ 2)⁻¹ * δ =
          (|c 3| + |c 4| + 1) * (δ / h ^ 2) := by ring
      _ ≤ (3 * K) * (δ / h ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith [hc 3, hc 4]
      _ = _ := by ring

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- Physical mesh N^(-40s) resolves every native coefficient frame at the
normalized mesh N^(-10s), uniformly over all true labels at fixed depth s. -/
theorem Prepared.eventually_native_mesh (h : cfg.Prepared) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ k in atTop, ∀ a : cfg.AssignmentLevel k s,
      108 * cfg.K k ^ 4 * cfg.N k ^ (-(40 * s)) ≤ cfg.N k ^ (-s) ∧
      cfg.N k ^ (-(10 * s)) ≤ cfg.K k ^ 2 ∧
      ∀ i e, (∑ j, |nativeFrameMatrix (cfg.timeLength k s)
        (cfg.c k s i 1) (-cfg.c k s i 3 - cfg.c k s i 4 * cfg.c k s i 1)
        (cfg.c k s i 4) e j| * cfg.N k ^ (-(40 * s))) ≤
          cfg.N k ^ (-(10 * s)) := by
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [h.scale k]
  have hsig := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2
    4 (show -(40 * s) < -s by linarith) (show (0 : ℝ) ≤ 108 by norm_num)
  have hmat := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2
    3 (show -(40 * s) + 2 * cfg.κ * s < -(10 * s) by
      nlinarith [mul_pos hs (show 0 < 1 - 2 * cfg.κ by linarith [h.subcritical_rate])])
    (show (0 : ℝ) ≤ 3 by norm_num)
  filter_upwards [hsig, hmat] with k hmesh hrow
  intro a
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hK0 : 0 ≤ cfg.K k := zero_le_one.trans hK
  have hq : 0 < cfg.timeLength k s := by unfold timeLength; positivity
  have hq1 : cfg.timeLength k s ≤ 1 := by
    unfold timeLength
    apply inv_le_one_of_one_le₀
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hinv : (cfg.timeLength k s)⁻¹ ≤ cfg.K k * cfg.N k ^ (cfg.κ * s) := by
    simpa only [timeLength, inv_inv] using a.time_upper
  have hinv2 : (cfg.timeLength k s ^ 2)⁻¹ ≤ cfg.K k ^ 2 * cfg.N k ^ (2 * cfg.κ * s) := by
    calc
      _ = ((cfg.timeLength k s)⁻¹) ^ 2 := by rw [inv_pow]
      _ ≤ (cfg.K k * cfg.N k ^ (cfg.κ * s)) ^ 2 :=
        pow_le_pow_left₀ (inv_nonneg.mpr hq.le) hinv 2
      _ = _ := by
        rw [mul_pow]
        congr 1
        rw [← Real.rpow_natCast (cfg.N k ^ (cfg.κ * s)) 2, ← Real.rpow_mul hN.le]
        congr 1
        norm_num
        ring
  refine ⟨hmesh.le, ?_, ?_⟩
  · exact (Real.rpow_le_one_of_one_le_of_nonpos (hN1 k) (by linarith)).trans
      (one_le_pow₀ hK)
  · intro i e
    calc
      _ ≤ 3 * cfg.K k * cfg.N k ^ (-(40 * s)) / cfg.timeLength k s ^ 2 :=
        atlas_matrix_row_bound hq hq1 hK (by positivity) _ (a.coefficient_bound i) e
      _ ≤ 3 * cfg.K k * cfg.N k ^ (-(40 * s)) *
          (cfg.K k ^ 2 * cfg.N k ^ (2 * cfg.κ * s)) := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hinv2 (by positivity)
      _ = 3 * cfg.K k ^ 3 * cfg.N k ^ (-(40 * s) + 2 * cfg.κ * s) := by
        rw [Real.rpow_add hN]
        ring
      _ ≤ cfg.N k ^ (-(10 * s)) := hrow.le

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
