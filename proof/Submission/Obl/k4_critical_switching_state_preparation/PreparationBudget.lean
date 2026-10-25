import Submission.Obl.k4_critical_switching_state_preparation.PreparedModel
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_critical_switching_state_preparation

open Filter
open scoped ENNReal

noncomputable section

/-- Time length cancels exactly in the final conditional time ceiling. -/
theorem pruning_time_coefficient {N H : ℝ} (hN : 0 < N) (hH : 0 < H) (C a : ℝ) :
    ENNReal.ofReal (C * H) / ENNReal.ofReal (N ^ (-a) * H) =
      ENNReal.ofReal (C * N ^ a) := by
  rw [← ENNReal.ofReal_div_of_pos (mul_pos (Real.rpow_pos_of_pos hN _) hH)]
  congr 1
  rw [Real.rpow_neg hN.le]
  field_simp [(Real.rpow_pos_of_pos hN a).ne', hH.ne']

theorem pruning_palette_coefficient {N : ℝ} (hN : 0 < N) (C a : ℝ) :
    ENNReal.ofReal C / ENNReal.ofReal (N ^ (-a)) = ENNReal.ofReal (C * N ^ a) := by
  simpa only [mul_one] using pruning_time_coefficient hN (show (0 : ℝ) < 1 by norm_num) C a

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- A single small primitive loss pays simultaneously for both reference
prunings, normalized time, the translated palette, and original-bin transport. -/
theorem Valid.eventually_preparation_budget (h : cfg.Valid) {δ η : ℝ}
    (hδ : 0 < δ) (hη : η ≤ δ / 100) :
    ∀ᶠ k in atTop,
      4294967296 * cfg.K k ^ 22 * cfg.N k ^ (-(δ / 4)) ≤ cfg.N k ^ (-η) ∧
      4 * cfg.N k ^ (-(δ / 4)) ≤ cfg.N k ^ (-η) ∧
      2 * cfg.N k ^ (-δ) ≤ cfg.N k ^ (-η) ∧
      cfg.K k * cfg.N k ^ (δ / 4) ≤ cfg.N k ^ δ ∧
      3072 * cfg.K k ^ 4 * cfg.N k ^ (δ / 4) ≤ cfg.N k ^ δ := by
  have hN := fun k => (by linarith [h.scale k] : 1 ≤ cfg.N k)
  have hstate := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN h.scale_limit h.subpower.1 h.subpower.2 22
    (show -(δ / 4) < -η by linarith) (A := 4294967296) (by norm_num)
  have hline := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN h.scale_limit h.subpower.1 h.subpower.2 0
    (show -(δ / 4) < -η by linarith) (A := 4) (by norm_num)
  have htransport := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN h.scale_limit h.subpower.1 h.subpower.2 0
    (show -δ < -η by linarith) (A := 2) (by norm_num)
  have htime := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN h.scale_limit h.subpower.1 h.subpower.2 1
    (show δ / 4 < δ by linarith) (A := 1) (by norm_num)
  have hpalette := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN h.scale_limit h.subpower.1 h.subpower.2 4
    (show δ / 4 < δ by linarith) (A := 3072) (by norm_num)
  filter_upwards [hstate, hline, htransport, htime, hpalette] with k hs hl ht hti hp
  exact ⟨hs.le, by simpa using hl.le, by simpa using ht.le,
    by simpa using hti.le, hp.le⟩

end Data

end

end Submission.Obl.k4_critical_switching_state_preparation
