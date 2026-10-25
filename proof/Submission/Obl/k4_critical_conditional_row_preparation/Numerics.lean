import Submission.Obl.k4_critical_conditional_row_preparation.OriginalMass
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_critical_conditional_row_preparation
noncomputable section
open Filter MeasureTheory
namespace Data
variable {α : Type} [MeasurableSpace α] {cfg : Data α}

theorem AssignmentLevel.length_bounds (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) :
    cfg.timeLength k s ≤ cfg.K k * cfg.N k ^ (-s / 2) ∧
      (cfg.timeLength k s)⁻¹ ≤ cfg.K k * cfg.N k ^ (s / 2) := by
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 0 < cfg.K k := by linarith [h.subpower.1 k]
  have hκ : cfg.κ = 1 / 2 := by linarith [h.critical_rate]
  have he : cfg.κ * s = s / 2 := by rw [hκ]; ring
  have hn : -cfg.κ * s = -s / 2 := by rw [hκ]; ring
  have hc := (time_length_comparison hN hK a.time_lower a.time_upper).1
  rw [hn] at hc
  refine ⟨?_, ?_⟩
  · simpa only [timeLength, mul_comm] using (div_le_iff₀ hK).mp hc
  · simpa only [timeLength, inv_inv, he] using a.time_upper

/-- A depth3s block is shorter than its parent and longer than its parent's
fine mesh. The frozen row error is already at most the target width. -/
theorem Valid.eventually_frozen_margins (h : cfg.Valid) (s : ℝ)
    (hs : 0 < s) (hse : s < cfg.e₀) :
    ∀ᶠ k in atTop, ∀ (a : cfg.AssignmentLevel k s) (deep : cfg.AssignmentLevel k (3 * s)),
      cfg.timeLength k s * cfg.N k ^ (-(200 * s)) ≤ cfg.timeLength k (3 * s) ∧
      cfg.timeLength k (3 * s) ≤ cfg.timeLength k s ∧
      2 * cfg.K k * cfg.N k ^ (-(3 * s)) / cfg.timeLength k (3 * s) +
        24 * cfg.K k ^ 5 * cfg.timeLength k (3 * s) +
        8 * cfg.K k ^ 4 * cfg.N k ^ (-cfg.e₀) ≤ cfg.N k ^ (-s) := by
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [h.scale k]
  have h₁ := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit h.subpower.1 h.subpower.2 2
    (show -s < 0 by linarith) (show (0 : ℝ) ≤ 1 by norm_num)
  have h₂ := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit h.subpower.1 h.subpower.2 2
    (show -(199 * s) < 0 by linarith) (show (0 : ℝ) ≤ 1 by norm_num)
  have h₃ := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit h.subpower.1 h.subpower.2 6
    (show -(3 * s) / 2 < -s by linarith) (show (0 : ℝ) ≤ 52 by norm_num)
  have h₄ := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit h.subpower.1 h.subpower.2 4
    (show -cfg.e₀ < -s by linarith) (show (0 : ℝ) ≤ 16 by norm_num)
  filter_upwards [h₁, h₂, h₃, h₄] with k hk₁ hk₂ hk₃ hk₄
  simp only [one_mul, Real.rpow_zero] at hk₁ hk₂
  intro a deep
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 0 ≤ cfg.K k := by linarith [h.subpower.1 k]
  have hHs : 0 < cfg.timeLength k s := by unfold timeLength; positivity
  have hHd : 0 < cfg.timeLength k (3 * s) := by unfold timeLength; positivity
  have hc := a.length_bounds h
  have hd := deep.length_bounds h
  have hmul (u v : ℝ) : cfg.N k ^ u * cfg.N k ^ v = cfg.N k ^ (u + v) :=
    (Real.rpow_add hN u v).symm
  have hr₁ : cfg.timeLength k (3 * s) / cfg.timeLength k s ≤ cfg.K k ^ 2 * cfg.N k ^ (-s) := by
    calc
      _ ≤ (cfg.K k * cfg.N k ^ (-(3 * s) / 2)) *
          (cfg.K k * cfg.N k ^ (s / 2)) := by
        rw [div_eq_mul_inv]
        exact mul_le_mul hd.1 hc.2 (by positivity) (by positivity)
      _ = _ := by
        rw [show -s = -(3 * s) / 2 + s / 2 by ring, Real.rpow_add hN]
        ring
  have hr₂ : (cfg.timeLength k s * cfg.N k ^ (-(200 * s))) / cfg.timeLength k (3 * s) ≤
      cfg.K k ^ 2 * cfg.N k ^ (-(199 * s)) := by
    calc
      _ ≤ (cfg.K k * cfg.N k ^ (-s / 2) * cfg.N k ^ (-(200 * s))) *
          (cfg.K k * cfg.N k ^ ((3 * s) / 2)) := by
        rw [div_eq_mul_inv]
        gcongr
        · exact hc.1
        · exact hd.2
      _ = _ := by
        have he : -(199 * s) = -s / 2 + -(200 * s) + (3 * s) / 2 := by ring
        rw [he, Real.rpow_add hN, Real.rpow_add hN]
        ring
  have hsix : cfg.K k ^ 2 ≤ cfg.K k ^ 6 := pow_le_pow_right₀ (h.subpower.1 k) (by norm_num)
  have hres : 2 * cfg.K k * cfg.N k ^ (-(3 * s)) / cfg.timeLength k (3 * s) ≤
      2 * cfg.K k ^ 6 * cfg.N k ^ (-(3 * s) / 2) := by
    calc
      _ ≤ 2 * cfg.K k * cfg.N k ^ (-(3 * s)) *
          (cfg.K k * cfg.N k ^ ((3 * s) / 2)) := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hd.2 (by positivity)
      _ = 2 * cfg.K k ^ 2 * cfg.N k ^ (-(3 * s) / 2) := by
        rw [show -(3 * s) / 2 = -(3 * s) + (3 * s) / 2 by ring, Real.rpow_add hN]
        ring
      _ ≤ _ := by gcongr
  have hvar : 24 * cfg.K k ^ 5 * cfg.timeLength k (3 * s) ≤
      24 * cfg.K k ^ 6 * cfg.N k ^ (-(3 * s) / 2) := by
    exact (mul_le_mul_of_nonneg_left hd.1 (by positivity)).trans_eq (by ring)
  refine ⟨(div_le_one hHd).mp (hr₂.trans hk₂.le),
    (div_le_one hHs).mp (hr₁.trans hk₁.le), ?_⟩
  nlinarith only [hres, hvar, hk₃.le, hk₄.le]

/-- All losses used in history pruning are chosen before the sample. -/
theorem Valid.eventually_pruning_losses (h : cfg.Valid) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k in atTop,
      32 * cfg.K k ^ 5 ≤ cfg.N k ^ η ∧ 2 * cfg.K k ≤ cfg.N k ^ η ∧
      27648 * cfg.K k ^ 11 / cfg.N k ^ (-(η / 10)) ≤ cfg.N k ^ η ∧
      36 * cfg.K k ^ 4 * cfg.N k ^ (-(η / 10)) + cfg.N k ^ (-η) < cfg.N k ^ (-(η / 100)) := by
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [h.scale k]
  have hb := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit h.subpower.1 h.subpower.2 5 hη (show (0 : ℝ) ≤ 32 by norm_num)
  have hc := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit h.subpower.1 h.subpower.2 1 hη (show (0 : ℝ) ≤ 2 by norm_num)
  have hd := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit h.subpower.1 h.subpower.2 11
    (show η / 10 < η by linarith) (show (0 : ℝ) ≤ 27648 by norm_num)
  have he := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit h.subpower.1 h.subpower.2 4
    (show -(η / 10) < -(η / 100) by linarith) (show (0 : ℝ) ≤ 108 by norm_num)
  have hf := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    h.scale_limit (show -η < -(η / 100) by linarith) (3 : ℝ)
  filter_upwards [hb, hc, hd, he, hf] with k hb hc hd he hf
  simp only [Real.rpow_zero, mul_one, pow_one] at hb hc
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  refine ⟨hb.le, hc.le, ?_, ?_⟩
  · simpa only [Real.rpow_neg hN.le, div_inv_eq_mul] using hd.le
  · nlinarith only [he, hf, Real.rpow_pos_of_pos hN (-(η / 100))]

end Data
end
end Submission.Obl.k4_critical_conditional_row_preparation
