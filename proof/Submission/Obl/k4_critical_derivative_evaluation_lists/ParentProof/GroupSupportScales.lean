/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, GroupSupportScales.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.NativeGroupSupport
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- All geometric and mass inputs to group support, in the frozen original
model, at one fixed sufficiently fine original mesh. -/
structure GroupSupportInputs (cfg : Data α) (k : ℕ) (s r : ℝ) : Prop where
  level : cfg.AssignmentLevel k s
  floors : cfg.FullLabelMassFloors k s
  caps : ∀ (q : Fin 3 → ℤ) (n : ℤ),
    cfg.μ k {y | baseGridCode (cfg.N k ^ (-r))
      ![y.2, (cfg.x k y.1 y.2) 1, (cfg.x k y.1 y.2) 2] = q ∧
      ⌊(cfg.x k y.1 y.2) 3⌋ = n} ≤ ENNReal.ofReal (cfg.K k * (cfg.N k ^ (-r)) ^ 3)
  scalar_time : cfg.N k ^ (-s) ≤ cfg.timeLength k s
  mesh_square : cfg.N k ^ (-r) ≤ cfg.timeLength k s ^ 2
  mesh_one : 3 * cfg.N k ^ (-r) ≤ 1

/-- The original frozen model supplies every support-count input on one
eventual set; the fine exponent is fixed before the sample index. -/
theorem Valid.eventually_group_support_inputs (h : cfg.Valid)
    (s : ℝ) (hs : 0 < s) (hsU : s ≤ cfg.U) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ k in atTop, cfg.GroupSupportInputs k s r := by
  let r := 2 * (s + 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hNone : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [h.scale k]
  have hscalar := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hNone h.scale_limit h.subpower.1 h.subpower.2 1
    (show -s / 2 < 0 by linarith) (show (0 : ℝ) ≤ 1 by norm_num)
  have hsquare := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hNone h.scale_limit h.subpower.1 h.subpower.2 2
    (show -r + s < 0 by dsimp [r]; linarith) (show (0 : ℝ) ≤ 1 by norm_num)
  have hmesh := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    h.scale_limit (show -r < 0 by linarith) (3 : ℝ)
  refine ⟨r, hr, ?_⟩
  filter_upwards [h.eventually_assignment_level hs hsU,
    h.eventually_full_label_mass_floor s hs hsU, h.eventually_native_pure_joint_cap r hr,
    hscalar, hsquare, hmesh] with k lev floors caps hk₁ hk₂ hk₃
  have hn : 0 < cfg.N k := by linarith [h.scale k]
  let H := cfg.timeLength k s
  have hH : 0 < H := cfg.timeLength_pos k s
  have hκ : cfg.κ = 1 / 2 := by linarith [h.critical_rate]
  have he : cfg.κ * s = s / 2 := by rw [hκ]; ring
  have hHi : H⁻¹ ≤ cfg.K k * cfg.N k ^ (s / 2) := by
    simpa only [H, timeLength, inv_inv, he] using lev.time_upper
  refine ⟨lev, floors, ?_, ?_, ?_, ?_⟩
  · intro q n
    simpa [Data.x] using caps q n
  · have hdiv : cfg.N k ^ (-s) / H ≤ 1 := by
      calc
        _ = cfg.N k ^ (-s) * H⁻¹ := by ring
        _ ≤ cfg.N k ^ (-s) * (cfg.K k * cfg.N k ^ (s / 2)) :=
          mul_le_mul_of_nonneg_left hHi (Real.rpow_nonneg hn.le _)
        _ = cfg.K k * cfg.N k ^ (-s / 2) := by
          rw [show -s / 2 = -s + s / 2 by ring, Real.rpow_add hn]
          ring
        _ ≤ 1 := by simpa only [pow_one, one_mul, Real.rpow_zero] using hk₁.le
    simpa only [one_mul] using (div_le_iff₀ hH).mp hdiv
  · have hhalf : (cfg.N k ^ (s / 2)) ^ 2 = cfg.N k ^ s := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
      congr 1
      ring
    have hdiv : cfg.N k ^ (-r) / H ^ 2 ≤ 1 := by
      calc
        _ = cfg.N k ^ (-r) * (H⁻¹) ^ 2 := by rw [div_eq_mul_inv, inv_pow]
        _ ≤ cfg.N k ^ (-r) * (cfg.K k * cfg.N k ^ (s / 2)) ^ 2 := by gcongr
        _ = cfg.K k ^ 2 * cfg.N k ^ (-r + s) := by
          rw [mul_pow, hhalf, Real.rpow_add hn]
          ring
        _ ≤ 1 := by simpa only [one_mul, Real.rpow_zero] using hk₂.le
    simpa only [one_mul] using (div_le_iff₀ (sq_pos_of_pos hH)).mp hdiv
  · simpa only [Real.rpow_zero] using hk₃.le

/-- The numerical constants of the full-witness support count are subpower
losses, uniformly before any choice of a group or retained measure. -/
theorem Valid.eventually_group_support_cost (h : cfg.Valid) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k in atTop, 33397665693696 * cfg.K k * (16 * cfg.K k ^ 5) ^ 9 ≤ cfg.N k ^ η := by
  have hh := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    (fun k => by linarith [h.scale k] : ∀ k, 1 ≤ cfg.N k)
    h.scale_limit h.subpower.1 h.subpower.2 46 hη
    (show (0 : ℝ) ≤ 33397665693696 * 16 ^ 9 by norm_num)
  filter_upwards [hh] with k hk
  have heq : 33397665693696 * cfg.K k * (16 * cfg.K k ^ 5) ^ 9 =
      (33397665693696 * 16 ^ 9) * cfg.K k ^ 46 := by ring
  rw [heq]
  simpa only [Real.rpow_zero, mul_one] using hk.le

end Data

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
