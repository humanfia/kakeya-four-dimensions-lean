-- Part of an offer for o106 assembled by x0678 (o064). Adapted from this LOT tree, o064's
-- repository, origin/x0447 at f61522e4 (x0447's file Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/WeakDiscoveryTools.lean);
-- only the namespace changed. See that file for the sources it in turn adapts.
import Submission.Obl.k4_isotropic_path_improvement.Repair.UniformPathRestriction
import Submission.Obl.k4_isotropic_path_improvement.Repair.WeakWidthBridge

/-! Shared grid and width tools for the two uniform discovery reductions. -/

namespace Submission.Obl.k4_isotropic_path_improvement.Repair.WeakUniformDiscoveryRepair

open MeasureTheory WeakWidthBridge UniformGridRefinement
open Submission.Obl.k4_quadratic_finite_greedy_cover

noncomputable def uniformGrid (m i : ℕ) : ℝ := ((i : ℝ) + 1) / (m : ℝ)

theorem uniform_grid_spec {m : ℕ} (hm : 0 < m) :
    (0 < m ∧ 0 < uniformGrid m 0 ∧
      (∀ i, i + 1 < m → uniformGrid m i < uniformGrid m (i + 1)) ∧
      uniformGrid m (m - 1) = 1) := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  refine ⟨hm, by dsimp [uniformGrid]; positivity, ?_, ?_⟩
  · intro i hi
    apply (div_lt_div_iff_of_pos_right hmR).mpr
    push_cast
    linarith
  · have hn : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel hm
    rw [uniformGrid, hn, div_self hmR.ne']

theorem uniform_grid_gap (m i : ℕ) :
    uniformGrid m (i + 1) - uniformGrid m i = 1 / (m : ℝ) := by
  dsimp [uniformGrid]
  push_cast
  ring

theorem width_weaken_gain
    {Nk L gain Δ τ : ℝ} {W m Mi Di : ℕ} {ω : Fin W → ℝ} {ν : Fin W → Measure Ln}
    {E : Fin W → Set Ev} {B : Fin W → ℝ} {r nw : ℕ → ℝ} {T : ℕ → ℕ}
    (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hB : ∀ w, 0 ≤ B w) (hΔ : Δ ≤ gain)
    (hw : width Nk L W ω ν E B m r T nw gain Mi Di τ) :
    width Nk L W ω ν E B m r T nw Δ Mi Di τ := by
  obtain ⟨i, hi, hroom, hs⟩ := hw
  refine ⟨i, hi, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right hΔ hL
    linarith
  · refine system_of_original_mass_atlas (α := τ)
      (extra := fun Q : Matrix (Fin 2) (Fin 2) ℝ =>
        |Q.det| * (4 : ℝ) ^ T i ≤ Nk ^ (-(nw i + gain * L)))
      (aux := fun _ _ _ _ known => known)
      (massFloor := ENNReal.ofReal (Nk ^ (-τ)))
      (mass := fun w F => ((ν w).prod volume) F)
      hN le_rfl hB (fun _ _ _ _ _ h => h)
      (fun Q hQ => hQ.trans (Real.rpow_le_rpow_of_exponent_le hN ?_))
      (fun _ _ => le_rfl) le_rfl hs
    nlinarith [mul_le_mul_of_nonneg_right hΔ hL]

end Submission.Obl.k4_isotropic_path_improvement.Repair.WeakUniformDiscoveryRepair
