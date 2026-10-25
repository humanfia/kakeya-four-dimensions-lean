import Submission.Obl.k4_scalar_guarded_entropic_path.Info.OriginalBlockCounts
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.StageAllowances
import Submission.Obl.k4_scalar_guarded_entropic_path.StageExponents

/-! Simultaneously calibrate every immutable original chart in the
actual stage, before the information window is selected. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.StagePath

open Filter PathMeasures
open scoped Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

variable {ctx : CriticalContext} {source : MaximizingFamily ctx} {k : ℕ} {R δ : ℝ}

/-- The original block generations used by point readouts obey the
same calibration as the final stage layers. No row or chart is replaced. -/
theorem eventually_original_geometry_blocks (s : StagePath ctx source k R δ)
    (al : StageAllowances s)
    (pe : PreparationExponents s.layout.scale δ al.v ctx.S₀ ctx.η) :
    ∀ᶠ j in atTop, ∀ (a : Fin (s.layout.targets.length + 1))
      (ℓ : Fin (s.views a).count)
      (Q : (s.views a).ChartAt pe.ε j ℓ),
      ChartGeometry.ofChart Q = (s.views a).geometry j ℓ →
      N s.final j ^ (ctx.κ * (s.views a).depth ℓ) /
          N s.final j ^ (s.layout.scale * δ / 100) ≤
          (2 : ℝ) ^ ((s.views a).geometry j ℓ).generation ∧
        (2 : ℝ) ^ ((s.views a).geometry j ℓ).generation ≤
          N s.final j ^ (s.layout.scale * δ / 100) *
            N s.final j ^ (ctx.κ * (s.views a).depth ℓ) := by
  have hscale := s.layout.scale_pos
  have hδ : 0 < δ := hscale.trans_le s.layout.scale_error
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hkv : al.v ≤ ((k + 1 : ℕ) : ℝ) * al.v := by nlinarith only [hk, al.v_pos]
  have hεloss : pe.ε < ((k + 1 : ℕ) : ℝ) * al.v := by
    linarith only [pe.ε_small, al.v_pos, hkv]
  have hloss := (power_allowance_loss_tendsto (N s.final) s.final_exact.1.2.1 al.v
    (k + 1)).eventually (le_mem_nhds hεloss)
  have hβ : s.layout.scale * δ / 10000 + pe.ε ≤ s.layout.scale * δ / 100 := by
    have hv := al.power_budget
    have hp : 0 < s.layout.scale * δ := by positivity
    linarith only [hv, hkv, pe.ε_small, hp]
  have hgain : s.layout.scale * δ / 1000 ≤ s.layout.scale * δ / 100 := by
    have hp : 0 < s.layout.scale * δ := by positivity
    linarith only [hp]
  filter_upwards [al.guard, hloss] with j hj hεj
  intro a ℓ Q hQ
  have hN : 1 ≤ N s.final j := (by norm_num : (1 : ℝ) ≤ 2).trans (s.final_exact.1.1 j)
  have hformat : (s.views a).complexity ≤ 2 ^ ((al.M₀ + k + 1) ^ 2) :=
    (al.formats a).1.trans (guard_format_ge al.M₀ k)
  have hguard : ∀ h : ℝ, h ≤ ctx.κ * (s.views a).depth ℓ -
      s.layout.scale * δ / 1000 →
      ¬Chart (s.views a).parent (2 ^ ((al.M₀ + k + 1) ^ 2))
        ((s.views a).depth ℓ) (L (s.views a).parent) h
        (Real.log ((N s.final j ^ al.v * Real.log (N s.final j)) ^ (k + 1)) /
          Real.log (N s.final j)) false ((s.views a).suffixChain.sample j) := by
    intro h hh
    exact hj a _ h ((s.views a).depth_bounds ℓ).1 ((s.views a).depth_bounds ℓ).2 hh
  have htime : (s.views a).time ℓ + pe.ε ≤ ctx.κ * (s.views a).depth ℓ +
      (s.layout.scale * δ / 10000 + pe.ε) := by
    have ht := (abs_le.mp ((s.grids a.val ℓ).2)).2
    change (s.views a).time ℓ - ctx.κ * (s.views a).depth ℓ ≤
      s.layout.scale * δ / 10000 at ht
    linarith only [ht]
  have hbpow : N (s.views a).parent ((s.views a).suffixChain.sample j) ^
      (s.layout.scale * δ / 10000 + pe.ε) ≤ N s.final j ^ (s.layout.scale * δ / 100) := by
    rw [s.views_resolution]
    exact Real.rpow_le_rpow_of_exponent_le hN hβ
  have hgpow : N (s.views a).parent ((s.views a).suffixChain.sample j) ^
      (s.layout.scale * δ / 1000) ≤ N s.final j ^ (s.layout.scale * δ / 100) := by
    rw [s.views_resolution]
    exact Real.rpow_le_rpow_of_exponent_le hN hgain
  have hb := (s.views a).original_geometry_block_bounds j ℓ Q hQ hformat hεj hguard
    htime hbpow hgpow
  simpa only [s.views_resolution] using hb

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.StagePath
