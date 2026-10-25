import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.StageAllowances
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.StageCore
import Submission.Obl.k4_scalar_guarded_entropic_path.ViewLayers

/-! The same late common core supplies all original TRUE layer
payloads in every positive candidate parent, before entropy selection. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.StagePath

open MeasureTheory Set Filter PathMeasures
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

variable {ctx : CriticalContext} {source : MaximizingFamily ctx} {k : ℕ} {R δ : ℝ}

theorem eventually_original_layer_payloads (s : StagePath ctx source k R δ) (hη : 0 < ctx.η)
    (allow : StageAllowances s)
    (pe : PreparationExponents s.layout.scale δ allow.v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent)
    (htolerance : ∀ a, (base a).tolerance = pe.τ) :
    ∀ᶠ j in atTop, ∀ a : s.ViewIndex, 0 < a.val →
      ∃ layers : Fin (s.views a).count → Layer (W (s.views a).parent ((s.views a).suffixChain.sample j)),
        ∀ ℓ, (s.views a).OriginalLayerGood j allow.M₀ pe.ε allow.v
          (N s.final j ^ allow.v) (N s.final j ^ (s.layout.scale * δ)) ctx.dstar ctx.κ
          (s.worldLaw pe base j a) ℓ (layers ℓ) := by
  have hscale := s.layout.scale_pos
  have hδ : 0 < δ := hscale.trans_le s.layout.scale_error
  have hn : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hvsmall : allow.v < s.layout.scale * δ / 100 := by
    nlinarith only [allow.power_budget, allow.v_pos, hn]
  have hεbudget : pe.ε ≤ s.layout.scale * δ / 10000 := by
    linarith only [hvsmall, pe.ε_small]
  have hεv : pe.ε ≤ allow.v := by linarith only [pe.ε_small, allow.v_pos]
  have hlimit : pe.ε < ((k + 1 : ℕ) : ℝ) * allow.v := by
    nlinarith only [pe.ε_small, allow.v_pos, hn]
  have hloss := (power_allowance_loss_tendsto (N s.final) s.final_exact.1.2.1 allow.v (k + 1)).eventually
    (le_mem_nhds hlimit)
  have htwo := ((tendsto_rpow_atTop (sub_pos.mpr pe.width_gap)).comp
    s.final_exact.1.2.1).eventually_ge_atTop 2
  have hwidth : ∀ᶠ j in atTop,
      2 * N s.final j ^ (pe.ε + pe.u) ≤ N s.final j ^ allow.v := by
    filter_upwards [htwo] with j hj
    have hN : 0 < N s.final j := by linarith [s.final_exact.1.1 j]
    calc
      _ ≤ N s.final j ^ (allow.v - (pe.ε + pe.u)) * N s.final j ^ (pe.ε + pe.u) :=
        mul_le_mul_of_nonneg_right hj (Real.rpow_nonneg hN.le _)
      _ = _ := by rw [← Real.rpow_add hN]; congr 1; ring
  have hβ : s.layout.scale * δ / 10000 + pe.ε ≤ s.layout.scale * δ := by
    nlinarith only [hεbudget, mul_pos hscale hδ]
  have hgain : s.layout.scale * δ / 1000 ≤ s.layout.scale * δ := by
    nlinarith only [mul_pos hscale hδ]
  have hτ : pe.τ ≤ s.layout.scale * δ := by
    nlinarith only [pe.τ_budget, mul_pos hscale hδ]
  filter_upwards [s.eventually_core_properties hη pe base,
    s.worldLaw_mass_subpower hη pe base allow.v allow.v_pos, allow.guard, hwidth, hloss]
    with j hcore hmass hguard hwidthj hlossj a ha
  classical
  choose P hchoice hgeometry hfloor using hcore.2.2.2.1 a
  have hN1 : 1 ≤ N s.final j := by linarith [s.final_exact.1.1 j]
  apply (s.views a).exists_original_layers j allow.M₀ (2 ^ ((allow.M₀ + k + 1) ^ 2))
    pe.ε allow.v pe.u (N s.final j ^ allow.v) (N s.final j ^ (s.layout.scale * δ))
    ctx.dstar ctx.κ (s.layout.scale * δ / 1000)
    (s.layout.scale * δ / 10000 + pe.ε)
    (Real.log ((N s.final j ^ allow.v * Real.log (N s.final j)) ^ (k + 1)) / Real.log (N s.final j))
    pe.τ P (allow.formats a).1 (guard_format_ge allow.M₀ k) hεv hlossj
    (by simpa only [s.views_resolution a j] using hwidthj)
    (s.worldLaw pe base j a) (s.worldLaw_le pe base j a) _ _
    (by simpa only [s.views_resolution a j] using hmass a) _ (hguard a) _ _ _ _ _
  · intro ℓ g
    have hcover := ((s.views a).chartChoice_spec pe.ε ℓ j (P ℓ) (hchoice ℓ)).2
    exact (s.views a).suffixChain.submeasureWorldLaw_chart_cover j (P ℓ)
      (show (normalizedWorldMixture s.final j).restrict (s.coreSet pe base j) ≤
        normalizedWorldMixture s.final j from Measure.restrict_le_self) hcover g
  · intro ℓ g
    rw [← (s.views a).layerAt_of_choice pe.ε ℓ j (P ℓ) (hchoice ℓ)]
    exact s.core_narrow_null pe base j a ℓ g
  · intro ℓ
    rw [s.views_resolution a j]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    have hp := s.view_absolute_profile (n := a.val) ha
    have hprof : |f (s.views a).parent ((s.views a).depth ℓ) -
        ctx.dstar * (s.views a).depth ℓ| ≤ s.layout.scale * δ / 10000 :=
      hp _ ((s.views a).depth_bounds ℓ).1 ((s.views a).depth_bounds ℓ).2.le
    nlinarith only [hprof, mul_pos hscale hδ]
  · intro ℓ
    have ht := (s.grids a.val ℓ).2
    change |(s.views a).time ℓ - ctx.κ * (s.views a).depth ℓ| ≤ s.layout.scale * δ / 10000 at ht
    have ht' := (abs_le.mp ht).2
    linarith only [ht']
  · rw [s.views_resolution a j]
    exact Real.rpow_le_rpow_of_exponent_le hN1 hβ
  · rw [s.views_resolution a j]
    exact Real.rpow_le_rpow_of_exponent_le hN1 hgain
  · rw [s.views_resolution a j]
    exact Real.rpow_le_rpow_of_exponent_le hN1 hτ
  · intro ℓ g
    have hp := s.core_pure_null pe base j a ((s.views a).depth ℓ)
      ((s.views a).layer_mem_withLayerTests (base a) ℓ) g
    simpa only [htolerance a] using hp

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.StagePath
