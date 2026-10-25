import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.StageObservations
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.StageRootView
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.StageCoreBudgets
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.WindowVelocity
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.GeometryWidths

/-! One original master velocity record has bounded logarithmic cost;
every actual candidate world has only four compatible local velocity bins. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.StagePath

open MeasureTheory Set Filter PathMeasures
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

variable {ctx : CriticalContext} {source : MaximizingFamily ctx} {k : ℕ} {R δ : ℝ}

theorem root_widths_on_core (s : StagePath ctx source k R δ) {v : ℝ}
    (pe : PreparationExponents s.layout.scale δ v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent) (j : ℕ) (H : ℝ)
    (hcore : PreparedViews.FlooredCoreProperties s.views (fun _ => pe.ε) (fun _ => pe.u)
      (s.densityTests base) pe.γ j (s.coreSet pe base j))
    (hH : 2 * N s.final j ^ (pe.ε + pe.u) ≤ H) :
    ∀ᵐ z ∂s.commonMeasure pe base j, ∀ ℓ : Fin s.layout.targets.length,
      (H * (2 : ℝ) ^ (s.path.rootGeometry s.outer s.certs j ℓ).generation)⁻¹ ≤
        (s.path.rootGeometry s.outer s.certs j ℓ).width (s.path.rootRow s.outer s.certs j ℓ z.1) := by
  have hprep : ∀ᵐ z ∂s.commonMeasure pe base j,
      z ∈ PreparedViews.core s.views (fun _ => pe.ε) (fun _ => pe.u) (s.densityTests base) j :=
    (Measure.absolutelyContinuous_of_le (s.core_restrict_le_prepared pe base j)).ae_le
      (ae_restrict_mem (PreparedViews.measurableSet_core _ _ _ _ _))
  have hwide : ∀ᵐ z ∂s.commonMeasure pe base j,
      ∀ (ℓ : Fin (s.views s.rootIndex).count)
        (d : Fin ((s.views s.rootIndex).geometry j ℓ).count),
        ((s.views s.rootIndex).geometry j ℓ).world d = ((s.views s.rootIndex).suffixChain.pullback j z).1 →
        ((s.views s.rootIndex).suffixChain.pullback j z).2 ∈
          ((s.views s.rootIndex).geometry j ℓ).selected d →
        (H * (2 : ℝ) ^ ((s.views s.rootIndex).geometry j ℓ).generation)⁻¹ ≤
          ((s.views s.rootIndex).geometry j ℓ).width d := by
    filter_upwards [hprep] with z hz ℓ d hw hs
    obtain ⟨Q, hchoice, hgeom, _⟩ := hcore.2.2.2.1 s.rootIndex ℓ
    obtain ⟨Λ, hcd⟩ := ChartGeometry.exists_chartData Q ((s.views s.rootIndex).geometry j ℓ) hgeom
    exact PreparedViews.fixed_row_width s.views (fun _ => pe.ε) (fun _ => pe.u)
      (s.densityTests base) j s.rootIndex ℓ Q hchoice hgeom z hz d hw hs
      ((hcd.2.2.2.2.2.1 d).2.1.le) H
      (by simpa only [s.views_resolution s.rootIndex j] using hH)
  rw [s.views_rootIndex] at hwide
  change ∀ᵐ z ∂s.commonMeasure pe base j, ∀ ℓ : Fin s.layout.targets.length,
    ∀ d : Fin (s.path.rootGeometry s.outer s.certs j ℓ).count,
      (s.path.rootGeometry s.outer s.certs j ℓ).world d =
          ((s.path.measuredChain s.outer s.certs).pullback j z).1 →
      ((s.path.measuredChain s.outer s.certs).pullback j z).2 ∈
          (s.path.rootGeometry s.outer s.certs j ℓ).selected d →
      (H * (2 : ℝ) ^ (s.path.rootGeometry s.outer s.certs j ℓ).generation)⁻¹ ≤
          (s.path.rootGeometry s.outer s.certs j ℓ).width d at hwide
  have hpath := (s.commonMeasure_ac pe base j).ae_le
    ((s.path.measuredChain s.outer s.certs).pathSet_ae j)
  filter_upwards [hwide, hpath] with z hw hz ℓ
  exact hw ℓ (s.path.rootRow s.outer s.certs j ℓ z.1)
    ((s.path.rootRow_world s.outer s.certs j ℓ z.1).trans
      ((s.path.measuredChain s.outer s.certs).pullback_world j z).symm)
    (s.path.rootRow_selected s.outer s.certs j z hz ℓ)

theorem eventually_master_velocity_bins (s : StagePath ctx source k R δ) {v : ℝ}
    (pe : PreparationExponents s.layout.scale δ v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent) :
    ∀ᶠ j in atTop, ∃ Sv : Finset ℤ,
      Real.log ((max Sv.card 1 : ℕ) : ℝ) ≤ ((s.layout.m : ℝ) + 4) * Real.log (s.tangentN j) ∧
      ∀ᵐ z ∂s.commonMeasure pe base j, s.masterVelocity j z ∈ Sv := by
  let chain := s.path.measuredChain s.outer s.certs
  have hroot : Exact s.root := (source.angular s.outer).1
  have hK : ∀ᶠ j in atTop, K s.root (chain.sample j) ≤ s.tangentN j := by
    filter_upwards [chain.sample_strictMono.tendsto_atTop.eventually
      (hroot.1.2.2.1.2 s.layout.scale s.layout.scale_pos)] with j hj
    have hres : N s.root (chain.sample j) = N s.final j := (chain.resolution j).symm
    rwa [hres] at hj
  filter_upwards [hK, s.tangentN_tendsto.eventually_ge_atTop 7] with j hKj hNj
  have hK0 : 0 ≤ K s.root (chain.sample j) :=
    zero_le_one.trans (hroot.1.2.2.1.1 (chain.sample j))
  obtain ⟨Sv, hcard, hSv⟩ := exists_master_velocity_bins hNj hK0 hKj
    (by positivity : 0 ≤ (s.layout.m : ℝ) + 2)
  refine ⟨Sv, ?_, ?_⟩
  · have hlog := master_velocity_log_bound (by linarith : 0 < s.tangentN j) hcard
    convert hlog using 1 <;> ring
  · have hb := chain.pullback_bounded_ae hroot j (s.commonMeasure pe base j)
      (s.commonMeasure_ac pe base j)
    filter_upwards [hb] with z hz
    apply hSv _
    simpa only [masterVelocity, s.path.velocityAt_zero, chain, root] using hz.2 1

theorem eventually_velocity_ambiguities (s : StagePath ctx source k R δ) (hη : 0 < ctx.η)
    (allow : StageAllowances s)
    (pe : PreparationExponents s.layout.scale δ allow.v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent) :
    ∀ᶠ j in atTop, ∀ a : Fin s.layout.L, ∀ g : Fin (s.windowWorlds j a.val), ∀ z₀ : ℤ,
      ∃ S : Finset ℤ, S.card ≤ 4 ∧ ∀ᵐ z ∂s.commonMeasure pe base j,
        s.windowWorld j a.val z.1 = g → s.masterVelocity j z = z₀ →
        Info.canonZ s.layout.m (Info.canonM (s.tangentN j) (s.graphK j) s.layout.m)
          (Info.canonX (s.tangentN j) s.layout.m
            (Info.canonM (s.tangentN j) (s.graphK j) s.layout.m) (s.windowMap j a.val z).2) ∈ S := by
  have hscale := s.layout.scale_pos
  have hK : ∀ᶠ j in atTop, ∀ a : s.ViewIndex,
      K (s.views a).parent ((s.views a).suffixChain.sample j) ≤ s.graphK j := by
    apply Filter.eventually_all.2
    intro a
    exact s.view_K_subpower a (s.layout.scale / 1000) (by positivity)
  have htwo := ((tendsto_rpow_atTop (sub_pos.mpr pe.width_gap)).comp
    s.final_exact.1.2.1).eventually_ge_atTop 2
  filter_upwards [s.eventually_core_properties hη pe base, hK, htwo] with j hcore hKj htwoj a g z₀
  have hN0 : 0 < N s.final j := by linarith [s.final_exact.1.1 j]
  have hN1 : 1 ≤ N s.final j := by linarith [s.final_exact.1.1 j]
  have hNren : 0 < s.tangentN j := zero_lt_one.trans_le (s.tangentN_ge_one j)
  have hH : 0 < N s.final j ^ allow.v := Real.rpow_pos_of_pos hN0 _
  have hwidth : 2 * N s.final j ^ (pe.ε + pe.u) ≤ N s.final j ^ allow.v := by
    calc
      _ ≤ N s.final j ^ (allow.v - (pe.ε + pe.u)) * N s.final j ^ (pe.ε + pe.u) :=
        mul_le_mul_of_nonneg_right htwoj (Real.rpow_nonneg hN0.le _)
      _ = _ := by rw [← Real.rpow_add hN0]; congr 1; ring
  have hrootWidths := s.root_widths_on_core pe base j (N s.final j ^ allow.v) hcore hwidth
  have hHren : N s.final j ^ allow.v ≤ s.tangentN j :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [allow.v_scale])
  have hresolution : N s.final j ^ allow.v * (s.tangentN j) ^ (-((s.layout.m : ℝ) + 2)) ≤
      (s.tangentN j) ^ (-(s.layout.m : ℝ)) := by
    calc
      _ ≤ s.tangentN j * (s.tangentN j) ^ (-((s.layout.m : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_right hHren (by positivity)
      _ = (s.tangentN j) ^ (1 - ((s.layout.m : ℝ) + 2)) := by
        rw [Real.rpow_sub hNren, Real.rpow_one, Real.rpow_neg hNren.le]
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (s.tangentN_ge_one j) (by linarith)
  have hbound := s.window_bounded_ae pe base j a (hKj (s.candidateIndex a))
  have hdecode : ∀ᵐ z ∂s.commonMeasure pe base j,
      Info.canonZ s.layout.m (Info.canonM (s.tangentN j) (s.graphK j) s.layout.m)
        (Info.canonX (s.tangentN j) s.layout.m
          (Info.canonM (s.tangentN j) (s.graphK j) s.layout.m) (s.windowMap j a.val z).2) =
      velocityBin (s.tangentN j) (s.layout.m : ℝ) ((s.windowMap j a.val z).2.1.2 1) := by
    filter_upwards [hbound] with z hz
    exact Info.canonZ_canonX (Info.gridTuple_mem_boxSet (s.tangentN_ge_one j) (s.graphK_ge_one j)
      s.layout.m_one hz.1 hz.2)
  let ℓ : Fin s.layout.targets.length := ⟨a.val, by rw [s.layout.targets_length]; have := a.isLt; omega⟩
  have hout := s.path.exists_four_canonical_velocity_bins s.outer s.certs s.laws
    (.nil _ (source.angular s.outer).1) j ℓ (s.commonMeasure pe base j) hNren hH s.layout.m
    (Info.canonM (s.tangentN j) (s.graphK j) s.layout.m) hresolution
    (hrootWidths.mono fun z hz => hz ℓ) hdecode g z₀
  simpa only [masterVelocity, windowWorld, windowMap, windowWorlds, view, root, final, CommonState, ℓ] using hout

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.StagePath
