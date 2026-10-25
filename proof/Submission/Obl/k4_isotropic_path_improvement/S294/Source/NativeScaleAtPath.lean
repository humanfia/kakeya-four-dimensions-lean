-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeScaleAtPath, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeScaleFactory
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeClockAtSample
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeMeshFit

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set Filter MeasureTheory
open Parent.Qualification.Jets2
open Parent.ParentSource.Native
open Submission.Lib.K4ContinuousKakeya

noncomputable section

/-- The native scalar factory at the actual child of a valid path.
Its common tail precedes every path, sample, graph and current source. -/
theorem eventually_native_scale_data_at_path
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop) (q : NativeScaleDesign)
    {L gain delta : ℝ} {m : ℕ} {s : ℕ → ℝ}
    (hL : 0 < L) (hgain : 0 < gain) (hGain : q.gainL=gain*L)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ gain/100)
    (hdeltaPower : 4*delta*L ≤ q.coefficient/2)
    (hgm : 8 ≤ gain*(m:ℝ)) (hs : ∀ l, s l=((l:ℝ)+1)/m)
    (Cmk : ℝ) (hCmk : 0 ≤ Cmk) (hMK : FiniteMK 3 Cmk) :
    ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ 1 ∧ ∀ᶠ k in atTop,
      ∀ (W : ℕ) (p : PathData W) (omega : Fin W → ℝ)
        (nu : Fin W → Measure (ℕ × (Fin 6 → ℝ)))
        (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : Fin W → ℝ)
        (f : ℝ → ℝ) (Mp Dp : ℕ) (sigmaPath : ℝ),
      p.Valid (N k) L omega nu E B f q.kappa1 m s delta Mp Dp sigmaPath →
      ∀ (i : ℕ), i+childOffset q.kappa1 q.Ep q.precision gain m < m →
      ∀ (nmesh steps : ℕ) (Kcensus stripWidth Kg : ℝ),
      1 ≤ Kg →
      80*Kg^7*Submission.Lib.K4DyadicRowScales.mesh nmesh^((1-q.dimension)/24) ≤
        (N k)^(-q.target) →
      1 ≤ Kcensus → Kcensus ≤ (N k)^(q.coefficient/1000) →
      Kcensus^(100:ℕ) ≤ (2:ℝ)^steps → (2:ℝ)^steps ≤ (N k)^(q.coefficient/5) →
      (N k)^(-q.coefficient) ≤ stripWidth →
      Nonempty (NativeScaleData q (N k) sigma
        (p.T (i+childOffset q.kappa1 q.Ep q.precision gain m)-p.T i)
        (3*nmesh) steps Kcensus stripWidth
        (thetaOf q.Ep q.precision q.loss gain (N k) L (p.r i)
          (p.r (i+childOffset q.kappa1 q.Ep q.precision gain m)) (p.T i)
          (p.T (i+childOffset q.kappa1 q.Ep q.precision gain m)))) := by
  have v := native_scale_design_bounds q
  obtain ⟨sigma,hSigma,hSigma1,hFactory⟩ := eventually_native_scale_data N hN q Cmk hCmk hMK
  have hLarge := ((tendsto_rpow_atTop q.gainL_pos).comp hN).eventually_ge_atTop 2
  have hHalf := ((tendsto_rpow_atTop (by linarith only [v.coefficient_pos] : 0 < q.coefficient/2)).comp hN).eventually_ge_atTop 2
  refine ⟨sigma,hSigma,hSigma1,?_⟩
  filter_upwards [hFactory,hN.eventually_gt_atTop 1,hLarge,hHalf] with k hFactory hNk hTwo hHalf
  intro W p omega nu E B f Mp Dp sigmaPath hp i hib nmesh steps Kcensus stripWidth Kg hKg hfit hKc hKcUpper hStepsLo hStepsHi hWidth
  have hTwo' : 2 ≤ (N k)^(gain*L) := by simpa only [Function.comp_apply,hGain] using hTwo
  obtain ⟨hTlt,hClockLo,hClockHi,hThetaLo,hThetaHi,hClockPower,hDegree⟩ :=
    native_clock_at_path hp hNk hL q.valid.2.2.1 q.valid.2.2.2.1
      q.valid.2.2.2.2.1 q.valid.2.2.2.2.2.1 q.valid.2.2.2.2.2.2
      hgain hdelta0 hdelta hgm hTwo' hs hib
  have hX : 1 ≤ ((q.Ep:ℝ)+1)*q.precision+3 := by
    have hEp : (1:ℝ) ≤ (q.Ep:ℝ)+1 := by have := Nat.cast_nonneg (α:=ℝ) q.Ep; linarith
    have hh := one_le_mul_of_one_le_of_one_le hEp q.valid.2.2.2.2.1
    linarith only [hh]
  have hClockLo' : q.gainL ≤ nativeClockExponent (N k)
      (p.T (i+childOffset q.kappa1 q.Ep q.precision gain m)-p.T i) := by
    rw [hGain]
    exact (le_mul_of_one_le_left (mul_pos hgain hL).le hX).trans hClockLo
  have hFloor : q.thetaFloor=3*(((q.Ep:ℝ)+1)*q.precision+3)*(gain*L)/q.kappa1 := by
    unfold NativeScaleDesign.thetaFloor NativeDesign.thetaFloorCoeff
    rw [hGain]
    ring
  have hThetaUpper := native_theta_ceiling_margin hNk hHalf hThetaHi
  have hThetaUpper' : thetaOf q.Ep q.precision q.loss gain (N k) L (p.r i)
      (p.r (i+childOffset q.kappa1 q.Ep q.precision gain m)) (p.T i)
      (p.T (i+childOffset q.kappa1 q.Ep q.precision gain m)) ≤ (N k)^q.coefficient := by
    apply hThetaUpper.trans
    exact Real.rpow_le_rpow_of_exponent_le hNk.le (by linarith only [hdeltaPower])
  apply hFactory _ _ _ Kcensus stripWidth _ (Nat.sub_pos_of_lt hTlt) hClockLo'
    (by simpa only [hGain] using hClockHi)
    (native_dyadic_width_le_fit nmesh hKg q.valid.1 hfit)
    hKc hKcUpper hStepsLo hStepsHi hWidth
    (by simpa only [hFloor] using hThetaLo) hThetaUpper'
  simpa only [NativeScaleDesign.degree,hFloor,neg_mul] using hClockPower

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
