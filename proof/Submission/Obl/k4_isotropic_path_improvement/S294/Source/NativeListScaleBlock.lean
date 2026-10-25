-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeListScaleBlock, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.ListLane
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeScaleData
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleListBlock

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData)

noncomputable section

/-- All original middle-level list inputs from native scale data and
the actual census geometry power. No list-room premise is an input. -/
theorem native_list_lane_of_scale_data
    (tune : Tuning) (hslack : FixedSourcePowers.slack ≤ tune.slack)
    {design : NativeScaleDesign} {d : ProblemData} (hd : d.Valid)
    {k m : ℕ} {p : PathData (d.W k)} {delta sigmaPath : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      design.kappa1 m s delta Mp Dp sigmaPath)
    (hs : ∀ l, s l=((l:ℝ)+1)/m)
    (hdelta0 : 0 ≤ delta) (hdeltaM : 4*delta*(m:ℝ) ≤ design.kappa1)
    {gain : ℝ} (hgain : 0 < gain) (hGain : design.gainL=gain*d.L)
    (hgm : 8 ≤ gain*(m:ℝ))
    (hbudget : tune.budget design.kappa1 design.dimension design.Ep design.precision design.loss=
      NativeDesign.budget design.kappa1 design.dimension design.Ep design.precision design.loss)
    (hdelta : delta ≤ tolOf tune design.kappa1 design.dimension design.Ep design.precision design.loss gain)
    {i nfam fine steps : ℕ} {sigmaNative Kcensus stripWidth θ τ aA q : ℝ}
    (native : NativeScaleData design (d.N k) sigmaNative
      (p.T (i+childOffset design.kappa1 design.Ep design.precision gain m)-p.T i)
      fine steps Kcensus stripWidth θ)
    (hib : i+childOffset design.kappa1 design.Ep design.precision gain m < m)
    (hcfam : childOffset design.kappa1 design.Ep design.precision gain m < nfam)
    (hτ : 0 ≤ τ)
    (hθdef : θ=thetaOf design.Ep design.precision design.loss gain (d.N k) d.L (p.r i)
      (p.r (i+childOffset design.kappa1 design.Ep design.precision gain m)) (p.T i)
      (p.T (i+childOffset design.kappa1 design.Ep design.precision gain m)))
    (haA : 0 < aA) (hq : 0 < q)
    (hlarge : 20000 ≤ d.N k^(design.coefficient/1000000))
    (hCore : coreK p τ ≤ d.N k^(3*delta*d.L))
    (h2 : 2 ≤ d.N k^(gain*d.L)) :
    ∃ jmid : Fin nfam,
      (∀ b, p.lev b = i + childOffset design.kappa1 design.Ep design.precision gain m → (i + (jmid : ℕ)) ≤ p.lev b) ∧
      (∀ b, p.lev b = i + childOffset design.kappa1 design.Ep design.precision gain m →
        p.lev b - childOffset design.kappa1 design.Ep design.precision gain m ≤ (i + (jmid : ℕ))) ∧
      0 ≤ p.r ((i + (jmid : ℕ))) ∧ p.r ((i + (jmid : ℕ))) ≤ d.L ∧
      δ (d.N k) (p.r ((i + (jmid : ℕ)))) ≤ δ (d.N k) (p.r i) ∧
      (∀ b, p.lev b = i + childOffset design.kappa1 design.Ep design.precision gain m →
        ((aA / q) * native.scales.Lp) * ((((2 : ℝ) ^ p.T (p.lev b))⁻¹ /
            ((2 : ℝ) ^ p.T (p.lev (p.par^[childOffset design.kappa1 design.Ep design.precision gain m] b)))⁻¹) * (2 * θ) +
          (2 * (coreK p τ ^ 14 * (coreK p τ ^ 6)⁻¹ * (δ (d.N k) (p.r ((i + (jmid : ℕ)))) /
            δ (d.N k) (p.r (p.lev (p.par^[childOffset design.kappa1 design.Ep design.precision gain m] b))))) +
            ((coreK p τ ^ (3 * FixedSourcePowers.coreRadius + 58 + 7)) ^ FixedSourcePowers.jet *
              (p.κ + coreK p τ ^ 14 * (coreK p τ ^ 6)⁻¹)) *
              (coreK p τ ^ FixedSourcePowers.coreRadius *
                ((1 + 2 * (p.κ * d.N k ^ (2 * delta * d.L)) * (1 + (d.K k + 2 * p.κ ^ 2))) *
                ((((2 : ℝ) ^ p.T (p.lev b))⁻¹ /
                  ((2 : ℝ) ^ p.T (p.lev (p.par^[p.lev b - (i + (jmid : ℕ))] b)))⁻¹) *
                    (6 * θ))))) +
          native.scales.ρ) ≤ (aA / q) * θ) := by
  have hN : (1:ℝ) < d.N k := lt_of_lt_of_le (by norm_num) (hd.1 k)
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hib
  have hLpPower : native.scales.Lp ≤ d.N k^(design.kappa1*(gain*d.L)/8) := by
    apply native.Lp_bound.trans (Real.rpow_le_rpow_of_exponent_le hN.le ?_)
    simpa only [hGain] using design.mass_half_le_clock
  apply sample_list_block tune hslack hd hp design.valid hbudget hs hm hgain hgm
    hdelta0 hdeltaM hdelta hib hcfam hτ hθdef haA hq native.scales.hLp
    native.lipRho_small native.lipClock_small hLpPower
    (zero_le_one.trans (hd.2.2.1.1 k)) hCore _ h2
  simpa only [NativeScaleDesign.coefficient,hGain] using hlarge

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
