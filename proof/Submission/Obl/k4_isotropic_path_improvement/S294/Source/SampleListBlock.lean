-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleListBlock, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.ListLane
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeListGeometryRate

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData)

noncomputable section

/-- All literal list fields of one sample from the native Lipschitz
bounds and the actual census geometry power. The polynomial, source,
clock-room and fixed-constant estimates are discharged internally. -/
theorem sample_list_block
    (tune : Tuning) (hslack : FixedSourcePowers.slack ≤ tune.slack)
    {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    {d₁ precision loss gain τ θ Lp ρ aA q : ℝ} {Ep i nfam : ℕ}
    (hv : NativeDesign.Valid κ₁ d₁ precision loss)
    (hbudget : tune.budget κ₁ d₁ Ep precision loss=NativeDesign.budget κ₁ d₁ Ep precision loss)
    (hs : ∀ j, s j=((j:ℝ)+1)/m) (hm : 0 < m) (hgain : 0 < gain)
    (hgm : 8 ≤ gain*(m:ℝ)) (hδ0 : 0 ≤ δ₀) (hδm : 4*δ₀*(m:ℝ) ≤ κ₁)
    (hδtol : δ₀ ≤ tolOf tune κ₁ d₁ Ep precision loss gain)
    (hib : i+childOffset κ₁ Ep precision gain m < m)
    (hcfam : childOffset κ₁ Ep precision gain m < nfam) (htau : 0 ≤ τ)
    (hθdef : θ=thetaOf Ep precision loss gain (d.N k) d.L (p.r i)
      (p.r (i+childOffset κ₁ Ep precision gain m)) (p.T i) (p.T (i+childOffset κ₁ Ep precision gain m)))
    (haA : 0 < aA) (hq : 0 < q)
    (hLp0 : 0 ≤ Lp) (hLpρ : Lp*ρ ≤ θ/8)
    (hLpClock : Lp*((2:ℝ)^(p.T (i+childOffset κ₁ Ep precision gain m)-p.T i))⁻¹ ≤ 1/8)
    (hLp : Lp ≤ d.N k^(κ₁*(gain*d.L)/8))
    (hKd : 0 ≤ d.K k) (hcore : coreK p τ ≤ d.N k^(3*δ₀*d.L))
    (hconstant : 20000 ≤ d.N k^((NativeDesign.coefficientCoeff κ₁ d₁ Ep precision loss*(gain*d.L))/1000000))
    (h2a : 2 ≤ d.N k^(gain*d.L)) :
    ∃ jmid : Fin nfam,
      (∀ b, p.lev b = i + childOffset κ₁ Ep precision gain m → (i + (jmid : ℕ)) ≤ p.lev b) ∧
      (∀ b, p.lev b = i + childOffset κ₁ Ep precision gain m →
        p.lev b - childOffset κ₁ Ep precision gain m ≤ (i + (jmid : ℕ))) ∧
      0 ≤ p.r ((i + (jmid : ℕ))) ∧ p.r ((i + (jmid : ℕ))) ≤ d.L ∧
      δ (d.N k) (p.r ((i + (jmid : ℕ)))) ≤ δ (d.N k) (p.r i) ∧
      (∀ b, p.lev b = i + childOffset κ₁ Ep precision gain m →
        ((aA / q) * Lp) * ((((2 : ℝ) ^ p.T (p.lev b))⁻¹ /
            ((2 : ℝ) ^ p.T (p.lev (p.par^[childOffset κ₁ Ep precision gain m] b)))⁻¹) * (2 * θ) +
          (2 * (coreK p τ ^ 14 * (coreK p τ ^ 6)⁻¹ * (δ (d.N k) (p.r ((i + (jmid : ℕ)))) /
            δ (d.N k) (p.r (p.lev (p.par^[childOffset κ₁ Ep precision gain m] b))))) +
            ((coreK p τ ^ (3 * FixedSourcePowers.coreRadius + 58 + 7)) ^ FixedSourcePowers.jet *
              (p.κ + coreK p τ ^ 14 * (coreK p τ ^ 6)⁻¹)) *
              (coreK p τ ^ FixedSourcePowers.coreRadius *
                ((1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + (d.K k + 2 * p.κ ^ 2))) *
                ((((2 : ℝ) ^ p.T (p.lev b))⁻¹ /
                  ((2 : ℝ) ^ p.T (p.lev (p.par^[p.lev b - (i + (jmid : ℕ))] b)))⁻¹) *
                    (6 * θ))))) +
          ρ) ≤ (aA / q) * θ) := by
  have hv0 := hv
  obtain ⟨_hd0,_hd1,hκ,hκ1,hprecision,hloss,hloss1⟩ := hv0
  have hN : 1 < d.N k := (by norm_num : (1:ℝ) < 2).trans_le (hd.1 k)
  have hL : 0 < d.L := hd.2.2.2.1
  have hKbounds := Native.native_pre_geometry_envelope_bounds (source:=d.K k) hp.1 hN.le (add_nonneg htau htau)
  have hKpos : 0 < coreK p τ := (by norm_num : (0:ℝ) < 2304).trans_le hKbounds.1
  have hmax : max p.κ (d.K k) ≤ d.N k^(3*δ₀*d.L) := hKbounds.2.2.1.trans hcore
  have hκpow := (le_max_left p.κ (d.K k)).trans hmax
  have hKdpow := (le_max_right p.κ (d.K k)).trans hmax
  have hbudgetList : ((((3*FixedSourcePowers.coreRadius+58+7)*FixedSourcePowers.jet+
      FixedSourcePowers.coreRadius+12:ℕ):ℝ))*(3*δ₀*d.L) ≤ κ₁*(gain*d.L)/64 := by
    have heq : 3*FixedSourcePowers.coreRadius+58+7=3*FixedSourcePowers.coreRadius+65 := by omega
    rw [heq]
    exact native_list_polynomial_rate tune hslack hv hbudget hgain hL hδ0 hδtol
  have h432 := native_list_constant_from_source hv hN.le (mul_pos hgain hL) hconstant
  obtain ⟨hA1,hA2⟩ := list_powers (R:=FixedSourcePowers.coreRadius) (J:=FixedSourcePowers.jet)
    hN hKpos (zero_le_one.trans hp.1) hKd (by positivity : (0:ℝ) ≤ 3*δ₀*d.L)
    (by positivity : (0:ℝ) ≤ κ₁*(gain*d.L)) hLp0 hLp hcore hκpow hKdpow
    (by nlinarith only [mul_nonneg hδ0 hL.le] : 2*δ₀*d.L ≤ 3*δ₀*d.L) hbudgetList h432
  obtain ⟨hroom1,hroom2⟩ := list_room (Ep:=Ep) hL hκ hκ1 hδ0 hδm hprecision hloss.le hloss1
    hgain hm hgm (le_refl (κ₁*(gain*d.L)/4)) (le_refl (κ₁*(gain*d.L)/4))
  exact list_lane hd hp hs hm hκ hκ1 hδ0 hδm hprecision hloss.le hgain hib hcfam htau hθdef haA hq
    hLp0 hLpρ hLpClock (by positivity) (by positivity) hA1 hA2 h2a hroom1 hroom2

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
