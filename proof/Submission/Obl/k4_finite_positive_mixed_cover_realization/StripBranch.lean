import Submission.Obl.k4_finite_positive_mixed_cover_realization.Branches
import Submission.Obl.k4_finite_positive_mixed_cover_realization.DeeperStrips
import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripOutput
import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripRetention
import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripAngularMass
import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripParameters

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory Set Filter Submission.Lib.K4XInterface

set_option maxHeartbeats 2000000 in
/-- Every positive-narrowness strip cover yields a strict width improvement,
uniformly in the smaller input tolerances and before choosing a sample. -/
theorem stripBranch : BranchStatement false := by
  classical
  intro _hMatch d₁ κ₁ ℓ S η _hd₁ _hd₁1 hκ₁ hκ₁1 hℓ hS _hS1 hη
  let b := min (1 / 4) (min (ℓ / 8) η)
  have hb : 0 < b := lt_min (by norm_num) (lt_min (by positivity) hη)
  have hb4 : b ≤ 1 / 4 := min_le_left _ _
  have hbℓ : 8 * b ≤ ℓ := by
    have he : b ≤ ℓ / 8 := (min_le_right _ _).trans (min_le_left _ _)
    linarith only [he]
  have hbη : b ≤ η := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨b / 128, by positivity, ?_⟩
  intro α hα hαb
  refine ⟨min (b / 128) (S * b / 128), lt_min (by positivity) (by positivity), ?_⟩
  intro ρ hρ hρmax hρ4 _hdρ m s gain δ₀ hs hgain hgain1 hδ₀ hδρ
    N K L d W ω ν E P B f g G hprob _hlin Mp Dp Mg Dg
  have hρb : ρ ≤ b / 128 := hρmax.trans (min_le_left _ _)
  have hρS : ρ ≤ S * b / 128 := hρmax.trans (min_le_right _ _)
  have hρ16 : ρ ≤ 1 / 16 := by linarith only [hρb, hb4]
  have hρℓ : 16 * ρ ≤ ℓ := by linarith only [hρb, hbℓ, hb.le]
  have hL : 0 < L := hprob.2.2.2.1
  let Mold : ℕ := Mp + Mg + ⌈2 * L⌉₊ + 4
  let Mr : ℕ := ⌈L⌉₊ + 1
  refine ⟨(2 * Mold + Mr + 8) + (Mg + Mr + 4), max Dp (max Dg 1), ?_⟩
  intro τ hτ
  let ζ := min 1 (min (τ / 8) (min (b * gain * L / 4096) (S * b * gain * L / 4096)))
  have hζ : 0 < ζ := lt_min one_pos (lt_min (by positivity)
    (lt_min (by positivity) (by positivity)))
  have hζ1 : ζ ≤ 1 := min_le_left _ _
  have hζτ : 8 * ζ ≤ τ := by
    have he : ζ ≤ τ / 8 := (min_le_right _ _).trans (min_le_left _ _)
    linarith only [he]
  have hζb : 4096 * ζ ≤ b * gain * L := by
    have he : ζ ≤ b * gain * L / 4096 :=
      ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
    linarith only [he]
  have hζS : 4096 * ζ ≤ S * b * gain * L := by
    have he : ζ ≤ S * b * gain * L / 4096 :=
      ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
    linarith only [he]
  obtain ⟨c₀, hc₀, htails⟩ := prob_strip_density_tails hprob hgain hb hbη hζ
    (ρ := ρ)
  let ε₀ := min ζ (c₀ / 16)
  have hε₀ : 0 < ε₀ := lt_min hζ (by positivity)
  have hεζ : ε₀ ≤ ζ := min_le_left _ _
  have hεc : 16 * ε₀ ≤ c₀ := by
    have := min_le_right ζ (c₀ / 16)
    change ε₀ ≤ c₀ / 16 at this
    linarith only [this]
  have hlarge : ∀ᶠ k in atTop, (2048 : ℝ) ≤ N k ^ ε₀ :=
    ((tendsto_rpow_atTop hε₀).comp hprob.2.1).eventually_ge_atTop _
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (hlarge.and htails)
  refine ⟨ε₀, ζ, hε₀, hεζ.trans hζ1, hζ, k₀, ?_⟩
  intro k hk ε σ hε hεε₀ _hσ hσζ p hp c hc ht
  obtain ⟨hlargek, htailk⟩ := hk₀ k hk
  have hN2 : 2 ≤ N k := hprob.1 k
  have hN : 1 ≤ N k := by linarith only [hN2]
  have hN0 : 0 < N k := zero_lt_one.trans_le hN
  have hκζ : p.κ ≤ N k ^ ζ := hp.slack_le.trans
    (Real.rpow_le_rpow_of_exponent_le hN hσζ)
  have hκN : p.κ ≤ N k := hκζ.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN hζ1)
  have hconst : 1242 ≤ N k ^ ζ := (show (1242 : ℝ) ≤ 2048 by norm_num).trans
    (hlargek.trans (Real.rpow_le_rpow_of_exponent_le hN hεζ))
  have hh : 0 < c.gain := hgain.trans_le hc.2.1
  have hbgh := mul_le_mul_of_nonneg_left hc.2.1 (mul_nonneg hb.le hL.le)
  have hSbgh := mul_le_mul_of_nonneg_left hc.2.1 (mul_nonneg (mul_nonneg hS.le hb.le) hL.le)
  have hmargin : 64 * ζ ≤ b * c.gain * L := by nlinarith only [hζb, hbgh, hζ.le]
  have hmarginS : 128 * ζ ≤ S * b * c.gain * L := by nlinarith only [hζS, hSbgh, hζ.le]
  have hεζ' : ε ≤ ζ := hεε₀.trans hεζ
  have hgeom := strip_power_estimates hN hp.one_le_slack hκζ hconst hζ.le
    hb.le hb4 hbℓ (mul_nonneg hh.le hL.le) hρ16 hεζ' hmargin
  obtain ⟨j, normal, bias, hij, hjm, hrj, hrjL, hn, hdeep⟩ :=
    hc.deeper_strip_table hp hs hN hL hgain hℓ.le hρ.le hρ4 hρℓ hδρ
  let Good := stripGood (N k) L (f L) S b c.gain ζ (B k) (fun w => g k w L)
    (fun w => G k w (b * c.gain * L / 4))
  have hbad : (∑ w, ENNReal.ofReal (ω k w) * (((ν k w).prod volume).restrict (E k w))
      (Good w)ᶜ) ≤ ENNReal.ofReal (2 * N k ^ (-16 * ε₀)) := by
    apply (htailk c.gain (mem_stripGainMenu hgain hρ hc.2.1 hc.2.2.1 hc.2.2.2.1)).trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hεc])) (by norm_num)
  have hangular : (∑ w, ENNReal.ofReal (ω k w) * ∑ bd : Fin c.n × Fin p.C,
      (((ν k w).prod volume).restrict (E k w))
        (c.misalignedPair normal bias (N k ^ (-b * c.gain * L / 8)) j w bd ∩ Good w)) ≤
      ENNReal.ofReal (N k ^ (-16 * ε₀)) := by
    apply (hc.strip_angular_mass hprob ht hp hrj.le hrjL normal bias hn hdeep hb hbη hh
      hgeom hκζ hconst hζ.le hρS hεζ' hmarginS).trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow_of_exponent_le hN
    linarith only [hmarginS, hεζ]
  have hmassnum := strip_mass_numerics hN hε₀ hεε₀
    (show 4 * ε₀ ≤ τ by linarith only [hζτ, hεζ, hζ.le]) ((show (6 : ℝ) ≤ 2048 by norm_num).trans hlargek)
  have hretained := hc.aligned_mass_floor (gap := N k ^ (-b * c.gain * L / 8)) hp
    normal bias hij.le hjm Good hN0.le hbad hangular (by positivity) (by positivity) hmassnum.1
  have hmass : ENNReal.ofReal (N k ^ (-τ)) ≤ ∑ a : Fin c.n,
      ENNReal.ofReal (ω k (p.world (c.old a))) * ((ν k (p.world (c.old a))).prod volume)
        (c.alignedWitness normal bias (N k ^ (-b * c.gain * L / 8)) j a) :=
    (ENNReal.ofReal_le_ofReal hmassnum.2).trans hretained
  have hwidth : 0 < N k ^ (-b * c.gain * L / 8) := Real.rpow_pos_of_pos hN0 _
  have hbhL : 0 ≤ b * c.gain * L := by positivity
  have hwidth1 : N k ^ (-b * c.gain * L / 8) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hN (show -b * c.gain * L / 8 ≤ 0 by linarith only [hbhL])
  have hfit : N k ^ (4 * ρ * c.gain * L + 4 * ε) * N k ^ (-c.gain * L) ≤
      N k ^ (-b * c.gain * L / 8) := hgeom.candidate.trans
    (Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hbhL]))
  have hinv : (N k ^ (-b * c.gain * L / 8))⁻¹ ≤ N k ^ Mr :=
    strip_reciprocal_width hN hb.le hb4 hh.le hc.2.2.1 hL.le
  have hδ1 : δ₀ ≤ 1 := by
    have hprod := mul_le_mul hρ16 hgain1 hgain.le (by norm_num : (0 : ℝ) ≤ 1 / 16)
    nlinarith only [hprod, hδρ]
  have hT : (2 : ℝ) ^ p.T c.level ≤ N k ^ Mold :=
    (hp.strip_time_budget hs hN hL.le hκ₁.le hκ₁1 hδ1 hc.1).trans
      (pow_le_pow_right₀ hN (by dsimp [Mold]; omega))
  have hslack : 1242 * p.κ ^ 2 ≤ N k ^ τ :=
    (strip_small_factor hN0 (by linarith only [hp.one_le_slack]) hκζ hconst le_rfl).trans
      (Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hζτ, hζ.le]))
  have hdepth : p.r c.level + (α * gain) * L ≤ L := by
    have hα1 : α ≤ 1 := by linarith only [hαb, hb4]
    have hag : α * gain ≤ c.gain := by nlinarith only [hα1, hgain.le, hc.2.1]
    have haL := mul_le_mul_of_nonneg_right hag hL.le
    have hroom := hc.2.2.2.2.1
    nlinarith only [haL, hroom, mul_pos hh hL]
  obtain ⟨Mpr, Dpr, hdata⟩ := hprob.2.2.2.2.2.2.2.2.1
  exact hc.strip_output ht hp hN2 (by dsimp [Mold]; omega) (by dsimp [Mold]; omega)
    hκN hT (fun w => ((hdata k).2.2.2.1 w).2.1.le) hwidth hwidth1 hinv hfit le_rfl
    hrj.le hrjL normal bias hdepth hgeom.factor
    (strip_saving hb.le hL.le hgain.le hc.2.1 hδρ hρb hαb) hslack hmass

end Submission.Obl.k4_finite_positive_mixed_cover_realization
