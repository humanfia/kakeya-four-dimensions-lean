import Submission.Obl.k4_compatible_pair_frame_preparation.Close
import Submission.Obl.k4_compatible_pair_frame_preparation.BandGeometry

namespace Submission.Obl.k4_compatible_pair_frame_preparation

open MeasureTheory Set
open scoped ENNReal

/-- Native pointwise depth caps give the band estimate for every measurable center. -/
theorem native_band_construction : BandConstruction := by
  intro N W ω ν E P B f g G L d hFD S a e u h ha he M D depths h0 hLmem hdep hcov
    ε₀ k p hκX hX b ρ U F hρ hU hF
  obtain ⟨hN, hNt, hL, hω, hωsum, hν, ⟨Mb, hB⟩, hE, hP, hmap, hd0, hd1, hprof⟩ := hFD
  have hNk : 2 ≤ N k := hN k
  have hNpos : 0 < N k := by linarith
  let hp := p.toPrep_hyp hNk (fun γ => (hB k γ).1)
  letI : ∀ γ : Fin p.toPrep.W, SFinite (ν k γ) := fun γ => by
    letI : IsProbabilityMeasure (ν k γ) := hν k γ
    infer_instance
  let J : ℝ := (100 * frameSlack p.κ) ^ 3 * |(p.toPrep.fQ b).det|
  let mass : ℝ → ENNReal := fun r => ENNReal.ofReal ((2 : ℝ) ^ p.T) ^ 2 *
    ((ν k (p.toPrep.fγ b)).prod (volume.prod volume))
      (p.toPrep.bandPairs (N k) (frameSlack p.κ) b r U F)
  have hκ2 := frameSlack_two p.κ_one
  have hκ0 : 0 ≤ frameSlack p.κ := zero_le_one.trans (frameSlack_one p.κ_one)
  have hGood (r : ℝ) (hr : r ∈ depths) : ∀ γ, ∀ z ∈ p.Good γ,
      g k γ r (obs (B k γ) (δ (N k) r) z) ≤ ENNReal.ofReal (N k ^ (-f r + a)) := by
    intro γ z hz
    exact ((p.hGood γ).2.2 z hz).2.2.2.1 r hr
  have hmono : Monotone mass := by
    intro r r' hrr
    apply mul_le_mul' le_rfl
    apply measure_mono
    intro z hz
    exact ⟨hz.1, hz.2.1, hz.2.2.trans hrr⟩
  have hdepth (r : ℝ) (hr : r ∈ depths) : mass (N k ^ (-r)) ≤
      ENNReal.ofReal (N k ^ (-f r + a) * (2 * N k ^ (-r) / δ (N k) r + 2) * J) * volume U := by
    have hm := hdep r hr
    exact hp.band_depth_le (ν k) (fun γ => g k γ r)
      (fun γ => (hmap k γ r hm.1 hm.2).1) (fun γ => (hmap k γ r hm.1 hm.2).2)
      (Real.rpow_nonneg hNpos.le _) (hGood r hr) hκ2 b
      (Real.rpow_nonneg hNpos.le _) U hU F hF
  have hwindow (r : ℝ) : mass r ≤
      ENNReal.ofReal (N k ^ (-f 0 + a) * (16 * (1 + p.κ ^ 2 / δ (N k) 0)) * J) * volume U := by
    exact hp.band_window_le (ν k) (fun γ => g k γ 0)
      (fun γ => (hmap k γ 0 le_rfl hL.le).1) (fun γ => (hmap k γ 0 le_rfl hL.le).2)
      (Real.rpow_nonneg hNpos.le _) (hGood 0 h0) (P k) (hP k)
      (lt_of_lt_of_le zero_lt_one p.κ_one)
      (fun γ z hz => ⟨((p.hGood γ).2.2 z hz).2.1, ((p.hGood γ).2.2 z hz).2.2.1⟩)
      hκ2 b U hU F
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hb := Band.band_bound_of_profile (by linarith : 1 < N k) hL.le he.le hd0 le_rfl
    p.κ_one hJ f depths h0 hLmem hcov
    (fun r hr => hprof r (hdep r hr).1 (hdep r hr).2) mass hmono hdepth hwindow hρ
  apply hb.trans
  apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hδ : 0 < δ (N k) L := by unfold δ; positivity
  exact mul_le_mul_of_nonneg_right
    (p.band_coefficient_le hNk ha he (fun γ => (hB k γ).1) hκX hX hd1 b)
    (Real.rpow_nonneg (by positivity) _)

/-- A universal constant `100` completes compatible native-pair frame preparation. -/
theorem preparation : FramePreparationStatement :=
  preparation_of_bandConstruction native_band_construction

end Submission.Obl.k4_compatible_pair_frame_preparation
