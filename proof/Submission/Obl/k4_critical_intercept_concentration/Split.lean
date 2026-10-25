import Submission.Obl.k4_critical_intercept_concentration.ChildAdapters
import Submission.Obl.k4_critical_intercept_concentration.AsymptoticRestore

namespace Submission.Obl.k4_critical_intercept_concentration

open MeasureTheory Set Filter

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The two substantive children give heavy midpoint bins in the original
residual units. All three losses are chosen before selecting a sample. -/
theorem candidates_of_switching_and_spreading
    (hprep : SwitchingPreparation) (hspread : LocalSpreading)
    (h : cfg.Valid) (hp : cfg.Primitive) : cfg.Candidates := by
  obtain ⟨s, hs, hsU, hse, hs1, hprimitive⟩ := hp
  have hv : 0 < s / 16 := by positivity
  have hgain : s / 16 < cfg.κ * s := by nlinarith [h.critical_rate]
  apply candidates_of_heavy_midpoint_bins h hs hs1 hv hgain (by linarith)
  intro ζ hζ
  obtain ⟨δ, hδ, hδζ, N₀, hN₀, hlocal⟩ :=
    hspread cfg.S (10 * s) (ζ / 4) h.palette_pos (by positivity) (by positivity)
  obtain ⟨η, hη, hηδ, hprepared⟩ :=
    hprep α cfg h s hs hsU hse hs1 δ hδ
  have hηζ : η ≤ ζ := by linarith
  have hlate : ∀ᶠ k in atTop, N₀ ≤ cfg.N k :=
    h.scale_limit.eventually (eventually_ge_atTop N₀)
  apply ((hprimitive η hη).and_eventually (hprepared.and hlate)).mono
  rintro k ⟨⟨i, L, hL₀, hL, hm⟩, hk, hNk⟩
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hN1 : 1 ≤ cfg.N k := by linarith [h.scale k]
  obtain ⟨source, σ, π₀, state, G, F, hsourceM, hsource, hcoeff,
      hlaw, hsupport, hcard, htransport⟩ := hk i L hL₀ hL hm
  let : IsProbabilityMeasure σ := hlaw.1
  obtain ⟨p, hpF⟩ := hsupport.exists
  have hF : 0 < (F.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (show F.Nonempty from ⟨_, hpF⟩)
  have hB : 0 < (F.card : ℝ) * (cfg.N k ^ (-10 * s)) ^ 3 := by positivity
  obtain ⟨j, hj⟩ := hlocal (cfg.N k) hNk α σ π₀
    (cfg.centeredLine k s i) (cfg.centeredVelocity k s i)
    (cfg.midpointBin k s (s / 16) i L) state G hlaw F
    (by simpa only [neg_mul] using hsupport)
  have hj' : ENNReal.ofReal
      (cfg.N k ^ (-cfg.d * (s / 16) - ζ + δ)) ≤
        σ {p | cfg.midpointBin k s (s / 16) i L p.1 = j} := by
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) hj
    rw [show -10 * s = -(10 * s) by ring] at hcard hB
    calc
      cfg.N k ^ (-cfg.d * (s / 16) - ζ + δ) ≤
          cfg.N k ^ (-cfg.d * (s / 16) - δ - ζ / 4) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = cfg.N k ^ (-(ζ / 4)) / cfg.N k ^ (cfg.d * (s / 16) + δ) := by
        rw [← Real.rpow_sub hN]
        congr 1
        ring
      _ ≤ cfg.N k ^ (-(ζ / 4)) /
          ((F.card : ℝ) * (cfg.N k ^ (-(10 * s))) ^ 3) :=
        div_le_div_of_nonneg_left (by positivity) hB hcard
  have hmass : ENNReal.ofReal
      (cfg.N k ^ (-cfg.d * (s / 16) - ζ) / (2 : ℝ) ^ cfg.T k s) *
        cfg.ν k (cfg.A k s i) ≤
      cfg.ρ k (source ∩ {p | cfg.midpointBin k s (s / 16) i L p.1 = j}) := by
    calc
      _ = (ENNReal.ofReal (cfg.N k ^ (-δ) / (2 : ℝ) ^ cfg.T k s) *
          cfg.ν k (cfg.A k s i)) *
            ENNReal.ofReal (cfg.N k ^ (-cfg.d * (s / 16) - ζ + δ)) := by
        rw [mul_assoc, mul_comm (cfg.ν k (cfg.A k s i)), ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [div_mul_eq_mul_div, ← Real.rpow_add hN]
        congr 2
        ring
      _ ≤ (ENNReal.ofReal (cfg.N k ^ (-δ) / (2 : ℝ) ^ cfg.T k s) *
          cfg.ν k (cfg.A k s i)) *
            σ {p | cfg.midpointBin k s (s / 16) i L p.1 = j} := by
        gcongr
      _ ≤ _ := htransport j
  refine ⟨i, L, source, j, hL₀, ?_, ?_, hcoeff, ?_⟩
  · intro e
    exact (hL e).trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hN1 hηζ) (by positivity))
  · intro p hp
    have hh := hsource hp
    exact ⟨hh.1, hh.2.1, hh.2.2.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hN1 hηζ) (by positivity))⟩
  · exact hmass

end Data

end

end Submission.Obl.k4_critical_intercept_concentration
