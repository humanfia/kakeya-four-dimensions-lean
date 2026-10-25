import Submission.Obl.k4_scalar_grid_cartesian_field.DataFacts
import Submission.Obl.k4_scalar_grid_cartesian_field.PacketRestriction

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory Filter MvPolynomial
open Submission.Obl.k4_scalar_noisy_block_packets (blockLeft blockLength blockInterval)

noncomputable def packetLength (data : Data) (k : ℕ) : ℝ := blockLength (data.T k 1)

noncomputable def originalOrigin (data : Data) (k : ℕ) (i : Fin (data.n k 1)) : Fin 2 → ℝ :=
  packetOrigin (data.T k 1) (data.j k 1 i) (data.u k 1 i) (data.v k 1 i)

/-- The original packet facts needed before and after the Cartesian restriction. -/
structure OriginalPacketFacts (data : Data) (k : ℕ) (i : Fin (data.n k 1)) : Prop where
  measurable_A : MeasurableSet (data.A k 1 i)
  probability_ν : IsProbabilityMeasure (data.ν k (data.γ k 1 i))
  probability_π : IsProbabilityMeasure (data.π k (data.γ k 1 i))
  coefficient_bound : ∀ᵐ l ∂data.ν k (data.γ k 1 i), ∀ e, |l.2 e| ≤ data.K k
  original_density : data.ρ k (data.γ k 1 i) ≤
    ENNReal.ofReal (data.K k) • (data.ν k (data.γ k 1 i)).prod volume
  horizon_lower : data.N k ^ (-data.κ) / data.K k ≤ packetLength data k
  horizon_upper : packetLength data k ≤ data.K k * data.N k ^ (-data.κ)
  positive_horizon : 0 < packetLength data k
  bounded_horizon : packetLength data k ≤ 1
  prior_lower : ENNReal.ofReal (data.N k ^ (-data.d) * packetLength data k / data.K k) ≤
    data.ν k (data.γ k 1 i) (data.A k 1 i)
  prior_upper : data.ν k (data.γ k 1 i) (data.A k 1 i) ≤
    ENNReal.ofReal (data.K k * data.N k ^ (-data.d) * packetLength data k)
  center_bound : ∀ e, |originalOrigin data k i e| ≤ data.K k
  normalized_bound : ∀ l ∈ data.A k 1 i, ∀ t ∈ I data (data.T k 1) (data.j k 1 i),
    ∀ e, |normalizedBase (packetLength data k) (originalOrigin data k i) (l,t) e| ≤ 2 * data.K k
  uv_bound : |data.u k 1 i| + |data.v k 1 i| ≤ data.K k
  quadratic : (data.F k 1 i).totalDegree ≤ 2
  predictor_norm : ∀ t ∈ I data (data.T k 1) (data.j k 1 i), ∀ w ∈ Icc (-2 : ℝ) 2,
    |eval ![t, data.u k 1 i + t * data.v k 1 i + w / (2 : ℝ) ^ data.T k 1]
      (data.F k 1 i)| ≤ data.K k
  fit : ∀ l ∈ data.A k 1 i, ∀ t ∈ I data (data.T k 1) (data.j k 1 i),
    |scalarY l t - data.u k 1 i - t * data.v k 1 i| ≤ data.K k / (2 : ℝ) ^ data.T k 1 ∧
    |scalarX l t - eval ![t, scalarY l t] (data.F k 1 i)| ≤ data.K k * data.N k ^ (-1 : ℝ)
  budget_one : 1 ≤ data.K k

/-- Specializing the frozen packet oracle to depth one preserves its full original prior. -/
theorem original_packet_facts_eventually (data : Data) (hscale : scaleHyp data)
    (hbase : baseHyp data) (hpacket : packetHyp data) :
    ∀ᶠ k in atTop, ∀ i : Fin (data.n k 1), OriginalPacketFacts data k i := by
  filter_upwards [hpacket 2 (by norm_num)] with k hk
  obtain ⟨hlo, hhi, hA, _, hi, _⟩ := hk 1 (by norm_num) (by norm_num)
  intro i
  obtain ⟨hmlo, hmhi, _, huv, hF, hnorm, hfit⟩ := hi i
  have hN : 0 < data.N k := by linarith [hscale.1 k]
  have hK : 1 ≤ data.K k := hscale.2.2.1.1 k
  have hKpos : 0 < data.K k := by linarith
  obtain ⟨hν, hπ, hcoeff, hdensity, _⟩ := (hbase k).2.2.1 (data.γ k 1 i)
  have hsc := blockLength_comparison hN hKpos (data.T k 1)
    (by simpa only [mul_one] using hlo) (by simpa only [mul_one] using hhi)
  have hmass := packet_mass_bounds (data.T k 1)
    ((data.ν k (data.γ k 1 i)) (data.A k 1 i))
    (by simpa only [mul_one] using hmlo) (by simpa only [mul_one] using hmhi)
  refine ⟨hA i, hν, hπ, hcoeff, hdensity, hsc.1, hsc.2,
    blockLength_pos _, blockLength_le_one _, hmass.1, hmass.2,
    packetOrigin_abs_le hK huv _ _, ?_, huv, hF, hnorm, ?_, hK⟩
  · intro l hl t ht
    exact normalizedBase_abs_le hK huv _ _ (by simpa only [I_eq_blockInterval] using ht)
      ((hfit l hl t ht).1)
  · simpa only [mul_one, y_eq_scalarY, x_eq_scalarX] using hfit

end Submission.Obl.k4_scalar_grid_cartesian_field
