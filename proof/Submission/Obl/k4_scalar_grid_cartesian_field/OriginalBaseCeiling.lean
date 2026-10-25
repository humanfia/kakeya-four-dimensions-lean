import Submission.Obl.k4_scalar_grid_cartesian_field.OriginalPacketFacts
import Submission.Obl.k4_scalar_grid_cartesian_field.PacketBaseCap

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory MvPolynomial
open Submission.Obl.k4_scalar_noisy_block_packets (blockLeft blockLength blockInterval)

/-- The original rectangular cap supplies the normalized base ceiling for every later packet submeasure. -/
theorem OriginalPacketFacts.normalized_base_cap {data : Data} {k : ℕ} {i : Fin (data.n k 1)}
    (p : OriginalPacketFacts data k i) (hN : 0 < data.N k)
    (μ : Measure Incidence) (hμ : μ ≤ data.ρ k (data.γ k 1 i))
    (hsupport : μ {x | x.1 ∈ data.A k 1 i ∧ x.2 ∈ I data (data.T k 1) (data.j k 1 i)}ᶜ = 0)
    (hcap : ∀ (q : Fin 2 → ℤ) (c : ℤ), data.ρ k (data.γ k 1 i)
      {x | (fun e : Fin 2 => (⌊(![x.2, scalarY x.1 x.2] : Fin 2 → ℝ) e /
        data.N k ^ (-(10 + data.κ))⌋ : ℤ)) = q ∧
        (⌊scalarX x.1 x.2 / data.N k ^ (-1 : ℝ)⌋ : ℤ) = c} ≤
      ENNReal.ofReal (data.K k * data.N k ^ (-2 * (10 + data.κ) - data.d)))
    (hsmall : 2880 * data.K k ^ 3 ≤ data.N k ^ (9 : ℝ)) :
    ∀ q : Fin 2 → ℤ, μ {x | (fun e : Fin 2 =>
      (⌊normalizedBase (packetLength data k) (originalOrigin data k i) x e /
        data.N k ^ (-10 : ℝ)⌋ : ℤ)) = q} ≤
      ENNReal.ofReal ((100000 * data.K k ^ 7 * packetLength data k) * data.N k ^ (-20 : ℝ)) *
        data.ν k (data.γ k 1 i) (data.A k 1 i) := by
  have hsupp : μ (data.A k 1 i ×ˢ blockInterval (data.T k 1) (data.j k 1 i))ᶜ = 0 := by
    change μ {x | x.1 ∈ data.A k 1 i ∧ x.2 ∈ blockInterval (data.T k 1) (data.j k 1 i)}ᶜ = 0
    simpa only [I_eq_blockInterval] using hsupport
  have hnorm : ∀ t ∈ blockInterval (data.T k 1) (data.j k 1 i), ∀ w ∈ Icc (-1 : ℝ) 1,
      |eval ![t, data.u k 1 i + t * data.v k 1 i + w / (2 : ℝ) ^ data.T k 1]
        (data.F k 1 i)| ≤ data.K k := by
    intro t ht w hw
    exact p.predictor_norm t (by simpa only [I_eq_blockInterval] using ht) w
      ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hfit : ∀ l ∈ data.A k 1 i, ∀ t ∈ blockInterval (data.T k 1) (data.j k 1 i),
      |scalarY l t - data.u k 1 i - t * data.v k 1 i| ≤ data.K k / (2 : ℝ) ^ data.T k 1 ∧
      |scalarX l t - eval ![t, scalarY l t] (data.F k 1 i)| ≤ data.K k * data.N k ^ (-1 : ℝ) := by
    intro l hl t ht
    exact p.fit l hl t (by simpa only [I_eq_blockInterval] using ht)
  have hraw := packet_base_cap_raw (data.ρ k (data.γ k 1 i)) μ hμ hN p.budget_one
    (data.T k 1) (data.j k 1 i) (data.A k 1 i) hsupp p.horizon_upper p.uv_bound
    (data.F k 1 i) p.quadratic hnorm (fun l hl t ht => (hfit l hl t ht).1)
    (fun l hl t ht => (hfit l hl t ht).2) hcap hsmall
  have hcal := packet_base_cap_calibration hN p.budget_one p.positive_horizon p.horizon_lower
    (data.ν k (data.γ k 1 i) (data.A k 1 i)) p.prior_lower
  exact fun q => (hraw q).trans hcal

end Submission.Obl.k4_scalar_grid_cartesian_field
