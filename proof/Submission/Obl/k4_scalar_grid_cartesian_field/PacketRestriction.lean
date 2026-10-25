import Submission.Obl.k4_scalar_grid_cartesian_field.PacketGeometry

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open MeasureTheory Set
open Submission.Obl.k4_scalar_noisy_block_packets
  (blockLeft blockLength blockInterval)

/-- Restriction keeps the original packet mass and bounded-density reference. -/
theorem packet_restriction (ν : Measure Trajectory) (ρ : Measure Incidence)
    {K : ℝ} (T : ℕ) (j : Fin (2 ^ T)) (A : Set Trajectory)
    (hA : MeasurableSet A)
    (hdom : ρ ≤ ENNReal.ofReal K • (ν.prod volume))
    (hmass : ENNReal.ofReal ((K * (2 : ℝ) ^ T)⁻¹) * ν A ≤
      ρ (A ×ˢ blockInterval T j)) :
    let μ := ρ.restrict (A ×ˢ blockInterval T j)
    μ ≤ ρ ∧ μ ≤ ENNReal.ofReal K • (ν.prod volume) ∧
    μ (A ×ˢ blockInterval T j)ᶜ = 0 ∧
    ENNReal.ofReal (blockLength T / K) * ν A ≤ μ univ := by
  dsimp only
  have hI : MeasurableSet (blockInterval T j) := measurableSet_Icc
  have hprod : MeasurableSet (A ×ˢ blockInterval T j) := hA.prod hI
  refine ⟨Measure.restrict_le_self, Measure.restrict_le_self.trans hdom, ?_, ?_⟩
  · rw [Measure.restrict_apply hprod.compl]
    simp
  · simpa only [Measure.restrict_apply_univ, blockLength, mul_inv_rev,
      div_eq_mul_inv, mul_comm] using hmass

/-- Every later submeasure of a packet retains the whole-block geometric bound. -/
theorem normalizedBase_ae_of_packet (μ : Measure Incidence)
    {K u v : ℝ} (hK : 1 ≤ K) (huv : |u| + |v| ≤ K)
    (T : ℕ) (j : Fin (2 ^ T)) (A : Set Trajectory)
    (hsupport : μ (A ×ˢ blockInterval T j)ᶜ = 0)
    (hy : ∀ l ∈ A, ∀ t ∈ blockInterval T j,
      |scalarY l t - u - t * v| ≤ K / (2 : ℝ) ^ T) :
    ∀ᵐ p ∂μ, ∀ t ∈ blockInterval T j, ∀ e,
      |normalizedBase (blockLength T) (packetOrigin T j u v) (p.1, t) e| ≤ 2 * K := by
  have hmem : ∀ᵐ p ∂μ, p ∈ A ×ˢ blockInterval T j := by
    rw [ae_iff]
    exact hsupport
  filter_upwards [hmem] with p hp
  intro t ht
  exact normalizedBase_abs_le hK huv T j ht (hy p.1 hp.1 t ht)

/-- The frozen trajectory floors use precisely the original block length. -/
theorem packet_mass_bounds {N K d : ℝ} (T : ℕ) (m : ENNReal)
    (hlo : ENNReal.ofReal (N ^ (-d) / (K * (2 : ℝ) ^ T)) ≤ m)
    (hhi : m ≤ ENNReal.ofReal (K * N ^ (-d) / (2 : ℝ) ^ T)) :
    ENNReal.ofReal (N ^ (-d) * blockLength T / K) ≤ m ∧
      m ≤ ENNReal.ofReal (K * N ^ (-d) * blockLength T) := by
  constructor
  · simpa only [blockLength, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm,
      mul_left_comm] using hlo
  · simpa only [blockLength, div_eq_mul_inv] using hhi

end Submission.Obl.k4_scalar_grid_cartesian_field
