import Submission.Obl.k4_scalar_grid_cartesian_field.OriginalPacketFacts
import Submission.Obl.k4_scalar_grid_cartesian_field.PacketPolynomial

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory MvPolynomial
open Submission.Obl.k4_scalar_noisy_block_packets (blockLeft blockLength blockInterval)

noncomputable def boundedAssignment (data : Data) (k : ℕ) (i : Fin (data.n k 1)) (L : ℝ) :
    Set Trajectory := data.A k 1 i ∩ {l | ∀ e, |l.2 e| ≤ L}

/-- A pointwise coefficient crop is measurable in the original trajectory space. -/
theorem measurableSet_boundedAssignment {data : Data} {k : ℕ} {i : Fin (data.n k 1)}
    (p : OriginalPacketFacts data k i) (L : ℝ) : MeasurableSet (boundedAssignment data k i L) := by
  exact p.measurable_A.inter (measurableSet_coefficient_bound L)

/-- The crop keeps the full unchanged original packet prior. -/
theorem boundedAssignment_mass {data : Data} {k : ℕ} {i : Fin (data.n k 1)}
    (p : OriginalPacketFacts data k i) {L : ℝ} (hL : data.K k ≤ L) :
    data.ν k (data.γ k 1 i) (boundedAssignment data k i L) =
      data.ν k (data.γ k 1 i) (data.A k 1 i) := by
  apply measure_inter_conull
  have hc : ∀ᵐ l ∂data.ν k (data.γ k 1 i), ∀ e, |l.2 e| ≤ L := by
    filter_upwards [p.coefficient_bound] with l hl
    exact fun e => (hl e).trans hL
  exact ae_iff.mp hc

/-- Every original packet trajectory stays in the unsheared base strip for the whole block. -/
theorem OriginalPacketFacts.base_strip {data : Data} {k : ℕ} {i : Fin (data.n k 1)}
    (p : OriginalPacketFacts data k i) {Λ : ℝ} (hΛ : 2 * data.K k ≤ Λ) :
    ∀ l ∈ data.A k 1 i, ∀ t ∈ I data (data.T k 1) (data.j k 1 i),
      |scalarY l t - originalOrigin data k i 1| ≤ Λ * packetLength data k := by
  intro l hl t ht
  have h := p.normalized_bound l hl t ht 1
  change |(scalarY l t - originalOrigin data k i 1) / packetLength data k| ≤ 2 * data.K k at h
  rw [abs_div, abs_of_pos p.positive_horizon] at h
  exact ((div_le_iff₀ p.positive_horizon).mp h).trans
    (mul_le_mul_of_nonneg_right hΛ p.positive_horizon.le)

/-- Whole-block original quadratic fits give the hidden-layer hypothesis of the Cartesian core. -/
theorem OriginalPacketFacts.hidden_layer {data : Data} {k : ℕ} {i : Fin (data.n k 1)}
    (p : OriginalPacketFacts data k i) {Λ : ℝ} (hN : 0 < data.N k)
    (hΛ : 3000 * data.K k ^ 3 ≤ Λ) :
    ∀ l ∈ data.A k 1 i, ∀ l' ∈ data.A k 1 i,
      ∀ t ∈ I data (data.T k 1) (data.j k 1 i), ∀ t' ∈ I data (data.T k 1) (data.j k 1 i),
      |scalarX l t - scalarX l' t'| ≤ Λ * data.N k ^ (-1 : ℝ) +
        Λ / packetLength data k * (|t - t'| + |scalarY l t - scalarY l' t'|) := by
  intro l hl l' hl' t ht t' ht'
  let K := data.K k
  let h := packetLength data k
  have hK : 1 ≤ K := p.budget_one
  have hh : 0 < h := p.positive_horizon
  have hv : |data.v k 1 i| ≤ K := by linarith [p.uv_bound, abs_nonneg (data.u k 1 i)]
  have hnorm : ∀ t₀ ∈ Icc (blockLeft (data.T k 1) (data.j k 1 i))
      (blockLeft (data.T k 1) (data.j k 1 i) + h), ∀ w ∈ Icc (-1 : ℝ) 1,
      |eval ![t₀, data.u k 1 i + t₀ * data.v k 1 i + h * w] (data.F k 1 i)| ≤ K := by
    intro t₀ ht₀ w hw
    have htI : t₀ ∈ I data (data.T k 1) (data.j k 1 i) := by
      rw [I_eq_blockInterval]
      exact ht₀
    have hwI : w ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hw.1], by linarith [hw.2]⟩
    simpa only [h, packetLength, blockLength, div_eq_mul_inv, mul_comm w] using p.predictor_norm t₀ htI w hwI
  have hyt : |scalarY l t - data.u k 1 i - t * data.v k 1 i| ≤ K * h := by
    simpa only [h, K, packetLength, blockLength, div_eq_mul_inv] using (p.fit l hl t ht).1
  have hyt' : |scalarY l' t' - data.u k 1 i - t' * data.v k 1 i| ≤ K * h := by
    simpa only [h, K, packetLength, blockLength, div_eq_mul_inv] using (p.fit l' hl' t' ht').1
  have hpoly := packet_polynomial_lipschitz (data.F k 1 i) p.quadratic hh hK hnorm
    (by simpa only [I_eq_blockInterval, blockInterval, h, packetLength] using ht)
    (by simpa only [I_eq_blockInterval, blockInterval, h, packetLength] using ht') hyt hyt'
  have hcoef : 480 * K * (1 + K) * (1 + |data.v k 1 i|) ≤ 1920 * K ^ 3 := by
    calc
      _ ≤ 480 * K * (2 * K) * (2 * K) := by gcongr <;> linarith
      _ = _ := by ring
  have hvar : |eval ![t, scalarY l t] (data.F k 1 i) -
      eval ![t', scalarY l' t'] (data.F k 1 i)| ≤
      1920 * K ^ 3 / h * (|t - t'| + |scalarY l t - scalarY l' t'|) := by
    apply hpoly.trans
    calc
      _ ≤ 480 * K * (1 + K) / h * ((1 + |data.v k 1 i|) *
          (|t - t'| + |scalarY l t - scalarY l' t'|)) := by gcongr; nlinarith [mul_nonneg (abs_nonneg (data.v k 1 i)) (abs_nonneg (scalarY l t - scalarY l' t'))]
      _ = (480 * K * (1 + K) * (1 + |data.v k 1 i|)) / h *
          (|t - t'| + |scalarY l t - scalarY l' t'|) := by ring
      _ ≤ _ := by gcongr
  have hK₃ : K ≤ K ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hK (show 1 ≤ 3 by norm_num)
  have htri : |scalarX l t - scalarX l' t'| ≤
      |scalarX l t - eval ![t, scalarY l t] (data.F k 1 i)| +
      |eval ![t, scalarY l t] (data.F k 1 i) - eval ![t', scalarY l' t'] (data.F k 1 i)| +
      |eval ![t', scalarY l' t'] (data.F k 1 i) - scalarX l' t'| := by
    have h₁ := abs_add_le (scalarX l t - eval ![t, scalarY l t] (data.F k 1 i))
      (eval ![t, scalarY l t] (data.F k 1 i) - eval ![t', scalarY l' t'] (data.F k 1 i))
    have h₂ := abs_add_le (scalarX l t - eval ![t', scalarY l' t'] (data.F k 1 i))
      (eval ![t', scalarY l' t'] (data.F k 1 i) - scalarX l' t')
    ring_nf at h₁ h₂ ⊢
    linarith
  rw [abs_sub_comm (eval ![t', scalarY l' t'] (data.F k 1 i))] at htri
  calc
    _ ≤ K * data.N k ^ (-1 : ℝ) + 1920 * K ^ 3 / h *
        (|t - t'| + |scalarY l t - scalarY l' t'|) + K * data.N k ^ (-1 : ℝ) :=
      htri.trans (add_le_add (add_le_add (p.fit l hl t ht).2 hvar) (p.fit l' hl' t' ht').2)
    _ = (2 * K) * data.N k ^ (-1 : ℝ) + (1920 * K ^ 3) / h *
        (|t - t'| + |scalarY l t - scalarY l' t'|) := by ring
    _ ≤ _ := by gcongr <;> linarith

end Submission.Obl.k4_scalar_grid_cartesian_field
