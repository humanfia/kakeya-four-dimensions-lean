import Submission.Obl.k4_scalar_grid_cartesian_field.PacketCellVariation
import Submission.Obl.k4_scalar_grid_cartesian_field.QuadraticDerivative
import Submission.Obl.k4_scalar_grid_cartesian_field.SteepCells
import Submission.Obl.k4_scalar_grid_cartesian_field.SteepNumerics

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory MvPolynomial
open Submission.Obl.k4_scalar_noisy_block_packets
  (blockLeft blockLength blockInterval blockLeft_nonneg blockRight_le_one)

/-- The original bounded-coefficient incidences on a steep part of an original packet. -/
noncomputable def steepPacket (data : Data) (k : ℕ) (i : Fin (data.n k 1)) (Q : ℝ) : Set Incidence :=
  {x | x.1 ∈ data.A k 1 i ∧ x.2 ∈ I data (data.T k 1) (data.j k 1 i) ∧
    (∀ e, |x.1.2 e| ≤ data.K k) ∧
    Q ≤ |eval ![x.2, scalarY x.1 x.2] (pderiv 1 (data.F k 1 i))|}

/-- The original whole-block quadratic fit bounds the predictor's directional derivative. -/
theorem OriginalPacketFacts.directional_bound {data : Data} {k : ℕ} {i : Fin (data.n k 1)}
    (p : OriginalPacketFacts data k i) (hN : 2 ≤ data.N k) (hκ : data.κ ≤ 1)
    (l : Trajectory) (hl : l ∈ data.A k 1 i) (hcoeff : ∀ e, |l.2 e| ≤ data.K k) :
    ∀ t ∈ I data (data.T k 1) (data.j k 1 i),
      |eval ![t, scalarY l t] (pderiv 0 (data.F k 1 i)) +
        l.2 1 * eval ![t, scalarY l t] (pderiv 1 (data.F k 1 i))| ≤ 30 * data.K k ^ 2 := by
  intro t ht
  apply packet_directional_scale_bound (data.F k 1 i) p.quadratic l hN p.budget_one hκ
    p.positive_horizon p.horizon_lower (blockLeft_nonneg _ _) (blockRight_le_one _ _) hcoeff
  · intro t₀ ht₀
    exact (p.fit l hl t₀ (by simpa only [I_eq_blockInterval, blockInterval, packetLength] using ht₀)).2
  · simpa only [I_eq_blockInterval, blockInterval, packetLength] using ht

/-- The fine base-cell sum of the original four-coordinate joint cap controls steep packet mass. -/
theorem packet_steep_mass_of_joint_cap {data : Data} {k : ℕ} {i : Fin (data.n k 1)}
    (p : OriginalPacketFacts data k i) (hN : 2 ≤ data.N k) (hκ : data.κ ≤ 1)
    {b : ℝ} (hb : 0 < b) (B : ENNReal)
    (hFsmall : 2880 * data.K k ^ 3 ≤ data.N k ^ (9 : ℝ))
    (hGsmall : 23040 * data.K k ^ 5 ≤ data.N k ^ (9 : ℝ))
    (hsep : 32 * data.K k ^ 2 ≤ data.N k ^ b)
    (hcap : ∀ (q : Fin 2 → ℤ) (a c : ℤ), data.ρ k (data.γ k 1 i)
      {x | z data (data.N k) (10 + data.κ) x = q ∧
        (⌊scalarX x.1 x.2 / data.N k ^ (-1 : ℝ)⌋ : ℤ) = a ∧
        (⌊x.1.2 1 / data.N k ^ (-b)⌋ : ℤ) = c} ≤ B) :
    data.ρ k (data.γ k 1 i) (steepPacket data k i (data.N k ^ (2 * b))) ≤
      ENNReal.ofReal (49 * data.K k ^ 2 * (data.N k ^ (-10 : ℝ))⁻¹ ^ 2) *
        (((2 * ⌈2 * data.K k + 1⌉₊ + 1) ^ 4 : ℕ) * B) := by
  let N := data.N k
  let K := data.K k
  let h := packetLength data k
  let ξ := N ^ (-10 : ℝ)
  let α := N ^ (-(10 + data.κ))
  let δ := N ^ (-1 : ℝ)
  let γ := N ^ (-b)
  let Q := N ^ (2 * b)
  let C := ⌈2 * K + 1⌉₊
  let S := steepPacket data k i Q
  let zbase : Incidence → Fin 2 → ℝ := fun x => ![x.2, scalarY x.1 x.2]
  have hNp : 0 < N := by dsimp [N]; linarith
  have hN₁ : 1 ≤ N := by dsimp [N]; linarith
  have hK : 1 ≤ K := p.budget_one
  have hC : 2 * K + 1 ≤ (C : ℝ) := Nat.le_ceil _
  have hCone : 1 ≤ C := by exact_mod_cast (show (1 : ℝ) ≤ (C : ℝ) by linarith)
  have hh : 0 < h := p.positive_horizon
  have hξ : 0 < ξ := Real.rpow_pos_of_pos hNp _
  have hα : 0 < α := Real.rpow_pos_of_pos hNp _
  have hδ : 0 < δ := Real.rpow_pos_of_pos hNp _
  have hγ : 0 < γ := Real.rpow_pos_of_pos hNp _
  have hQ : 0 < Q := Real.rpow_pos_of_pos hNp _
  have hwidth : h * ξ ≤ (C : ℝ) * α := by
    calc
      _ ≤ (K * N ^ (-data.κ)) * ξ := mul_le_mul_of_nonneg_right p.horizon_upper hξ.le
      _ = K * α := by dsimp [ξ, α]; rw [mul_assoc, ← Real.rpow_add hNp]; congr 2; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hα.le
  have hsmall : 30 * K ^ 2 + (1 + K) * 1 ≤ Q * γ := by
    have heq : Q * γ = N ^ b := by dsimp [Q, γ]; rw [← Real.rpow_add hNp]; congr 1; ring
    rw [heq]
    have hKK : 0 ≤ (K - 1) * K := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hdir : ∀ x ∈ S,
      |eval (zbase x) (pderiv 0 (data.F k 1 i)) + x.1.2 1 *
        eval (zbase x) (pderiv 1 (data.F k 1 i))| ≤ 30 * K ^ 2 := by
    intro x hx
    exact p.directional_bound hN hκ x.1 hx.1 hx.2.2.1 x.2 hx.2.1
  have hvar : ∀ x ∈ S, ∀ x' ∈ S,
      (fun e => (⌊(zbase x e - originalOrigin data k i e) / h / ξ⌋ : ℤ)) =
      (fun e => (⌊(zbase x' e - originalOrigin data k i e) / h / ξ⌋ : ℤ)) →
      |eval (zbase x) (data.F k 1 i) - eval (zbase x') (data.F k 1 i)| ≤ δ ∧
      |eval (zbase x) (pderiv 0 (data.F k 1 i)) - eval (zbase x') (pderiv 0 (data.F k 1 i))| ≤ 1 ∧
      |eval (zbase x) (pderiv 1 (data.F k 1 i)) - eval (zbase x') (pderiv 1 (data.F k 1 i))| ≤ 1 := by
    intro x hx x' hx' hc
    obtain ⟨hf, hg⟩ := p.fine_cell_variations hN hκ hFsmall hGsmall
      x hx.1 hx.2.1 x' hx'.1 hx'.2.1 hc
    exact ⟨hf, hg 0, hg 1⟩
  have hcells := normalized_steep_cell_cap (data.ρ k (data.γ k 1 i)) zbase
    (fun x => scalarX x.1 x.2) (fun x => x.1.2 1)
    (fun z => eval z (data.F k 1 i)) (fun z => eval z (pderiv 0 (data.F k 1 i)))
    (fun z => eval z (pderiv 1 (data.F k 1 i))) S hh hξ hα hδ hγ
    (by linarith : 0 ≤ K) (by norm_num : (0 : ℝ) ≤ 1) hQ (originalOrigin data k i) C
    hwidth hC hCone hsmall B
    (by
      intro q a c
      have hc := hcap q a c
      change data.ρ k (data.γ k 1 i) {x |
        (fun e => (⌊zbase x e / α⌋ : ℤ)) = q ∧
        (⌊scalarX x.1 x.2 / δ⌋ : ℤ) = a ∧ (⌊x.1.2 1 / γ⌋ : ℤ) = c} ≤ B at hc
      exact hc)
    (fun x hx => (p.fit x.1 hx.1 x.2 hx.2.1).2)
    (fun x hx => hx.2.2.1 1) hdir (fun x hx => hx.2.2.2) hvar
  have hnorm : ∀ x ∈ S, ∀ e, |normalizedBase h (originalOrigin data k i) x e| ≤ 2 * K := by
    intro x hx
    exact p.normalized_bound x.1 hx.1 x.2 hx.2.1
  exact mass_le_of_bounded_base_cell_caps (data.ρ k (data.γ k 1 i))
    (normalizedBase h (originalOrigin data k i)) S hK hξ
    (Real.rpow_le_one_of_one_le_of_nonpos hN₁ (by norm_num)) _ hnorm hcells

/-- The original joint cap and the ORIGINAL angular prior give a small full-prior packet loss. -/
theorem packet_steep_mass_bound {data : Data} {k : ℕ} {i : Fin (data.n k 1)}
    (p : OriginalPacketFacts data k i) (hN : 2 ≤ data.N k) (hκ : data.κ ≤ 1)
    {b : ℝ} (hb : 0 < b)
    (hFsmall : 2880 * data.K k ^ 3 ≤ data.N k ^ (9 : ℝ))
    (hGsmall : 23040 * data.K k ^ 5 ≤ data.N k ^ (9 : ℝ))
    (hsep : 32 * data.K k ^ 2 ≤ data.N k ^ b)
    (hπ : ∀ c : ℤ, data.π k (data.γ k 1 i) (vel data k b c) ≤
      ENNReal.ofReal (data.K k * data.N k ^ (-data.S * b)))
    (hρ : ∀ (q : Fin 2 → ℤ) (a c : ℤ), data.ρ k (data.γ k 1 i)
      {x | z data (data.N k) (10 + data.κ) x = q ∧
        (⌊scalarX x.1 x.2 / data.N k ^ (-1 : ℝ)⌋ : ℤ) = a ∧ x.1.2 1 ∈ vel data k b c} ≤
      ENNReal.ofReal (data.K k * data.N k ^ (-2 * (10 + data.κ) - data.d)) *
        data.π k (data.γ k 1 i) (vel data k b c)) :
    data.ρ k (data.γ k 1 i) (steepPacket data k i (data.N k ^ (2 * b))) ≤
      ENNReal.ofReal (400000 * data.K k ^ 11 * data.N k ^ (-data.S * b)) *
        (ENNReal.ofReal (packetLength data k) * data.ν k (data.γ k 1 i) (data.A k 1 i)) := by
  have hNp : 0 < data.N k := by linarith
  have hK := p.budget_one
  let B := ENNReal.ofReal (data.K k ^ 2 * data.N k ^ (-2 * (10 + data.κ) - data.d - data.S * b))
  have hrect : ∀ (q : Fin 2 → ℤ) (a c : ℤ), data.ρ k (data.γ k 1 i)
      {x | z data (data.N k) (10 + data.κ) x = q ∧
        (⌊scalarX x.1 x.2 / data.N k ^ (-1 : ℝ)⌋ : ℤ) = a ∧
        (⌊x.1.2 1 / data.N k ^ (-b)⌋ : ℤ) = c} ≤ B := by
    intro q a c
    apply (hρ q a c).trans
    calc
      _ ≤ ENNReal.ofReal (data.K k * data.N k ^ (-2 * (10 + data.κ) - data.d)) *
          ENNReal.ofReal (data.K k * data.N k ^ (-data.S * b)) := mul_le_mul' le_rfl (hπ c)
      _ = _ := steep_rectangular_cap_product hNp (by linarith)
  calc
    _ ≤ ENNReal.ofReal (49 * data.K k ^ 2 * (data.N k ^ (-10 : ℝ))⁻¹ ^ 2) *
        (((2 * ⌈2 * data.K k + 1⌉₊ + 1) ^ 4 : ℕ) * B) :=
      packet_steep_mass_of_joint_cap p hN hκ hb B hFsmall hGsmall hsep hrect
    _ ≤ ENNReal.ofReal (400000 * data.K k ^ 6 * data.N k ^ (20 : ℝ)) * B :=
      steep_code_count_bound hNp hK B
    _ = ENNReal.ofReal (400000 * data.K k ^ 8 * data.N k ^ (-2 * data.κ - data.d - data.S * b)) :=
      steep_mass_normalization hNp (by linarith)
    _ ≤ _ := steep_mass_prior_calibration hNp hK p.positive_horizon p.horizon_lower _ p.prior_lower

end Submission.Obl.k4_scalar_grid_cartesian_field
