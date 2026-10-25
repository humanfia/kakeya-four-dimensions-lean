-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.IteratePackets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.PacketStep

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open Module MeasureTheory Set Metric
open scoped ENNReal

/-- Numerical hypotheses sufficient for the geometric iteration. -/
structure IterationParameters (δ h S τ κ t θ : ℝ) (N K : ℕ) : Prop where
  delta_pos : 0 < δ
  delta_small : δ ≤ 1
  scale_large : 1000000000 ≤ S
  depth_scale : (1 / 2 : ℝ) ^ K < δ / (6 * S)
  tau_pos : 0 < τ
  tau_small : τ ≤ 1
  tau_density : 3072 * τ ≤ 1
  tau_budget : 8 * (1000000 * (K + 1 : ℕ)) * (400000 * S) * 384 * τ ≤ 1
  tau_shape : τ * (K + 1 : ℕ) ^ 2 ≤ 1
  tau_slab : 768 * (1 + 320 * K : ℝ) * τ ≤ 1
  quality_pos : 0 < h
  width_pos : 0 < t
  width_small : t ≤ 1
  angle_pos : 0 < θ
  shrink_pos : 0 < κ
  quality_density : h ≤ τ ^ (N + 1)
  quality_angle : h ≤ θ
  quality_slab : h * 6144 ≤ t * τ ^ (N + 1)
  width_shrink : 2048 * S * t ≤ κ
  angle_width : 9 * θ ≤ t
  shape_lower : δ ^ (100 : ℕ) ≤ δ / (12 * S)
  quality_small : h ≤ 1 / (12 * S)
  jacobian_lower : δ ^ (100 : ℕ) ≤ δ ^ 3
  jacobian_upper : 512 * S ^ 3 ≤ δ ^ (-100 : ℝ)
  extinction : 8 * κ ^ N < δ ^ 3 / 8

set_option maxHeartbeats 600000 in
lemma iterate_physical_packets {n K N : ℕ} {δ h S τ κ t θ : ℝ}
    {x v : Fin n → E} {Y : Fin n → Set E}
    (p : IterationParameters δ h S τ κ t θ N K)
    (hv : ∀ i, ‖v i‖ = 1) (htube : ∀ i, tube δ (x i) (v i) ⊆ ball (0 : E) 1)
    (hbottom : (1 / 2 : ℝ) ^ K * (384 * (n : ℝ)) ≤ 1)
    (C₀ : PhysicalPacket n) (hC₀ : C₀.Valid δ τ x v Y) (hV₀ : volume C₀.region ≤ 8) :
    ∃ L : List (AffineCell n K), (∀ G ∈ L, G.Valid δ h x v Y ∧ G.support ⊆ C₀.support) ∧
      L.Pairwise (fun G G' => Disjoint G.support G'.support) ∧
      τ ^ (N * (2 * N + 5)) * (C₀.indices.card : ℝ) ≤
        (L.map fun G => (G.indices.card : ℝ)).sum := by
  have hκ := p.shrink_pos
  let P : ℕ → PhysicalPacket n → Prop := fun j C =>
    C.Valid δ (τ ^ (j + 1)) x v Y ∧ volume C.region ≤ ENNReal.ofReal (8 * κ ^ j)
  let α : ℝ := τ ^ (2 * N + 5)
  have hα : 0 ≤ α := (pow_pos p.tau_pos _).le
  have hα1 : α ≤ 1 := pow_le_one₀ p.tau_pos.le p.tau_small
  have hstop : ∀ C, ¬ P N C := by
    intro C hC
    obtain ⟨i, hi⟩ := hC.1.1
    have hlow := whole_tube_container_volume_lower p.delta_pos (x i) (v i)
      (hC.1.2.2.2.2.1 i hi)
    have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 8 * κ ^ N)).mp (hlow.trans hC.2)
    exact (not_le_of_gt p.extinction) hreal
  have hstep : ∀ j < N, ∀ C, P j C → ∃ L : List (AffineCell n K ⊕ PhysicalPacket n),
      (∀ z ∈ L, (Sum.elim (fun G => G.Valid δ h x v Y) (P (j + 1))) z ∧
        (Sum.elim AffineCell.support ShadedCell.support) z ⊆ C.support) ∧
      L.Pairwise (fun z z' => Disjoint ((Sum.elim AffineCell.support ShadedCell.support) z)
        ((Sum.elim AffineCell.support ShadedCell.support) z')) ∧
      α * (C.indices.card : ℝ) ≤ (L.map (Sum.elim (fun G => (G.indices.card : ℝ))
        (fun C => (C.indices.card : ℝ)))).sum := by
    intro j hj C hC
    have hd : 0 < τ ^ (j + 1) := pow_pos p.tau_pos _
    have hd1 : τ ^ (j + 1) ≤ 1 := pow_le_one₀ p.tau_pos.le p.tau_small
    have hq1 : τ ^ (j + 1) * τ ≤ 1 := by
      rw [← pow_succ]
      exact pow_le_one₀ p.tau_pos.le p.tau_small
    have hqmin : τ ^ (N + 1) ≤ τ ^ (j + 1) * τ := by
      rw [← pow_succ]
      exact pow_le_pow_of_le_one p.tau_pos.le p.tau_small (by omega)
    obtain ⟨L, hL, hdisj, hmass⟩ := physical_packet_step hC.1 p.delta_pos p.delta_small p.scale_large
      hv htube p.depth_scale hbottom hd hd1 p.tau_pos p.tau_small p.tau_density p.tau_budget p.tau_shape
      p.tau_slab p.quality_pos p.width_pos p.angle_pos
      ((mul_le_of_le_one_right p.width_pos.le hq1).trans p.width_small)
      (p.quality_density.trans hqmin) p.quality_angle
      (p.quality_slab.trans (mul_le_mul_of_nonneg_left hqmin p.width_pos.le))
      p.width_shrink p.angle_width p.shape_lower p.quality_small p.jacobian_lower p.jacobian_upper
    refine ⟨L, ?_, hdisj, ?_⟩
    · intro z hz
      obtain ⟨hvalid, hsub⟩ := hL z hz
      refine ⟨?_, hsub⟩
      cases z with
      | inl G => exact hvalid
      | inr C' =>
        obtain ⟨hC', hshrink⟩ := hvalid
        refine ⟨?_, ?_⟩
        · simpa only [pow_succ] using hC'
        · have hmul := mul_le_mul_right hC.2 (ENNReal.ofReal κ)
          apply (hshrink.trans hmul).trans
          rw [← ENNReal.ofReal_mul p.shrink_pos.le]
          apply le_of_eq
          congr 1
          rw [pow_succ]
          ring
    · have hcoef : α ≤ (τ ^ (j + 1)) ^ 2 * τ ^ 3 := by
        rw [← pow_mul, ← pow_add]
        exact pow_le_pow_of_le_one p.tau_pos.le p.tau_small (by omega)
      exact (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)).trans hmass
  obtain ⟨L, hL, hdisj, hmass⟩ := finite_depth_extraction N P (fun G => G.Valid δ h x v Y)
    ShadedCell.support AffineCell.support (fun C => (C.indices.card : ℝ))
    (fun G => (G.indices.card : ℝ)) (fun G => Nat.cast_nonneg _) hα hα1 hstop hstep
    C₀ (by simpa only [P, Nat.zero_add, pow_zero, pow_one, mul_one, ENNReal.ofReal_ofNat] using And.intro hC₀ hV₀)
  refine ⟨L, hL, hdisj, ?_⟩
  simpa only [α, ← pow_mul, Nat.mul_comm] using hmass

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
