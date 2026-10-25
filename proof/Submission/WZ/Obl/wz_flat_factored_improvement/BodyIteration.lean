-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.BodyIteration.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyStep
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.ParameterChoice

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_regular_transverse_affine_cells

theorem iterate_body_packets {n K N : ℕ} {U Y : Fin n → Set Space} {x : Fin n → Space}
    {δ B w h S τ κ t θ : ℝ} (F : BodyGeometry U x δ B w)
    (hw : 0 < w) (hB : 0 ≤ B)
    (p : IterationParameters δ h S τ κ t θ N K)
    (hbottom : (1 / 2 : ℝ) ^ K * (384 * (n : ℝ)) ≤ 1)
    (C₀ : PhysicalPacket n) (hC₀ : BodyPacketValid U Y τ C₀) (hvol : volume C₀.region ≤ 8) :
    ∃ L : List (AffineCell n K),
      (∀ G ∈ L, BodyCellValid U Y B h G ∧ G.support ⊆ C₀.support) ∧
      L.Pairwise (fun G G' => Disjoint G.support G'.support) ∧
      τ ^ (N * (2 * N + 5)) * (C₀.indices.card : ℝ) ≤
        (L.map fun G => (G.indices.card : ℝ)).sum := by
  have hκ : 0 < κ := p.shrink_pos
  let P : ℕ → PhysicalPacket n → Prop := fun j C =>
    BodyPacketValid U Y (τ ^ (j + 1)) C ∧ volume C.region ≤ ENNReal.ofReal (8 * κ ^ j)
  let α := τ ^ (2 * N + 5)
  have hstop : ∀ C, ¬ P N C := by
    intro C hC
    obtain ⟨i, hi⟩ := hC.1.nonempty
    have hlower : ENNReal.ofReal (δ ^ 3 / 8) ≤ volume C.region :=
      (volume_ball_lower p.delta_pos (x i)).trans
        (measure_mono ((F.interior i).trans (hC.1.whole i hi)))
    have hh := (ENNReal.ofReal_le_ofReal_iff
      (by positivity : 0 ≤ 8 * κ ^ N)).mp (hlower.trans hC.2)
    exact (not_le_of_gt p.extinction) hh
  have hstep : ∀ j < N, ∀ C, P j C → ∃ L : List (AffineCell n K ⊕ PhysicalPacket n),
      (∀ z ∈ L, (Sum.elim (BodyCellValid U Y B h) (P (j + 1))) z ∧
        (Sum.elim AffineCell.support ShadedCell.support) z ⊆ C.support) ∧
      L.Pairwise (fun z z' => Disjoint ((Sum.elim AffineCell.support ShadedCell.support) z)
        ((Sum.elim AffineCell.support ShadedCell.support) z')) ∧
      α * (C.indices.card : ℝ) ≤ (L.map (Sum.elim (fun G => (G.indices.card : ℝ))
        (fun C => (C.indices.card : ℝ)))).sum := by
    intro j hj C hC
    have hmin : τ ^ (N + 1) ≤ τ ^ (j + 1) * τ := by
      rw [← pow_succ]
      exact pow_le_pow_of_le_one p.tau_pos.le p.tau_small (by omega)
    obtain ⟨L, hL, hdisj, hmass⟩ := body_packet_step F hw hB p hC.1 hbottom
      (pow_pos p.tau_pos _) (pow_le_one₀ p.tau_pos.le p.tau_small)
      (p.quality_density.trans hmin)
      (p.quality_slab.trans (mul_le_mul_of_nonneg_left hmin p.width_pos.le))
    refine ⟨L, ?_, hdisj, ?_⟩
    · intro z hz
      obtain ⟨hgood, hsub⟩ := hL z hz
      refine ⟨?_, hsub⟩
      cases z with
      | inl G => exact hgood
      | inr C' =>
        obtain ⟨hvalid, hsmall⟩ := hgood
        refine ⟨?_, ?_⟩
        · simpa only [pow_succ] using hvalid
        · apply (hsmall.trans (mul_le_mul' le_rfl hC.2)).trans
          rw [← ENNReal.ofReal_mul p.shrink_pos.le]
          apply le_of_eq
          congr 1
          rw [pow_succ]
          ring
    · have hα : α ≤ (τ ^ (j + 1)) ^ 2 * τ ^ 3 := by
        rw [← pow_mul, ← pow_add]
        exact pow_le_pow_of_le_one p.tau_pos.le p.tau_small (by omega)
      exact (mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg _)).trans hmass
  obtain ⟨L, hL, hdisj, hmass⟩ := finite_depth_extraction N P (BodyCellValid U Y B h)
    ShadedCell.support AffineCell.support (fun C => (C.indices.card : ℝ))
    (fun G => (G.indices.card : ℝ)) (fun G => Nat.cast_nonneg _)
    (pow_pos p.tau_pos (2 * N + 5)).le (pow_le_one₀ p.tau_pos.le p.tau_small)
    hstop hstep C₀ (by
      simpa only [P, Nat.zero_add, pow_zero, pow_one, mul_one, ENNReal.ofReal_ofNat]
        using And.intro hC₀ hvol)
  exact ⟨L, hL, hdisj, by simpa only [α, ← pow_mul, Nat.mul_comm] using hmass⟩

/-- The regular transverse extraction applies to convex bodies, retaining their
middle width in every terminal affine cell. -/
theorem body_cells (s : ℝ) (hs : 0 < s) :
    ∃ η : ℝ, 0 < η ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 100 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ (n : ℕ) (U Y : Fin n → Set Space)
      (x : Fin n → Space) (B w : ℝ),
    0 < n → (n : ℝ) ≤ δ ^ (-100 : ℝ) → 0 ≤ B → 0 < w →
    BodyGeometry U x δ B w → (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ U i) →
    (∀ i, ENNReal.ofReal (δ ^ η) * volume (U i) ≤ volume (Y i)) →
    ∃ (K : ℕ) (L : List (AffineCell n K)),
      (K + 1 : ℕ) * δ ^ s ≤ 1 ∧
      (∀ G ∈ L, BodyCellValid U Y B (δ ^ s) G ∧ G.support ⊆ ⋃ i, Y i) ∧
      L.Pairwise (fun G G' => Disjoint G.support G'.support) ∧
      δ ^ s * (n : ℝ) ≤ (L.map fun G => (G.indices.card : ℝ)).sum := by
  obtain ⟨η, hη, δ₀, hδ₀, hδ₀small, hparams⟩ := asymptotic_iteration_parameters s hs
  refine ⟨η, hη, δ₀, hδ₀, hδ₀small, ?_⟩
  intro δ hδ hδmax n U Y x B w hn hnmax hB hw F hYm hYU hYd
  obtain ⟨N, K, τ, κ, t, θ, p, hinit, hret, hbottom⟩ := hparams δ hδ hδmax
  let C₀ : PhysicalPacket n := ⟨Finset.univ, closedBall 0 1, Y⟩
  have hC₀ : BodyPacketValid U Y τ C₀ := {
    nonempty := Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn),
    compact := isCompact_closedBall _ _, convex := convex_closedBall _ _,
    bounded := Subset.rfl, whole := fun i _ => F.bounded i,
    measurable := fun i _ => hYm i, original := fun _ _ => Subset.rfl,
    source := fun i _ => hYU i,
    density := fun i _ =>
      (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith [p.tau_pos] : τ ≤ δ ^ η))
        le_rfl).trans (hYd i) }
  obtain ⟨L, hL, hdisj, hmass⟩ := iterate_body_packets F hw hB p
    (by apply le_trans _ hbottom; gcongr) C₀ hC₀ volume_unit_closedBall_upper
  refine ⟨K, L, ?_, ?_, hdisj, ?_⟩
  · have hhτ : δ ^ s ≤ τ := p.quality_density.trans
      (pow_le_of_le_one p.tau_pos.le p.tau_small (by omega))
    have hK1 : (1 : ℝ) ≤ (K + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le K)
    calc
      (K + 1 : ℕ) * δ ^ s ≤ (K + 1 : ℕ) * τ := by gcongr
      _ = τ * (K + 1 : ℕ) := by ring
      _ ≤ τ * (K + 1 : ℕ) ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) p.tau_pos.le
      _ ≤ _ := p.tau_shape
  · intro G hG
    exact ⟨(hL G hG).1, by simpa [C₀, ShadedCell.support] using (hL G hG).2⟩
  · have hret' : δ ^ s ≤ τ ^ (N * (2 * N + 5)) :=
      hret.trans (pow_le_pow_of_le_one p.tau_pos.le p.tau_small (by omega))
    exact (mul_le_mul_of_nonneg_right hret' (Nat.cast_nonneg n)).trans (by simpa [C₀] using hmass)

end WangZahlLot.Obl.wz_flat_factored_improvement
