-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.BodyBalance.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyCover
import Submission.WZ.Obl.wz_weighted_affine_packet_balancing.Refinement

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (AffineCell)
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover (netConst)

structure BalancedBodyCover {n K : ℕ} (G : AffineCell n K) (d τ : ℝ) where
  count : ℕ
  multiplicity : ℕ
  count_pos : 0 < count
  multiplicity_pos : 0 < multiplicity
  start : Fin count → Space
  direction : Fin count → Space
  fiber : Fin count → Finset (Fin n)
  shading : Fin count → Set Space
  unit_direction : ∀ j, ‖direction j‖ = 1
  bounded : ∀ j, Tube (4 * G.b) (start j) (direction j) ⊆ ball (0 : Space) 1
  separated : ∀ j k, j ≠ k →
    volume (Tube (4 * G.b) (start j) (direction j) ∩ Tube (4 * G.b) (start k) (direction k)) ≤
      (1 / 2 : ℝ≥0∞) * volume (Tube (4 * G.b) (start j) (direction j))
  measurable : ∀ j, MeasurableSet (shading j)
  shading_tube : ∀ j, shading j ⊆ Tube (4 * G.b) (start j) (direction j)
  shading_cell : ∀ j, shading j ⊆ ⋃ i ∈ G.indices, G.shading i
  density : ∀ j, ENNReal.ofReal (d * (4 * G.b) ^ 2) ≤ volume (shading j)
  fiber_indices : ∀ j, fiber j ⊆ G.indices
  fiber_card : ∀ j, (fiber j).card = multiplicity
  fiber_disjoint : ∀ j k, j ≠ k → Disjoint (fiber j) (fiber k)
  retained : τ * (G.indices.card : ℝ) ≤ (count : ℝ) * (multiplicity : ℝ)
  whole : ∀ j, ∀ i ∈ fiber j, G.body i ⊆ Tube (4 * G.b) (start j) (direction j)

theorem balance_body_cover {n K b : ℕ} {G : AffineCell n K} {d R : ℝ}
    (V : RoundBodyCover G d) (hb : 0 < b) (hR : 1 < R) (hn : (n : ℝ) < R ^ b) :
    Nonempty (BalancedBodyCover G d (netConst / ((b : ℝ) * R))) := by
  obtain ⟨N, q, u, F, hN, hq, hu, hFsub, hFcard, hFdisj, hmass⟩ :=
    WangZahlLot.Obl.wz_weighted_affine_packet_balancing.balanced_fibers
      V.count_pos hb V.fiber V.fiber_nonempty V.fiber_disjoint hR hn
  refine ⟨{
    count := N, multiplicity := q, count_pos := hN, multiplicity_pos := hq,
    start := V.start ∘ u, direction := V.direction ∘ u, fiber := F, shading := V.shading ∘ u,
    unit_direction := fun j => V.unit_direction (u j), bounded := fun j => V.bounded (u j),
    separated := fun j k hne => V.separated _ _ (hu.ne hne),
    measurable := fun j => V.measurable (u j), shading_tube := fun j => V.shading_tube (u j),
    shading_cell := fun j => V.shading_cell (u j), density := fun j => V.density (u j),
    fiber_indices := fun j => (hFsub j).trans (V.fiber_indices (u j)),
    fiber_card := hFcard, fiber_disjoint := hFdisj,
    retained := ?_, whole := fun j i hi => V.whole _ i (hFsub j hi) }⟩
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hR' : 0 < R := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos hb' hR')]
  nlinarith only [V.retained.trans hmass]

theorem balanced_body_slabs {n K : ℕ} {U Y : Fin n → Set Space} {B h d τ : ℝ}
    {G : AffineCell n K} (H : BodyCellValid U Y B h G) (V : BalancedBodyCover G d τ)
    (hh : 0 < h) (hτ : 0 < τ) :
    SlabCount (4 * G.b) (h * τ)⁻¹ V.count V.start V.direction := by
  have hweighted : ∀ (ν : Space) (s r : ℝ), ‖ν‖ = 1 → 0 < r →
      ENNReal.ofReal (Set.ncard {i : Fin n | ∃ j, i ∈ V.fiber j ∧
        Tube (4 * G.b) (V.start j) (V.direction j) ⊆
          ball (0 : Space) 1 ∩ {p | |inner ℝ ν p - s| ≤ r}} : ℝ) ≤
      ENNReal.ofReal (h⁻¹ * (G.indices.card : ℝ)) *
        volume (ball (0 : Space) 1 ∩ {p | |inner ℝ ν p - s| ≤ r}) := by
    intro ν s r hν hr
    apply le_trans _ (H.slabs ν s r hν hr)
    apply ENNReal.ofReal_le_ofReal
    exact_mod_cast (Set.ncard_le_ncard (show
      {i : Fin n | ∃ j, i ∈ V.fiber j ∧ Tube (4 * G.b) (V.start j) (V.direction j) ⊆
        ball (0 : Space) 1 ∩ {p | |inner ℝ ν p - s| ≤ r}} ⊆
      {i : Fin n | i ∈ G.indices ∧ G.body i ⊆
        ball (0 : Space) 1 ∩ {p | |inner ℝ ν p - s| ≤ r}} from by
      rintro i ⟨j, hi, hj⟩
      exact ⟨V.fiber_indices j hi, (V.whole j i hi).trans hj⟩))
  apply WangZahlLot.Obl.wz_weighted_affine_packet_balancing.slab_restrict
    (mul_pos hh hτ) hh V.multiplicity_pos V.start V.direction V.fiber
    id V.fiber (fun _ => Subset.rfl) V.fiber_card V.fiber_disjoint _ hweighted
  nlinarith only [mul_le_mul_of_nonneg_left V.retained hh.le]

end WangZahlLot.Obl.wz_flat_factored_improvement
