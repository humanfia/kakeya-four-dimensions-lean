-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.BlockTubes.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/BlockTubes.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NormalizedGrainBlocks
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NaturalTubes

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate
  (unit norm_unit norm_smul_unit image_tube_extend)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis inner_boxAxis)
open WangZahlLot.Obl.wz_separated_cover_refinement (enumerate)

noncomputable section

/-- A macroscopic chord in a slab controls the normal component of its
unit direction. -/
theorem chord_unit_normal {x v u : V} {a t : ℝ}
    (ha : 0 ≤ a) (hv : (1 / 4 : ℝ) ≤ ‖v‖)
    (hleft : |inner ℝ u x - t| ≤ a / 2)
    (hright : |inner ℝ u (x + v) - t| ≤ a / 2) :
    |inner ℝ u (unit v)| ≤ 4 * a := by
  have hvpos : 0 < ‖v‖ := by linarith
  have hnormal : |inner ℝ u v| ≤ a := by
    have hh := abs_sub (inner ℝ u (x + v) - t) (inner ℝ u x - t)
    rw [sub_sub_sub_cancel_right, inner_add_right, add_sub_cancel_left] at hh
    rw [inner_add_right] at hright
    linarith
  rw [WangZahlLot.Obl.wz_affine_robust_cluster_estimate.unit,
    inner_smul_right, abs_mul, abs_of_pos (inv_pos.mpr hvpos)]
  calc
    _ ≤ ‖v‖⁻¹ * a := mul_le_mul_of_nonneg_left hnormal (by positivity)
    _ ≤ 4 * a := by
      apply mul_le_mul_of_nonneg_right _ ha
      rw [inv_eq_one_div, div_le_iff₀ hvpos]
      linarith

/-- The short carrier extends to a unit one with the same direction and
radius; the original axis endpoints remain available separately. -/
theorem short_tube_unit_extension {r : ℝ} (x v : V) (hv : v ≠ 0) (hhi : ‖v‖ ≤ 1) :
    T r x v ⊆ T r (x + (1 / 2 : ℝ) • v - (1 / 2 : ℝ) • unit v) (unit v) := by
  have hh := image_tube_extend (AffineEquiv.refl ℝ V).toContinuousAffineEquiv
    x v (unit v) (δ := r) (by norm_num : (0 : ℝ) < 1) (norm_nonneg v) hhi
    (norm_smul_unit hv).symm (fun p q => by simp)
  simpa only [AffineEquiv.coe_toContinuousAffineEquiv, AffineEquiv.coe_refl,
    Set.image_id, one_mul, id_eq, T, WangZahlLot.Obl.wz_affine_robust_cluster_estimate.tube] using hh

namespace ConcentratedGrainData

variable {ω ζ δ ε b ρ c : ℝ} {p n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}

/-- A normalized block has genuine short round-tube models. Their unit
extensions and their common slab direction bounds use the same axes. -/
theorem NormalizedBlock.tube_data
    {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
    {R : Finset (Fin D.L)} (G : D.NormalizedBlock R) (hδ : 0 < δ) :
    ∃ s t : Fin R.card → V,
      (∀ i, (1 / 4 : ℝ) ≤ ‖t i‖ ∧ ‖t i‖ ≤ 1) ∧
      (∀ i, D.normalizedBody R G.affine i ⊆ T (2 * ρ) (s i) (t i)) ∧
      (∀ i, s i ∈ D.normalizedBody R G.affine i ∧ s i + t i ∈ D.normalizedBody R G.affine i) ∧
      (∀ i, ‖unit (t i)‖ = 1) ∧
      (∀ i, D.normalizedBody R G.affine i ⊆
        T (2 * ρ) (s i + (1 / 2 : ℝ) • t i - (1 / 2 : ℝ) • unit (t i)) (unit (t i))) ∧
      (∀ i, |inner ℝ (boxAxis G.frame 0) (unit (t i))| ≤ 4 * G.short) := by
  obtain ⟨ha, hρ, _, hc, _⟩ := D.dimensions hδ
  have hex i := natural_grain_tube_data ha hρ hc D.grains.2.1
    (D.z (enumerate R i)) (D.z G.natural_anchor) (D.e (enumerate R i))
    (D.e G.natural_anchor) G.affine (G.natural_near i) G.coordinates G.inverse_lipschitz
  choose s t hlo hhi hsub hleft hright using hex
  have htne i : t i ≠ 0 := by intro he; have hh := hlo i; rw [he, norm_zero] at hh; norm_num at hh
  refine ⟨s, t, fun i => ⟨hlo i, hhi i⟩, hsub, fun i => ⟨hleft i, hright i⟩,
    fun i => norm_unit (htne i), fun i => (hsub i).trans
      (short_tube_unit_extension (s i) (t i) (htne i) (hhi i)), ?_⟩
  intro i
  apply chord_unit_normal (x := s i) G.short_pos.le (hlo i)
    (t := inner ℝ (boxAxis G.frame 0) G.center)
  · have hh := (G.enclosure i (hleft i)).1
    change |G.frame (s i - G.center) 0| ≤ G.short / 2 at hh
    simpa only [map_sub, PiLp.sub_apply, inner_boxAxis] using hh
  · have hh := (G.enclosure i (hright i)).1
    change |G.frame (s i + t i - G.center) 0| ≤ G.short / 2 at hh
    simpa only [map_sub, PiLp.sub_apply, inner_boxAxis] using hh

end ConcentratedGrainData
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
