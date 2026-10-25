-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.RotationCrossing.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainRotation
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TSGeometry

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, RotationCrossing.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V P T rotatedFrame rotatedFrame_apply rotated_prism)

theorem rotated_tube_mem (R : V ≃ₗᵢ[ℝ] V) (δ : ℝ) (x v p : V) :
    R p ∈ T δ (R x) (R v) ↔ p ∈ T δ x v := by
  constructor
  · intro hp
    obtain ⟨t, ht, hpt⟩ := WangZahlLot.Obl.wz_extremal_lipschitz_grains.exists_param_of_mem_Tube hp
    apply WangZahlLot.Obl.wz_extremal_lipschitz_grains.mem_Tube_of_param ht
    simpa only [← map_smul, ← map_add, ← map_sub, R.norm_map] using hpt
  · intro hp
    obtain ⟨t, ht, hpt⟩ := WangZahlLot.Obl.wz_extremal_lipschitz_grains.exists_param_of_mem_Tube hp
    apply WangZahlLot.Obl.wz_extremal_lipschitz_grains.mem_Tube_of_param ht
    simpa only [← map_smul, ← map_add, ← map_sub, R.norm_map] using hpt

theorem rotated_prism_mem (R e : V ≃ₗᵢ[ℝ] V) (a b c : ℝ) (z p : V) :
    R p ∈ P a b c (R z) (rotatedFrame R e) ↔ p ∈ P a b c z e := by
  simp only [P, WangZahlLot.Obl.wz_clustered_cover_volume_gain.ι, Set.mem_ofPred_eq,
    ← map_sub, rotatedFrame_apply]

theorem rotated_prism_frontier_mem (R e : V ≃ₗᵢ[ℝ] V) (a b c : ℝ) (z p : V) :
    R p ∈ frontier (P a b c (R z) (rotatedFrame R e)) ↔ p ∈ frontier (P a b c z e) := by
  have he : R '' frontier (P a b c z e) = frontier (R '' P a b c z e) :=
    R.toHomeomorph.image_frontier _
  rw [rotated_prism] at he
  rw [← he]
  constructor
  · rintro ⟨q, hq, heq⟩
    exact R.injective heq ▸ hq
  · intro hp
    exact ⟨p, hp, rfl⟩

/-- Exact long-face crossing is invariant under a common spatial rotation. -/
theorem rotated_prism_crossing_iff (R e : V ≃ₗᵢ[ℝ] V) (δ a b c : ℝ) (x v z : V) :
    ((∀ p ∈ T δ (R x) (R v) ∩ frontier (P a b c (R z) (rotatedFrame R e)),
        |rotatedFrame R e (p - R z) 2| = c / 2) ∧
      ∀ t ∈ ({-c / 2, c / 2} : Set ℝ), ∃ p ∈ T δ (R x) (R v) ∩
        P a b c (R z) (rotatedFrame R e), rotatedFrame R e (p - R z) 2 = t) ↔
    ((∀ p ∈ T δ x v ∩ frontier (P a b c z e), |e (p - z) 2| = c / 2) ∧
      ∀ t ∈ ({-c / 2, c / 2} : Set ℝ), ∃ p ∈ T δ x v ∩ P a b c z e, e (p - z) 2 = t) := by
  constructor
  · rintro ⟨hfront, hends⟩
    constructor
    · intro p hp
      have hh := hfront (R p) ⟨(rotated_tube_mem R δ x v p).mpr hp.1,
        (rotated_prism_frontier_mem R e a b c z p).mpr hp.2⟩
      simpa only [← map_sub, rotatedFrame_apply] using hh
    · intro t ht
      obtain ⟨p, hp, he⟩ := hends t ht
      refine ⟨R.symm p, ⟨?_, ?_⟩, ?_⟩
      · exact (rotated_tube_mem R δ x v (R.symm p)).mp (by simpa only [R.apply_symm_apply] using hp.1)
      · exact (rotated_prism_mem R e a b c z (R.symm p)).mp (by simpa only [R.apply_symm_apply] using hp.2)
      · simpa only [rotatedFrame, LinearIsometryEquiv.trans_apply, map_sub, R.symm_apply_apply] using he
  · rintro ⟨hfront, hends⟩
    constructor
    · intro p hp
      have hh := hfront (R.symm p) ⟨(rotated_tube_mem R δ x v (R.symm p)).mp
        (by simpa only [R.apply_symm_apply] using hp.1),
        (rotated_prism_frontier_mem R e a b c z (R.symm p)).mp
          (by simpa only [R.apply_symm_apply] using hp.2)⟩
      simpa only [rotatedFrame, LinearIsometryEquiv.trans_apply, map_sub, R.symm_apply_apply] using hh
    · intro t ht
      obtain ⟨p, hp, he⟩ := hends t ht
      refine ⟨R p, ⟨(rotated_tube_mem R δ x v p).mpr hp.1,
        (rotated_prism_mem R e a b c z p).mpr hp.2⟩, ?_⟩
      simpa only [← map_sub, rotatedFrame_apply] using he

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
