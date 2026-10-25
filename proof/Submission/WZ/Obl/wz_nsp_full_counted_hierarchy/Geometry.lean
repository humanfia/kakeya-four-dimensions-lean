-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_tower_convex_count_composition.Containment
import Submission.WZ.Obl.wz_frostman_rigid_copies_volume

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

open Set Metric LeanEval.Analysis.WangZahlKakeya

abbrev Tube (r : ℝ) (x v : Space) : Set Space :=
  thickening r (segment ℝ x (x + v))

/-- Two unit-segment containers with a common fine descendant become nested
when the coarser radius is enlarged by four times the finer radius. -/
theorem common_descendant_nesting {δ r s : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    {x v y w z u : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hsmall : Tube δ x v ⊆ Tube s y w)
    (hlarge : Tube δ x v ⊆ Tube r z u) :
    Tube s y w ⊆ Tube (r + 4 * s) z u := by
  have h := WangZahlLot.Obl.wz_tower_convex_count_composition.parent_subset_thickening
    hs hδ hv hw ((convex_segment z (z + u)).thickening r) hlarge hsmall
  exact h.trans (by simpa only [Tube, add_comm] using
    thickening_thickening_subset (4 * s) r (segment ℝ z (z + u)))

/-- The defining formula for a tube commutes with every rigid motion. -/
theorem rigid_tube_image (A : Space ≃ᵃⁱ[ℝ] Space) (r : ℝ) (x v : Space) :
    A '' Tube r x v = Tube r (A x) (A.linear v) := by
  apply Set.Subset.antisymm
  · exact WangZahlLot.Obl.wz_frostman_rigid_copies_volume.affine_tube_image_subset A r x v
  · intro p hp
    obtain ⟨z, hz, hpz⟩ := mem_thickening_iff.mp hp
    have hseg : A '' segment ℝ x (x + v) =
        segment ℝ (A x) (A x + A.linear v) := by
      have h := image_segment ℝ A.toAffineEquiv.toAffineMap x (x + v)
      change A '' segment ℝ x (x + v) = segment ℝ (A x) (A (x + v)) at h
      have he : A (x + v) = A x + A.linear v := by
        simpa only [vadd_eq_add, add_comm, AffineIsometryEquiv.coe_toAffineEquiv] using
          A.toAffineEquiv.map_vadd x v
      rwa [he] at h
    rw [← hseg] at hz
    obtain ⟨q, hq, rfl⟩ := hz
    refine ⟨A.symm p, mem_thickening_iff.mpr ⟨q, hq, ?_⟩, A.apply_symm_apply p⟩
    have he := A.dist_map (A.symm p) q
    rw [A.apply_symm_apply] at he
    rwa [← he]

/-- Motion bounded on the original core consumes the same amount of radius buffer. -/
theorem moved_tube_subset {r t : ℝ} (A : Space ≃ᵃⁱ[ℝ] Space) (x v : Space)
    (hmove : ∀ p ∈ segment ℝ x (x + v), ‖A p - p‖ ≤ t) :
    Tube r (A x) (A.linear v) ⊆ Tube (r + t) x v := by
  rw [← rigid_tube_image]
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  refine mem_thickening_iff.mpr ⟨q, hq, ?_⟩
  have hd := dist_triangle (A p) (A q) q
  have hm : dist (A q) q ≤ t := by simpa only [dist_eq_norm] using hmove q hq
  rw [A.dist_map] at hd
  linarith

/-- A displacement bound on the unit ball applies to every core whose tube is
contained in that ball. -/
theorem moved_tube_subset_of_ball {r t : ℝ} (hr : 0 < r)
    (A : Space ≃ᵃⁱ[ℝ] Space) (x v : Space)
    (hball : Tube r x v ⊆ ball 0 1)
    (hmove : ∀ p : Space, ‖p‖ < 1 → ‖A p - p‖ ≤ t) :
    Tube r (A x) (A.linear v) ⊆ Tube (r + t) x v := by
  apply moved_tube_subset
  intro p hp
  exact hmove p (by simpa using hball (self_subset_thickening hr _ hp))

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
