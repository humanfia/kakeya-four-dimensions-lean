-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.Equivariance.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Geometry

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- Reindexing a finite family preserves counts of every predicate. -/
theorem ncard_equiv {α β : Type*} (e : α ≃ β) (P : β → Prop) :
    Set.ncard {i | P (e i)} = Set.ncard {i | P i} := by
  apply Set.ncard_congr (fun i _ => e i) (fun _ hi => hi)
  · intro i j _ _ hij
    exact e.injective hij
  · intro j hj
    refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
    change P (e (e.symm j))
    rw [e.apply_symm_apply]
    exact hj

/-- A rigid motion preserves a convex counting estimate, also within any fixed
subset of the index set. -/
theorem rigid_convex_counts {ι : Type*} {r L : ℝ} (x v : ι → Space)
    (P : ι → Prop) (A : Space ≃ᵃⁱ[ℝ] Space)
    (h : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal ((Set.ncard {i | P i ∧ Tube r (x i) (v i) ⊆ W} : ℝ) * r ^ 2) ≤
        ENNReal.ofReal L * volume W) :
    ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal ((Set.ncard {i | P i ∧ Tube r (A (x i)) (A.linear (v i)) ⊆ W} : ℝ) * r ^ 2) ≤
        ENNReal.ofReal L * volume W := by
  intro W hW
  have hpre : Convex ℝ (A ⁻¹' W) := hW.affine_preimage A.toAffineEquiv.toAffineMap
  have hvol : volume (A ⁻¹' W) = volume W :=
    (WangZahlLot.Obl.wz_frostman_rigid_copies_volume.affine_measurePreserving A).measure_preimage_emb
      A.toHomeomorph.measurableEmbedding W
  have he : {i | P i ∧ Tube r (A (x i)) (A.linear (v i)) ⊆ W} =
      {i | P i ∧ Tube r (x i) (v i) ⊆ A ⁻¹' W} := by
    ext i
    simp only [Set.mem_ofPred_eq, ← rigid_tube_image, Set.image_subset_iff]
  rw [he, ← hvol]
  exact h (A ⁻¹' W) hpre

/-- Rigid images of unit directions are still unit directions. -/
theorem rigid_unit (A : Space ≃ᵃⁱ[ℝ] Space) {v : Space} (hv : ‖v‖ = 1) :
    ‖A.linear v‖ = 1 := by
  change ‖A.linearIsometryEquiv v‖ = 1
  simpa using hv

/-- Apply a common outer motion to an assigned containment. -/
theorem rigid_containment (A : Space ≃ᵃⁱ[ℝ] Space) {r s : ℝ}
    {x v y w : Space} (h : Tube r x v ⊆ Tube s y w) :
    Tube r (A x) (A.linear v) ⊆ Tube s (A y) (A.linear w) := by
  rw [← rigid_tube_image, ← rigid_tube_image]
  exact Set.image_mono h

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
