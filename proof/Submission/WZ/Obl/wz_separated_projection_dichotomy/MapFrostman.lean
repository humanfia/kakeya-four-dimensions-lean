-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.MapFrostman.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.IndexedGeometry
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Anisotropic

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

/-- A map which does not decrease distances preserves the Frostman counting
condition, with a factor two allowing a center in the indexed family. -/
theorem IndexedFrostman.map_expanding {I : Type*} [Fintype I] {f : I → Plane}
    {δ C : ℝ} (hF : IndexedFrostman δ C f) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (φ : Plane → Plane) (hφ : ∀ x y, dist x y ≤ dist (φ x) (φ y)) :
    IndexedFrostman δ (2 * C) (fun i => φ (f i)) := by
  classical
  intro x r hδr
  have hr : 0 ≤ r := hδ.trans hδr
  have hcount := hF.card_of_diameter
    (Finset.univ.filter (fun i => dist (φ (f i)) x ≤ r)) hC (by positivity : 0 ≤ 2 * r)
    (by linarith : δ ≤ 2 * r) (by
      intro i hi j hj
      have hi' := (Finset.mem_filter.mp hi).2
      have hj' := (Finset.mem_filter.mp hj).2
      calc dist (f i) (f j) ≤ dist (φ (f i)) (φ (f j)) := hφ _ _
        _ ≤ dist (φ (f i)) x + dist (φ (f j)) x := dist_triangle_right _ _ _
        _ ≤ 2 * r := by linarith)
  convert hcount using 1 <;> ring

theorem ClosedFiniteFrostman.map_expanding {δ C : ℝ} {S : Finset Plane}
    (hF : ClosedFiniteFrostman δ C S) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (φ : Plane → Plane) (hφ : ∀ x y, dist x y ≤ dist (φ x) (φ y)) :
    ClosedFiniteFrostman δ (2 * C) (S.image φ) := by
  classical
  have hinj : Function.Injective φ := by
    intro x y hxy
    have h := hφ x y
    rw [hxy, dist_self] at h
    exact dist_eq_zero.mp (le_antisymm h dist_nonneg)
  have hf := hF.indexed.map_expanding hδ hC φ hφ
  intro x r hδr
  have heq : (Finset.univ.filter (fun y : S => dist (φ y) x ≤ r)).card =
      ((S.image φ).filter (fun y => dist y x ≤ r)).card := by
    have himg : (S.image φ).filter (fun y => dist y x ≤ r) =
        (S.filter (fun y => dist (φ y) x ≤ r)).image φ := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, hdist⟩
        exact ⟨z, ⟨hz, hdist⟩, rfl⟩
      · rintro ⟨z, ⟨hz, hdist⟩, rfl⟩
        exact ⟨⟨z, hz, rfl⟩, hdist⟩
    rw [himg, Finset.card_image_of_injective _ hinj]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_coe_sort S (fun y => if dist (φ y) x ≤ r then (1 : ℕ) else 0)
  have hh := hf x r hδr
  rw [heq, Fintype.card_coe] at hh
  rw [Finset.card_image_of_injective _ hinj]
  convert hh using 1
  congr 1
  rw [← Set.ncard_coe_finset]
  congr 1
  ext y
  simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_inter_iff, Metric.mem_closedBall]

theorem ClosedFiniteFrostman.anisotropic {δ C : ℝ} {S : Finset Plane}
    (hF : ClosedFiniteFrostman δ C S) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    {e : Plane} (he : ‖e‖ = 1) {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ClosedFiniteFrostman δ (2 * C) (S.image (anisotropicMap e p q)) :=
  hF.map_expanding hδ hC _ (anisotropicMap_dist_lower he hp hq)

end WangZahlLot.Obl.wz_separated_projection_dichotomy
