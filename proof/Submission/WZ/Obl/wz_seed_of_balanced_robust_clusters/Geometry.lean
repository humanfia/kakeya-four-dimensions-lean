-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
namespace WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters

open Set Metric MeasureTheory
open scoped ENNReal

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Tube (δ : ℝ) (x v : Space) : Set Space := thickening δ (segment ℝ x (x + v))
abbrev Cylinder (r : ℝ) (z w : Space) : Set Space :=
  thickening r (segment ℝ z (z + (6 : ℝ) • w))
abbrev Slab (u : Space) (t r : ℝ) : Set Space :=
  ball (0 : Space) 1 ∩ {p | |inner ℝ u p - t| ≤ r}

lemma exists_basis_first {u : Space} (hu : ‖u‖ = 1) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ Space, b 0 = u := by
  have ho : Orthonormal ℝ (({0} : Set (Fin 3)).domRestrict (fun _ => u)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subtype.ext (by simpa using i.property.trans j.property.symm)
    subst j
    simp [Set.domRestrict, hu]
  obtain ⟨b, hb⟩ := ho.exists_orthonormalBasis_extension_of_card_eq
    (by simp [Space])
  exact ⟨b, hb 0 (by simp)⟩

lemma coordinate_box_volume (b : OrthonormalBasis (Fin 3) ℝ Space) (z : Space)
    (a c : Fin 3 → ℝ) :
    volume {p : Space | ∀ i, a i ≤ b.repr (p - z) i ∧ b.repr (p - z) i ≤ c i} =
      ∏ i, ENNReal.ofReal (c i - a i) := by
  have hm : MeasurePreserving (fun p : Space => WithLp.ofLp (b.repr (p - z))) :=
    (PiLp.volume_preserving_ofLp (Fin 3)).comp
      (b.measurePreserving_repr.comp (measurePreserving_sub_right volume z))
  have he : {p : Space | ∀ i, a i ≤ b.repr (p - z) i ∧ b.repr (p - z) i ≤ c i} =
      (fun p : Space => WithLp.ofLp (b.repr (p - z))) ⁻¹' Icc a c := by
    ext p
    simp only [mem_ofPred_eq, mem_preimage, mem_Icc, Pi.le_def]
    exact forall_and
  rw [he, hm.measure_preimage measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]

lemma slab_volume_le {u : Space} (hu : ‖u‖ = 1) (t r : ℝ) (hr : 0 ≤ r) :
    volume (Slab u t r) ≤ ENNReal.ofReal (8 * r) := by
  classical
  obtain ⟨b, hb⟩ := exists_basis_first hu
  let a : Fin 3 → ℝ := fun i => if i = 0 then t - r else -1
  let c : Fin 3 → ℝ := fun i => if i = 0 then t + r else 1
  calc
    volume (Slab u t r) ≤ volume {p : Space | ∀ i,
        a i ≤ b.repr (p - 0) i ∧ b.repr (p - 0) i ≤ c i} := by
      apply measure_mono
      intro p hp i
      have hn : ‖p‖ < 1 := by simpa using hp.1
      simp only [sub_zero, OrthonormalBasis.repr_apply_apply]
      by_cases hi : i = 0
      · subst i
        simpa [a, c, hb, abs_le, sub_le_iff_le_add, sub_le_iff_le_add', add_comm] using hp.2
      · have hinner := abs_real_inner_le_norm (b i) p
        rw [b.norm_eq_one i, one_mul] at hinner
        have h := (abs_le.mp (hinner.trans hn.le))
        simpa [a, c, hi] using h
    _ = ENNReal.ofReal (8 * r) := by
      rw [coordinate_box_volume]
      simp [a, c, Fin.prod_univ_succ, ENNReal.ofReal_add hr hr]
      norm_num
      ring

lemma exists_unit_perp {w : Space} (hw : ‖w‖ = 1) :
    ∃ u : Space, ‖u‖ = 1 ∧ inner ℝ u w = 0 := by
  obtain ⟨b, hb⟩ := exists_basis_first hw
  refine ⟨b 1, b.norm_eq_one 1, ?_⟩
  rw [← hb, orthonormal_iff_ite.mp b.orthonormal]
  norm_num

lemma cylinder_subset_slab {u w : Space} (hu : ‖u‖ = 1)
    (huw : inner ℝ u w = 0) (z : Space) (r : ℝ) :
    Cylinder r z w ⊆ {p | |inner ℝ u p - inner ℝ u z| ≤ r} := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨a, ha, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq
  have he : inner ℝ u p - inner ℝ u z =
      inner ℝ u (p - (z + a • ((6 : ℝ) • w))) := by
    simp [inner_sub_right, inner_add_right, inner_smul_right, huw]
  rw [mem_ofPred_eq, he]
  exact (abs_real_inner_le_norm _ _).trans
    (by simpa [hu, dist_eq_norm] using hpq.le)

lemma tube_subset_slab {u v : Space} (hu : ‖u‖ = 1)
    (huv : inner ℝ u v = 0) (x : Space) (δ : ℝ) :
    Tube δ x v ⊆ {p | |inner ℝ u p - inner ℝ u x| ≤ δ} := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨a, ha, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq
  have he : inner ℝ u p - inner ℝ u x = inner ℝ u (p - (x + a • v)) := by
    simp [inner_sub_right, inner_add_right, inner_smul_right, huv]
  rw [mem_ofPred_eq, he]
  exact (abs_real_inner_le_norm _ _).trans
    (by simpa [hu, dist_eq_norm] using hpq.le)

lemma cylinder_coordinates (b : OrthonormalBasis (Fin 3) ℝ Space) (z : Space)
    {r : ℝ} {p : Space} (hp : p ∈ Cylinder r z (b 0)) (i : Fin 3) :
    |b.repr (p - z) i| ≤ if i = 0 then 6 + r else r := by
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨a, ha, rfl⟩ := hq
  simp only [add_sub_cancel_left, dist_eq_norm] at hpq
  have hq : inner ℝ (b i) (a • ((6 : ℝ) • b 0)) = if i = 0 then 6 * a else 0 := by
    simp only [inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]
    split_ifs <;> ring
  have he : p - z = (p - (z + a • ((6 : ℝ) • b 0))) + a • ((6 : ℝ) • b 0) := by
    module
  rw [OrthonormalBasis.repr_apply_apply, he, inner_add_right, hq]
  have hi := abs_real_inner_le_norm (b i) (p - (z + a • ((6 : ℝ) • b 0)))
  rw [b.norm_eq_one, one_mul] at hi
  by_cases h : i = 0
  · simp only [h, ite_true] at *
    have h6 : |6 * a| ≤ 6 := by
      rw [abs_of_nonneg (mul_nonneg (by norm_num) ha.1)]
      linarith [ha.2]
    exact (abs_add_le _ _).trans (by linarith)
  · simpa [h] using hi.trans hpq.le

lemma cylinder_volume_le {w : Space} (hw : ‖w‖ = 1) (z : Space)
    {r : ℝ} (hr : 0 ≤ r) :
    volume (Cylinder r z w) ≤ ENNReal.ofReal (8 * (6 + r) * r ^ 2) := by
  classical
  obtain ⟨b, hb⟩ := exists_basis_first hw
  let c : Fin 3 → ℝ := fun i => if i = 0 then 6 + r else r
  calc
    volume (Cylinder r z w) ≤ volume {p : Space | ∀ i,
        -c i ≤ b.repr (p - z) i ∧ b.repr (p - z) i ≤ c i} := by
      apply measure_mono
      intro p hp i
      exact abs_le.mp (cylinder_coordinates b z (by simpa [hb] using hp) i)
    _ = ENNReal.ofReal (8 * (6 + r) * r ^ 2) := by
      rw [coordinate_box_volume]
      simp only [Fin.prod_univ_three, c, Fin.isValue, ↓reduceIte, sub_neg_eq_add]
      simp only [show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide, ite_false]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

lemma cylinder_scaled_volume_le {w : Space} (hw : ‖w‖ = 1) (z : Space)
    {C θ : ℝ} (hC : 0 ≤ C) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    volume (Cylinder (C * θ) z w) ≤
      ENNReal.ofReal ((8 * (6 + C) * C ^ 2) * θ ^ 2) := by
  apply (cylinder_volume_le hw z (mul_nonneg hC hθ)).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    8 * (6 + C * θ) * (C * θ) ^ 2 ≤ 8 * (6 + C) * (C * θ) ^ 2 := by
      gcongr
      exact mul_le_of_le_one_right hC hθ1
    _ = _ := by ring

end WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters
