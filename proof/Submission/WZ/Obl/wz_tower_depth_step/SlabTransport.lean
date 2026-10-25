-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_tower_depth_step.SlabTransport.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_tower_depth_step.CountTransport

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_tower_depth_step

open Set Metric MeasureTheory Module

abbrev Slab (u : Space) (t ρ : ℝ) : Set Space := {p | |inner ℝ u p - t| ≤ ρ}

/-- Two small contractions about a point in a slab compare slab sections of different bodies. -/
theorem slab_volume_compare_nine {U V : Set Space} {p u : Space} {t ρ : ℝ}
    (hρ : 0 < ρ) (hp : p ∈ Slab u t ρ)
    (hpos : AffineMap.homothety p (1 / 10 : ℝ) '' U ⊆ V)
    (hneg : AffineMap.homothety p (-1 / 10 : ℝ) '' U ⊆ V) :
    volume (U ∩ Slab u t (9 * ρ)) ≤ (2000 : ENNReal) * volume (V ∩ Slab u t ρ) := by
  let A := U ∩ Slab u t (9 * ρ) ∩ {q | 0 ≤ inner ℝ u (q - p)}
  let B := U ∩ Slab u t (9 * ρ) ∩ {q | inner ℝ u (q - p) ≤ 0}
  have hcover : U ∩ Slab u t (9 * ρ) ⊆ A ∪ B := by
    intro q hq
    rcases le_total 0 (inner ℝ u (q - p)) with h | h
    · exact Or.inl ⟨hq, h⟩
    · exact Or.inr ⟨hq, h⟩
  have hscaled (X : Set Space) (lam : ℝ) (hlam : lam = 1 / 10 ∨ lam = -1 / 10)
      (hX : AffineMap.homothety p lam '' X ⊆ V ∩ Slab u t ρ) :
      volume X ≤ (1000 : ENNReal) * volume (V ∩ Slab u t ρ) := by
    have h := mul_le_mul' (le_refl (1000 : ENNReal)) (measure_mono (μ := volume) hX)
    rw [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin] at h
    rcases hlam with rfl | rfl <;> norm_num [← mul_assoc, ENNReal.ofReal_div_of_pos] at h ⊢ <;>
      simpa only [ENNReal.mul_inv_cancel (by norm_num : (1000 : ENNReal) ≠ 0) (by norm_num : (1000 : ENNReal) ≠ ⊤), one_mul] using h
  have hp' := abs_le.mp (show |inner ℝ u p - t| ≤ ρ from hp)
  have hformula (lam : ℝ) (q : Space) :
      inner ℝ u (AffineMap.homothety p lam q) - t =
        inner ℝ u p - t + lam * inner ℝ u (q - p) := by
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, inner_add_right,
      inner_smul_right]
    ring
  have hboth : volume A ≤ (1000 : ENNReal) * volume (V ∩ Slab u t ρ) ∧
      volume B ≤ (1000 : ENNReal) * volume (V ∩ Slab u t ρ) := by
    by_cases hs : 0 ≤ inner ℝ u p - t
    · constructor
      · apply hscaled A (-1 / 10) (Or.inr rfl)
        rintro z ⟨q, hq, rfl⟩
        refine ⟨hneg ⟨q, hq.1.1, rfl⟩, ?_⟩
        rw [Slab, mem_ofPred_eq, hformula, abs_le]
        have hq' := abs_le.mp (show |inner ℝ u q - t| ≤ 9 * ρ from hq.1.2)
        have hd : 0 ≤ inner ℝ u (q - p) := hq.2
        rw [inner_sub_right] at hd ⊢
        constructor <;> linarith [hq'.1, hq'.2, hp'.1, hp'.2]
      · apply hscaled B (1 / 10) (Or.inl rfl)
        rintro z ⟨q, hq, rfl⟩
        refine ⟨hpos ⟨q, hq.1.1, rfl⟩, ?_⟩
        rw [Slab, mem_ofPred_eq, hformula, abs_le]
        have hq' := abs_le.mp (show |inner ℝ u q - t| ≤ 9 * ρ from hq.1.2)
        have hd : inner ℝ u (q - p) ≤ 0 := hq.2
        rw [inner_sub_right] at hd ⊢
        constructor <;> linarith [hq'.1, hq'.2, hp'.1, hp'.2]
    · constructor
      · apply hscaled A (1 / 10) (Or.inl rfl)
        rintro z ⟨q, hq, rfl⟩
        refine ⟨hpos ⟨q, hq.1.1, rfl⟩, ?_⟩
        rw [Slab, mem_ofPred_eq, hformula, abs_le]
        have hq' := abs_le.mp (show |inner ℝ u q - t| ≤ 9 * ρ from hq.1.2)
        have hd : 0 ≤ inner ℝ u (q - p) := hq.2
        rw [inner_sub_right] at hd ⊢
        constructor <;> linarith [hq'.1, hq'.2, hp'.1, hp'.2]
      · apply hscaled B (-1 / 10) (Or.inr rfl)
        rintro z ⟨q, hq, rfl⟩
        refine ⟨hneg ⟨q, hq.1.1, rfl⟩, ?_⟩
        rw [Slab, mem_ofPred_eq, hformula, abs_le]
        have hq' := abs_le.mp (show |inner ℝ u q - t| ≤ 9 * ρ from hq.1.2)
        have hd : inner ℝ u (q - p) ≤ 0 := hq.2
        rw [inner_sub_right] at hd ⊢
        constructor <;> linarith [hq'.1, hq'.2, hp'.1, hp'.2]
  calc
    _ ≤ volume (A ∪ B) := measure_mono hcover
    _ ≤ volume A + volume B := measure_union_le _ _
    _ ≤ 1000 * volume (V ∩ Slab u t ρ) + 1000 * volume (V ∩ Slab u t ρ) :=
      add_le_add hboth.1 hboth.2
    _ = _ := by rw [← add_mul]; norm_num

/-- Threefold slab widening is a special case of the buffered comparison. -/
theorem slab_volume_compare {U V : Set Space} {p u : Space} {t ρ : ℝ}
    (hρ : 0 < ρ) (hp : p ∈ Slab u t ρ)
    (hpos : AffineMap.homothety p (1 / 10 : ℝ) '' U ⊆ V)
    (hneg : AffineMap.homothety p (-1 / 10 : ℝ) '' U ⊆ V) :
    volume (U ∩ Slab u t (3 * ρ)) ≤ (2000 : ENNReal) * volume (V ∩ Slab u t ρ) := by
  apply (measure_mono (μ := volume) (Set.inter_subset_inter_right U ?_)).trans
    (slab_volume_compare_nine hρ hp hpos hneg)
  intro q hq
  change |inner ℝ u q - t| ≤ 9 * ρ
  exact le_trans hq (by linarith)

/-- A moved unit tube inside a slab puts its original tube in a slab three times as wide. -/
lemma axial_translate_slab_bounded {s a t ρ H : ℝ} (hs : 0 < s) (ha : |a| ≤ H)
    {x v u : Space} (hsub : Tube s (x + a • v) v ⊆ Slab u t ρ) :
    Tube s x v ⊆ Slab u t ((1 + 2 * H) * ρ) := by
  have h₀ := hsub (self_subset_thickening hs _ (left_mem_segment ℝ _ _))
  have h₁ := hsub (self_subset_thickening hs _ (right_mem_segment ℝ _ _))
  change |inner ℝ u (x + a • v) - t| ≤ ρ at h₀
  change |inner ℝ u (x + a • v + v) - t| ≤ ρ at h₁
  have hv : |inner ℝ u v| ≤ 2 * ρ := by
    have h := abs_sub (inner ℝ u (x + a • v + v) - t)
      (inner ℝ u (x + a • v) - t)
    rw [inner_add_right u (x + a • v) v] at h h₁
    have he : inner ℝ u (x + a • v) + inner ℝ u v - t -
        (inner ℝ u (x + a • v) - t) = inner ℝ u v := by ring
    rw [he] at h
    exact h.trans (by linarith)
  intro p hp
  have hh := hsub (mem_tube_axial_translate hp)
  have he : inner ℝ u p - t =
      (inner ℝ u (p + a • v) - t) - a * inner ℝ u v := by
    rw [inner_add_right, inner_smul_right]
    ring
  change |inner ℝ u p - t| ≤ (1 + 2 * H) * ρ
  rw [he]
  have hh' : |inner ℝ u (p + a • v) - t| ≤ ρ := hh
  calc
    _ ≤ |inner ℝ u (p + a • v) - t| + |a * inner ℝ u v| := abs_sub _ _
    _ ≤ ρ + H * (2 * ρ) := by
      rw [abs_mul]
      exact add_le_add hh' (mul_le_mul ha hv (abs_nonneg _) ((abs_nonneg a).trans ha))
    _ = _ := by ring

/-- The unit-displacement version of the slab transfer. -/
lemma axial_translate_slab {s a t ρ : ℝ} (hs : 0 < s) (ha : |a| ≤ 1)
    {x v u : Space} (hsub : Tube s (x + a • v) v ⊆ Slab u t ρ) :
    Tube s x v ⊆ Slab u t (3 * ρ) := by
  simpa only [show (1 + 2 * (1 : ℝ)) = 3 by norm_num] using
    axial_translate_slab_bounded hs ha hsub

/-- A point in the new unit parent is a center for both small contractions of the old doubled parent. -/
theorem doubled_parent_contractions {r R b lam : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hb : |b| ≤ 3) (hlam : lam = 1 / 10 ∨ lam = -1 / 10) {y w p : Space}
    (hp : p ∈ Tube R (y + b • w) w) :
    AffineMap.homothety p lam '' Tube (2 * r) (y - (1 / 2 : ℝ) • w) (2 • w) ⊆
      Tube (2 * R) (y + b • w - (1 / 2 : ℝ) • w) (2 • w) := by
  obtain ⟨z, hz, hpz⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  simp only [add_sub_cancel_left] at hpz
  let e := p - (y + b • w + t • w)
  have he : ‖e‖ < R := by simpa [e, dist_eq_norm] using hpz
  rintro q ⟨z, hz, rfl⟩
  obtain ⟨z₀, hz₀, hzz₀⟩ := mem_thickening_iff.mp hz
  rw [segment_eq_image'] at hz₀
  obtain ⟨a, ha, rfl⟩ := hz₀
  simp only [add_sub_cancel_left] at hzz₀
  let f := z - (y - (1 / 2 : ℝ) • w + a • (2 • w))
  have hf : ‖f‖ < 2 * r := by simpa [f, dist_eq_norm] using hzz₀
  let c := (1 - lam) * t + lam * (-1 / 2 + 2 * a - b)
  have hc : -(1 / 2) ≤ c ∧ c ≤ 3 / 2 := by
    have hb' := abs_le.mp hb
    dsimp [c]
    rcases hlam with rfl | rfl <;> constructor <;> nlinarith [ht.1, ht.2, ha.1, ha.2, hb'.1, hb'.2]
  apply mem_thickening_iff.mpr
  refine ⟨y + b • w + c • w, ?_, ?_⟩
  · rw [segment_eq_image']
    refine ⟨(c + 1 / 2) / 2, ⟨by linarith [hc.1], by linarith [hc.2]⟩, ?_⟩
    module
  · rw [dist_eq_norm]
    have heq : AffineMap.homothety p lam z - (y + b • w + c • w) =
        (1 - lam) • e + lam • f := by
      simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
      dsimp [e, f, c]
      module
    rw [heq]
    calc
      _ ≤ ‖(1 - lam) • e‖ + ‖lam • f‖ := norm_add_le _ _
      _ = |1 - lam| * ‖e‖ + |lam| * ‖f‖ := by simp only [norm_smul, Real.norm_eq_abs]
      _ < 2 * R := by
        rcases hlam with rfl | rfl <;> norm_num <;> linarith

/-- Slab sections remain comparable after a bounded axial move and an enlargement of the parent. -/
theorem shifted_parent_slab_volume {r R b t ρ : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hb : |b| ≤ 3) (hρ : 0 < ρ) {y w p u : Space}
    (hp : p ∈ Tube R (y + b • w) w) (hps : p ∈ Slab u t ρ) :
    volume (Tube (2 * r) (y - (1 / 2 : ℝ) • w) (2 • w) ∩ Slab u t (3 * ρ)) ≤
      (2000 : ENNReal) *
        volume (Tube (2 * R) (y + b • w - (1 / 2 : ℝ) • w) (2 • w) ∩ Slab u t ρ) :=
  slab_volume_compare hρ hps
    (doubled_parent_contractions hr hrR hb (Or.inl rfl) hp)
    (doubled_parent_contractions hr hrR hb (Or.inr rfl) hp)

end WangZahlLot.Obl.wz_tower_depth_step
