-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_translation_model.Counting.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_translation_model.Geometry

namespace WangZahlLot.Obl.wz_nsp_translation_model

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

lemma ncard_eq_sum {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (ncard {i | p i} : ℝ) = ∑ i, if p i then 1 else 0 := by
  classical
  rw [ncard_eq_toFinset_card, Finset.sum_boole]
  simp

lemma ncard_prod_sum {α β : Type*} [Fintype α] [Fintype β] (p : α → β → Prop) :
    (ncard {q : α × β | p q.1 q.2} : ℝ) =
      ∑ a, (ncard {b : β | p a b} : ℝ) := by
  classical
  simp only [ncard_eq_sum, Fintype.sum_prod_type]

lemma tube_translate (r : ℝ) (x v t : Space) :
    Tube r (x + t) v = (fun p : Space => p + t) '' Tube r x v := by
  ext p
  constructor
  · intro hp
    obtain ⟨y, hy, hpy⟩ := mem_thickening_iff.mp hp
    rw [segment_eq_image'] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    refine ⟨p - t, mem_thickening_iff.mpr ⟨x + a • v, ?_, ?_⟩, sub_add_cancel _ _⟩
    · rw [segment_eq_image']
      exact ⟨a, ha, by simp⟩
    · convert hpy using 1
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      module
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨y, hy, hzy⟩ := mem_thickening_iff.mp hz
    rw [segment_eq_image'] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    refine mem_thickening_iff.mpr ⟨x + t + a • v, ?_, ?_⟩
    · rw [segment_eq_image']
      exact ⟨a, ha, by simp⟩
    · convert hzy using 1
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      module

lemma translated_ball {r ρ : ℝ} (hρ1 : ρ ≤ 1) {x v t : Space}
    (ht : ‖t‖ ≤ ρ) (hball : Tube r x v ⊆ ball (0 : Space) 1) :
    Tube r (x + t) v ⊆ ball (0 : Space) 2 := by
  rw [tube_translate]
  rintro _ ⟨p, hp, rfl⟩
  have hn : ‖p‖ < 1 := mem_ball_zero_iff.mp (hball hp)
  exact mem_ball_zero_iff.mpr ((norm_add_le _ _).trans_lt (by linarith))

lemma translated_count {r L : ℝ} {K n : ℕ}
    (x v : Fin n → Space) (g : Fin n → Fin K)
    (hcount : ∀ (k : Fin K) (W : Set Space), Convex ℝ W →
      ENNReal.ofReal ((ncard {i : Fin n | g i = k ∧ Tube r (x i) (v i) ⊆ W} : ℝ) * r ^ 2)
        ≤ ENNReal.ofReal L * volume W)
    (k : Fin K) (W : Set Space) (hW : Convex ℝ W) (t : Space) :
    ENNReal.ofReal ((ncard {i : Fin n | g i = k ∧ Tube r (x i + t) (v i) ⊆ W} : ℝ) * r ^ 2)
      ≤ ENNReal.ofReal L * volume W := by
  have hc := hcount k ((fun p : Space => p + t) ⁻¹' W)
    (hW.affine_preimage (AffineEquiv.vaddConst ℝ t).toAffineMap)
  simpa only [tube_translate, image_subset_iff, measure_preimage_add_right] using hc

lemma sum_counts_swap {K n m : ℕ} (g : Fin n → Fin K)
    (p : Fin m → Fin n → Prop) (k : Fin K) :
    (∑ s, (ncard {i : Fin n | g i = k ∧ p s i} : ℝ)) =
      ∑ i, if g i = k then (ncard {s : Fin m | p s i} : ℝ) else 0 := by
  classical
  simp only [ncard_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hg : g i = k <;> simp [hg]

lemma group_average {r ρ M : ℝ}
    {K n m : ℕ} (t : Fin m → Space) (x v : Fin n → Space) (g : Fin n → Fin K)
    (hgroup : ∀ k, (ncard {i : Fin n | g i = k} : ℝ) ≤ M)
    (hv : ∀ i, ‖v i‖ = 1)
    (havg : ∀ (x v : Space), ‖v‖ = 1 → ∀ W : Set Space, volume W ≠ ⊤ →
      (ncard {s : Fin m | Tube r (x + t s) v ⊆ W} : ℝ) * ρ ^ 2 ≤
        4096 * (m : ℝ) * volume.real W)
    (k : Fin K) (W : Set Space) (hW : volume W ≠ ⊤) :
    (∑ s, (ncard {i : Fin n | g i = k ∧ Tube r (x i + t s) (v i) ⊆ W} : ℝ)) * ρ ^ 2
      ≤ 4096 * (m : ℝ) * M * volume.real W := by
  classical
  rw [sum_counts_swap, Finset.sum_mul]
  calc
    _ ≤ ∑ i : Fin n, if g i = k then 4096 * (m : ℝ) * volume.real W else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hg : g i = k
      · simpa only [ite_eq_left hg] using havg (x i) (v i) (hv i) W hW
      · simp [hg]
    _ = (ncard {i : Fin n | g i = k} : ℝ) * (4096 * (m : ℝ) * volume.real W) := by
      rw [ncard_eq_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> simp
    _ ≤ M * (4096 * (m : ℝ) * volume.real W) := by
      exact mul_le_mul_of_nonneg_right (hgroup k) (by positivity)
    _ = 4096 * (m : ℝ) * M * volume.real W := by ring

end WangZahlLot.Obl.wz_nsp_translation_model
