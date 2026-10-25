-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_off_stem_brush_overlap.Counts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_off_stem_brush_overlap.Geometry

namespace WangZahlLot.Obl.wz_off_stem_brush_overlap

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

lemma cap_count {δ r θ m : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) (hr1 : r ≤ 1)
    (hδθ : δ ≤ θ) (hm : 0 ≤ m) {n : ℕ} {x v : Fin n → Space}
    (hv : ∀ j, ‖v j‖ = 1) (hball : ∀ j, Tube δ (x j) (v j) ⊆ ball (0 : Space) 1)
    (hcount : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal ((ncard {j : Fin n | Tube δ (x j) (v j) ⊆ W} : ℝ) * δ ^ 2) ≤
        ENNReal.ofReal m * volume W)
    (i i₀ : Fin n) (G : Finset (Fin n))
    (hbase : (Tube δ (x i) (v i) ∩ Tube δ (x i₀) (v i₀)).Nonempty)
    (hstem : ∀ j ∈ G, (Tube δ (x j) (v j) ∩ Tube δ (x i₀) (v i₀)).Nonempty)
    (hoff : ∀ j ∈ G, ((Tube δ (x i) (v i) \ thickening r (Stem (x i₀) (v i₀))) ∩
      Tube δ (x j) (v j)).Nonempty)
    (hangle : ∀ j ∈ G, angle (v i) (v j) ≤ θ) :
    (G.card : ℝ) ≤ (1024 * m / (r * δ)) * θ := by
  have hr : 0 < r := hδ.trans_le hδr
  have hθ : 0 ≤ θ := hδ.le.trans hδθ
  obtain ⟨W, hWc, hWvol, hW⟩ := off_stem_container hδ hδr hr1 hδθ (hball i) hbase
  have hcard : G.card ≤ ncard {j : Fin n | Tube δ (x j) (v j) ⊆ W} := by
    rw [← ncard_coe_finset]
    refine ncard_le_ncard ?_ (Set.toFinite _)
    intro j hj
    exact hW (x j) (v j) (hv j) (hball j) (hstem j hj) (hoff j hj) (hangle j hj)
  have hbound : ENNReal.ofReal ((G.card : ℝ) * δ ^ 2) ≤
      ENNReal.ofReal (m * (1024 * θ * δ / r)) := by
    calc
      _ ≤ ENNReal.ofReal ((ncard {j : Fin n | Tube δ (x j) (v j) ⊆ W} : ℝ) * δ ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg δ)
      _ ≤ ENNReal.ofReal m * volume W := hcount W hWc
      _ ≤ ENNReal.ofReal m * ENNReal.ofReal (1024 * θ * δ / r) := by gcongr
      _ = _ := (ENNReal.ofReal_mul hm).symm
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ m * (1024 * θ * δ / r))).mp hbound
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hδ)).1 (show (G.card : ℝ) * δ ^ 2 ≤
      ((1024 * m / (r * δ)) * θ) * δ ^ 2 by
    convert hreal using 1; field_simp)

lemma tube_volume_upper {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (x v : Space) (hv : ‖v‖ = 1) :
    volume (Tube δ x v) ≤ ENNReal.ofReal (384 * δ ^ 2) := by
  have hseg : (fun t : ℝ => x + t • v) '' Icc 0 1 = segment ℝ x (x + v) := by
    rw [segment_eq_image']
    simp
  have hd : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist s t ≤ 1 := by
    intro s hs t ht
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have h := WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper
    x v hv (T := Icc 0 1) Subset.rfl hδ (by norm_num : (0 : ℝ) ≤ 1) hd
  rw [hseg] at h
  exact h.trans (ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg δ]))

lemma angle_le_two {v w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) : angle v w ≤ 2 := by
  exact (min_le_left _ _).trans ((norm_sub_le v w).trans (by rw [hv, hw]; norm_num))

lemma regularized_intersection {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {x v y w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    volume (Tube δ x v ∩ Tube δ y w) ≤
      ENNReal.ofReal (8192 * δ ^ 3 / max δ (angle v w)) := by
  by_cases ha : angle v w ≤ δ
  · rw [max_eq_left ha]
    calc
      _ ≤ volume (Tube δ x v) := measure_mono inter_subset_left
      _ ≤ ENNReal.ofReal (384 * δ ^ 2) := tube_volume_upper hδ hδ1 x v hv
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [le_div_iff₀ hδ]
        nlinarith [pow_pos hδ 3]
  · have ha0 : 0 < angle v w := hδ.trans (lt_of_not_ge ha)
    rw [max_eq_right (lt_of_not_ge ha).le]
    have hb1 : angle v w / 2 ≤ 1 := by linarith [angle_le_two hv hw]
    have hb : angle v w / 2 ≤ min ‖v - w‖ ‖v + w‖ := by change angle v w / 2 ≤ angle v w; linarith
    have h := WangZahlLot.Obl.wz_transverse_brush_selection.transverse_intersection_volume
      (x := x) (y := y) hδ (by positivity : 0 < angle v w / 2) hb1 hv hw hb
    convert h using 1
    congr 1
    ring

end WangZahlLot.Obl.wz_off_stem_brush_overlap
