-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.ParentSlabs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.GroupCounts
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.SlabComparison
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.CoarseBuffer

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal

lemma doubled_subset_dilation {R : ℝ} (x v : Space) :
    doubled R x v ⊆ AffineMap.homothety (x + (1 / 2 : ℝ) • v) (2 : ℝ) '' tube R x v := by
  apply homothety_image_of_contraction _ (by norm_num : (2 : ℝ) ≠ 0)
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨p, hp, hqp⟩ := mem_thickening_iff.mp hq
  rw [segment_eq_image'] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  simp only [add_sub_cancel_left, dist_eq_norm] at hqp
  have he : q - (x + (1 / 2 : ℝ) • v) - (2 * t - 1) • v =
      q - (x - (1 / 2 : ℝ) • v + t • (2 • v)) := by module
  apply homothety_mem_tube (A := 2 * t - 1) (B := ‖q - (x + (1 / 2 : ℝ) • v) - (2 * t - 1) • v‖)
  · apply abs_le.mpr
    constructor <;> linarith [ht.1, ht.2]
  · exact le_rfl
  · rw [he]
    norm_num
    linarith

/-- Every point of the parent tube is a uniformly buffered center in its doubled tube. -/
lemma parent_buffer {r a : ℝ} (hr : 0 < r) (ha : |a| ≤ 1 / 100)
    {y w p : Space} (hp : p ∈ tube r y w) :
    AffineMap.homothety p a '' doubled r y w ⊆ doubled r y w := by
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨p₀, hp₀, hpp⟩ := mem_thickening_iff.mp hp
  obtain ⟨q₀, hq₀, hqq⟩ := mem_thickening_iff.mp hq
  rw [segment_eq_image'] at hp₀ hq₀
  obtain ⟨b, hb, rfl⟩ := hp₀
  obtain ⟨c, hc, rfl⟩ := hq₀
  simp only [add_sub_cancel_left, dist_eq_norm] at hpp hqq
  let A := b - 1 / 2 + a * (2 * c - 1 / 2 - b)
  have hA : |A| ≤ 1 := by
    have hb' : |b - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩
    have hc' : |2 * c - 1 / 2 - b| ≤ 2 := abs_le.mpr
      ⟨by linarith [hc.1, hb.2], by linarith [hc.2, hb.1]⟩
    calc
      _ ≤ |b - 1 / 2| + |a| * |2 * c - 1 / 2 - b| := by
        simpa only [abs_mul] using abs_add_le (b - 1 / 2) (a * (2 * c - 1 / 2 - b))
      _ ≤ 1 / 2 + (1 / 100 : ℝ) * 2 := add_le_add hb'
        (mul_le_mul ha hc' (abs_nonneg _) (by norm_num))
      _ ≤ _ := by norm_num
  have ha' : |1 - a| ≤ 101 / 100 := by
    have hh := abs_sub_le 1 0 a
    norm_num at hh
    linarith
  apply mem_thickening_iff.mpr
  refine ⟨y + (1 / 2 : ℝ) • w + A • w, centered_doubled_segment y w hA, ?_⟩
  rw [dist_eq_norm]
  have he : AffineMap.homothety p a q - (y + (1 / 2 : ℝ) • w + A • w) =
      (1 - a) • (p - (y + b • w)) + a • (q - (y - (1 / 2 : ℝ) • w + c • (2 • w))) := by
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
    dsimp [A]
    module
  rw [he]
  calc
    _ ≤ ‖(1 - a) • (p - (y + b • w))‖ +
        ‖a • (q - (y - (1 / 2 : ℝ) • w + c • (2 • w)))‖ := norm_add_le _ _
    _ = |1 - a| * ‖p - (y + b • w)‖ +
        |a| * ‖q - (y - (1 / 2 : ℝ) • w + c • (2 • w))‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (101 / 100 : ℝ) * r + (1 / 100 : ℝ) * (2 * r) :=
      add_le_add (mul_le_mul ha' hpp.le (norm_nonneg _) (by norm_num))
        (mul_le_mul ha hqq.le (norm_nonneg _) (by norm_num))
    _ < _ := by linarith

lemma parent_cover_slab {r s R B H L : ℝ} (hr : 0 < r) (hR : 0 < R)
    {m n N : ℕ} (hn : 0 < n) (S : Finset (Fin m)) (f : Fin m → Fin N)
    (j : Fin m → Fin n) (hj : Function.Injective j) (hB : 0 ≤ B) (hH : 0 < H) (hL : 0 ≤ L)
    (hret : H * n ≤ S.card)
    (hbal : ∀ k l, ((S.filter (fun i => f i = k)).card : ℝ) ≤
      B * (S.filter (fun i => f i = l)).card)
    (y w : Space) (x v : Fin n → Space) (z u : Fin N → Space)
    (hT : ∀ i, tube s (x i) (v i) ⊆ tube r y w)
    (hp : ∀ k, z k + (1 / 2 : ℝ) • u k ∈ tube r y w)
    (hc : ∀ i ∈ S, tube s (x (j i)) (v (j i)) ⊆ doubled R (z (f i)) (u (f i)))
    (hSb : SlabBound (doubled r y w) L (fun _ => True) (fun i => tube s (x i) (v i))) :
    SlabBound (doubled r y w) (2000000 * (B * L / H)) (fun _ => True)
      (fun k => tube R (z k) (u k)) := by
  let V := fun k => ⋃ i ∈ S, ⋃ (_ : f i = k), tube s (x (j i)) (v (j i))
  have hgroup := grouped_slabBound hn S f j hj hB hH hL hret hbal
    (fun i => tube s (x i) (v i)) hSb
  have hmain := slabBound_of_comparable (a := 1 / 100) (B := 1) (C := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun k => z k + (1 / 2 : ℝ) • u k)
    (U := fun k => tube R (z k) (u k)) (V := V)
    (fun k _ => self_subset_thickening hR _ (by simpa using centered_segment (z k) (u k) (a := 0) (by norm_num)))
    (by
      intro k _ q hq
      simp only [V, mem_iUnion] at hq
      obtain ⟨i, hi, hfi, hq⟩ := hq
      exact tube_subset_doubled hr.le y w (hT (j i) hq))
    (by
      intro k _ q hq
      simp only [V, mem_iUnion] at hq
      obtain ⟨i, hi, hfi, hq⟩ := hq
      rw [← hfi]
      exact doubled_subset_dilation _ _ (hc i hi hq))
    (fun k _ => parent_buffer hr (by norm_num) (hp k))
    (fun k _ => parent_buffer hr (by norm_num) (hp k))
    (by simp) hgroup
  norm_num at hmain
  exact hmain

end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
