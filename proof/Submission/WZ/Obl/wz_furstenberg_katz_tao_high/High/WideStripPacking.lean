-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.WideStripPacking.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o222/x0722 High/WideStripPacking.lean (c61cafd).
-- Adapted from local obligation o157, branch x0675, commit 5a2c82ba2c9f.
-- Source: High/WideStripPacking.lean. Shared half definitions imported from accepted o213.
-- Ported from internal o141, session x0563's WideStripPacking.lean (branch x0563); namespace renamed.
import Submission.WZ.Obl.wz_osw_single_scale_heavy_pairs.StripCount
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.Maximal

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half (exists_maximal_pairwise)

attribute [local instance] Classical.propDecidable

/-- A framed strip count with separate incidence width and label separation. -/
theorem wide_frame_count {u y : E2} {r a w : ℝ} (hu : ‖u‖ = 1)
    (hr : 0 < r) (ha : 0 ≤ a) (hw : 0 ≤ w)
    (J : Finset (E2 × E2)) (hsep : (J : Set (E2 × E2)).Pairwise (StripSep r))
    (hJ : ∀ j ∈ J, ‖j.2‖ = 1 ∧ ‖y - j.1‖ ≤ 8 ∧
      (inner ℝ j.2 u) ^ 2 ≤ 1 / 2 ∧ |inner ℝ j.2 u| ≤ a ∧
      |inner ℝ (y - j.1) j.2| ≤ w) :
    (J.card : ℝ) ≤ 2 * (64 * a / r + 2) * (4 * w / r + 2) := by
  classical
  let box : Finset (ℤ × ℤ × ℤ) := Finset.Icc 0 1 ×ˢ
    (Finset.Icc ⌊-(32 * a / r)⌋ ⌊32 * a / r⌋ ×ˢ
      Finset.Icc ⌊-(2 * w / r)⌋ ⌊2 * w / r⌋)
  have hmaps : Set.MapsTo (stripCode u y (r / 32) (r / 2)) (↑J) (↑box) := by
    intro j hj
    obtain ⟨_, _, _, hangle, hoff⟩ := hJ j hj
    simp only [box, stripCode, Finset.mem_coe, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨by split_ifs <;> norm_num, by split_ifs <;> norm_num⟩,
      ⟨Int.floor_le_floor ?_, Int.floor_le_floor ?_⟩,
      ⟨Int.floor_le_floor ?_, Int.floor_le_floor ?_⟩⟩
    · apply (le_div_iff₀ (by positivity : 0 < r / 32)).mpr
      field_simp
      nlinarith [(abs_le.mp hangle).1]
    · apply (div_le_iff₀ (by positivity : 0 < r / 32)).mpr
      field_simp
      nlinarith [(abs_le.mp hangle).2]
    · apply (le_div_iff₀ (by positivity : 0 < r / 2)).mpr
      field_simp
      nlinarith [(abs_le.mp hoff).1]
    · apply (div_le_iff₀ (by positivity : 0 < r / 2)).mpr
      field_simp
      nlinarith [(abs_le.mp hoff).2]
  have hinj := stripCode_injOn hu (show 0 < r / 32 by positivity)
    (show 0 < r / 2 by positivity) (by linarith) hsep
    (fun j hj => ⟨(hJ j hj).1, (hJ j hj).2.1, (hJ j hj).2.2.1⟩)
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  have ha' := card_Icc_floor_le (show 0 ≤ 32 * a / r by positivity)
  have hw' := card_Icc_floor_le (show 0 ≤ 2 * w / r by positivity)
  have hbox : (box.card : ℝ) ≤ 2 * (64 * a / r + 2) * (4 * w / r + 2) := by
    simp only [box, Finset.card_product]
    push_cast
    have h01 : ((Finset.Icc (0 : ℤ) 1).card : ℝ) = 2 := by norm_num
    rw [h01]
    have hmul := mul_le_mul ha' hw' (Nat.cast_nonneg _)
      (show 0 ≤ 2 * (32 * a / r) + 2 by positivity)
    convert mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
  exact (Nat.cast_le.mpr hcard).trans hbox

private lemma frame_rot_norm (e : E2) : ‖rot e‖ = ‖e‖ := by
  have h := norm_sq_coords (rot e)
  have h' := norm_sq_coords e
  simp only [rot_zero, rot_one, neg_sq] at h
  nlinarith [norm_nonneg (rot e), norm_nonneg e]

private lemma frame_rot_orthogonal (e : E2) : inner ℝ e (rot e) = 0 := by
  rw [inner_coords]
  simp only [rot_zero, rot_one]
  ring

private lemma close_orthogonal_bound {e v u : E2} {w : ℝ}
    (hu : ‖u‖ = 1) (hvu : inner ℝ v u = 0) (hclose : dist e v < w) :
    |inner ℝ e u| < w := by
  have hid : inner ℝ e u = inner ℝ (e - v) u := by rw [inner_sub_left, hvu, sub_zero]
  rw [hid]
  calc
    |inner ℝ (e - v) u| ≤ ‖e - v‖ * ‖u‖ := abs_real_inner_le_norm _ _
    _ = dist e v := by rw [hu, mul_one, dist_eq_norm]
    _ < w := hclose

private lemma unoriented_angle_bound {e v u : E2} {w : ℝ}
    (hu : ‖u‖ = 1) (hvu : inner ℝ v u = 0)
    (hclose : dist e v < w ∨ dist e (-v) < w) : |inner ℝ e u| < w := by
  rcases hclose with hp | hn
  · exact close_orthogonal_bound hu hvu hp
  · exact close_orthogonal_bound hu (by rw [inner_neg_left, hvu, neg_zero]) hn

private lemma close_offset_bound {x e v : E2} {w : ℝ} (hx : ‖x‖ ≤ 8)
    (hbase : |inner ℝ x v| < w) (hclose : dist e v < w) :
    |inner ℝ x e| < 9 * w := by
  have hid : inner ℝ x e = inner ℝ x v + inner ℝ x (e - v) := by
    rw [inner_sub_right]
    ring
  have herr : |inner ℝ x (e - v)| < 8 * w := by
    calc
      |inner ℝ x (e - v)| ≤ ‖x‖ * ‖e - v‖ := abs_real_inner_le_norm _ _
      _ ≤ 8 * ‖e - v‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
      _ < 8 * w := by rw [← dist_eq_norm]; linarith
  rw [hid]
  exact (abs_add_le _ _).trans_lt (by linarith)

private lemma unoriented_offset_bound {x e v : E2} {w : ℝ} (hx : ‖x‖ ≤ 8)
    (hbase : |inner ℝ x v| < w)
    (hclose : dist e v < w ∨ dist e (-v) < w) : |inner ℝ x e| < 9 * w := by
  rcases hclose with hp | hn
  · exact close_offset_bound hx hbase hp
  · exact close_offset_bound hx (by simpa only [inner_neg_right, abs_neg] using hbase) hn

/-- The neighbors excluded by a coarse separation condition have bounded
cardinality inside a finer separated family. Both orders of `StripSep` are kept. -/
theorem strip_neighbor_count {r w : ℝ} (hr : 0 < r) (hw : 0 < w) (hw2 : w ≤ 1 / 2)
    (J : Finset (E2 × E2)) (hJ : ∀ j ∈ J, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1)
    (hsep : (J : Set (E2 × E2)).Pairwise (StripSep r))
    {k : E2 × E2} (hk : k ∈ J) :
    ((J.filter (fun j => ¬ StripSep w j k ∨ ¬ StripSep w k j)).card : ℝ) ≤
      2 * (64 * w / r + 2) * (36 * w / r + 2) := by
  classical
  let F := J.filter fun j => ¬ StripSep w j k ∨ ¬ StripSep w k j
  have hu : ‖rot k.2‖ = 1 := by rw [frame_rot_norm, (hJ k hk).2]
  have hb := wide_frame_count (y := k.1) (u := rot k.2) hu hr hw.le
    (show 0 ≤ 9 * w by positivity) F
    (hsep.mono (Finset.filter_subset _ _)) (by
      intro j hj
      obtain ⟨hjJ, hnear⟩ := Finset.mem_filter.mp hj
      have hclose : dist j.2 k.2 < w ∨ dist j.2 (-k.2) < w := by
        rcases hnear with hforward | hbackward
        · have hh : (dist j.2 k.2 < w ∨ dist j.2 (-k.2) < w) ∧
              |inner ℝ (j.1 - k.1) j.2| < w := by
            simpa only [StripSep, not_or, not_and_or, not_le] using hforward
          exact hh.1
        · have hh : (dist k.2 j.2 < w ∨ dist k.2 (-j.2) < w) ∧
              |inner ℝ (k.1 - j.1) k.2| < w := by
            simpa only [StripSep, not_or, not_and_or, not_le] using hbackward
          rcases hh.1 with hp | hn
          · exact Or.inl (by simpa only [dist_comm] using hp)
          · exact Or.inr (by simpa only [dist_eq_norm, sub_neg_eq_add, add_comm] using hn)
      have ha := unoriented_angle_bound hu (frame_rot_orthogonal k.2) hclose
      have hoff : |inner ℝ (k.1 - j.1) j.2| < 9 * w := by
        rcases hnear with hforward | hbackward
        · have hh : (dist j.2 k.2 < w ∨ dist j.2 (-k.2) < w) ∧
              |inner ℝ (j.1 - k.1) j.2| < w := by
            simpa only [StripSep, not_or, not_and_or, not_le] using hforward
          have hid : |inner ℝ (k.1 - j.1) j.2| = |inner ℝ (j.1 - k.1) j.2| := by
            rw [← neg_sub j.1 k.1, inner_neg_left, abs_neg]
          rw [hid]
          linarith [hh.2]
        · have hh : (dist k.2 j.2 < w ∨ dist k.2 (-j.2) < w) ∧
              |inner ℝ (k.1 - j.1) k.2| < w := by
            simpa only [StripSep, not_or, not_and_or, not_le] using hbackward
          exact unoriented_offset_bound (norm_le_eight_of_norm_le_four
            (hJ k hk).1 (hJ j hjJ).1) hh.2 hclose
      refine ⟨(hJ j hjJ).2, norm_le_eight_of_norm_le_four (hJ k hk).1 (hJ j hjJ).1,
        ?_, ha.le, hoff.le⟩
      rw [← sq_abs]
      have hnonneg := abs_nonneg (inner ℝ j.2 (rot k.2))
      nlinarith)
  convert hb using 1 <;> ring

/-- A separated strip family has a large subfamily separated at any prescribed
coarser scale, with a quadratic loss in the ratio of scales. -/
theorem strip_coarse_subfamily {r w : ℝ} (hr : 0 < r) (hw : 0 < w) (hw2 : w ≤ 1 / 2)
    (J : Finset (E2 × E2)) (hJ : ∀ j ∈ J, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1)
    (hsep : (J : Set (E2 × E2)).Pairwise (StripSep r)) :
    ∃ F ⊆ J, (F : Set (E2 × E2)).Pairwise (StripSep w) ∧
      (J.card : ℝ) ≤ 2 * (64 * w / r + 2) * (36 * w / r + 2) * F.card := by
  classical
  obtain ⟨F, hFJ, hFsep, hmax⟩ := exists_maximal_pairwise J (StripSep w)
  let N : (E2 × E2) → Finset (E2 × E2) :=
    fun k => J.filter fun j => ¬ StripSep w j k ∨ ¬ StripSep w k j
  have hcover : J ⊆ F.biUnion N := by
    intro j hj
    by_cases hjF : j ∈ F
    · apply Finset.mem_biUnion.mpr
      refine ⟨j, hjF, Finset.mem_filter.mpr ⟨hj, Or.inl ?_⟩⟩
      simp only [StripSep, dist_self, le_zero_iff, sub_self, inner_zero_left, abs_zero]
      intro hh
      rcases hh with h | h <;> linarith [hw]
    · obtain ⟨k, hk, hnear⟩ := hmax j hj hjF
      exact Finset.mem_biUnion.mpr ⟨k, hk, Finset.mem_filter.mpr ⟨hj, hnear⟩⟩
  have hcount : J.card ≤ ∑ k ∈ F, (N k).card :=
    (Finset.card_le_card hcover).trans (Finset.card_biUnion_le)
  refine ⟨F, hFJ, hFsep, ?_⟩
  calc
    (J.card : ℝ) ≤ ∑ k ∈ F, ((N k).card : ℝ) := by exact_mod_cast hcount
    _ ≤ ∑ _k ∈ F, 2 * (64 * w / r + 2) * (36 * w / r + 2) :=
      Finset.sum_le_sum fun k hk => strip_neighbor_count hr hw hw2 J hJ hsep (hFJ hk)
    _ = 2 * (64 * w / r + 2) * (36 * w / r + 2) * F.card := by simp [mul_comm]

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
