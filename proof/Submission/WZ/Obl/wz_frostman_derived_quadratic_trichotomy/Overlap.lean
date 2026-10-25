-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.Overlap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_transverse_stem_deletion
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.Canonical

/-!
# Overlap and containment of unit tubes (towards exact `S`-covers of aligned families)

For the sticky branch of a repaired trichotomy (`Repair.lean`), exact `S`-covers of an
axially aligned (canonical) family are built from ρ-tubes around canonical segments of a net
of lines. This file collects the geometric facts such a cover needs:

* `half_overlap_of_transverse`: ρ-tubes whose directions differ by at least `8000 ρ`
  (up to sign) overlap in at most half their volume (from accepted o029's
  `tube_line_intersection_volume_le` and o008's `tube_volume_lower`);
* `half_overlap_of_far`: δ-tubes around segments at distance at least `2 δ` are disjoint;
* `endpoints_near_of_subset`: a unit δ-tube inside a unit ρ-tube has both endpoints within
  `ρ` of the ρ-segment.
-/

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy

open MeasureTheory

/-- ρ-tubes whose directions are `8000 ρ`-separated (up to sign) overlap in at most half
their volume. -/
theorem half_overlap_of_transverse {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 1000)
    {z w z' w' : Sp} (hw : ‖w‖ = 1) (hw' : ‖w'‖ = 1)
    (hsep : 8000 * ρ ≤ min ‖w - w'‖ ‖w + w'‖) :
    volume (Metric.thickening ρ (segment ℝ z (z + w)) ∩
        Metric.thickening ρ (segment ℝ z' (z' + w'))) ≤
      (1 / 2 : ENNReal) * volume (Metric.thickening ρ (segment ℝ z (z + w))) := by
  have hb : 0 < 8000 * ρ := by positivity
  -- the second tube lies in the ρ-neighbourhood of its line
  have hseg : segment ℝ z' (z' + w') ⊆ Set.range (fun t : ℝ => z' + t • w') := by
    intro y hy
    obtain ⟨θ, -, -, rfl⟩ := mem_segment_add_iff.1 hy
    exact ⟨θ, rfl⟩
  have hsub : Metric.thickening ρ (segment ℝ z (z + w)) ∩
      Metric.thickening ρ (segment ℝ z' (z' + w')) ⊆
      Metric.thickening ρ (segment ℝ z (z + w)) ∩
        Metric.thickening ρ (Set.range (fun t : ℝ => z' + t • w')) :=
    Set.inter_subset_inter_right _ (Metric.thickening_subset_of_subset ρ hseg)
  have hint := WangZahlLot.Obl.wz_transverse_stem_deletion.tube_line_intersection_volume_le
    (x := z) (y := z')
    hρ hρ hb hw hw' hsep
  have hlow := WangZahlLot.Obl.wz_direction_density_transfer.tube_volume_lower hρ z w hw
  have hnum : 128 * (8 * (ρ + ρ) / (8000 * ρ) + ρ) * ρ ^ 2 ≤ 1 / 2 * ρ ^ 2 := by
    have e : 8 * (ρ + ρ) / (8000 * ρ) = 1 / 500 := by field_simp; ring
    rw [e]
    have : 128 * (1 / 500 + ρ) ≤ 1 / 2 := by linarith
    nlinarith [sq_nonneg ρ]
  calc volume (Metric.thickening ρ (segment ℝ z (z + w)) ∩
        Metric.thickening ρ (segment ℝ z' (z' + w')))
      ≤ volume (Metric.thickening ρ (segment ℝ z (z + w)) ∩
          Metric.thickening ρ (Set.range (fun t : ℝ => z' + t • w'))) := measure_mono hsub
    _ ≤ ENNReal.ofReal (128 * (8 * (ρ + ρ) / (8000 * ρ) + ρ) * ρ ^ 2) := hint
    _ ≤ ENNReal.ofReal (1 / 2 * ρ ^ 2) := ENNReal.ofReal_le_ofReal hnum
    _ = (1 / 2 : ENNReal) * ENNReal.ofReal (ρ ^ 2) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        congr 1
        rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2), one_div,
          ENNReal.ofReal_ofNat]
    _ ≤ (1 / 2 : ENNReal) * volume (Metric.thickening ρ (segment ℝ z (z + w))) := by
        gcongr

/-- δ-tubes around segments at distance at least `2 δ` are disjoint, so they overlap in at
most half their volume. -/
theorem half_overlap_of_far {δ : ℝ} {A A' : Set Sp}
    (hfar : ∀ a ∈ A, ∀ a' ∈ A', 2 * δ ≤ dist a a') :
    volume (Metric.thickening δ A ∩ Metric.thickening δ A') ≤
      (1 / 2 : ENNReal) * volume (Metric.thickening δ A) := by
  have hempty : Metric.thickening δ A ∩ Metric.thickening δ A' = ∅ := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hy hy'
    obtain ⟨a, ha, hya⟩ := Metric.mem_thickening_iff.1 hy
    obtain ⟨a', ha', hya'⟩ := Metric.mem_thickening_iff.1 hy'
    have := hfar a ha a' ha'
    have := dist_triangle_left a a' y
    linarith
  rw [hempty, measure_empty]
  exact zero_le

/-- A δ-tube inside a ρ-tube has its endpoints within `ρ` of the ρ-segment. -/
theorem endpoints_near_of_subset {δ ρ : ℝ} (hδ : 0 < δ) {x v z w : Sp}
    (hsub : Metric.thickening δ (segment ℝ x (x + v)) ⊆
      Metric.thickening ρ (segment ℝ z (z + w))) :
    (∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ dist x (z + θ • w) < ρ) ∧
      (∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ dist (x + v) (z + θ • w) < ρ) := by
  have h1 : x ∈ Metric.thickening ρ (segment ℝ z (z + w)) :=
    hsub (Metric.self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v)))
  have h2 : x + v ∈ Metric.thickening ρ (segment ℝ z (z + w)) :=
    hsub (Metric.self_subset_thickening hδ _ (right_mem_segment ℝ x (x + v)))
  obtain ⟨y1, hy1, hd1⟩ := Metric.mem_thickening_iff.1 h1
  obtain ⟨y2, hy2, hd2⟩ := Metric.mem_thickening_iff.1 h2
  obtain ⟨θ1, h01, h11, rfl⟩ := mem_segment_add_iff.1 hy1
  obtain ⟨θ2, h02, h12, rfl⟩ := mem_segment_add_iff.1 hy2
  exact ⟨⟨θ1, h01, h11, hd1⟩, ⟨θ2, h02, h12, hd2⟩⟩

/-- A unit δ-tube inside a unit ρ-tube has direction within `4 ρ` of `±w`. -/
theorem direction_near_of_subset {δ ρ : ℝ} (hδ : 0 < δ) {x v z w : Sp} (hv : ‖v‖ = 1)
    (hw : ‖w‖ = 1)
    (hsub : Metric.thickening δ (segment ℝ x (x + v)) ⊆
      Metric.thickening ρ (segment ℝ z (z + w))) :
    min ‖v - w‖ ‖v + w‖ < 4 * ρ := by
  obtain ⟨⟨θ1, h01, h11, hd1⟩, ⟨θ2, h02, h12, hd2⟩⟩ := endpoints_near_of_subset hδ hsub
  -- `v` is within `2ρ` of `(θ2 - θ1) w`
  have hclose : ‖v - (θ2 - θ1) • w‖ < 2 * ρ := by
    have e : v - (θ2 - θ1) • w = ((x + v) - (z + θ2 • w)) - (x - (z + θ1 • w)) := by module
    rw [e]
    calc ‖((x + v) - (z + θ2 • w)) - (x - (z + θ1 • w))‖
        ≤ ‖(x + v) - (z + θ2 • w)‖ + ‖x - (z + θ1 • w)‖ := norm_sub_le _ _
      _ < ρ + ρ := by rw [← dist_eq_norm, ← dist_eq_norm]; exact add_lt_add hd2 hd1
      _ = 2 * ρ := by ring
  have hρ : 0 < ρ := by
    have := norm_nonneg (v - (θ2 - θ1) • w); linarith
  -- `|θ2 - θ1| ≥ 1 - 2ρ`
  have hnorm : ‖(θ2 - θ1) • w‖ = |θ2 - θ1| := by rw [norm_smul, hw, mul_one, Real.norm_eq_abs]
  have hge : 1 - 2 * ρ < |θ2 - θ1| := by
    have := norm_sub_norm_le v ((θ2 - θ1) • w)
    rw [hv, hnorm] at this
    linarith
  have hle : |θ2 - θ1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  rcases le_total 0 (θ2 - θ1) with hpos | hneg
  · -- `v ≈ w`
    have : ‖v - w‖ < 4 * ρ := by
      have e : v - w = (v - (θ2 - θ1) • w) + ((θ2 - θ1) - 1) • w := by module
      rw [e]
      calc ‖(v - (θ2 - θ1) • w) + ((θ2 - θ1) - 1) • w‖
          ≤ ‖v - (θ2 - θ1) • w‖ + ‖((θ2 - θ1) - 1) • w‖ := norm_add_le _ _
        _ = ‖v - (θ2 - θ1) • w‖ + |(θ2 - θ1) - 1| := by
            rw [norm_smul, hw, mul_one, Real.norm_eq_abs]
        _ < 2 * ρ + 2 * ρ := by
            rw [abs_of_nonneg hpos] at hge hle
            have : |(θ2 - θ1) - 1| = 1 - (θ2 - θ1) := by
              rw [abs_of_nonpos (by linarith)]; ring
            rw [this]; linarith
        _ = 4 * ρ := by ring
    exact lt_of_le_of_lt (min_le_left _ _) this
  · -- `v ≈ -w`
    have : ‖v + w‖ < 4 * ρ := by
      have e : v + w = (v - (θ2 - θ1) • w) + ((θ2 - θ1) + 1) • w := by module
      rw [e]
      calc ‖(v - (θ2 - θ1) • w) + ((θ2 - θ1) + 1) • w‖
          ≤ ‖v - (θ2 - θ1) • w‖ + ‖((θ2 - θ1) + 1) • w‖ := norm_add_le _ _
        _ = ‖v - (θ2 - θ1) • w‖ + |(θ2 - θ1) + 1| := by
            rw [norm_smul, hw, mul_one, Real.norm_eq_abs]
        _ < 2 * ρ + 2 * ρ := by
            rw [abs_of_nonpos hneg] at hge hle
            have : |(θ2 - θ1) + 1| = (θ2 - θ1) + 1 := by
              rw [abs_of_nonneg (by linarith)]
            rw [this]; linarith
        _ = 4 * ρ := by ring
    exact lt_of_le_of_lt (min_le_right _ _) this

/-- The separation of a net of unit ρ-tubes: transverse directions, or segments at distance at
least `2ρ`. -/
def NetSeparated (ρ : ℝ) {q : ℕ} (z w : Fin q → Sp) : Prop :=
  ∀ j j', j ≠ j' → 8000 * ρ ≤ min ‖w j - w j'‖ ‖w j + w j'‖ ∨
    ∀ a ∈ segment ℝ (z j) (z j + w j), ∀ a' ∈ segment ℝ (z j') (z j' + w j'), 2 * ρ ≤ dist a a'

/-- min-distance between `±` directions is symmetric. -/
lemma min_dir_comm (u u' : Sp) : min ‖u - u'‖ ‖u + u'‖ = min ‖u' - u‖ ‖u' + u‖ := by
  rw [norm_sub_rev, add_comm]

/-- Triangle inequality for directions up to sign. -/
lemma min_dir_triangle {v w w' : Sp} :
    min ‖w - w'‖ ‖w + w'‖ ≤ min ‖v - w‖ ‖v + w‖ + min ‖v - w'‖ ‖v + w'‖ := by
  have h1 : ‖w - w'‖ ≤ ‖v - w‖ + ‖v - w'‖ := by
    calc ‖w - w'‖ = ‖(v - w') - (v - w)‖ := by congr 1; abel
      _ ≤ ‖v - w'‖ + ‖v - w‖ := norm_sub_le _ _
      _ = ‖v - w‖ + ‖v - w'‖ := by ring
  have h2 : ‖w - w'‖ ≤ ‖v + w‖ + ‖v + w'‖ := by
    calc ‖w - w'‖ = ‖(v + w) - (v + w')‖ := by congr 1; abel
      _ ≤ ‖v + w‖ + ‖v + w'‖ := norm_sub_le _ _
  have h3 : ‖w + w'‖ ≤ ‖v - w‖ + ‖v + w'‖ := by
    calc ‖w + w'‖ = ‖(v + w') - (v - w)‖ := by congr 1; abel
      _ ≤ ‖v + w'‖ + ‖v - w‖ := norm_sub_le _ _
      _ = ‖v - w‖ + ‖v + w'‖ := by ring
  have h4 : ‖w + w'‖ ≤ ‖v + w‖ + ‖v - w'‖ := by
    calc ‖w + w'‖ = ‖(v + w) - (v - w')‖ := by congr 1; abel
      _ ≤ ‖v + w‖ + ‖v - w'‖ := norm_sub_le _ _
  rcases min_cases ‖v - w‖ ‖v + w‖ with ⟨ha, -⟩ | ⟨ha, -⟩ <;>
  rcases min_cases ‖v - w'‖ ‖v + w'‖ with ⟨hb, -⟩ | ⟨hb, -⟩ <;> rw [ha, hb]
  · exact le_trans (min_le_left _ _) h1
  · exact le_trans (min_le_right _ _) h3
  · exact le_trans (min_le_right _ _) h4
  · exact le_trans (min_le_left _ _) h2

/-- One scale of an exact cover: if every δ-tube lies in its assigned tube of a separated net
of unit ρ-tubes, then the net tubes pairwise overlap in at most half their volume and each
δ-tube lies in exactly one of them. -/
theorem exact_cover_of_netSeparated {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 1000)
    {n q : ℕ} (x v : Fin n → Sp) (z w : Fin q → Sp) (hv : ∀ i, ‖v i‖ = 1)
    (hw : ∀ j, ‖w j‖ = 1) (hsep : NetSeparated ρ z w) (f : Fin n → Fin q)
    (hf : ∀ i, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
      Metric.thickening ρ (segment ℝ (z (f i)) (z (f i) + w (f i)))) :
    (∀ j j', j ≠ j' → volume (Metric.thickening ρ (segment ℝ (z j) (z j + w j)) ∩
        Metric.thickening ρ (segment ℝ (z j') (z j' + w j'))) ≤
        (1 / 2 : ENNReal) * volume (Metric.thickening ρ (segment ℝ (z j) (z j + w j)))) ∧
    (∀ i, ∃! j, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
      Metric.thickening ρ (segment ℝ (z j) (z j + w j))) := by
  refine ⟨fun j j' hjj' => ?_, fun i => ⟨f i, hf i, fun j hj => ?_⟩⟩
  · rcases hsep j j' hjj' with htr | hfar
    · exact half_overlap_of_transverse hρ hρ1 (hw j) (hw j') htr
    · exact half_overlap_of_far hfar
  · by_contra hne
    rcases hsep j (f i) hne with htr | hfar
    · -- both contain the δ-tube, so their directions are `8ρ`-close
      have h1 := direction_near_of_subset hδ (hv i) (hw j) hj
      have h2 := direction_near_of_subset hδ (hv i) (hw (f i)) (hf i)
      have := min_dir_triangle (v := v i) (w := w j) (w' := w (f i))
      linarith
    · -- both contain the start of the δ-tube, so the segments come within `2ρ`
      obtain ⟨⟨θ1, h01, h11, hd1⟩, -⟩ := endpoints_near_of_subset hδ hj
      obtain ⟨⟨θ2, h02, h12, hd2⟩, -⟩ := endpoints_near_of_subset hδ (hf i)
      have := hfar (z j + θ1 • w j) (mem_segment_add_iff.2 ⟨θ1, h01, h11, rfl⟩)
        (z (f i) + θ2 • w (f i)) (mem_segment_add_iff.2 ⟨θ2, h02, h12, rfl⟩)
      have := dist_triangle_left (z j + θ1 • w j) (z (f i) + θ2 • w (f i)) (x i)
      linarith

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy
