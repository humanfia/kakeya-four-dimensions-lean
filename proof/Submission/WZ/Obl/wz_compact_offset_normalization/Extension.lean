-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_compact_offset_normalization.Extension.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_compact_offset_normalization.Shear

/-!
# The new round tubes

For a transversal unit tube `(x, v)` with `v 2 ≥ 1/2` in the unit ball, the image of its axis
under `shear c` is a segment of length `l ∈ [v 2, 1]`. We extend it to a unit segment towards
the height `0`; the extended segment stays in the closed ball of radius `1 - δ`, so its
`δ`-thickening is a round unit tube in the unit ball containing the image of the old tube.
-/

namespace WangZahlLot.Obl.wz_compact_offset_normalization

open Set Metric MeasureTheory
open scoped ENNReal

/-- The direction of the new tube. -/
noncomputable def newDir (c : ℝ) (v : Space) : Space := ‖shear c v‖⁻¹ • shear c v

/-- The base point of the new tube. -/
noncomputable def newBase (c : ℝ) (x v : Space) : Space :=
  if 0 ≤ 2 * x 2 + v 2 then shear c x + shear c v - newDir c v else shear c x

section

variable {c : ℝ} {v : Space}

theorem shear_norm_ge : v 2 ≤ ‖shear c v‖ := by
  have := abs_coord_le_norm (shear c v) 2
  rw [shear_apply_two] at this
  exact (le_abs_self _).trans this

theorem shear_norm_pos (hv2 : 1 / 2 ≤ v 2) : 0 < ‖shear c v‖ := by
  have := shear_norm_ge (c := c) (v := v)
  linarith

theorem newDir_norm (hv2 : 1 / 2 ≤ v 2) : ‖newDir c v‖ = 1 := by
  rw [newDir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (shear_norm_pos hv2).ne']

theorem shear_eq_smul_newDir (hv2 : 1 / 2 ≤ v 2) : shear c v = ‖shear c v‖ • newDir c v := by
  rw [newDir, smul_smul, mul_inv_cancel₀ (shear_norm_pos hv2).ne', one_smul]

theorem newDir_apply (i : Fin 3) : newDir c v i = shear c v i / ‖shear c v‖ := by
  rw [newDir]
  simp [div_eq_inv_mul]

theorem newDir_two_ge (hc : |c| ≤ 100) (hv : ‖v‖ = 1) (hv2 : 1 / 2 ≤ v 2) :
    v 2 ≤ newDir c v 2 := by
  rw [newDir_apply, shear_apply_two, le_div_iff₀ (shear_norm_pos hv2)]
  have h1 : ‖shear c v‖ ≤ 1 := hv ▸ shear_norm_le hc v
  nlinarith

theorem newDir_two_le (hv2 : 1 / 2 ≤ v 2) : newDir c v 2 ≤ 1 := by
  rw [newDir_apply, shear_apply_two, div_le_one (shear_norm_pos hv2)]
  exact shear_norm_ge

theorem newDir_transversal (hc : |c| ≤ 100) (hv : ‖v‖ = 1) (hv2 : 1 / 2 ≤ v 2) :
    (1 / 2 : ℝ) ≤ |newDir c v 2| :=
  hv2.trans ((newDir_two_ge hc hv hv2).trans (le_abs_self _))

theorem newDir_horizontal (hc : |c| ≤ 100) (hv : ‖v‖ = 1) (hv2 : 1 / 2 ≤ v 2) :
    newDir c v 0 ^ 2 + newDir c v 1 ^ 2 ≤ 1 / 10 := by
  rw [newDir_apply, newDir_apply, div_pow, div_pow, ← add_div,
    div_le_iff₀ (pow_pos (shear_norm_pos hv2) 2)]
  have h1 := shear_horizontal hc v
  have h2 : v 0 ^ 2 + v 1 ^ 2 ≤ 1 := by
    have := norm_sq_eq v
    rw [hv] at this
    nlinarith [sq_nonneg (v 2)]
  have h3 : (1 / 2 : ℝ) ^ 2 ≤ ‖shear c v‖ ^ 2 :=
    pow_le_pow_left₀ (by norm_num) (hv2.trans shear_norm_ge) 2
  nlinarith

end

/-- The image of the old axis lies on the new axis. -/
theorem segment_subset_new {c : ℝ} (hc : |c| ≤ 100) {x v : Space} (hv : ‖v‖ = 1)
    (hv2 : 1 / 2 ≤ v 2) :
    segment ℝ (shear c x) (shear c x + shear c v) ⊆
      segment ℝ (newBase c x v) (newBase c x v + newDir c v) := by
  set l := ‖shear c v‖ with hl
  have hl1 : l ≤ 1 := hv ▸ shear_norm_le hc v
  have hl0 : 0 ≤ l := norm_nonneg _
  have hAv : shear c v = l • newDir c v := shear_eq_smul_newDir hv2
  apply (convex_segment _ _).segment_subset
  · rw [newBase]
    split_ifs
    · refine mem_segment_param.mpr ⟨1 - l, ⟨by linarith, by linarith⟩, ?_⟩
      rw [hAv]
      module
    · exact left_mem_segment _ _ _
  · rw [newBase]
    split_ifs
    · refine mem_segment_param.mpr ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
      module
    · exact mem_segment_param.mpr ⟨l, ⟨hl0, hl1⟩, by rw [hAv]⟩

/-- An endpoint of the new axis away from the image axis stays well inside the ball. -/
private theorem far_endpoint_norm {δ : ℝ} (hδ1 : δ ≤ 1 / 100) {e q u : Space}
    (hq : q 0 ^ 2 + q 1 ^ 2 ≤ 1 / 40) (hu : u 0 ^ 2 + u 1 ^ 2 ≤ 1 / 10)
    (he0 : e 0 ^ 2 + e 1 ^ 2 ≤ 2 * (q 0 ^ 2 + q 1 ^ 2) + 2 * (u 0 ^ 2 + u 1 ^ 2))
    (he2 : |e 2| ≤ 3 / 4) : ‖e‖ ≤ 1 - δ := by
  apply norm_le_of_sq_le (by linarith)
  have h2 : e 2 ^ 2 ≤ (3 / 4) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) he2 2
  nlinarith

/-- The new axis lies in the closed ball of radius `1 - δ`. -/
theorem new_segment_subset {c : ℝ} (hc : |c| ≤ 100) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100)
    {x v : Space} (hv : ‖v‖ = 1) (hv2 : 1 / 2 ≤ v 2) (hT : Tube δ x v ⊆ ball 0 1) :
    segment ℝ (newBase c x v) (newBase c x v + newDir c v) ⊆ closedBall 0 (1 - δ) := by
  have hseg := segment_subset_of_tube hδ hT
  have hx : ‖x‖ ≤ 1 - δ := mem_closedBall_zero_iff.mp (hseg (left_mem_segment _ _ _))
  have hxv : ‖x + v‖ ≤ 1 - δ := mem_closedBall_zero_iff.mp (hseg (right_mem_segment _ _ _))
  have hu := newDir_horizontal hc hv hv2
  have hu2 := newDir_two_ge hc hv hv2
  have hu2' := newDir_two_le (c := c) hv2
  have hhor : ∀ q : Space, ‖q‖ ≤ 1 → shear c q 0 ^ 2 + shear c q 1 ^ 2 ≤ 1 / 40 := by
    intro q hq
    have h1 := shear_horizontal hc q
    have h2 := norm_sq_eq q
    have h3 : ‖q‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg q]
    nlinarith [sq_nonneg (q 2)]
  have hsum : ∀ a b : ℝ, (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := fun a b => by
    nlinarith [sq_nonneg (a - b)]
  have hdiff : ∀ a b : ℝ, (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := fun a b => by
    nlinarith [sq_nonneg (a + b)]
  have hx2 : |x 2| ≤ 1 := (abs_coord_le_norm x 2).trans (by linarith)
  have hxv2 : |(x + v) 2| ≤ 1 := (abs_coord_le_norm (x + v) 2).trans (by linarith)
  have hball : ∀ q : Space, ‖q‖ ≤ 1 - δ → shear c q ∈ closedBall (0 : Space) (1 - δ) :=
    fun q hq => mem_closedBall_zero_iff.mpr ((shear_norm_le hc q).trans hq)
  apply (convex_closedBall (0 : Space) (1 - δ)).segment_subset
  · rw [newBase]
    split_ifs with h
    · rw [mem_closedBall_zero_iff, ← map_add]
      apply far_endpoint_norm hδ1 (hhor (x + v) (by linarith)) hu
      · simp only [PiLp.sub_apply]
        exact add_le_add (hdiff _ _) (hdiff _ _) |>.trans (by linarith)
      · simp only [PiLp.sub_apply, shear_apply_two, PiLp.add_apply] at hxv2 ⊢
        rw [abs_le] at hxv2 ⊢
        constructor <;> linarith
    · exact hball x hx
  · rw [newBase]
    split_ifs with h
    · rw [sub_add_cancel, ← map_add]
      exact hball _ hxv
    · rw [mem_closedBall_zero_iff]
      apply far_endpoint_norm hδ1 (hhor x (by linarith)) hu
      · simp only [PiLp.add_apply]
        exact add_le_add (hsum _ _) (hsum _ _) |>.trans (by linarith)
      · simp only [PiLp.add_apply, shear_apply_two] at hx2 ⊢
        rw [abs_le] at hx2 ⊢
        constructor <;> linarith

/-- The new tube lies in the unit ball. -/
theorem new_tube_subset_ball {c : ℝ} (hc : |c| ≤ 100) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100)
    {x v : Space} (hv : ‖v‖ = 1) (hv2 : 1 / 2 ≤ v 2) (hT : Tube δ x v ⊆ ball 0 1) :
    Tube δ (newBase c x v) (newDir c v) ⊆ ball 0 1 :=
  tube_subset_of_segment hδ (by linarith) (new_segment_subset hc hδ hδ1 hv hv2 hT)

/-- The image of the old tube lies in the new tube. -/
theorem shear_image_tube_subset_new {c : ℝ} (hc : |c| ≤ 100) (δ : ℝ) {x v : Space}
    (hv : ‖v‖ = 1) (hv2 : 1 / 2 ≤ v 2) :
    shear c '' Tube δ x v ⊆ Tube δ (newBase c x v) (newDir c v) :=
  (shear_image_tube hc δ x v).trans
    (thickening_subset_of_subset δ (segment_subset_new hc hv hv2))

end WangZahlLot.Obl.wz_compact_offset_normalization
