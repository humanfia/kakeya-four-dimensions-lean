-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.PolyExtension.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_intermediate_twist_normalization.PolyShear

/-!
# The new round tubes for an arbitrary offset

For a transversal unit tube `(x, v)` with `v 2 ≥ 1/2` in the unit ball, the image of its axis
under `pshear c` is a segment of length `l ∈ [v 2, 1]`. We extend it to a unit segment towards
the height `0`; the extended segment stays in the closed ball of radius `1 - δ`, so its
`δ`-thickening is a round unit tube in the unit ball containing the image of the old tube.
The constants do not depend on `c`, since `pshear c` compresses the horizontal coordinates by
the factor `1/40` in square for every `c`.
-/

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_compact_offset_normalization (Space Tube mem_segment_param
  segment_subset_of_tube tube_subset_of_segment norm_le_of_sq_le abs_coord_le_norm)

/-- The direction of the new tube. -/
noncomputable def pnewDir (c : ℝ) (v : Space) : Space := ‖pshear c v‖⁻¹ • pshear c v

/-- The base point of the new tube. -/
noncomputable def pnewBase (c : ℝ) (x v : Space) : Space :=
  if 0 ≤ 2 * x 2 + v 2 then pshear c x + pshear c v - pnewDir c v else pshear c x

section

variable {c : ℝ} {v : Space}

theorem pshear_norm_ge : v 2 ≤ ‖pshear c v‖ := by
  have := abs_coord_le_norm (pshear c v) 2
  rw [pshear_apply_two] at this
  exact (le_abs_self _).trans this

theorem pshear_norm_pos (hv2 : 1 / 2 ≤ v 2) : 0 < ‖pshear c v‖ := by
  have := pshear_norm_ge (c := c) (v := v)
  linarith

theorem pnewDir_norm (hv2 : 1 / 2 ≤ v 2) : ‖pnewDir c v‖ = 1 := by
  rw [pnewDir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (pshear_norm_pos hv2).ne']

theorem pshear_eq_smul_pnewDir (hv2 : 1 / 2 ≤ v 2) :
    pshear c v = ‖pshear c v‖ • pnewDir c v := by
  rw [pnewDir, smul_smul, mul_inv_cancel₀ (pshear_norm_pos hv2).ne', one_smul]

theorem pnewDir_apply (i : Fin 3) : pnewDir c v i = pshear c v i / ‖pshear c v‖ := by
  rw [pnewDir]
  simp [div_eq_inv_mul]

theorem pnewDir_two_ge (hv : ‖v‖ = 1) (hv2 : 1 / 2 ≤ v 2) :
    v 2 ≤ pnewDir c v 2 := by
  rw [pnewDir_apply, pshear_apply_two, le_div_iff₀ (pshear_norm_pos hv2)]
  have h1 : ‖pshear c v‖ ≤ 1 := hv ▸ pshear_norm_le c v
  nlinarith

theorem pnewDir_two_le (hv2 : 1 / 2 ≤ v 2) : pnewDir c v 2 ≤ 1 := by
  rw [pnewDir_apply, pshear_apply_two, div_le_one (pshear_norm_pos hv2)]
  exact pshear_norm_ge

theorem pnewDir_transversal (hv : ‖v‖ = 1) (hv2 : 1 / 2 ≤ v 2) :
    (1 / 2 : ℝ) ≤ |pnewDir c v 2| :=
  hv2.trans ((pnewDir_two_ge hv hv2).trans (le_abs_self _))

theorem pnewDir_horizontal (hv : ‖v‖ = 1) (hv2 : 1 / 2 ≤ v 2) :
    pnewDir c v 0 ^ 2 + pnewDir c v 1 ^ 2 ≤ 1 / 10 := by
  rw [pnewDir_apply, pnewDir_apply, div_pow, div_pow, ← add_div,
    div_le_iff₀ (pow_pos (pshear_norm_pos hv2) 2)]
  have h1 := pshear_horizontal c v
  have h2 : v 0 ^ 2 + v 1 ^ 2 ≤ 1 := by
    have := WangZahlLot.Obl.wz_compact_offset_normalization.norm_sq_eq v
    rw [hv] at this
    nlinarith [sq_nonneg (v 2)]
  have h3 : (1 / 2 : ℝ) ^ 2 ≤ ‖pshear c v‖ ^ 2 :=
    pow_le_pow_left₀ (by norm_num) (hv2.trans pshear_norm_ge) 2
  nlinarith

end

/-- The image of the old axis lies on the new axis. -/
theorem psegment_subset_new (c : ℝ) {x v : Space} (hv : ‖v‖ = 1)
    (hv2 : 1 / 2 ≤ v 2) :
    segment ℝ (pshear c x) (pshear c x + pshear c v) ⊆
      segment ℝ (pnewBase c x v) (pnewBase c x v + pnewDir c v) := by
  set l := ‖pshear c v‖ with hl
  have hl1 : l ≤ 1 := hv ▸ pshear_norm_le c v
  have hl0 : 0 ≤ l := norm_nonneg _
  have hAv : pshear c v = l • pnewDir c v := pshear_eq_smul_pnewDir hv2
  apply (convex_segment _ _).segment_subset
  · rw [pnewBase]
    split_ifs
    · refine mem_segment_param.mpr ⟨1 - l, ⟨by linarith, by linarith⟩, ?_⟩
      rw [hAv]
      module
    · exact left_mem_segment _ _ _
  · rw [pnewBase]
    split_ifs
    · refine mem_segment_param.mpr ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
      module
    · exact mem_segment_param.mpr ⟨l, ⟨hl0, hl1⟩, by rw [hAv]⟩

/-- An endpoint of the new axis away from the image axis stays well inside the ball. -/
private theorem far_endpoint_norm' {δ : ℝ} (hδ1 : δ ≤ 1 / 100) {e q u : Space}
    (hq : q 0 ^ 2 + q 1 ^ 2 ≤ 1 / 40) (hu : u 0 ^ 2 + u 1 ^ 2 ≤ 1 / 10)
    (he0 : e 0 ^ 2 + e 1 ^ 2 ≤ 2 * (q 0 ^ 2 + q 1 ^ 2) + 2 * (u 0 ^ 2 + u 1 ^ 2))
    (he2 : |e 2| ≤ 3 / 4) : ‖e‖ ≤ 1 - δ := by
  apply norm_le_of_sq_le (by linarith)
  have h2 : e 2 ^ 2 ≤ (3 / 4) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) he2 2
  nlinarith

/-- The new axis lies in the closed ball of radius `1 - δ`. -/
theorem pnew_segment_subset (c : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100)
    {x v : Space} (hv : ‖v‖ = 1) (hv2 : 1 / 2 ≤ v 2) (hT : Tube δ x v ⊆ ball 0 1) :
    segment ℝ (pnewBase c x v) (pnewBase c x v + pnewDir c v) ⊆ closedBall 0 (1 - δ) := by
  have hseg := segment_subset_of_tube hδ hT
  have hx : ‖x‖ ≤ 1 - δ := mem_closedBall_zero_iff.mp (hseg (left_mem_segment _ _ _))
  have hxv : ‖x + v‖ ≤ 1 - δ := mem_closedBall_zero_iff.mp (hseg (right_mem_segment _ _ _))
  have hu := pnewDir_horizontal (c := c) hv hv2
  have hu2 := pnewDir_two_ge (c := c) hv hv2
  have hu2' := pnewDir_two_le (c := c) hv2
  have hhor : ∀ q : Space, ‖q‖ ≤ 1 → pshear c q 0 ^ 2 + pshear c q 1 ^ 2 ≤ 1 / 40 := by
    intro q hq
    have h1 := pshear_horizontal c q
    have h2 := WangZahlLot.Obl.wz_compact_offset_normalization.norm_sq_eq q
    have h3 : ‖q‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg q]
    nlinarith [sq_nonneg (q 2)]
  have hsum : ∀ a b : ℝ, (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := fun a b => by
    nlinarith [sq_nonneg (a - b)]
  have hdiff : ∀ a b : ℝ, (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := fun a b => by
    nlinarith [sq_nonneg (a + b)]
  have hx2 : |x 2| ≤ 1 := (abs_coord_le_norm x 2).trans (by linarith)
  have hxv2 : |(x + v) 2| ≤ 1 := (abs_coord_le_norm (x + v) 2).trans (by linarith)
  have hball : ∀ q : Space, ‖q‖ ≤ 1 - δ → pshear c q ∈ closedBall (0 : Space) (1 - δ) :=
    fun q hq => mem_closedBall_zero_iff.mpr ((pshear_norm_le c q).trans hq)
  apply (convex_closedBall (0 : Space) (1 - δ)).segment_subset
  · rw [pnewBase]
    split_ifs with h
    · rw [mem_closedBall_zero_iff, ← map_add]
      apply far_endpoint_norm' hδ1 (hhor (x + v) (by linarith)) hu
      · simp only [PiLp.sub_apply]
        exact add_le_add (hdiff _ _) (hdiff _ _) |>.trans (by linarith)
      · simp only [PiLp.sub_apply, pshear_apply_two, PiLp.add_apply] at hxv2 ⊢
        rw [abs_le] at hxv2 ⊢
        constructor <;> linarith
    · exact hball x hx
  · rw [pnewBase]
    split_ifs with h
    · rw [sub_add_cancel, ← map_add]
      exact hball _ hxv
    · rw [mem_closedBall_zero_iff]
      apply far_endpoint_norm' hδ1 (hhor x (by linarith)) hu
      · simp only [PiLp.add_apply]
        exact add_le_add (hsum _ _) (hsum _ _) |>.trans (by linarith)
      · simp only [PiLp.add_apply, pshear_apply_two] at hx2 ⊢
        rw [abs_le] at hx2 ⊢
        constructor <;> linarith

/-- The new tube lies in the unit ball. -/
theorem pnew_tube_subset_ball (c : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100)
    {x v : Space} (hv : ‖v‖ = 1) (hv2 : 1 / 2 ≤ v 2) (hT : Tube δ x v ⊆ ball 0 1) :
    Tube δ (pnewBase c x v) (pnewDir c v) ⊆ ball 0 1 :=
  tube_subset_of_segment hδ (by linarith) (pnew_segment_subset c hδ hδ1 hv hv2 hT)

/-- The image of the old tube lies in the new tube. -/
theorem pshear_image_tube_subset_new (c δ : ℝ) {x v : Space}
    (hv : ‖v‖ = 1) (hv2 : 1 / 2 ≤ v 2) :
    pshear c '' Tube δ x v ⊆ Tube δ (pnewBase c x v) (pnewDir c v) :=
  (pshear_image_tube c δ x v).trans
    (thickening_subset_of_subset δ (psegment_subset_new c hv hv2))

end WangZahlLot.Obl.wz_intermediate_twist_normalization
