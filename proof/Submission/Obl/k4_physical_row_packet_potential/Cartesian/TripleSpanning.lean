-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/TripleSpanning.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/-
x1037 (o287). Per-state spanning probability from strip breadth: three
independent samples of a velocity-bin law whose centers are not concentrated
on strips of width `w` span `ℝ³` after lifting, with determinant at least
`w²`, except with product mass `2 ps M³`.

If `|c₁ - c₀| < w` the second sample is in a strip around the first; otherwise
a small determinant puts the third sample in the strip of half-width `w` about
the line through the first two.
-/
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.TripleSelection
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.LiftFrame

set_option autoImplicit false

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

/-- Three planar velocities as the columns' data of `liftMatrix`. -/
def tripleVel {β : Type*} (c : β → EuclideanSpace ℝ (Fin 2)) (t : β × β × β) :
    Fin 3 → Fin 2 → ℝ :=
  ![fun k => c t.1 k, fun k => c t.2.1 k, fun k => c t.2.2 k]

theorem det_liftMatrix (J : Fin 3 → Fin 2 → ℝ) :
    (liftMatrix J).det = (J 1 0 - J 0 0) * (J 2 1 - J 0 1) - (J 2 0 - J 0 0) * (J 1 1 - J 0 1) := by
  rw [Matrix.det_fin_three]
  simp only [liftMatrix_apply, lift, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- A unit normal to a nonzero planar vector. -/
def unitNormal (d : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  ‖d‖⁻¹ • WithLp.toLp 2 ![-(d 1), d 0]

theorem norm_rot (d : EuclideanSpace ℝ (Fin 2)) :
    ‖(WithLp.toLp 2 ![-(d 1), d 0] : EuclideanSpace ℝ (Fin 2))‖ = ‖d‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_two, Fin.sum_univ_two]
  congr 1
  simp only [PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Real.norm_eq_abs, sq_abs, neg_sq]
  ring

theorem norm_unitNormal {d : EuclideanSpace ℝ (Fin 2)} (hd : d ≠ 0) : ‖unitNormal d‖ = 1 := by
  unfold unitNormal
  rw [norm_smul, norm_rot, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hd)]

theorem inner_unitNormal (d x : EuclideanSpace ℝ (Fin 2)) :
    ⟪unitNormal d, x⟫ = ‖d‖⁻¹ * (d 0 * x 1 - d 1 * x 0) := by
  unfold unitNormal
  rw [inner_smul_left, PiLp.inner_apply, Fin.sum_univ_two]
  simp only [PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    RCLike.inner_apply, conj_trivial, RCLike.conj_to_real]
  ring

/-- Small lifted determinants put a sample in a strip. -/
theorem small_det_strip (c₀ c₁ c₂ : EuclideanSpace ℝ (Fin 2)) {w : ℝ} (hw : 0 < w)
    (hdet : |(liftMatrix ![fun k => c₀ k, fun k => c₁ k, fun k => c₂ k]).det| < w ^ 2) :
    |c₁ 0 - c₀ 0| ≤ w ∨
      (w ≤ ‖c₁ - c₀‖ ∧ |⟪unitNormal (c₁ - c₀), c₂⟫ - ⟪unitNormal (c₁ - c₀), c₀⟫| ≤ w) := by
  by_cases hd : ‖c₁ - c₀‖ < w
  · left
    have h := PiLp.norm_apply_le (c₁ - c₀) 0
    rw [PiLp.sub_apply, Real.norm_eq_abs] at h
    linarith
  · right
    push_neg at hd
    refine ⟨hd, ?_⟩
    have hd0 : 0 < ‖c₁ - c₀‖ := hw.trans_le hd
    rw [← inner_sub_right, inner_unitNormal, abs_mul, abs_inv, abs_norm]
    rw [det_liftMatrix] at hdet
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at hdet
    have heq : (c₁ - c₀) 0 * (c₂ - c₀) 1 - (c₁ - c₀) 1 * (c₂ - c₀) 0 =
        (c₁ 0 - c₀ 0) * (c₂ 1 - c₀ 1) - (c₂ 0 - c₀ 0) * (c₁ 1 - c₀ 1) := by
      simp only [PiLp.sub_apply]
      ring
    rw [heq, inv_mul_le_iff₀ hd0]
    have : w ^ 2 ≤ ‖c₁ - c₀‖ * w := by nlinarith
    linarith

variable {β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β]

/-- **Spanning triples.** Strip breadth of the bin centers bounds the product
mass of nearly degenerate triples. -/
theorem prod3_small_det_le (ρ : Measure β) [IsFiniteMeasure ρ]
    (c : β → EuclideanSpace ℝ (Fin 2)) {w : ℝ} (hw : 0 < w) (ps M : ℝ≥0∞)
    (hM : ρ univ ≤ M)
    (hstrip : ∀ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 → ∀ s : ℝ,
      ρ {b | |⟪n, c b⟫ - s| ≤ w} ≤ ps * M) :
    (ρ.prod (ρ.prod ρ)) {t | |(liftMatrix (tripleVel c t)).det| < w ^ 2} ≤ 2 * ps * M ^ 3 := by
  have hmeas : ∀ S : Set (β × β × β), MeasurableSet S := fun S => (Set.to_countable S).measurableSet
  have hmeas2 : ∀ S : Set (β × β), MeasurableSet S := fun S => (Set.to_countable S).measurableSet
  let e : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
  have he : ‖e‖ = 1 := by simp [e]
  have hee (x : EuclideanSpace ℝ (Fin 2)) : ⟪e, x⟫ = x 0 := by
    simp [e, EuclideanSpace.inner_single_left]
  let A1 : Set (β × β × β) := {t | |c t.2.1 0 - c t.1 0| ≤ w}
  let A2 : Set (β × β × β) := {t | w ≤ ‖c t.2.1 - c t.1‖ ∧
    |⟪unitNormal (c t.2.1 - c t.1), c t.2.2⟫ - ⟪unitNormal (c t.2.1 - c t.1), c t.1⟫| ≤ w}
  have hsub : {t : β × β × β | |(liftMatrix (tripleVel c t)).det| < w ^ 2} ⊆ A1 ∪ A2 := by
    intro t ht
    exact small_det_strip (c t.1) (c t.2.1) (c t.2.2) hw ht
  have hA1 : (ρ.prod (ρ.prod ρ)) A1 ≤ ps * M ^ 3 := by
    rw [Measure.prod_apply (hmeas A1)]
    calc ∫⁻ b₀, (ρ.prod ρ) (Prod.mk b₀ ⁻¹' A1) ∂ρ ≤ ∫⁻ _, ps * M * M ∂ρ := by
          apply lintegral_mono
          intro b₀
          dsimp only
          have hset : Prod.mk b₀ ⁻¹' A1 = {b | |⟪e, c b⟫ - c b₀ 0| ≤ w} ×ˢ univ := by
            ext x
            simp only [A1, mem_preimage, mem_setOf_eq, mem_prod, mem_univ, and_true, hee]
          rw [hset, Measure.prod_prod]
          exact mul_le_mul' (hstrip e he _) hM
      _ = ps * M * M * ρ univ := lintegral_const _
      _ ≤ ps * M * M * M := by gcongr
      _ = ps * M ^ 3 := by ring
  have hA2 : (ρ.prod (ρ.prod ρ)) A2 ≤ ps * M ^ 3 := by
    rw [Measure.prod_apply (hmeas A2)]
    calc ∫⁻ b₀, (ρ.prod ρ) (Prod.mk b₀ ⁻¹' A2) ∂ρ ≤ ∫⁻ _, ps * M * M ∂ρ := by
          apply lintegral_mono
          intro b₀
          dsimp only
          rw [Measure.prod_apply (hmeas2 _)]
          calc ∫⁻ b₁, ρ (Prod.mk b₁ ⁻¹' (Prod.mk b₀ ⁻¹' A2)) ∂ρ ≤ ∫⁻ _, ps * M ∂ρ := by
                apply lintegral_mono
                intro b₁
                dsimp only
                by_cases hfar : w ≤ ‖c b₁ - c b₀‖
                · have hne : c b₁ - c b₀ ≠ 0 := by
                    intro h0
                    rw [h0, norm_zero] at hfar
                    linarith
                  refine (measure_mono ?_).trans (hstrip _ (norm_unitNormal hne)
                    ⟪unitNormal (c b₁ - c b₀), c b₀⟫)
                  intro b₂ hb₂
                  exact hb₂.2
                · have hempty : Prod.mk b₁ ⁻¹' (Prod.mk b₀ ⁻¹' A2) = ∅ := by
                    ext b₂
                    simp only [A2, mem_preimage, mem_setOf_eq, mem_empty_iff_false, iff_false,
                      not_and]
                    intro h
                    exact absurd h hfar
                  rw [hempty, measure_empty]
                  exact zero_le
            _ = ps * M * ρ univ := lintegral_const _
            _ ≤ ps * M * M := by gcongr
      _ = ps * M * M * ρ univ := lintegral_const _
      _ ≤ ps * M * M * M := by gcongr
      _ = ps * M ^ 3 := by ring
  calc (ρ.prod (ρ.prod ρ)) {t | |(liftMatrix (tripleVel c t)).det| < w ^ 2}
      ≤ (ρ.prod (ρ.prod ρ)) (A1 ∪ A2) := measure_mono hsub
    _ ≤ (ρ.prod (ρ.prod ρ)) A1 + (ρ.prod (ρ.prod ρ)) A2 := measure_union_le _ _
    _ ≤ ps * M ^ 3 + ps * M ^ 3 := add_le_add hA1 hA2
    _ = 2 * ps * M ^ 3 := by ring

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
