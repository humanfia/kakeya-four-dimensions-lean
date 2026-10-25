-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.SlabVolume.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.OrthogonalBox
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Slab
import Submission.WZ.Obl.wz_seed_of_balanced_robust_clusters.Geometry

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open Module MeasureTheory Set Metric
open scoped ENNReal

lemma volume_ball_inter_slab_le {ν : E} (hν : ‖ν‖ = 1) (s : ℝ) {r R : ℝ}
    (hr : 0 ≤ r) (hR : 0 ≤ R) :
    volume (closedBall (0 : E) R ∩ slab (innerSL ℝ ν) s r) ≤ ENNReal.ofReal (8 * r * R ^ 2) := by
  obtain ⟨u, hu⟩ := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.exists_basis_first hν
  have hsub : closedBall (0 : E) R ∩ slab (innerSL ℝ ν) s r ⊆
      orthogonalBox ![r, R, R] (s • ν) u := by
    rintro q ⟨hq, hsl⟩ i
    have hqnorm : ‖q‖ ≤ R := by simpa using hq
    have hcoord (j : Fin 3) : |inner ℝ (u j) q| ≤ R := by
      exact (abs_real_inner_le_norm _ _).trans (by rw [u.norm_eq_one, one_mul]; exact hqnorm)
    have horth (j : Fin 3) : inner ℝ (u j) ν = if j = 0 then 1 else 0 := by
      rw [← hu]
      exact orthonormal_iff_ite.mp u.orthonormal j 0
    change |inner ℝ (u i) (q - s • ν)| ≤ ![r, R, R] i
    rw [inner_sub_right, real_inner_smul_right, horth]
    fin_cases i
    · simpa [slab, hu] using hsl
    · simpa using hcoord 1
    · simpa using hcoord 2
  calc volume (closedBall (0 : E) R ∩ slab (innerSL ℝ ν) s r)
      ≤ volume (orthogonalBox ![r, R, R] (s • ν) u) := measure_mono hsub
    _ = ENNReal.ofReal (8 * r * R ^ 2) := by
      rw [volume_orthogonalBox]
      · congr 1
        simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        ring
      · intro i
        fin_cases i <;> first | exact hr | exact hR

/-- A slab meeting the small central ball occupies at least a constant times its
truncated width inside the unit ball, uniformly in its offset and orientation. -/
lemma volume_ball_inter_slab_ge {ν p : E} (hν : ‖ν‖ = 1)
    {s r : ℝ} (hr : 0 < r) (hp : ‖p‖ ≤ 1 / 100)
    (hps : |inner ℝ ν p - s| ≤ r) :
    ENNReal.ofReal (min r 1 / 8) ≤ volume (ball (0 : E) 1 ∩ slab (innerSL ℝ ν) s r) := by
  obtain ⟨u, hu⟩ := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.exists_basis_first hν
  let α : ℝ := min r 1 / 4
  have hα : 0 < α := by dsimp [α]; positivity
  have hαr : 2 * α ≤ r := by
    have h := min_le_left r (1 : ℝ)
    dsimp [α]
    linarith [lt_min hr (by norm_num : (0 : ℝ) < 1)]
  have hα1 : α ≤ 1 / 4 := by dsimp [α]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  let z := inner ℝ ν p - s
  let t : ℝ := if 0 ≤ z then -α else α
  let c : E := p + t • ν
  have ht : |t| = α := by
    dsimp [t]
    split_ifs <;> simp [abs_of_pos hα, abs_neg]
  have hc : ‖c‖ ≤ 1 / 100 + α := by
    calc ‖c‖ ≤ ‖p‖ + ‖t • ν‖ := norm_add_le _ _
      _ = ‖p‖ + α := by rw [norm_smul, Real.norm_eq_abs, hν, mul_one, ht]
      _ ≤ _ := by linarith
  have hboxball : orthogonalBox ![α, 1 / 4, 1 / 4] c u ⊆ ball (0 : E) 1 := by
    apply orthogonalBox_subset_ball _ _ _ (by norm_num : (0 : ℝ) ≤ 1 / 4)
    · intro i
      fin_cases i
      · exact hα1
      · exact le_rfl
      · exact le_rfl
    · linarith
  have hboxslab : orthogonalBox ![α, 1 / 4, 1 / 4] c u ⊆ slab (innerSL ℝ ν) s r := by
    intro q hq
    have hq0 := hq 0
    change |inner ℝ (u 0) (q - c)| ≤ α at hq0
    rw [hu] at hq0
    have hself : inner ℝ ν ν = 1 := by rw [real_inner_self_eq_norm_sq, hν]; norm_num
    have he : inner ℝ ν q - s = inner ℝ ν (q - c) + z + t := by
      dsimp [c, z]
      rw [inner_sub_right, inner_add_right, real_inner_smul_right, hself, mul_one]
      ring
    change |inner ℝ ν q - s| ≤ r
    rw [he, abs_le]
    have hz := abs_le.mp hps
    have hq' := abs_le.mp hq0
    dsimp [t]
    split_ifs with h
    · constructor <;> change _ ≤ _ <;> dsimp [z] at h ⊢ <;> linarith
    · constructor <;> change _ ≤ _ <;> dsimp [z] at h ⊢ <;> linarith
  calc ENNReal.ofReal (min r 1 / 8)
      = volume (orthogonalBox ![α, 1 / 4, 1 / 4] c u) := by
        rw [volume_orthogonalBox]
        · congr 1
          simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
          dsimp [α]
          ring
        · intro i
          fin_cases i
          · exact hα.le
          · norm_num
          · norm_num
    _ ≤ _ := measure_mono (subset_inter hboxball hboxslab)

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
