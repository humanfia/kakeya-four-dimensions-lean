import Mathlib
import Submission.Obl.k4_algebraic_sheet_bound.LineGeometry

/- Adapted from session x0381, o112, commit e55b3ba,
   Submission/Obl/k4_local_algebraic_graph_matching/RealGeometry.lean. -/
namespace Submission.Obl.k4_algebraic_real_jet_comparison

open Set Metric

/-- The standard real slice of complex Euclidean space as a real linear isometry. -/
noncomputable def realEmbedding (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) where
  toFun x := WithLp.toLp 2 (fun i => (x i : ℂ))
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp
  norm_map' x := Submission.Obl.k4_algebraic_sheet_bound.norm_complexify x

lemma realEmbedding_line {n : ℕ} (x v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    realEmbedding n (x + t • v) = realEmbedding n x + (t : ℂ) • realEmbedding n v := by
  ext i
  simp [realEmbedding]

lemma norm_line_le_of_endpoints {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x v : E) {t s B : ℝ} (ht : 0 ≤ t) (hs : s ∈ Icc (0 : ℝ) t)
    (hx : ‖x‖ ≤ B) (hy : ‖x + t • v‖ ≤ B) : ‖x + s • v‖ ≤ B := by
  by_cases ht0 : t = 0
  · have hs0 : s = 0 := by linarith [hs.1, hs.2]
    simpa [hs0] using hx
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hu0 : 0 ≤ s / t := div_nonneg hs.1 ht
  have hu1 : s / t ≤ 1 := (div_le_one htpos).mpr hs.2
  have he : (1 - s / t) • x + (s / t) • (x + t • v) = x + s • v := by
    calc
      _ = x + ((s / t) * t) • v := by module
      _ = _ := by rw [div_mul_cancel₀ _ ht0]
  have hh := (convex_closedBall (0 : E) B)
    (mem_closedBall_zero_iff.mpr hx) (mem_closedBall_zero_iff.mpr hy)
    (sub_nonneg.mpr hu1) hu0 (by ring : 1 - s / t + s / t = 1)
  simpa only [he, mem_closedBall_zero_iff] using hh

/-- Parametrize the displacement between two points of the real half-ball by a unit vector. -/
lemma exists_real_unit_displacement (x y : EuclideanSpace ℝ (Fin 3))
    (hx : ‖x‖ ≤ (1 : ℝ) / 2) (hy : ‖y‖ ≤ (1 : ℝ) / 2) :
    ∃ (t : ℝ) (v : EuclideanSpace ℝ (Fin 3)), t ∈ Icc (0 : ℝ) 1 ∧ ‖v‖ = 1 ∧
      y = x + t • v := by
  by_cases he : y = x
  · refine ⟨0, WithLp.toLp 2 ![1, 0, 0], by norm_num, ?_, by simpa using he⟩
    norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_succ]
  · let t := ‖y - x‖
    have ht : 0 < t := norm_pos_iff.mpr (sub_ne_zero.mpr he)
    refine ⟨t, t⁻¹ • (y - x), ⟨ht.le, ?_⟩, ?_, ?_⟩
    · exact (norm_sub_le y x).trans (by linarith)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
      exact inv_mul_cancel₀ ht.ne'
    · rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
      abel

end Submission.Obl.k4_algebraic_real_jet_comparison
