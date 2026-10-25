import Mathlib
import Submission.Obl.k4_algebraic_real_jet_comparison.SheetBounds
import Submission.Obl.k4_algebraic_real_jet_comparison.DirectionalDetection

/- Adapted from session x0381, o112, commit e55b3ba,
   Submission/Obl/k4_local_algebraic_graph_matching/DirectionalComparison.lean. -/
namespace Submission.Obl.k4_algebraic_real_jet_comparison

open Set Metric

/-- Uniform upper jets and finite-direction lower norm comparison for real algebraic sheets. -/
theorem exists_sheet_directional_comparison (D : ℕ) :
    ∃ q : ℕ, 1 ≤ q ∧ ∃ c : ℝ, 0 < c ∧
      ∃ V : Finset (EuclideanSpace ℝ (Fin 3)), V.Nonempty ∧
        (∀ v ∈ V, ‖v‖ = 1) ∧ ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧
        ∀ (f : EuclideanSpace ℂ (Fin 3) → ℂ),
          HasSheetRelation 3 D f → DifferentiableOn ℂ f (ball 0 4) →
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 → (f (realEmbedding 3 x)).im = 0) →
          (∀ A : ℝ, 0 < A →
            (∀ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ (1 : ℝ) / 2 → ‖f (realEmbedding 3 y)‖ ≤ A) →
            ∀ (x v : EuclideanSpace ℝ (Fin 3)), ‖x‖ ≤ (3 : ℝ) / 4 → ‖v‖ ≤ 1 → ∀ m : ℕ,
              |iteratedDeriv m (fun t : ℝ => (f (realEmbedding 3 x +
                (t : ℂ) • realEmbedding 3 v)).re) 0| ≤ B m * A) ∧
          (∀ (x y : EuclideanSpace ℝ (Fin 3)), ‖x‖ ≤ (1 : ℝ) / 2 → ‖y‖ ≤ (1 : ℝ) / 2 →
            ∃ v ∈ V, ∃ j : ℕ, j < q ∧ c * ‖f (realEmbedding 3 y)‖ ≤
              |iteratedDeriv j (fun t : ℝ => (f (realEmbedding 3 x +
                (t : ℂ) • realEmbedding 3 v)).re) 0|) := by
  classical
  obtain ⟨C, hC, hnorm⟩ := exists_sheet_norm_constant_two 3 D
  obtain ⟨q, hq, c, hc, V, hVne, hV, hdetect⟩ := exists_finite_directional_detection C hC
  let B : ℕ → ℝ := fun m => (m.factorial : ℝ) * C / (5 / 4 : ℝ) ^ m
  have hB : ∀ m, 0 < B m := by
    intro m
    dsimp [B]
    exact div_pos (mul_pos (by exact_mod_cast Nat.factorial_pos m) hC) (by positivity)
  refine ⟨q, hq, c, hc, V, hVne, hV, B, hB, ?_⟩
  intro f hrel hf hreal
  constructor
  · intro A hA hbase x v hx hv m
    have hbound := hnorm f hrel hf A hA hbase
    have hin : ‖realEmbedding 3 x + (0 : ℂ) • realEmbedding 3 v‖ + (5 : ℝ) / 4 ≤ 2 := by
      simp only [zero_smul, add_zero, LinearIsometry.norm_map]
      linarith
    have hh := directional_real_jet_bound hf hbound (realEmbedding 3 x) (realEmbedding 3 v)
      (by simpa only [LinearIsometry.norm_map] using hv) 0
      (by norm_num : (0 : ℝ) < 5 / 4) hin m
    convert hh using 1 <;> dsimp [B] <;> ring
  · intro x y hx hy
    have hfcont : ContinuousOn (fun z : EuclideanSpace ℝ (Fin 3) => ‖f (realEmbedding 3 z)‖)
        (closedBall 0 (1 / 2)) := by
      apply (hf.continuousOn.comp (realEmbedding 3).continuous.continuousOn ?_).norm
      intro z hz
      rw [mem_ball, dist_zero_right, LinearIsometry.norm_map]
      have hz' := mem_closedBall_zero_iff.mp hz
      linarith
    obtain ⟨w, hw, hmax⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2)).exists_isMaxOn
      (by exact ⟨0, by simp⟩) hfcont
    let S := ‖f (realEmbedding 3 w)‖
    have hS : 0 ≤ S := norm_nonneg _
    have hbase : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ (1 : ℝ) / 2 →
        ‖f (realEmbedding 3 z)‖ ≤ S := by
      intro z hz
      exact hmax (mem_closedBall_zero_iff.mpr hz)
    by_cases hS0 : S = 0
    · obtain ⟨v, hv⟩ := hVne
      have hzero : ‖f (realEmbedding 3 y)‖ = 0 :=
        le_antisymm (by simpa only [hS0] using hbase y hy) (norm_nonneg _)
      refine ⟨v, hv, 0, by omega, ?_⟩
      simp only [hzero, mul_zero]
      exact abs_nonneg _
    · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
      let F : EuclideanSpace ℂ (Fin 3) → ℂ := fun z => ((S⁻¹ : ℝ) : ℂ) * f z
      have hFnorm (z) : ‖F z‖ = ‖f z‖ / S := by
        simp only [F, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hSpos), div_eq_inv_mul]
      have hFbound : ∀ z, ‖z‖ ≤ 2 → ‖F z‖ ≤ C := by
        intro z hz
        rw [hFnorm]
        exact (div_le_iff₀ hSpos).mpr (hnorm f hrel hf S hSpos hbase z hz)
      have hFreal : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ 1 →
          (F (realEmbedding 3 z)).im = 0 := by
        intro z hz
        simp [F, Complex.mul_im, hreal z hz]
      have hFw : 1 ≤ ‖F (realEmbedding 3 w)‖ := by
        rw [hFnorm]
        change 1 ≤ S / S
        rw [div_self hS0]
      obtain ⟨v, hv, j, hj, hlarge⟩ := hdetect F (hf.const_mul _) hFbound hFreal
        ⟨w, mem_closedBall_zero_iff.mp hw, hFw⟩ x hx
      have he : (fun t : ℝ => (F (realEmbedding 3 x + (t : ℂ) • realEmbedding 3 v)).re) =
          (fun t : ℝ => S⁻¹ * (f (realEmbedding 3 x + (t : ℂ) • realEmbedding 3 v)).re) := by
        funext t
        simp [F, Complex.mul_re]
      rw [he, iteratedDeriv_const_mul_field, abs_mul, abs_inv, abs_of_pos hSpos] at hlarge
      have hh : c * S ≤ |iteratedDeriv j
          (fun t : ℝ => (f (realEmbedding 3 x + (t : ℂ) • realEmbedding 3 v)).re) 0| := by
        apply (le_div_iff₀ hSpos).mp
        simpa only [div_eq_inv_mul] using hlarge
      exact ⟨v, hv, j, hj, (mul_le_mul_of_nonneg_left (hbase y hy) hc.le).trans hh⟩

end Submission.Obl.k4_algebraic_real_jet_comparison
