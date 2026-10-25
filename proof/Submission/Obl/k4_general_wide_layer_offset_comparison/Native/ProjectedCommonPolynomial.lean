-- Adapted from this LOT tree, obligation o254, branch x0898, commit f25a0cc9, file Submission/Obl/k4_general_parent_wide_layer_candidates/Native/ProjectedCommonPolynomial.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
/- Adapted from this LOT tree, obligation o200, session x0934, commit 3ef9d3b45123d3245f500a2dc2bd85270a8fff3d,
   Submission/Obl/k4_finite_projected_horizontal_candidates/ProjectedCommonPolynomial.lean. Original source attributions are retained below. -/
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.CommonPhysicalFrame
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.ProjectedPolynomialNorm
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.ProjectedFrameBounds

/-! Literal projected polynomials on a common comparison domain. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.CommonDomain

open MvPolynomial Set
open Submission.Lib.K4ScalarSwitching.PolynomialDegree

noncomputable section

def projectedCommonSub (q g m : ℝ) (c : Code) : Fin 2 → MvPolynomial (Fin 3) ℝ :=
  ![C (timeCenter q c) + C (100 * q) * X 0,
    C ((c 4 : ℝ) * m) + C (100 * q * ((c 3 : ℝ) * g)) * X 0 + C (100 * m) * X 2]

def projectedCommonPolynomial (G : MvPolynomial (Fin 2) ℝ) (q g m : ℝ) (c : Code) :
    MvPolynomial (Fin 3) ℝ := aeval (projectedCommonSub q g m c) G

theorem projectedCommonSub_degree (q g m : ℝ) (c : Code) (i : Fin 2) :
    (projectedCommonSub q g m c i).totalDegree ≤ 1 := by
  fin_cases i
  · change (C (timeCenter q c) + C (100 * q) * X (0 : Fin 3)).totalDegree ≤ 1
    exact degree_add_le (by simp) ((degree_C_mul_le _ _).trans (by simp))
  · change (C ((c 4 : ℝ) * m) + C (100 * q * ((c 3 : ℝ) * g)) * X (0 : Fin 3) + C (100 * m) * X 2).totalDegree ≤ 1
    exact degree_add_le (degree_add_le (by simp only [totalDegree_C]; omega) ((degree_C_mul_le _ _).trans (by simp)))
      ((degree_C_mul_le _ _).trans (by simp))

theorem projectedCommonPolynomial_degree (G : MvPolynomial (Fin 2) ℝ) (q g m : ℝ) (c : Code) :
    (projectedCommonPolynomial G q g m c).totalDegree ≤ G.totalDegree :=
  degree_aeval_le G _ (projectedCommonSub_degree q g m c)

theorem projectedCommonPolynomial_eval (G : MvPolynomial (Fin 2) ℝ) (q χ g m : ℝ) (c : Code)
    (x : Fin 3 → ℝ) :
    eval x (projectedCommonPolynomial G q g m c) =
      eval ![(physicalBase q χ g m c x) 0, (physicalBase q χ g m c x) 2] G := by
  unfold projectedCommonPolynomial
  rw [aeval_def]
  change eval₂ (RingHom.id ℝ) x (eval₂ C (projectedCommonSub q g m c) G) = _
  rw [← eval₂_assoc]
  congr 1
  ext i
  fin_cases i <;> simp [projectedCommonSub, physicalBase, minorCenter] <;> ring

theorem projectedCommonPolynomial_at_source (G : MvPolynomial (Fin 2) ℝ)
    {q χ g m : ℝ} (hq : q ≠ 0) (hχ : χ ≠ 0) (hm : m ≠ 0) (c : Code) (source : Fin 3 → ℝ) :
    eval (coords q χ g m c source) (projectedCommonPolynomial G q g m c) = eval ![source 0, source 2] G := by
  rw [projectedCommonPolynomial_eval G q χ g m, physicalBase_coords hq hχ hm]

theorem projectedCommonPolynomial_eval_complex (G : MvPolynomial (Fin 2) ℝ) (q g m : ℝ) (c : Code)
    (z : EuclideanSpace ℂ (Fin 3)) :
    eval₂ (algebraMap ℝ ℂ) (fun i => z i) (projectedCommonPolynomial G q g m c) =
      eval₂ (algebraMap ℝ ℂ) ![complexTime q c z, complexMinor q g m c z] G := by
  unfold projectedCommonPolynomial
  rw [aeval_def]
  change eval₂ (algebraMap ℝ ℂ) (fun i => z i) (eval₂ C (projectedCommonSub q g m c) G) = _
  rw [← eval₂_assoc]
  congr 1
  ext i
  fin_cases i
  · change eval₂ (algebraMap ℝ ℂ) (fun i => z i)
      (C (timeCenter q c) + C (100 * q) * X 0) = complexTime q c z
    simp only [eval₂_add, eval₂_mul, eval₂_C, eval₂_X, complexTime]
    rfl
  · change eval₂ (algebraMap ℝ ℂ) (fun i => z i)
      (C ((c 4 : ℝ) * m) + C (100 * q * ((c 3 : ℝ) * g)) * X 0 + C (100 * m) * X 2) =
        complexMinor q g m c z
    simp only [eval₂_add, eval₂_mul, eval₂_C, eval₂_X, complexMinor]
    rfl

/-- Every actual projected label/domain has a complex bound which is a fixed
power of its old loss. Thin strip widths and the original mesh cause no loss. -/
theorem exists_projected_common_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : MvPolynomial (Fin 2) ℝ), G.totalDegree ≤ 2 →
      ∀ (H β q χ g m t u v : ℝ), 1 ≤ H → 0 < β → 0 < q → q ≤ 1 → 0 < g → 0 < m →
        q * g ≤ m → m ≤ β → ∀ (b : Fin 6 → ℝ), t ∈ Icc (0 : ℝ) 1 →
      (∀ r ∈ Icc (0 : ℝ) 1, |b 1 + r * b 4 - u - r * v| ≤ H * β) →
      (∀ r ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1, |eval ![r, u + r * v + β * w] G| ≤ H) →
      ∀ z : EuclideanSpace ℂ (Fin 3), ‖z‖ ≤ 4 →
        ‖eval₂ (algebraMap ℝ ℂ) (fun i => z i)
          (projectedCommonPolynomial G q g m (code q χ g m b t))‖ ≤ C * H ^ 3 := by
  obtain ⟨C, hC, hbound⟩ := exists_projected_strip_complex_bound
  refine ⟨9000000 * C, by positivity, ?_⟩
  intro G hG H β q χ g m t u v hH hβ hq hq1 hg hm hqg hmβ b ht hfit hstrip z hz
  let c := code q χ g m b t
  let x : Fin 2 → ℂ := ![complexTime q c z,
    ((complexMinor q g m c z - (u : ℂ) - complexTime q c z * (v : ℂ)) / (β : ℂ) + 1) / 2]
  have hx := projected_common_complex_box (χ := χ) hH hβ hq hq1 hg hm hqg hmβ b ht hfit z hz
  have hx' : ∀ i, ‖x i‖ ≤ 1000 * H := by
    intro i
    fin_cases i
    · exact hx.1
    · exact hx.2
  have h := hbound G hG u v β H (by linarith only [hH]) hstrip (1000 * H) (by linarith only [hH]) x hx'
  have hxy : (![x 0, (u : ℂ) + (v : ℂ) * x 0 + (β : ℂ) * (2 * x 1 - 1)] : Fin 2 → ℂ) =
      ![complexTime q c z, complexMinor q g m c z] := by
    ext i
    fin_cases i
    · rfl
    · dsimp [x]
      field_simp [Complex.ofReal_ne_zero.mpr hβ.ne']
      ring
  rw [hxy] at h
  rw [projectedCommonPolynomial_eval_complex]
  exact h.trans_eq (by ring)

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.CommonDomain
