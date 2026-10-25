import Submission.Lib.K4ProjectedGroups.LineSignal
import Submission.Lib.K4ContactNormalization
import Submission.Lib.K4HiddenQuadratic

/-! Adapted from: here:o223
   (x0927). Fixed time padding using the accepted native signal coefficients. -/

namespace Submission.Lib.K4ContactAffine

open Set MvPolynomial
open Submission.Lib.K4ContactNormalization

theorem unit_signal_with_time_margin (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (b : Fin 6 → ℝ) {H : ℝ}
    (hfit : ∀ t ∈ Icc (0 : ℝ) 1, |eval (point b t) P| ≤ H) :
    ∀ t ∈ Icc (-1 : ℝ) 2, |eval (point b t) P| ≤ 49 * H := by
  have hs : ∀ t ∈ Icc (0 : ℝ) 1, |Submission.Lib.K4ProjectedGroups.sig P b t| ≤ H := hfit
  have hH : 0 ≤ H := (abs_nonneg _).trans (hfit 0 ⟨le_rfl, zero_le_one⟩)
  have hc₀ := Submission.Lib.K4ProjectedGroups.abs_sc0_le hs
  have hc₁ := Submission.Lib.K4ProjectedGroups.abs_sc1_le hs
  have hc₂ := Submission.Lib.K4ProjectedGroups.abs_sc2_le hs
  intro t ht
  have ht2 : |t| ≤ 2 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have ht4 : |t ^ 2| ≤ 4 := by
    rw [abs_pow]
    nlinarith [abs_nonneg t]
  change |Submission.Lib.K4ProjectedGroups.sig P b t| ≤ _
  rw [Submission.Lib.K4ProjectedGroups.sig_eq hP]
  calc
    _ ≤ |Submission.Lib.K4ProjectedGroups.sc0 P b| + |t| * |Submission.Lib.K4ProjectedGroups.sc1 P b| +
        |t ^ 2| * |Submission.Lib.K4ProjectedGroups.sc2 P b| := by
      have h1 := abs_add_le
        (Submission.Lib.K4ProjectedGroups.sc0 P b + t * Submission.Lib.K4ProjectedGroups.sc1 P b)
        (t ^ 2 * Submission.Lib.K4ProjectedGroups.sc2 P b)
      have h2 := abs_add_le (Submission.Lib.K4ProjectedGroups.sc0 P b)
        (t * Submission.Lib.K4ProjectedGroups.sc1 P b)
      simp only [abs_mul] at h1 h2
      linarith
    _ ≤ H + 2 * (8 * H) + 4 * (8 * H) := by gcongr
    _ = 49 * H := by ring

theorem unit_native_fit_with_time_margin (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (b : Fin 6 → ℝ) {H : ℝ}
    (hfit : ∀ t ∈ Icc (0 : ℝ) 1, |eval (point b t) P| ≤ H ∧
      |eval (point b t) (pderiv 3 P)| ≤ H ∧
      |eval (point b t) (pderiv 3 (pderiv 3 P))| ≤ H) :
    ∀ t ∈ Icc (-1 : ℝ) 2, |eval (point b t) P| ≤ 432 * H ∧
      |eval (point b t) (pderiv 3 P)| ≤ 432 * H ∧
      |eval (point b t) (pderiv 3 (pderiv 3 P))| ≤ 432 * H := by
  have hH : 0 ≤ H := (abs_nonneg _).trans (hfit 0 ⟨le_rfl, zero_le_one⟩).1
  have h₁ : (pderiv (3 : Fin 4) P).totalDegree ≤ 2 :=
    (Submission.Lib.K4HiddenQuadratic.totalDegree_pderiv_le_pred P 3).trans (by omega)
  have h₂ : (pderiv (3 : Fin 4) (pderiv 3 P)).totalDegree ≤ 2 :=
    (Submission.Lib.K4HiddenQuadratic.totalDegree_pderiv_le_pred (pderiv 3 P) 3).trans (by omega)
  have h49 : 49 * H ≤ 432 * H := by linarith
  intro t ht
  exact ⟨(unit_signal_with_time_margin P hP b (fun t ht => (hfit t ht).1) t ht).trans h49,
    (unit_signal_with_time_margin (pderiv 3 P) h₁ b (fun t ht => (hfit t ht).2.1) t ht).trans h49,
    (unit_signal_with_time_margin (pderiv 3 (pderiv 3 P)) h₂ b (fun t ht => (hfit t ht).2.2) t ht).trans h49⟩

end Submission.Lib.K4ContactAffine
