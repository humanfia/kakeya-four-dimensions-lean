-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/RootTestInclusion.lean (namespace renamed).

import Submission.Obl.k4_clean_cover_graph_atlas.RootTests

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MvPolynomial Submission.Lib.K4QuadraticSheets

/-- A close root with a narrow signed derivative window supplies the finite value
and derivative tests at the original point. -/
theorem point_tests_of_near_root {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2)
    {s η : ℝ} (hs : 0 < s) (hη : 0 ≤ η) (hcurv : |qc P| * η ≤ s / 20)
    (pos : Bool) (x : Fin 4 → ℝ) (w : ℝ)
    (hroot : eval (Fin.snoc (Fin.init x) w : Fin 4 → ℝ) P = 0)
    (hclose : |x 3 - w| ≤ η)
    (hder : if pos then
      19 / 20 * s ≤ eval (Fin.snoc (Fin.init x) w : Fin 4 → ℝ) (pderiv 3 P) ∧
      eval (Fin.snoc (Fin.init x) w : Fin 4 → ℝ) (pderiv 3 P) ≤ 21 / 20 * s
    else
      19 / 20 * s ≤ -eval (Fin.snoc (Fin.init x) w : Fin 4 → ℝ) (pderiv 3 P) ∧
      -eval (Fin.snoc (Fin.init x) w : Fin 4 → ℝ) (pderiv 3 P) ≤ 21 / 20 * s) :
    |eval x P| ≤ 2 * s * η ∧
      if pos then
        9 / 10 * s ≤ eval x (pderiv 3 P) ∧ eval x (pderiv 3 P) ≤ 11 / 10 * s
      else
        9 / 10 * s ≤ -eval x (pderiv 3 P) ∧ -eval x (pderiv 3 P) ≤ 11 / 10 * s := by
  let g := eval (Fin.snoc (Fin.init x) w : Fin 4 → ℝ) (pderiv 3 P)
  have hx : x = (Fin.snoc (Fin.init x) (x 3) : Fin 4 → ℝ) := (snoc_init_eq x).symm
  have hvalue : eval x P = g * (x 3 - w) + qc P / 2 * (x 3 - w) ^ 2 := by
    conv_lhs => rw [hx]
    rw [eval_quad_expand hP, hroot, zero_add]
  have hsource : eval x (pderiv 3 P) = g + qc P * (x 3 - w) := by
    conv_lhs => rw [hx]
    exact eval_pderiv_expand hP _ _ _
  have hg : |g| ≤ 21 / 20 * s := by
    cases pos <;> simp only [Bool.coe_false, Bool.coe_true, ite_false, ite_true] at hder
    · rw [abs_of_neg (by dsimp only [g]; linarith)]
      exact hder.2
    · rw [abs_of_pos (by dsimp only [g]; linarith)]
      exact hder.2
  have he : |qc P| * |x 3 - w| ≤ s / 20 :=
    (mul_le_mul_of_nonneg_left hclose (abs_nonneg _)).trans hcurv
  have herror : |qc P * (x 3 - w)| ≤ s / 20 := by simpa only [abs_mul] using he
  have hlinear : |g| * |x 3 - w| ≤ 21 / 20 * s * η :=
    mul_le_mul hg hclose (abs_nonneg _) (by positivity)
  have hsecond : |qc P| * |x 3 - w| * |x 3 - w| ≤ s / 20 * η :=
    mul_le_mul he hclose (abs_nonneg _) (by positivity)
  constructor
  · rw [hvalue]
    calc
      _ ≤ |g| * |x 3 - w| + |qc P| / 2 * |x 3 - w| ^ 2 := by
        calc
          _ ≤ |g * (x 3 - w)| + |qc P / 2 * (x 3 - w) ^ 2| := abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul, abs_div, abs_two, abs_pow]
      _ ≤ 2 * s * η := by nlinarith [mul_nonneg hs.le hη]
  · rw [hsource]
    obtain ⟨helo, hehi⟩ := abs_le.mp herror
    cases pos <;> simp only [Bool.coe_false, Bool.coe_true, ite_false, ite_true] at hder ⊢ <;>
      dsimp only [g] at * <;> constructor <;> linarith

/-- Root proximity at three sample times implies membership in the geometric root-test
set, with enough curvature margin for the whole-block root certificate. -/
theorem rootTestSet_of_near_roots {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2)
    {s η ta tb : ℝ} (hs : 0 < s) (hη : 0 ≤ η) (hcurv : |qc P| * η ≤ s / 80)
    (pos : Bool) (l : ℕ × (Fin 6 → ℝ))
    (hfit : ∀ t, t = ta ∨ t = (ta + tb) / 2 ∨ t = tb →
      ∃ w : ℝ, eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ) P = 0 ∧
        |(Submission.Lib.K4XInterface.gx l t) 3 - w| ≤ η ∧
        if pos then
          19 / 20 * s ≤ eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ) (pderiv 3 P) ∧
          eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ) (pderiv 3 P) ≤ 21 / 20 * s
        else
          19 / 20 * s ≤ -eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ) (pderiv 3 P) ∧
          -eval (Fin.snoc (Fin.init (Submission.Lib.K4XInterface.gx l t)) w : Fin 4 → ℝ) (pderiv 3 P) ≤ 21 / 20 * s) :
    l ∈ rootTestSet P s (2 * s * η) ta tb ∧ |qc P| * (2 * s * η) ≤ s ^ 2 / 40 := by
  have hcurv' : |qc P| * η ≤ s / 20 := hcurv.trans (by linarith)
  obtain ⟨wa, hra, hca, hda⟩ := hfit ta (Or.inl rfl)
  obtain ⟨wm, hrm, hcm, hdm⟩ := hfit ((ta + tb) / 2) (Or.inr (Or.inl rfl))
  obtain ⟨wb, hrb, hcb, hdb⟩ := hfit tb (Or.inr (Or.inr rfl))
  obtain ⟨hva, hwa⟩ := point_tests_of_near_root hP hs hη hcurv' pos _ wa hra hca hda
  obtain ⟨hvm, -⟩ := point_tests_of_near_root hP hs hη hcurv' pos _ wm hrm hcm hdm
  obtain ⟨hvb, hwb⟩ := point_tests_of_near_root hP hs hη hcurv' pos _ wb hrb hcb hdb
  constructor
  · refine ⟨hva, hvm, hvb, ?_⟩
    cases pos
    · exact Or.inr ⟨hwa.1, hwa.2, hwb.1, hwb.2⟩
    · exact Or.inl ⟨hwa.1, hwa.2, hwb.1, hwb.2⟩
  · nlinarith

end Submission.Obl.k4_clean_cover_graph_atlas
