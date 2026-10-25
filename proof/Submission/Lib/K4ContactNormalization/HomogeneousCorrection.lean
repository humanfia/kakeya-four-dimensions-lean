import Submission.Lib.K4ContactNormalization.ResidualNormalization
import Submission.Lib.K4HiddenQuadratic
import Submission.Lib.K4PolynomialRemezThree.OriginalMass

/-! Adapted from: here:o200 (session x0696). -/

/-! A base correction preserves the original hidden derivatives. Its
coefficients can be calibrated by original base mass instead of the size of
the affine hidden predictor. -/

namespace Submission.Lib.K4ContactNormalization

open MvPolynomial MeasureTheory Set
open Submission.Lib.K4ChartLifting

noncomputable section

def affineBaseThree (L : Fin 4 → ℝ) : MvPolynomial (Fin 3) ℝ :=
  C (L 0) + C (L 1) * X 0 + C (L 2) * X 1 + C (L 3) * X 2

def affineSheetRestriction (L : Fin 4 → ℝ) (F : MvPolynomial (Fin 4) ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  bind₁ ![X 0, X 1, X 2, affineBaseThree L] F

def baseCalibratedTest (F : MvPolynomial (Fin 4) ℝ) (G : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 4) ℝ := F - rename Fin.castSucc G

theorem affineBaseThree_degree (L : Fin 4 → ℝ) :
    (affineBaseThree L).totalDegree ≤ 1 :=
  deg1_add (deg1_add (deg1_add (deg1_C _) (deg1_C_mul _ (deg1_X _)))
    (deg1_C_mul _ (deg1_X _))) (deg1_C_mul _ (deg1_X _))

theorem affineSheetRestriction_degree (L : Fin 4 → ℝ) (F : MvPolynomial (Fin 4) ℝ) :
    (affineSheetRestriction L F).totalDegree ≤ F.totalDegree := by
  apply totalDegree_bind₁_le_of_le_one
  intro i
  fin_cases i
  · exact deg1_X _
  · exact deg1_X _
  · exact deg1_X _
  · exact affineBaseThree_degree L

theorem baseCalibratedTest_degree {F : MvPolynomial (Fin 4) ℝ}
    {G : MvPolynomial (Fin 3) ℝ} (hF : F.totalDegree ≤ 2) (hG : G.totalDegree ≤ 2) :
    (baseCalibratedTest F G).totalDegree ≤ 2 := by
  apply (totalDegree_sub _ _).trans
  exact max_le hF ((totalDegree_rename_le Fin.castSucc G).trans hG)

theorem pderiv_rename_base (G : MvPolynomial (Fin 3) ℝ) :
    pderiv (3 : Fin 4) (rename Fin.castSucc G) = 0 := by
  induction G using MvPolynomial.induction_on with
  | C a => simp
  | add G H hG hH => simp [hG, hH]
  | mul_X G i hG =>
    have hi : i.castSucc ≠ (3 : Fin 4) := by fin_cases i <;> decide
    simp [hG, pderiv_X, hi]

theorem pderiv_baseCalibratedTest (F : MvPolynomial (Fin 4) ℝ)
    (G : MvPolynomial (Fin 3) ℝ) :
    pderiv (3 : Fin 4) (baseCalibratedTest F G) = pderiv 3 F := by
  simp [baseCalibratedTest, pderiv_rename_base]

theorem second_pderiv_baseCalibratedTest (F : MvPolynomial (Fin 4) ℝ)
    (G : MvPolynomial (Fin 3) ℝ) :
    pderiv (3 : Fin 4) (pderiv 3 (baseCalibratedTest F G)) = pderiv 3 (pderiv 3 F) := by
  rw [pderiv_baseCalibratedTest]

theorem eval_affineSheetRestriction (L : Fin 4 → ℝ) (F : MvPolynomial (Fin 4) ℝ)
    (x : Fin 4 → ℝ) :
    eval (x ∘ Fin.castSucc) (affineSheetRestriction L F) =
      eval (Function.update x 3 (eval x (affineBase L))) F := by
  rw [affineSheetRestriction, eval_bind₁']
  apply congrArg (fun z : Fin 4 → ℝ => eval z F)
  funext i
  fin_cases i <;> simp [affineBaseThree, affineBase, Function.comp_def]

theorem eval_baseCalibratedTest (F : MvPolynomial (Fin 4) ℝ)
    (G : MvPolynomial (Fin 3) ℝ) (x : Fin 4 → ℝ) :
    eval x (baseCalibratedTest F G) = eval x F - eval (x ∘ Fin.castSucc) G := by
  simp [baseCalibratedTest, eval_rename]

/-- The fine value error depends on the distance to the affine predictor and
the ORIGINAL hidden derivatives; the predictor's coefficients do not enter. -/
theorem affine_correction_error (L : Fin 4 → ℝ) (F : MvPolynomial (Fin 4) ℝ)
    (hF : F.totalDegree ≤ 2) (x : Fin 4 → ℝ) {r H J : ℝ}
    (hr : 0 ≤ r)
    (hclose : |eval x (affineBase L) - x 3| ≤ r)
    (hd : |eval x (pderiv 3 F)| ≤ H)
    (hdd : |eval x (pderiv 3 (pderiv 3 F))| ≤ J) :
    |eval x (baseCalibratedTest F (affineSheetRestriction L F))| ≤ r * H + r ^ 2 / 2 * J := by
  rw [eval_baseCalibratedTest, eval_affineSheetRestriction]
  have ht := Submission.Lib.K4HiddenQuadratic.eval_update_add F hF x (3 : Fin 4)
    (eval x (affineBase L) - x 3)
  rw [show x 3 + (eval x (affineBase L) - x 3) = eval x (affineBase L) by ring] at ht
  rw [ht]
  set s := eval x (affineBase L) - x 3
  have hs : |s| ≤ r := hclose
  have hs2 : s ^ 2 ≤ r ^ 2 := by
    calc
      s ^ 2 = |s| ^ 2 := (sq_abs s).symm
      _ ≤ r ^ 2 := pow_le_pow_left₀ (abs_nonneg s) hs 2
  calc
    _ = |s * eval x (pderiv 3 F) + s ^ 2 / 2 * eval x (pderiv 3 (pderiv 3 F))| := by
      rw [show eval x F - (eval x F + s * eval x (pderiv 3 F) +
        s ^ 2 / 2 * eval x (pderiv 3 (pderiv 3 F))) =
        -(s * eval x (pderiv 3 F) + s ^ 2 / 2 * eval x (pderiv 3 (pderiv 3 F))) by ring,
        abs_neg]
    _ ≤ |s| * |eval x (pderiv 3 F)| + s ^ 2 / 2 * |eval x (pderiv 3 (pderiv 3 F))| := by
      have hh := abs_add_le (s * eval x (pderiv 3 F))
        (s ^ 2 / 2 * eval x (pderiv 3 (pderiv 3 F)))
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ s ^ 2 / 2)] at hh
      exact hh
    _ ≤ r * H + r ^ 2 / 2 * J :=
      add_le_add (mul_le_mul hs hd (abs_nonneg _) hr)
        (mul_le_mul (div_le_div_of_nonneg_right hs2 (by norm_num)) hdd (abs_nonneg _) (by positivity))

theorem affineSheetRestriction_value_bound (L : Fin 4 → ℝ)
    (F : MvPolynomial (Fin 4) ℝ) (hF : F.totalDegree ≤ 2) (x : Fin 4 → ℝ)
    {a H : ℝ} (ha : 0 < a) (hH : 0 ≤ H)
    (hv : |eval x F| ≤ H * a)
    (hd : |eval x (pderiv 3 F)| ≤ H)
    (hdd : |eval x (pderiv 3 (pderiv 3 F))| ≤ H / a)
    (hclose : |eval x (affineBase L) - x 3| ≤ a) :
    |eval (x ∘ Fin.castSucc) (affineSheetRestriction L F)| ≤ 3 * H * a := by
  have hc := affine_correction_error L F hF x ha.le hclose hd hdd
  have he : a * H + a ^ 2 / 2 * (H / a) ≤ 2 * H * a := by
    field_simp
    nlinarith [mul_nonneg hH ha.le]
  have hid : eval (x ∘ Fin.castSucc) (affineSheetRestriction L F) =
      eval x F - eval x (baseCalibratedTest F (affineSheetRestriction L F)) := by
    rw [eval_baseCalibratedTest]
    ring
  rw [hid]
  exact (abs_sub _ _).trans ((add_le_add hv (hc.trans he)).trans (by ring_nf; exact le_rfl))

/-- A predictor accurate at a fine width produces the full-time quadratic
fit at that width. The original true test supplies both derivative bounds. -/
theorem affine_correction_full_fit (L : Fin 4 → ℝ) (F : MvPolynomial (Fin 4) ℝ)
    (hF : F.totalDegree ≤ 2) (b : Fin 6 → ℝ) (I : Set ℝ)
    {a c H : ℝ} (_ha : 0 < a) (hc : 0 < c) (hca : c ≤ a) (hH : 0 ≤ H)
    (hfit : ∀ t ∈ I, |eval (point b t) F| ≤ H * a ∧
      |eval (point b t) (pderiv 3 F)| ≤ H ∧
      |eval (point b t) (pderiv 3 (pderiv 3 F))| ≤ H / a)
    (hclose : ∀ t ∈ I, |eval (point b t) (affineBase L) - point b t 3| ≤ c) :
    ∀ t ∈ I, |eval (point b t) (baseCalibratedTest F (affineSheetRestriction L F))| ≤ (2 * H) * c ∧
      |eval (point b t) (pderiv 3 (baseCalibratedTest F (affineSheetRestriction L F)))| ≤ 2 * H ∧
      |eval (point b t) (pderiv 3 (pderiv 3 (baseCalibratedTest F (affineSheetRestriction L F))))| ≤
        (2 * H) / c := by
  intro t ht
  obtain ⟨-, hd, hdd⟩ := hfit t ht
  have hcurv : H / a ≤ H / c := div_le_div_of_nonneg_left hH hc hca
  have he := affine_correction_error L F hF (point b t) hc.le (hclose t ht) hd (hdd.trans hcurv)
  have hv : c * H + c ^ 2 / 2 * (H / c) ≤ 2 * H * c := by
    field_simp
    nlinarith [mul_nonneg hH hc.le]
  simp only [pderiv_baseCalibratedTest]
  refine ⟨he.trans hv, hd.trans (by linarith), hdd.trans (hcurv.trans ?_)⟩
  exact div_le_div_of_nonneg_right (by linarith : H ≤ 2 * H) hc.le

theorem coeff_rename_base_le (G : MvPolynomial (Fin 3) ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hG : ∀ d, |G.coeff d| ≤ B) (e : Fin 4 →₀ ℕ) :
    |(rename Fin.castSucc G).coeff e| ≤ B := by
  by_cases he : (rename Fin.castSucc G).coeff e = 0
  · simpa [he] using hB
  · obtain ⟨d, rfl, -⟩ := coeff_rename_ne_zero Fin.castSucc G e he
    simpa only [coeff_rename_mapDomain Fin.castSucc (Fin.castSucc_injective 3)] using hG d

/-- Calibration from a filled ORIGINAL base law, without a bound on the
affine predictor. No conditional probability replaces the original mass. -/
theorem exists_calibrated_coefficient_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type*) [MeasurableSpace Ω]
      (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) (F : MvPolynomial (Fin 4) ℝ)
      (G : MvPolynomial (Fin 3) ℝ), G.totalDegree ≤ 2 →
      ∀ m β E : ℝ, 0 < m → 0 < β → m ≤ β → 0 ≤ E →
      ENNReal.ofReal m ≤ μ univ →
      (∀ U : Set (Fin 3 → ℝ), MeasurableSet U →
        μ (Z ⁻¹' U) ≤ ENNReal.ofReal β * volume U) →
      (∀ᵐ ω ∂μ, Z ω ∈ Icc (0 : Fin 3 → ℝ) 1 ∧ |eval (Z ω) G| ≤ E) →
      ∀ e, |(baseCalibratedTest F G).coeff e| ≤
        coeffL1 F + C * (96 / (m / β)) ^ 6 * E := by
  obtain ⟨C, hC, hbound⟩ :=
    Submission.Lib.K4PolynomialRemezThree.exists_coefficient_bound_from_dominated_mass 2
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ Z F G hG m β E hm hβ hmβ hE hmass hdom htrace e
  have hc := hbound Ω μ Z G hG m β E hm hβ hmβ hE hmass hdom htrace
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd, Nat.reduceMul, show (32 : ℝ) * (2 + 1) = 96 by norm_num] at hc
  have hr := coeff_rename_base_le G (by positivity : 0 ≤ C * (96 / (m / β)) ^ 6 * E) hc e
  calc
    _ ≤ |F.coeff e| + |(rename Fin.castSucc G).coeff e| := by
      simpa [baseCalibratedTest] using abs_sub (F.coeff e) ((rename Fin.castSucc G).coeff e)
    _ ≤ coeffL1 F + C * (96 / (m / β)) ^ 6 * E :=
      add_le_add (abs_coeff_le_coeffL1 F e) hr

end
end Submission.Lib.K4ContactNormalization
