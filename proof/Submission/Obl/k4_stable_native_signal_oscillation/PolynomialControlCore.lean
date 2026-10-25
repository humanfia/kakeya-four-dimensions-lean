import Submission.Obl.k4_stable_native_signal_oscillation.Dilation
import Submission.Obl.k4_stable_native_signal_oscillation.PolynomialBounds
import Submission.Obl.k4_stable_native_signal_oscillation.PowerBounds

namespace Submission.Obl.k4_stable_native_signal_oscillation
open MvPolynomial Set Metric MeasureTheory

/-- The real polynomial consequence of algebraic-sheet Remez. -/
def PolynomialRemezInput (D : ℕ) (C : ℝ) : Prop :=
  ∀ (P : MvPolynomial (Fin 3) ℝ), P.totalDegree ≤ D →
    ∀ (E : Set (EuclideanSpace ℝ (Fin 3))) (θ V : ℝ),
      MeasurableSet E → E ⊆ closedBall 0 (1 / 2) →
      0 < θ → θ ≤ 1 → 0 ≤ V →
      ENNReal.ofReal θ * volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2)) ≤ volume E →
      (∀ x ∈ E, |eval (fun i => x i) P| ≤ V) →
      ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 2 →
        |eval (fun i => x i) P| ≤ C * θ ^ (-C) * V

lemma polynomial_control_of_remez (D m : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (hremez : PolynomialRemezInput D C) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ K : ℝ, 2 ≤ K →
      ∀ (P : MvPolynomial (Fin 3) ℝ), P.totalDegree ≤ D →
      ∀ (E : Set (EuclideanSpace ℝ (Fin 3))) (V : ℝ), 0 ≤ V →
      E ⊆ closedBall 0 K → ENNReal.ofReal ((K ^ m)⁻¹) ≤ volume E →
      (∀ x ∈ E, |eval (fun i => x i) P| ≤ V) →
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 3 * K → |eval (fun i => x i) P| ≤ K ^ N * V) ∧
      ∀ x y : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 3 * K → ‖y‖ ≤ 3 * K →
        |eval (fun i => x i) P - eval (fun i => y i) P| ≤ K ^ N * V * ‖x - y‖ := by
  obtain ⟨L, hL, hlip⟩ := exists_polynomial_lipschitz_of_ball_bound D
  let B := closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2)
  have hBpos : 0 < volume B := measure_closedBall_pos _ _ (by norm_num)
  have hBfin : volume B ≠ ⊤ := (isCompact_closedBall _ _).measure_ne_top
  let b := (volume B).toReal
  have hb : 0 < b := ENNReal.toReal_pos hBpos.ne' hBfin
  have hbE : ENNReal.ofReal b = volume B := ENNReal.ofReal_toReal hBfin
  let d : ℝ := 8 * (3 : ℝ) ^ (m + 3)
  have hd : 0 < d := by dsimp [d]; positivity
  let c := min (1 : ℝ) ((d * b)⁻¹)
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcb : c * b ≤ d⁻¹ := by
    have hh : c * (d * b) ≤ 1 := by
      apply (le_div_iff₀ (mul_pos hd hb)).mp
      simpa only [one_div] using (min_le_right (1 : ℝ) ((d * b)⁻¹))
    rw [← one_div]
    apply (le_div_iff₀ hd).mpr
    simpa only [one_div] using (show c * b * d ≤ 1 by nlinarith [hh])
  let e : ℝ := ((m + 3 : ℕ) : ℝ) * C
  let A : ℝ := (L + 1) * C * c ^ (-C)
  obtain ⟨N, hN, hpower⟩ := exists_nat_power_bound A e
  refine ⟨N, hN, ?_⟩
  intro K hK P hP E V hV hE hmass hbound
  have hKpos : 0 < K := by linarith
  have hKone : 1 ≤ K := by linarith
  have h3K : 0 < 3 * K := by positivity
  let T := dilatePolynomial (2 * (3 * K)) P
  have hT : T.totalDegree ≤ D := (dilatePolynomial_degree _ _).trans hP
  let W : Set (EuclideanSpace ℝ (Fin 3)) :=
    {x | ‖x‖ ≤ 1 / 2 ∧ |eval (fun i => x i) T| ≤ V}
  have hW : MeasurableSet W := (isClosed_le continuous_norm continuous_const).measurableSet.inter
    (isClosed_le (continuous_real_polynomial T).abs continuous_const).measurableSet
  have hWsub : W ⊆ closedBall 0 (1 / 2) := fun x hx => mem_closedBall_zero_iff.mpr hx.1
  have hmass3 : ENNReal.ofReal (((3 * K) ^ m)⁻¹) ≤ volume E := by
    apply le_trans _ hmass
    apply ENNReal.ofReal_le_ofReal
    exact inv_anti₀ (pow_pos hKpos m) (pow_le_pow_left₀ hKpos.le (by linarith) m)
  have hE3 : E ⊆ closedBall 0 (3 * K) := by
    intro x hx
    exact mem_closedBall_zero_iff.mpr ((mem_closedBall_zero_iff.mp (hE hx)).trans (by linarith))
  have hWmass : ENNReal.ofReal ((8 * (3 * K) ^ (m + 3))⁻¹) ≤ volume W :=
    normalized_witness_mass_power m (3 * K) h3K P E V hE3 hmass3 hbound
  let θ : ℝ := c * K ^ (-((m + 3 : ℕ) : ℝ))
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθeq : θ = c * (K ^ (m + 3))⁻¹ := by
    dsimp [θ]
    rw [Real.rpow_neg hKpos.le, Real.rpow_natCast]
  have hθ1 : θ ≤ 1 := by
    rw [hθeq]
    exact (mul_le_mul hc1 (inv_le_one_of_one_le₀ (one_le_pow₀ hKone))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring)
  have hθmass : ENNReal.ofReal θ * volume B ≤ volume W := by
    apply le_trans _ hWmass
    rw [← hbE, ← ENNReal.ofReal_mul hθ.le]
    apply ENNReal.ofReal_le_ofReal
    calc
      θ * b = (c * b) * (K ^ (m + 3))⁻¹ := by rw [hθeq]; ring
      _ ≤ d⁻¹ * (K ^ (m + 3))⁻¹ := mul_le_mul_of_nonneg_right hcb (by positivity)
      _ = (8 * (3 * K) ^ (m + 3))⁻¹ := by dsimp [d]; rw [mul_pow]; field_simp
  have hR : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 2 →
      |eval (fun i => x i) T| ≤ C * θ ^ (-C) * V :=
    hremez T hT W θ V hW hWsub hθ hθ1 hV hθmass (fun _ hx => hx.2)
  have hθpow : θ ^ (-C) = c ^ (-C) * K ^ e := by
    dsimp [θ, e]
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg hKpos.le _), ← Real.rpow_mul hKpos.le]
    congr 2
    ring
  have hC0 : 0 ≤ C := by linarith
  have hcoef : C * θ ^ (-C) ≤ K ^ N := by
    apply le_trans _ (hpower K hK)
    rw [hθpow]
    dsimp [A]
    have ht : 0 ≤ C * c ^ (-C) * K ^ e := by positivity
    nlinarith
  have hcoefL : L * (C * θ ^ (-C)) ≤ K ^ N := by
    apply le_trans _ (hpower K hK)
    rw [hθpow]
    dsimp [A]
    have ht : 0 ≤ C * c ^ (-C) * K ^ e := by positivity
    nlinarith
  constructor
  · intro x hx
    have hnx := norm_normalized_point (3 * K) h3K x hx
    have hr := hR ((2 * (3 * K))⁻¹ • x) hnx
    rw [eval_dilatePolynomial_inv _ (by positivity : 2 * (3 * K) ≠ 0)] at hr
    exact hr.trans (mul_le_mul_of_nonneg_right hcoef hV)
  · intro x y hx hy
    have hnx := norm_normalized_point (3 * K) h3K x hx
    have hny := norm_normalized_point (3 * K) h3K y hy
    have hV0 : 0 ≤ C * θ ^ (-C) * V := by positivity
    have hinner : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ 1 / 8 →
        |eval (fun i => z i) T| ≤ C * θ ^ (-C) * V := fun z hz => hR z (by linarith)
    have hh := hlip T hT (C * θ ^ (-C) * V) hV0 hinner
      ((2 * (3 * K))⁻¹ • x) ((2 * (3 * K))⁻¹ • y) (by linarith) (by linarith)
    have hevalx := eval_dilatePolynomial_inv (2 * (3 * K)) (by positivity : 2 * (3 * K) ≠ 0) P x
    have hevaly := eval_dilatePolynomial_inv (2 * (3 * K)) (by positivity : 2 * (3 * K) ≠ 0) P y
    change eval (fun i => ((2 * (3 * K))⁻¹ • x : EuclideanSpace ℝ (Fin 3)) i) T = _ at hevalx
    change eval (fun i => ((2 * (3 * K))⁻¹ • y : EuclideanSpace ℝ (Fin 3)) i) T = _ at hevaly
    rw [hevalx, hevaly] at hh
    have hdiff : ‖(2 * (3 * K))⁻¹ • x - (2 * (3 * K))⁻¹ • y‖ ≤ ‖x - y‖ := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (2 * (3 * K))⁻¹)]
      exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ (by linarith))
    calc
      _ ≤ L * (C * θ ^ (-C) * V) * ‖(2 * (3 * K))⁻¹ • x - (2 * (3 * K))⁻¹ • y‖ := hh
      _ ≤ L * (C * θ ^ (-C) * V) * ‖x - y‖ := mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = (L * (C * θ ^ (-C))) * V * ‖x - y‖ := by ring
      _ ≤ K ^ N * V * ‖x - y‖ := by gcongr

end Submission.Obl.k4_stable_native_signal_oscillation
