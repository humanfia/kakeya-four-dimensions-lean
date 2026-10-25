import Submission.Obl.k4_quadratic_atlas_normalization.Curvature
import Submission.Obl.k4_real_conic_restoration.ScalarRoot

namespace Submission.Obl.k4_stable_native_signal_oscillation
open MvPolynomial
open Submission.Obl.k4_quadratic_slope_volume
open Submission.Obl.k4_quadratic_atlas_normalization

lemma polynomial_quadratic_taylor (p : Polynomial ℝ) (hp : p.natDegree ≤ 2)
    (x h : ℝ) : p.eval (x + h) = p.eval x + p.derivative.eval x * h +
      p.derivative.derivative.eval x * h ^ 2 / 2 := by
  obtain ⟨a, b, c, rfl⟩ := Submission.Lib.K4QuadraticSublevel.quadratic_eq_coefficients p hp
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_X, Polynomial.derivative_C,
    Polynomial.derivative_one, map_zero,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_zero, Polynomial.eval_one]
  ring

lemma quadratic_coordinate_taylor {σ : Type*} [DecidableEq σ]
    (P : MvPolynomial σ ℝ) (hP : P.totalDegree ≤ 2)
    (v : σ → ℝ) (i : σ) (h : ℝ) :
    eval (Function.update v i (v i + h)) P = eval v P +
      eval v (pderiv i P) * h + curvature P i * h ^ 2 / 2 := by
  have hd : (coordinatePolynomialHom v i P).natDegree ≤ 2 := by
    apply (natDegree_eval₂_affine_le P _ ?_).trans hP
    intro j
    split_ifs <;> simp
  have ht := polynomial_quadratic_taylor (coordinatePolynomialHom v i P) hd (v i) h
  simpa only [derivative_coordinatePolynomialHom, eval_coordinatePolynomialHom,
    Function.update_eq_self, second_pderiv_eq_curvature P hP i, eval_C] using ht

lemma quadratic_coordinate_derivative {σ : Type*} [DecidableEq σ]
    (P : MvPolynomial σ ℝ) (hP : P.totalDegree ≤ 2)
    (v : σ → ℝ) (i : σ) (h : ℝ) :
    eval (Function.update v i (v i + h)) (pderiv i P) =
      eval v (pderiv i P) + curvature P i * h := by
  have ht := quadratic_coordinate_taylor (pderiv i P)
    ((totalDegree_pderiv_le P i).trans (by omega)) v i h
  rw [second_pderiv_eq_curvature P hP i, eval_C] at ht
  have hz : curvature (pderiv i P) i = 0 := by
    unfold curvature
    rw [second_pderiv_eq_curvature P hP i, pderiv_C]
    simp
  simpa only [hz, zero_mul, zero_div, add_zero] using ht

/-- The error in a quadratic signal caused by moving only the hidden coordinate. -/
lemma signal_error_le {σ : Type*} [DecidableEq σ]
    (S : MvPolynomial σ ℝ) (hS : S.totalDegree ≤ 2)
    (v : σ → ℝ) (i : σ) {K d : ℝ} (hK : 0 ≤ K) (_hd : 0 ≤ d)
    (hfirst : |eval v (pderiv i S)| ≤ K) (hsecond : |curvature S i| ≤ K)
    {h : ℝ} (hh : |h| ≤ d) :
    |eval (Function.update v i (v i + h)) S - eval v S| ≤ K * d + K * d ^ 2 / 2 := by
  rw [quadratic_coordinate_taylor S hS v i h]
  have heq : eval v S + eval v (pderiv i S) * h + curvature S i * h ^ 2 / 2 -
      eval v S = eval v (pderiv i S) * h + curvature S i * h ^ 2 / 2 := by ring
  rw [heq]
  calc
    _ ≤ |eval v (pderiv i S) * h| + |curvature S i * h ^ 2 / 2| := abs_add_le _ _
    _ = |eval v (pderiv i S)| * |h| + |curvature S i| * |h| ^ 2 / 2 := by
      rw [abs_mul, abs_div, abs_mul, abs_pow]
      norm_num
    _ ≤ K * d + K * d ^ 2 / 2 := by
      gcongr

/-- A nearby exact zero of a test, under the scale-invariant small-curvature condition. -/
lemma exists_nearby_zero {σ : Type*} [DecidableEq σ]
    (P : MvPolynomial σ ℝ) (hP : P.totalDegree ≤ 2)
    (v : σ → ℝ) (i : σ)
    (hfirst : eval v (pderiv i P) ≠ 0)
    (hsmall : 2 * |curvature P i| * |eval v P| ≤ (eval v (pderiv i P)) ^ 2) :
    ∃ w : ℝ, eval (Function.update v i w) P = 0 ∧
      |w - v i| ≤ 2 * |eval v P| / |eval v (pderiv i P)| := by
  obtain ⟨h, heq, hh⟩ := Submission.Obl.k4_real_conic_restoration.quadratic_near_zero
    (curvature P i / 2) (eval v (pderiv i P)) (eval v P) hfirst (by
      rw [abs_div]
      norm_num
      nlinarith [hsmall])
  refine ⟨v i + h, ?_, by simpa only [add_sub_cancel_left] using hh⟩
  rw [quadratic_coordinate_taylor P hP v i h]
  nlinarith [heq]

/-- A displacement of order `a` produces a signal error of order `a`.
The quadratic remainder is absorbed using `a ≤ 1`. -/
lemma signal_error_scale {σ : Type*} [DecidableEq σ]
    (S : MvPolynomial σ ℝ) (hS : S.totalDegree ≤ 2)
    (v : σ → ℝ) (i : σ) {K L a : ℝ}
    (hK : 0 ≤ K) (hL : 0 ≤ L) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hfirst : |eval v (pderiv i S)| ≤ K) (hsecond : |curvature S i| ≤ K)
    {h : ℝ} (hh : |h| ≤ L * a) :
    |eval (Function.update v i (v i + h)) S - eval v S| ≤ K * (L + L ^ 2) * a := by
  have hb := signal_error_le S hS v i hK (mul_nonneg hL ha) hfirst hsecond hh
  have hsquare : (L * a) ^ 2 ≤ L ^ 2 * a := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (by nlinarith : a ^ 2 ≤ a) (sq_nonneg L)
  calc
    _ ≤ K * (L * a) + K * (L * a) ^ 2 / 2 := hb
    _ ≤ K * (L * a) + K * (L ^ 2 * a) := by
      have hn : 0 ≤ K * (L * a) ^ 2 := mul_nonneg hK (sq_nonneg _)
      have hm := mul_le_mul_of_nonneg_left hsquare hK
      linarith
    _ = K * (L + L ^ 2) * a := by ring

/-- The common signal error used for either centers or nearby roots. -/
lemma signal_error_power {σ : Type*} [DecidableEq σ]
    (S : MvPolynomial σ ℝ) (hS : S.totalDegree ≤ 2)
    (v : σ → ℝ) (i : σ) {K a : ℝ}
    (hK : 2 ≤ K) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hfirst : |eval v (pderiv i S)| ≤ K) (hsecond : |curvature S i| ≤ K)
    {h : ℝ} (hh : |h| ≤ K ^ 6 * a) :
    |eval (Function.update v i (v i + h)) S - eval v S| ≤ K ^ 14 * a := by
  have hK0 : 0 ≤ K := by linarith
  have hK1 : 1 ≤ K := by linarith
  apply (signal_error_scale S hS v i hK0 (pow_nonneg hK0 _) ha ha1 hfirst hsecond hh).trans
  apply mul_le_mul_of_nonneg_right _ ha
  calc
    K * (K ^ 6 + (K ^ 6) ^ 2) ≤ K * (K ^ 12 + K ^ 12) := by
      rw [show (K ^ 6) ^ 2 = K ^ 12 by ring]
      exact mul_le_mul_of_nonneg_left
        (add_le_add (pow_le_pow_right₀ hK1 (by decide : 6 ≤ 12)) le_rfl) hK0
    _ = 2 * K ^ 13 := by ring
    _ ≤ K * K ^ 13 := mul_le_mul_of_nonneg_right hK (pow_nonneg hK0 _)
    _ = K ^ 14 := by ring

/-- The unique critical center of a non-affine hidden quadratic. -/
noncomputable def hiddenCenter {σ : Type*} (P : MvPolynomial σ ℝ)
    (v : σ → ℝ) (i : σ) : ℝ := v i - eval v (pderiv i P) / curvature P i

lemma hiddenCenter_update {σ : Type*} [DecidableEq σ]
    (P : MvPolynomial σ ℝ) (hP : P.totalDegree ≤ 2)
    (v : σ → ℝ) (i : σ) (hc : curvature P i ≠ 0) (w : ℝ) :
    hiddenCenter P (Function.update v i w) i = hiddenCenter P v i := by
  have hd := quadratic_coordinate_derivative P hP v i (w - v i)
  rw [add_sub_cancel] at hd
  simp only [hiddenCenter, Function.update_self, hd]
  field_simp
  ring

lemma hiddenCenter_critical {σ : Type*} [DecidableEq σ]
    (P : MvPolynomial σ ℝ) (hP : P.totalDegree ≤ 2)
    (v : σ → ℝ) (i : σ) (hc : curvature P i ≠ 0) :
    eval (Function.update v i (hiddenCenter P v i)) (pderiv i P) = 0 := by
  have hd := quadratic_coordinate_derivative P hP v i
    (-eval v (pderiv i P) / curvature P i)
  have heq : v i + -eval v (pderiv i P) / curvature P i = hiddenCenter P v i := by
    simp only [hiddenCenter, neg_div, sub_eq_add_neg]
  rw [heq] at hd
  rw [hd]
  field_simp
  ring

/-- In the large-curvature case the center is at thickness scale. -/
lemma hiddenCenter_distance {σ : Type*}
    (P : MvPolynomial σ ℝ) (v : σ → ℝ) (i : σ) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a)
    (hlarge : (K ^ 5 * a)⁻¹ ≤ |curvature P i|)
    (hfirst : |eval v (pderiv i P)| ≤ K) :
    |hiddenCenter P v i - v i| ≤ K ^ 6 * a := by
  have hpos : 0 < (K ^ 5 * a)⁻¹ := by positivity
  calc
    _ = |eval v (pderiv i P)| / |curvature P i| := by
      simp [hiddenCenter, abs_div]
    _ ≤ K / (K ^ 5 * a)⁻¹ :=
      div_le_div₀ hK.le hfirst hpos hlarge
    _ = K ^ 6 * a := by rw [div_inv_eq_mul]; ring

/-- Moving to a quadratic center preserves the signal up to thickness scale. -/
lemma hiddenCenter_signal_error {σ : Type*} [DecidableEq σ]
    (P S : MvPolynomial σ ℝ) (hS : S.totalDegree ≤ 2)
    (v : σ → ℝ) (i : σ) {K a : ℝ}
    (hK : 2 ≤ K) (ha : 0 < a) (ha1 : a ≤ 1)
    (hlarge : (K ^ 5 * a)⁻¹ ≤ |curvature P i|)
    (hfirstP : |eval v (pderiv i P)| ≤ K)
    (hfirstS : |eval v (pderiv i S)| ≤ K) (hsecondS : |curvature S i| ≤ K) :
    |eval (Function.update v i (hiddenCenter P v i)) S - eval v S| ≤ K ^ 14 * a := by
  have hh := hiddenCenter_distance P v i (by linarith : 0 < K) ha hlarge hfirstP
  have hb := signal_error_power S hS v i hK ha.le ha1 hfirstS hsecondS hh
  simpa only [add_sub_cancel] using hb

lemma small_curvature_error {K a c p : ℝ} (hK : 2 ≤ K) (ha : 0 < a)
    (hc : |c| ≤ (K ^ 5 * a)⁻¹) (hp : |p| ≤ K * a) :
    2 * |c| * |p| ≤ (K⁻¹) ^ 2 / 2 := by
  have hK0 : 0 < K := by linarith
  have hprod : |c| * |p| ≤ K / K ^ 5 := by
    calc
      _ ≤ (K ^ 5 * a)⁻¹ * (K * a) :=
        mul_le_mul hc hp (abs_nonneg _) (by positivity)
      _ = K / K ^ 5 := by field_simp
  calc
    2 * |c| * |p| = 2 * (|c| * |p|) := by ring
    _ ≤ 2 * (K / K ^ 5) := mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ ≤ (K⁻¹) ^ 2 / 2 := by
      field_simp
      nlinarith [mul_le_mul_of_nonneg_left (show 4 ≤ K ^ 2 by nlinarith) hK0.le]

lemma residual_ratio {K a p d : ℝ} (hK : 0 < K) (ha : 0 ≤ a)
    (hp : |p| ≤ K * a) (hd : K⁻¹ ≤ |d|) :
    2 * |p| / |d| ≤ 2 * K ^ 2 * a := by
  calc
    _ ≤ (2 * (K * a)) / K⁻¹ :=
      div_le_div₀ (by positivity) (by gcongr) (by positivity) hd
    _ = 2 * K ^ 2 * a := by rw [div_inv_eq_mul]; ring

lemma exists_nearby_regular_zero {σ : Type*} [DecidableEq σ]
    (P : MvPolynomial σ ℝ) (hP : P.totalDegree ≤ 2)
    (v : σ → ℝ) (i : σ) {K a : ℝ}
    (hK : 2 ≤ K) (ha : 0 < a)
    (hcurv : |curvature P i| ≤ (K ^ 5 * a)⁻¹)
    (hval : |eval v P| ≤ K * a)
    (hfirst : K⁻¹ ≤ |eval v (pderiv i P)|) :
    ∃ w : ℝ, eval (Function.update v i w) P = 0 ∧
      |w - v i| ≤ 2 * K ^ 2 * a ∧
      |eval v (pderiv i P)| / 2 ≤ |eval (Function.update v i w) (pderiv i P)| := by
  let d := eval v (pderiv i P)
  have hK0 : 0 < K := by linarith
  have hd : 0 < |d| := (inv_pos.mpr hK0).trans_le hfirst
  have hd0 : d ≠ 0 := abs_pos.mp hd
  have hsmall := small_curvature_error hK ha hcurv hval
  have hsquare : (K⁻¹) ^ 2 ≤ d ^ 2 := by
    rw [← sq_abs d]
    exact pow_le_pow_left₀ (by positivity) hfirst 2
  obtain ⟨w, hw, hdist⟩ := exists_nearby_zero P hP v i hd0 (by
    dsimp [d] at hsquare
    linarith [sq_nonneg (K⁻¹)])
  refine ⟨w, hw, hdist.trans (residual_ratio hK0 ha.le hval hfirst), ?_⟩
  have hstep : |curvature P i * (w - v i)| ≤ |d| / 2 := by
    rw [abs_mul]
    calc
      _ ≤ |curvature P i| * (2 * |eval v P| / |d|) :=
        mul_le_mul_of_nonneg_left hdist (abs_nonneg _)
      _ = (2 * |curvature P i| * |eval v P|) / |d| := by ring
      _ ≤ |d| / 2 := by
        apply (div_le_iff₀ hd).mpr
        nlinarith [hsquare, sq_abs d]
  have hder := quadratic_coordinate_derivative P hP v i (w - v i)
  rw [add_sub_cancel] at hder
  change |d| / 2 ≤ _
  rw [hder]
  have habs := abs_sub_abs_le_abs_sub d (d + curvature P i * (w - v i))
  have hsimp : |d - (d + curvature P i * (w - v i))| =
      |curvature P i * (w - v i)| := by
    rw [show d - (d + curvature P i * (w - v i)) =
      -(curvature P i * (w - v i)) by ring, abs_neg]
  rw [hsimp] at habs
  linarith

/-- A nearby simple root also approximates the native quadratic signal. -/
lemma root_signal_approximation {σ : Type*} [DecidableEq σ]
    (P S : MvPolynomial σ ℝ) (hP : P.totalDegree ≤ 2) (hS : S.totalDegree ≤ 2)
    (v : σ → ℝ) (i : σ) {K a : ℝ}
    (hK : 2 ≤ K) (ha : 0 < a) (ha1 : a ≤ 1)
    (hcurv : |curvature P i| ≤ (K ^ 5 * a)⁻¹)
    (hval : |eval v P| ≤ K * a) (hfirstP : K⁻¹ ≤ |eval v (pderiv i P)|)
    (hfirstS : |eval v (pderiv i S)| ≤ K) (hsecondS : |curvature S i| ≤ K) :
    ∃ w : ℝ, eval (Function.update v i w) P = 0 ∧
      eval (Function.update v i w) (pderiv i P) ≠ 0 ∧
      |w - v i| ≤ 2 * K ^ 2 * a ∧
      |eval (Function.update v i w) S - eval v S| ≤ K ^ 14 * a := by
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  obtain ⟨w, hw, hdist, hder⟩ := exists_nearby_regular_zero P hP v i hK ha hcurv hval hfirstP
  have hnonzero : eval (Function.update v i w) (pderiv i P) ≠ 0 := by
    apply abs_pos.mp
    have hd := (inv_pos.mpr hK0).trans_le hfirstP
    linarith
  refine ⟨w, hw, hnonzero, hdist, ?_⟩
  have hp : 2 * K ^ 2 ≤ K ^ 6 := by
    calc
      _ ≤ K * K ^ 2 := mul_le_mul_of_nonneg_right hK (sq_nonneg K)
      _ = K ^ 3 := by ring
      _ ≤ K ^ 6 := pow_le_pow_right₀ hK1 (by decide : 3 ≤ 6)
  have hdist' : |w - v i| ≤ K ^ 6 * a :=
    hdist.trans (mul_le_mul_of_nonneg_right hp ha.le)
  have hs := signal_error_power S hS v i hK ha.le ha1 hfirstS hsecondS hdist'
  simpa only [add_sub_cancel] using hs

/-- The base discriminant is polynomially bounded at every admissible point. -/
lemma discriminant_bound {σ : Type*}
    (P : MvPolynomial σ ℝ) (v : σ → ℝ) (i : σ) {K a : ℝ}
    (hK : 2 ≤ K) (ha : 0 < a)
    (hcurv : |curvature P i| ≤ K / a)
    (hval : |eval v P| ≤ K * a) (hfirst : |eval v (pderiv i P)| ≤ K) :
    |eval v (discriminant P i)| ≤ K ^ 4 := by
  have hK0 : 0 ≤ K := by linarith
  have hprod : |curvature P i| * |eval v P| ≤ K ^ 2 := by
    calc
      _ ≤ (K / a) * (K * a) := mul_le_mul hcurv hval (abs_nonneg _) (by positivity)
      _ = K ^ 2 := by field_simp
  rw [discriminant_eval]
  calc
    _ ≤ |(eval v (pderiv i P)) ^ 2| + |2 * curvature P i * eval v P| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le ((eval v (pderiv i P)) ^ 2) (-(2 * curvature P i * eval v P))
    _ = |eval v (pderiv i P)| ^ 2 + 2 * (|curvature P i| * |eval v P|) := by
      rw [abs_pow, abs_mul, abs_mul]
      norm_num
      ring
    _ ≤ K ^ 2 + 2 * K ^ 2 := by
      gcongr
    _ ≤ K ^ 4 := by nlinarith [sq_nonneg (K ^ 2 - 2)]

/-- In the small-curvature case the base discriminant has a quantitative positive floor. -/
lemma discriminant_floor {σ : Type*}
    (P : MvPolynomial σ ℝ) (v : σ → ℝ) (i : σ) {K a : ℝ}
    (hK : 2 ≤ K) (ha : 0 < a)
    (hcurv : |curvature P i| ≤ (K ^ 5 * a)⁻¹)
    (hval : |eval v P| ≤ K * a) (hfirst : K⁻¹ ≤ |eval v (pderiv i P)|) :
    (K⁻¹) ^ 2 / 2 ≤ eval v (discriminant P i) := by
  have hsmall := small_curvature_error hK ha hcurv hval
  have hsquare : (K⁻¹) ^ 2 ≤ (eval v (pderiv i P)) ^ 2 := by
    rw [← sq_abs (eval v (pderiv i P))]
    exact pow_le_pow_left₀ (by positivity) hfirst 2
  have habs := le_abs_self (curvature P i * eval v P)
  rw [abs_mul] at habs
  rw [discriminant_eval]
  nlinarith

end Submission.Obl.k4_stable_native_signal_oscillation
