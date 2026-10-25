/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/RawQuadraticSampling.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.QuadraticSampling

/-! The midpoint crossing tests at the actual hidden-bin width a/B. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

noncomputable def rescaleHiddenPolynomial (a B : ℝ) (p : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C a⁻¹ * p.comp (Polynomial.C (a / B) * Polynomial.X)

theorem rescaleHiddenPolynomial_degree (a B : ℝ) (p : Polynomial ℝ) :
    (rescaleHiddenPolynomial a B p).natDegree ≤ p.natDegree := by
  unfold rescaleHiddenPolynomial
  calc
    _ ≤ (Polynomial.C a⁻¹).natDegree +
        (p.comp (Polynomial.C (a / B) * Polynomial.X)).natDegree := Polynomial.natDegree_mul_le
    _ = (p.comp (Polynomial.C (a / B) * Polynomial.X)).natDegree := by simp
    _ ≤ p.natDegree * (Polynomial.C (a / B) * Polynomial.X).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ p.natDegree * 1 := Nat.mul_le_mul_left _
      (Polynomial.natDegree_mul_le.trans (by simp))
    _ = _ := Nat.mul_one _

theorem rescaleHiddenPolynomial_derivative (a B : ℝ) (p : Polynomial ℝ) :
    (rescaleHiddenPolynomial a B p).derivative =
      Polynomial.C (a⁻¹ * (a / B)) *
        p.derivative.comp (Polynomial.C (a / B) * Polynomial.X) := by
  simp only [rescaleHiddenPolynomial, Polynomial.derivative_C_mul,
    Polynomial.derivative_comp, Polynomial.derivative_X, mul_one,
    ← mul_assoc, ← Polynomial.C_mul]

theorem rescaleHiddenPolynomial_second (a B : ℝ) (p : Polynomial ℝ) :
    (rescaleHiddenPolynomial a B p).derivative.derivative =
      Polynomial.C (a⁻¹ * (a / B) ^ 2) *
        p.derivative.derivative.comp (Polynomial.C (a / B) * Polynomial.X) := by
  rw [rescaleHiddenPolynomial_derivative]
  simp only [Polynomial.derivative_C_mul, Polynomial.derivative_comp,
    Polynomial.derivative_X, mul_one, ← mul_assoc, ← Polynomial.C_mul]
  congr 2
  ring

theorem rescaleHiddenPolynomial_eval {a B : ℝ} (ha : a ≠ 0) (hB : B ≠ 0)
    (p : Polynomial ℝ) (w : ℝ) :
    (rescaleHiddenPolynomial a B p).eval (B * w / a) = p.eval w / a := by
  have harg : a / B * (B * w / a) = w := by field_simp
  simp only [rescaleHiddenPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, Polynomial.eval_X, harg]
  simp only [div_eq_inv_mul]

theorem rescaleHiddenPolynomial_derivative_eval {a B : ℝ} (ha : a ≠ 0) (hB : B ≠ 0)
    (p : Polynomial ℝ) (w : ℝ) :
    (rescaleHiddenPolynomial a B p).derivative.eval (B * w / a) =
      p.derivative.eval w / B := by
  have harg : a / B * (B * w / a) = w := by field_simp
  rw [rescaleHiddenPolynomial_derivative]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
    Polynomial.eval_X, harg]
  field_simp

theorem rescaleHiddenPolynomial_second_eval {a B : ℝ} (ha : a ≠ 0) (hB : B ≠ 0)
    (p : Polynomial ℝ) (w : ℝ) :
    (rescaleHiddenPolynomial a B p).derivative.derivative.eval (B * w / a) =
      (a / B ^ 2) * p.derivative.derivative.eval w := by
  have harg : a / B * (B * w / a) = w := by field_simp
  rw [rescaleHiddenPolynomial_second]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
    Polynomial.eval_X, harg]
  field_simp

/-- Whole-block native bounds and a selected derivative floor imply the finite
crossing test for the original hidden label floor(B*w/a). -/
theorem mem_rawSampledQuadraticBins (p : Polynomial ℝ) (hp : p.natDegree ≤ 2)
    {κ a B w : ℝ} (hκ : 1 ≤ κ) (ha : 0 < a) (hB : 0 < B)
    {m : ℕ} (hm : 4 * κ ^ 2 ≤ m) (hval : |p.eval w| ≤ κ * a)
    (hlower : B / κ ≤ |p.derivative.eval w|)
    (hupper : |p.derivative.eval w| ≤ κ * B)
    (hsecond : |p.derivative.derivative.eval w| ≤ κ * B ^ 2 / a) :
    ⌊B * w / a⌋ ∈ sampledQuadraticBins (rescaleHiddenPolynomial a B p) κ m := by
  apply mem_sampledQuadraticBins _ ((rescaleHiddenPolynomial_degree a B p).trans hp) hκ hm
  · rw [rescaleHiddenPolynomial_eval ha.ne' hB.ne', abs_div, abs_of_pos ha]
    exact (div_le_iff₀ ha).mpr hval
  · rw [rescaleHiddenPolynomial_derivative_eval ha.ne' hB.ne', abs_div, abs_of_pos hB]
    apply (le_div_iff₀ hB).mpr
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hlower
  · rw [rescaleHiddenPolynomial_derivative_eval ha.ne' hB.ne', abs_div, abs_of_pos hB]
    exact (div_le_iff₀ hB).mpr hupper
  · rw [rescaleHiddenPolynomial_second_eval ha.ne' hB.ne', abs_mul,
      abs_of_pos (by positivity : 0 < a / B ^ 2)]
    calc
      _ ≤ (a / B ^ 2) * (κ * B ^ 2 / a) := mul_le_mul_of_nonneg_left hsecond (by positivity)
      _ = κ := by field_simp

end Submission.Obl.k4_balanced_native_packet_transport.CPF
