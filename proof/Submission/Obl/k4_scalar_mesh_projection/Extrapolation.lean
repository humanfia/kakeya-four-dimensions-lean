import Submission.Obl.k4_eligibility_sign_description.Families

/-!
Whole-time recovery for scalar mesh packets. The block-to-unit-interval losses
are explicit, so a subpower lower bound on block length suffices.
-/

namespace Submission.Obl.k4_scalar_mesh_projection

open Set
open Submission.Obl.k4_eligibility_sign_description

/-- Whole-time affine confinement controls both coefficients, including velocity. -/
theorem affine_coefficients_of_confinement {b w u v R : ℝ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |b + t * w - u - t * v| ≤ R) :
    |b - u| ≤ R ∧ |w - v| ≤ 2 * R := by
  have h₀ : |b - u| ≤ R := by simpa using h 0 ⟨le_rfl, zero_le_one⟩
  have h₁ : |b + w - u - v| ≤ R := by simpa using h 1 ⟨zero_le_one, le_rfl⟩
  refine ⟨h₀, ?_⟩
  calc
    |w - v| = |(b + w - u - v) - (b - u)| := by congr 1 <;> ring
    _ ≤ |b + w - u - v| + |b - u| := abs_sub _ _
    _ ≤ 2 * R := by linarith

/-- A bound on the endpoints controls an affine function between the endpoints. -/
theorem affine_bound_of_endpoints {b v R : ℝ}
    (h₀ : |b| ≤ R) (h₁ : |b + v| ≤ R) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |b + t * v| ≤ R := by
  have hR : 0 ≤ R := (abs_nonneg b).trans h₀
  have hb := abs_le.mp h₀
  have hb' := abs_le.mp h₁
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hb'.1),
      mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hb.1)]
  · nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hb'.2),
      mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hb.2)]

theorem abs_sub_le_one {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : |x - y| ≤ 1 := by
  exact abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩

/-- Extrapolating an affine function from a block of length `q` to unit time. -/
theorem affine_extrapolate {b v a q E : ℝ} (hq : 0 < q)
    (ha : 0 ≤ a) (haq : a + q ≤ 1)
    (h₀ : |b + a * v| ≤ E) (h₁ : |b + (a + q) * v| ≤ E)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |b + t * v| ≤ 2 * E / q := by
  have hE : 0 ≤ E := (abs_nonneg _).trans h₀
  have hta : |t - a| ≤ 1 := abs_sub_le_one ht ⟨ha, by linarith⟩
  have htaq : |a + q - t| ≤ 1 := abs_sub_le_one ⟨by linarith, haq⟩ ht
  apply (le_div_iff₀ hq).2
  calc
    |b + t * v| * q = |q * (b + t * v)| := by
      rw [abs_mul, abs_of_pos hq, mul_comm]
    _ = |(a + q - t) * (b + a * v) + (t - a) * (b + (a + q) * v)| := by
      congr 1 <;> ring
    _ ≤ |a + q - t| * |b + a * v| + |t - a| * |b + (a + q) * v| := by
      simpa only [abs_mul] using abs_add_le ((a + q - t) * (b + a * v))
        ((t - a) * (b + (a + q) * v))
    _ ≤ 1 * E + 1 * E := add_le_add
      (mul_le_mul htaq h₀ (abs_nonneg _) (by norm_num))
      (mul_le_mul hta h₁ (abs_nonneg _) (by norm_num))
    _ = 2 * E := by ring

/-- Three-point interpolation, with the denominator cleared. -/
theorem quadratic_interpolation (f : ℝ → ℝ) (hf : Quadratic f) (a q t : ℝ) :
    q ^ 2 * f t =
      2 * (t - a - q / 2) * (t - a - q) * f a -
      4 * (t - a) * (t - a - q) * f (a + q / 2) +
      2 * (t - a) * (t - a - q / 2) * f (a + q) := by
  obtain ⟨A, B, C, h⟩ := hf
  simp only [h]
  ring

/-- A quadratic bounded at the ends and midpoint of a short block is bounded
throughout unit time, at the explicit loss `8 / q^2`. -/
theorem quadratic_extrapolate (f : ℝ → ℝ) (hf : Quadratic f)
    {a q E : ℝ} (hq : 0 < q) (ha : 0 ≤ a) (haq : a + q ≤ 1)
    (h₀ : |f a| ≤ E) (h₁ : |f (a + q / 2)| ≤ E) (h₂ : |f (a + q)| ≤ E)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |f t| ≤ 8 * E / q ^ 2 := by
  have hE : 0 ≤ E := (abs_nonneg _).trans h₀
  have hta : |t - a| ≤ 1 := abs_sub_le_one ht ⟨ha, by linarith⟩
  have htm : |t - a - q / 2| ≤ 1 := by
    simpa only [sub_sub] using abs_sub_le_one ht
      (show a + q / 2 ∈ Icc (0 : ℝ) 1 from ⟨by linarith, by linarith⟩)
  have htb : |t - a - q| ≤ 1 := by
    simpa only [sub_sub] using abs_sub_le_one ht
      (show a + q ∈ Icc (0 : ℝ) 1 from ⟨by linarith, haq⟩)
  have hpair₀ : |t - a - q / 2| * |t - a - q| ≤ 1 :=
    (mul_le_mul htm htb (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hpair₁ : |t - a| * |t - a - q| ≤ 1 :=
    (mul_le_mul hta htb (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hpair₂ : |t - a| * |t - a - q / 2| ≤ 1 :=
    (mul_le_mul hta htm (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  apply (le_div_iff₀ (sq_pos_of_pos hq)).2
  calc
    |f t| * q ^ 2 = |q ^ 2 * f t| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg q), mul_comm]
    _ = |2 * (t - a - q / 2) * (t - a - q) * f a -
        4 * (t - a) * (t - a - q) * f (a + q / 2) +
        2 * (t - a) * (t - a - q / 2) * f (a + q)| := by
      rw [quadratic_interpolation f hf]
    _ ≤ |2 * (t - a - q / 2) * (t - a - q) * f a| +
        |4 * (t - a) * (t - a - q) * f (a + q / 2)| +
        |2 * (t - a) * (t - a - q / 2) * f (a + q)| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ = 2 * (|t - a - q / 2| * |t - a - q| * |f a|) +
        4 * (|t - a| * |t - a - q| * |f (a + q / 2)|) +
        2 * (|t - a| * |t - a - q / 2| * |f (a + q)|) := by
      simp only [abs_mul]
      norm_num
      ring
    _ ≤ 2 * (1 * E) + 4 * (1 * E) + 2 * (1 * E) := by
      gcongr
    _ = 8 * E := by ring

/-- Whole-block quadratic control suffices for the preceding three-point estimate. -/
theorem quadratic_extrapolate_of_block (f : ℝ → ℝ) (hf : Quadratic f)
    {a q E : ℝ} (hq : 0 < q) (ha : 0 ≤ a) (haq : a + q ≤ 1)
    (h : ∀ t ∈ Icc a (a + q), |f t| ≤ E) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : |f t| ≤ 8 * E / q ^ 2 :=
  quadratic_extrapolate f hf hq ha haq (h a ⟨le_rfl, by linarith⟩)
    (h (a + q / 2) ⟨by linarith, by linarith⟩) (h (a + q) ⟨by linarith, le_rfl⟩) ht

/-- Restricting a scalar quadratic predictor to an affine trajectory remains quadratic. -/
theorem quadratic_along_scalar_trajectory (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) (b v : ℝ) :
    Quadratic (fun t => MvPolynomial.eval ![t, b + t * v] P) := by
  have h := Quadratic.mv_line P hP (![0, b] : Fin 2 → ℝ) ![1, v]
  convert h using 1
  funext t
  apply congrArg (fun f : Fin 2 → ℝ => MvPolynomial.eval f P)
  funext i
  fin_cases i <;> simp

/-- The fitting residual is quadratic in time, so it can be extrapolated. -/
theorem quadratic_scalar_residual (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) (b₀ b₁ b₂ b₃ b₄ : ℝ) :
    Quadratic (fun t => b₂ + t * b₃ + t ^ 2 * b₄ -
      MvPolynomial.eval ![t, b₀ + t * b₁] P) := by
  obtain ⟨A, B, C, h⟩ := quadratic_along_scalar_trajectory P hP b₀ b₁
  refine ⟨b₄ - A, b₃ - B, b₂ - C, fun t => ?_⟩
  dsimp only
  have ht := h t
  dsimp only at ht
  rw [ht]
  ring

/-- Full-time fitting error recovered from a positive-length block. -/
theorem scalar_fit_extrapolate (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) (b₀ b₁ b₂ b₃ b₄ : ℝ)
    {a q E : ℝ} (hq : 0 < q) (ha : 0 ≤ a) (haq : a + q ≤ 1)
    (h : ∀ t ∈ Icc a (a + q), |b₂ + t * b₃ + t ^ 2 * b₄ -
      MvPolynomial.eval ![t, b₀ + t * b₁] P| ≤ E) :
    ∀ t ∈ Icc (0 : ℝ) 1, |b₂ + t * b₃ + t ^ 2 * b₄ -
      MvPolynomial.eval ![t, b₀ + t * b₁] P| ≤ 8 * E / q ^ 2 := by
  intro t ht
  exact quadratic_extrapolate_of_block _
    (quadratic_scalar_residual P hP b₀ b₁ b₂ b₃ b₄) hq ha haq h ht

/-- The adapted norm of a quadratic predictor extrapolates with the same loss. -/
theorem scalar_adapted_norm_extrapolate (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) (u v β : ℝ)
    {a q E : ℝ} (hq : 0 < q) (ha : 0 ≤ a) (haq : a + q ≤ 1)
    (h : ∀ t ∈ Icc a (a + q), ∀ w ∈ Icc (-1 : ℝ) 1,
      |MvPolynomial.eval ![t, u + t * v + β * w] P| ≤ E) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
      |MvPolynomial.eval ![t, u + t * v + β * w] P| ≤ 8 * E / q ^ 2 := by
  intro t ht w hw
  have hf : Quadratic (fun t => MvPolynomial.eval ![t, u + t * v + β * w] P) := by
    convert quadratic_along_scalar_trajectory P hP (u + β * w) v using 1
    funext t
    apply congrArg (fun f : Fin 2 → ℝ => MvPolynomial.eval f P)
    funext i
    fin_cases i
    · simp
    · simp
      ring
  exact quadratic_extrapolate_of_block _ hf hq ha haq (fun t ht => h t ht w hw) ht

/-- Whole-block affine confinement gives a quantitative velocity window. -/
theorem velocity_bound_of_block {b w u v a q R : ℝ} (hq : 0 < q)
    (h : ∀ t ∈ Icc a (a + q), |b + t * w - u - t * v| ≤ R) :
    |w - v| ≤ 2 * R / q := by
  have h₀ := h a ⟨le_rfl, by linarith⟩
  have h₁ := h (a + q) ⟨by linarith, le_rfl⟩
  apply (le_div_iff₀ hq).2
  calc
    |w - v| * q = |(b + (a + q) * w - u - (a + q) * v) -
        (b + a * w - u - a * v)| := by
      rw [show (b + (a + q) * w - u - (a + q) * v) -
          (b + a * w - u - a * v) = (w - v) * q by ring,
        abs_mul, abs_of_pos hq]
    _ ≤ |b + (a + q) * w - u - (a + q) * v| + |b + a * w - u - a * v| :=
      abs_sub _ _
    _ ≤ 2 * R := by linarith

/-- Full-time affine confinement recovered from a block. -/
theorem scalar_confinement_extrapolate {b w u v a q R : ℝ} (hq : 0 < q)
    (ha : 0 ≤ a) (haq : a + q ≤ 1)
    (h : ∀ t ∈ Icc a (a + q), |b + t * w - u - t * v| ≤ R) :
    ∀ t ∈ Icc (0 : ℝ) 1, |b + t * w - u - t * v| ≤ 2 * R / q := by
  have h₀ : |(b - u) + a * (w - v)| ≤ R := by
    convert h a ⟨le_rfl, by linarith⟩ using 1 <;> congr 1 <;> ring
  have h₁ : |(b - u) + (a + q) * (w - v)| ≤ R := by
    convert h (a + q) ⟨by linarith, le_rfl⟩ using 1 <;> congr 1 <;> ring
  intro t ht
  convert affine_extrapolate hq ha haq h₀ h₁ ht using 1 <;> congr 1 <;> ring

/-- An occupied block controls its moving center using the assigned trajectory. -/
theorem center_bound_of_block {b w u v a q R B : ℝ} (hq : 0 < q)
    (ha : 0 ≤ a) (haq : a + q ≤ 1) (hb : |b| ≤ B) (hw : |w| ≤ B)
    (h : ∀ t ∈ Icc a (a + q), |b + t * w - u - t * v| ≤ R) :
    |u| + |v| ≤ 2 * B + 4 * R / q := by
  have hc₀ : |b - u| ≤ 2 * R / q := by
    simpa using scalar_confinement_extrapolate hq ha haq h 0 ⟨le_rfl, zero_le_one⟩
  have hc₁ := velocity_bound_of_block hq h
  have hu : |u| ≤ B + 2 * R / q := by
    calc
      |u| = |b - (b - u)| := by congr 1 <;> ring
      _ ≤ |b| + |b - u| := abs_sub _ _
      _ ≤ B + 2 * R / q := add_le_add hb hc₀
  have hv : |v| ≤ B + 2 * R / q := by
    calc
      |v| = |w - (w - v)| := by congr 1 <;> ring
      _ ≤ |w| + |w - v| := abs_sub _ _
      _ ≤ B + 2 * R / q := add_le_add hw hc₁
  calc
    |u| + |v| ≤ (B + 2 * R / q) + (B + 2 * R / q) := add_le_add hu hv
    _ = 2 * B + 4 * R / q := by ring

end Submission.Obl.k4_scalar_mesh_projection
