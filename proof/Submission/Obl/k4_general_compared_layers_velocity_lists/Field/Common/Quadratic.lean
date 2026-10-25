-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Common.Quadratic; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254 (k4_general_parent_wide_layer_candidates), session x0900.
   Uses the accepted quadratic coefficient tools of this LOT tree
   (`k4_fixed_budget_quadratic_recovery/QuadraticPolynomial.lean`,
   `k4_scalar_terminal_chart_packet_extraction/QuadBounds.lean`). -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Interfaces
import Submission.Obl.k4_fixed_budget_quadratic_recovery.QuadraticPolynomial

/-!
# Transverse coefficients of a projected quadratic

For a projected quadratic `G(t, Y)` of total degree at most two:

* `∂_Y G` is affine and `∂_Y^2 G` is constant (`exists_quadratic_derivs`);
* in the adapted frame `Y = u + t v + β w` of a projected label, where `|G| ≤ H` on
  `[0,1] × [-1,1]`, both are controlled by `8 H` coefficients (`adapted_derivs`).

Along the virtual line of an original block with normalized intercept `bb` and velocity
`vv`, the transverse slope coefficient `transB` is affine in block time (`lineB_affine`);
two virtual lines differ by an explicit multiple of the second derivative (`lineB_sub`).
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_fixed_budget_quadratic_recovery (quadraticValue quadraticPolynomial
  quadraticExponent polynomial_eq_of_quadratic_values quadratic_coefficients_bound)
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction (isQuad2_eval)

noncomputable section

namespace FieldCommon

theorem eval_pderiv_quadraticPolynomial (g : Fin 6 → ℝ) (t z : ℝ) :
    eval ![t, z] (pderiv 1 (quadraticPolynomial g)) = g 2 + g 4 * t + 2 * g 5 * z := by
  unfold quadraticPolynomial
  simp [Fin.sum_univ_succ, quadraticExponent, pderiv_monomial, eval_monomial,
    Finsupp.prod_fintype, Fin.prod_univ_two]
  ring

theorem eval_pderiv_pderiv_quadraticPolynomial (g : Fin 6 → ℝ) (x : Fin 2 → ℝ) :
    eval x (pderiv 1 (pderiv 1 (quadraticPolynomial g))) = 2 * g 5 := by
  unfold quadraticPolynomial
  simp [Fin.sum_univ_succ, quadraticExponent, pderiv_monomial, eval_monomial,
    Finsupp.prod_fintype, Fin.prod_univ_two]
  ring

/-- A two-variable polynomial of total degree at most two has an affine `Y`-derivative and a
constant second `Y`-derivative. -/
theorem exists_quadratic_derivs (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2) :
    ∃ g : Fin 6 → ℝ, (∀ t z, eval ![t, z] G = quadraticValue g t z) ∧
      (∀ t z, eval ![t, z] (pderiv 1 G) = g 2 + g 4 * t + 2 * g 5 * z) ∧
      (∀ x, eval x (pderiv 1 (pderiv 1 G)) = 2 * g 5) := by
  obtain ⟨g, hg⟩ := isQuad2_eval G hG
  have hg' : ∀ t z, eval ![t, z] G = quadraticValue g t z := fun t z => hg t z
  have hG' : G = quadraticPolynomial g := polynomial_eq_of_quadratic_values hg'
  refine ⟨g, hg', ?_, ?_⟩
  · intro t z
    rw [hG']
    exact eval_pderiv_quadraticPolynomial g t z
  · intro x
    rw [hG']
    exact eval_pderiv_pderiv_quadraticPolynomial g x

/-- **Adapted derivative bounds.** If `|G(t, u + t v + β w)| ≤ H` on `[0,1] × [-1,1]`, the
derivatives of `G` in `Y` are given, in the adapted frame, by six coefficients bounded by
`8 H`. -/
theorem adapted_derivs (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2)
    {H u v β : ℝ} (hβ : 0 < β)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
      |eval ![t, u + t * v + β * w] G| ≤ H) :
    ∃ c : Fin 6 → ℝ, (∀ i, |c i| ≤ 8 * H) ∧
      (∀ t Y, β * eval ![t, Y] (pderiv 1 G) =
        c 2 + c 4 * t + 2 * c 5 * ((Y - u - t * v) / β)) ∧
      (∀ x, β ^ 2 * eval x (pderiv 1 (pderiv 1 G)) = 2 * c 5) := by
  obtain ⟨g, hg, hd1, hd2⟩ := exists_quadratic_derivs G hG
  let c : Fin 6 → ℝ := ![g 0 + g 2 * u + g 5 * u ^ 2,
    g 1 + g 2 * v + g 4 * u + 2 * g 5 * u * v,
    g 2 * β + 2 * g 5 * u * β,
    g 3 + g 4 * v + g 5 * v ^ 2,
    g 4 * β + 2 * g 5 * v * β,
    g 5 * β ^ 2]
  have c0 : c 0 = g 0 + g 2 * u + g 5 * u ^ 2 := rfl
  have c1 : c 1 = g 1 + g 2 * v + g 4 * u + 2 * g 5 * u * v := rfl
  have c2 : c 2 = g 2 * β + 2 * g 5 * u * β := rfl
  have c3 : c 3 = g 3 + g 4 * v + g 5 * v ^ 2 := rfl
  have c4 : c 4 = g 4 * β + 2 * g 5 * v * β := rfl
  have c5 : c 5 = g 5 * β ^ 2 := rfl
  have hc : ∀ t w, eval ![t, u + t * v + β * w] G = quadraticValue c t w := by
    intro t w
    rw [hg]
    simp only [quadraticValue, c0, c1, c2, c3, c4, c5]
    ring
  refine ⟨c, ?_, ?_, ?_⟩
  · apply quadratic_coefficients_bound
    intro t ht w hw
    rw [← hc]
    exact hbound t ht w hw
  · intro t Y
    rw [hd1, c2, c4, c5]
    field_simp
    ring
  · intro x
    rw [hd2, c5]
    ring

/-- The transverse slope coefficient is bounded where the tilted center stays within
`2 H^2` adapted widths of the label's line. -/
theorem transverse_slope_bound {G : MvPolynomial (Fin 2) ℝ} {c : Fin 6 → ℝ}
    {H u v β w t Y : ℝ} (hH : 1 ≤ H) (hβ : 0 < β) (hc : ∀ i, |c i| ≤ 8 * H)
    (hrep : β * eval ![t, Y] (pderiv 1 G) = c 2 + c 4 * t + 2 * c 5 * ((Y - u - t * v) / β))
    (hw : 0 ≤ w) (hwβ : w ≤ H * β) (ht : |t| ≤ 1) (hY : |Y - u - t * v| ≤ 2 * H ^ 2 * β) :
    |w * eval ![t, Y] (pderiv 1 G)| ≤ 48 * H ^ 4 := by
  have hH0 : 0 ≤ H := by linarith
  have hρ : w / β ≤ H := by rw [div_le_iff₀ hβ]; linarith
  have hρ0 : 0 ≤ w / β := div_nonneg hw hβ.le
  have heq : w * eval ![t, Y] (pderiv 1 G) =
      (w / β) * (c 2 + c 4 * t + 2 * c 5 * ((Y - u - t * v) / β)) := by
    rw [← hrep]
    field_simp
  have hYβ : |(Y - u - t * v) / β| ≤ 2 * H ^ 2 := by
    rw [abs_div, abs_of_pos hβ, div_le_iff₀ hβ]
    exact hY
  have hinner : |c 2 + c 4 * t + 2 * c 5 * ((Y - u - t * v) / β)| ≤ 48 * H ^ 3 := by
    have h2 := hc 2
    have h4 := hc 4
    have h5 := hc 5
    have hct : |c 4 * t| ≤ 8 * H := by
      rw [abs_mul]
      calc |c 4| * |t| ≤ 8 * H * 1 := mul_le_mul h4 ht (abs_nonneg _) (by linarith)
        _ = 8 * H := by ring
    have hc5 : |2 * c 5 * ((Y - u - t * v) / β)| ≤ 32 * H ^ 3 := by
      rw [abs_mul, abs_mul, abs_two]
      calc 2 * |c 5| * |(Y - u - t * v) / β| ≤ 2 * (8 * H) * (2 * H ^ 2) := by
            gcongr
        _ = 32 * H ^ 3 := by ring
    have hH3 : H ≤ H ^ 3 := by nlinarith
    calc _ ≤ |c 2| + |c 4 * t| + |2 * c 5 * ((Y - u - t * v) / β)| := by
          grw [abs_add_le, abs_add_le]
      _ ≤ 8 * H + 8 * H + 32 * H ^ 3 := by linarith
      _ ≤ 48 * H ^ 3 := by linarith
  rw [heq, abs_mul, abs_of_nonneg hρ0]
  calc w / β * |c 2 + c 4 * t + 2 * c 5 * ((Y - u - t * v) / β)| ≤ H * (48 * H ^ 3) :=
        mul_le_mul hρ hinner (abs_nonneg _) hH0
    _ = 48 * H ^ 4 := by ring

/-- The transverse curvature coefficient is bounded by `8 H^3`. -/
theorem transverse_curvature_bound {G : MvPolynomial (Fin 2) ℝ} {c : Fin 6 → ℝ}
    {H β w : ℝ} (hH : 1 ≤ H) (hβ : 0 < β) (hc : ∀ i, |c i| ≤ 8 * H)
    (hrep : ∀ x, β ^ 2 * eval x (pderiv 1 (pderiv 1 G)) = 2 * c 5)
    (hw : 0 ≤ w) (hwβ : w ≤ H * β) :
    |transD G w| ≤ 8 * H ^ 3 := by
  have hH0 : 0 ≤ H := by linarith
  have hρ : w / β ≤ H := by rw [div_le_iff₀ hβ]; linarith
  have hρ0 : 0 ≤ w / β := div_nonneg hw hβ.le
  have heq : transD G w = (w / β) ^ 2 * c 5 := by
    unfold transD
    have h := hrep ![0, 0]
    have he : eval ![0, 0] (pderiv 1 (pderiv 1 G)) = 2 * c 5 / β ^ 2 := by
      rw [eq_div_iff (by positivity), mul_comm]
      exact h
    rw [he]
    field_simp
  rw [heq, abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc (w / β) ^ 2 * |c 5| ≤ H ^ 2 * (8 * H) :=
        mul_le_mul (pow_le_pow_left₀ hρ0 hρ 2) (hc 5) (abs_nonneg _) (by positivity)
    _ = 8 * H ^ 3 := by ring

/-- The second `Y`-derivative is controlled by the adapted coefficients. -/
theorem second_derivative_bound {G : MvPolynomial (Fin 2) ℝ} {c : Fin 6 → ℝ}
    {H β : ℝ} (hβ : 0 < β) (hc : ∀ i, |c i| ≤ 8 * H)
    (hrep : ∀ x, β ^ 2 * eval x (pderiv 1 (pderiv 1 G)) = 2 * c 5) (x : Fin 2 → ℝ) :
    |eval x (pderiv 1 (pderiv 1 G))| ≤ 16 * H / β ^ 2 := by
  have hβ2 : 0 < β ^ 2 := by positivity
  have heq : eval x (pderiv 1 (pderiv 1 G)) = 2 * c 5 / β ^ 2 := by
    rw [eq_div_iff hβ2.ne', mul_comm, hrep x]
  rw [heq, abs_div, abs_of_pos hβ2, abs_mul, abs_two]
  apply div_le_div_of_nonneg_right _ hβ2.le
  linarith [hc 5]

end FieldCommon

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- The normalized major intercept of a trajectory in an original block: the value of the
normalized major coordinate `ζ` at block time `0`. -/
def majorIntercept (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (l : α) : ℝ :=
  (p.b k l 0 + p.blockStart k r Q * (p.b k l 3 - p.c k r Q 1) - p.c k r Q 0) / p.blockLen k r

/-- The transverse slope coefficient of `G` along the virtual line of the block with
normalized major intercept `bb` and velocity `vv`, at block time `τ`. -/
def lineB (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (G : MvPolynomial (Fin 2) ℝ)
    (bb vv τ : ℝ) : ℝ :=
  transB G (p.tiltY k r Q) (p.blockWidth k r) (p.blockStart k r Q + p.blockLen k r * τ)
    (p.c k r Q 0 + p.c k r Q 1 * p.blockStart k r Q + p.blockLen k r * bb +
      p.blockLen k r * τ * vv)

/-- The affine-in-time coefficients and the curvature coefficient of `G` along a virtual
line: the entry of a fiber list. -/
def lineCoeff (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (G : MvPolynomial (Fin 2) ℝ)
    (bb vv : ℝ) : Fin 3 → ℝ :=
  ![p.lineB k r Q G bb vv 0, p.lineB k r Q G bb vv 1 - p.lineB k r Q G bb vv 0,
    transD G (p.blockWidth k r)]

theorem common_blockLen_pos (k : ℕ) (r : ℝ) : 0 < p.blockLen k r := by
  unfold blockLen
  positivity

theorem common_blockLen_le_one (k : ℕ) (r : ℝ) : p.blockLen k r ≤ 1 := by
  unfold blockLen
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

/-- Along a virtual line the transverse slope coefficient is affine in block time. -/
theorem lineB_affine (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) {G : MvPolynomial (Fin 2) ℝ}
    (hG : G.totalDegree ≤ 2) (bb vv τ : ℝ) :
    p.lineB k r Q G bb vv τ = p.lineB k r Q G bb vv 0 +
      (p.lineB k r Q G bb vv 1 - p.lineB k r Q G bb vv 0) * τ := by
  obtain ⟨g, -, hd1, -⟩ := FieldCommon.exists_quadratic_derivs G hG
  simp only [lineB, transB, tiltY, hd1]
  ring

/-- Two virtual lines differ by an explicit multiple of the second derivative. -/
theorem lineB_sub (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) {G : MvPolynomial (Fin 2) ℝ}
    (hG : G.totalDegree ≤ 2) (bb vv bb' vv' τ : ℝ) :
    p.lineB k r Q G bb vv τ - p.lineB k r Q G bb' vv' τ =
      p.blockWidth k r * eval ![0, 0] (pderiv 1 (pderiv 1 G)) * p.c k r Q 4 *
        p.blockLen k r * ((bb - bb') + τ * (vv - vv')) := by
  obtain ⟨g, -, hd1, hd2⟩ := FieldCommon.exists_quadratic_derivs G hG
  simp only [lineB, transB, tiltY, hd1, hd2]
  ring

/-- The first transverse coefficient of an incidence is the virtual-line coefficient at its
own major intercept, velocity and block time. -/
theorem transPair_zero_eq_lineB (k : ℕ) (r : ℝ) (Q : Fin (p.n k r))
    (G : MvPolynomial (Fin 2) ℝ) (ω : α × ℝ) :
    p.transPair k r Q G ω 0 =
      p.lineB k r Q G (p.majorIntercept k r Q ω.1) (p.b k ω.1 3) (p.tauN k r Q ω) := by
  have hq := (p.common_blockLen_pos k r).ne'
  have ht : p.blockStart k r Q + p.blockLen k r * p.tauN k r Q ω = ω.2 := by
    unfold tauN
    field_simp
    ring
  have hZ : p.c k r Q 0 + p.c k r Q 1 * p.blockStart k r Q +
      p.blockLen k r * p.majorIntercept k r Q ω.1 +
      p.blockLen k r * p.tauN k r Q ω * p.b k ω.1 3 = p.x k ω.1 ω.2 1 := by
    unfold majorIntercept tauN
    simp only [Submission.Obl.k4_critical_intercept_concentration.Data.x,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    field_simp
    ring
  simp only [transPair, Matrix.cons_val_zero, lineB]
  rw [ht, hZ]

/-- The second transverse coefficient is the constant curvature coefficient. -/
theorem transPair_one_eq (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (G : MvPolynomial (Fin 2) ℝ)
    (ω : α × ℝ) : p.transPair k r Q G ω 1 = transD G (p.blockWidth k r) := by
  simp [transPair]

/-- The normalized major coordinate is the major intercept moved by the relative
velocity. -/
theorem common_zetaN_eq (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (ω : α × ℝ) :
    p.zetaN k r Q ω = p.majorIntercept k r Q ω.1 +
      p.tauN k r Q ω * (p.b k ω.1 3 - p.c k r Q 1) := by
  have hq := (p.common_blockLen_pos k r).ne'
  unfold zetaN majorIntercept tauN
  simp only [Submission.Obl.k4_critical_intercept_concentration.Data.x,
    Matrix.cons_val_one, Matrix.cons_val_zero]
  field_simp
  ring

end Parent

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
