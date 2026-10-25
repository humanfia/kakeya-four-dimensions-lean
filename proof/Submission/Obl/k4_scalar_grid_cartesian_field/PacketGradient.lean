import Submission.Obl.k4_scalar_grid_cartesian_field.PacketPolynomial
import Submission.Lib.K4PolynomialPotential.AffineCurl
import Submission.Obl.k4_quadratic_atlas_normalization.Curvature

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open MvPolynomial
open Submission.Lib.K4PolynomialPotential

/-- The packet substitution agrees with the accepted affine polynomial homomorphism. -/
theorem packetPolynomial_eq_scalarAffineHom (F : MvPolynomial (Fin 2) ℝ) (a h u v : ℝ) :
    packetPolynomial F a h u v =
      scalarAffineHom ![a, u + a * v] ![![h, 0], ![h * v, h]] F := by
  unfold packetPolynomial Submission.Obl.k4_scalar_candidate_original_return.Normalize.affSubst
    scalarAffineHom
  apply congrArg (fun g : Fin 2 → MvPolynomial (Fin 2) ℝ => MvPolynomial.aeval g F)
  funext e
  ring

/-- Partial derivatives retain the physical time and transverse scaling factors. -/
theorem pderiv_packetPolynomial (F : MvPolynomial (Fin 2) ℝ) (a h u v : ℝ) (i : Fin 2) :
    pderiv i (packetPolynomial F a h u v) =
      C ((![h, 0] : Fin 2 → ℝ) i) * packetPolynomial (pderiv 0 F) a h u v +
        C ((![h * v, h] : Fin 2 → ℝ) i) * packetPolynomial (pderiv 1 F) a h u v := by
  rw [packetPolynomial_eq_scalarAffineHom, pderiv_scalarAffineHom,
    ← packetPolynomial_eq_scalarAffineHom, ← packetPolynomial_eq_scalarAffineHom]
  rfl

/-- The two exact chain-rule identities in normalized packet coordinates. -/
theorem eval_packetPolynomial_partials (F : MvPolynomial (Fin 2) ℝ)
    (a h u v τ w : ℝ) :
    eval ![τ, w] (pderiv 0 (packetPolynomial F a h u v)) =
        h * (eval ![a + h * τ, u + (a + h * τ) * v + h * w] (pderiv 0 F) +
          v * eval ![a + h * τ, u + (a + h * τ) * v + h * w] (pderiv 1 F)) ∧
    eval ![τ, w] (pderiv 1 (packetPolynomial F a h u v)) =
        h * eval ![a + h * τ, u + (a + h * τ) * v + h * w] (pderiv 1 F) := by
  constructor <;> simp [pderiv_packetPolynomial, eval_packetPolynomial] <;> ring

noncomputable def packetPoint (a h u v : ℝ) (z : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![a + h * z 0, u + (a + h * z 0) * v + h * z 1]

/-- Fine normalized cells make the physical predictor gradient almost constant. -/
theorem packet_gradient_variation (F : MvPolynomial (Fin 2) ℝ)
    (hF : F.totalDegree ≤ 2) {a h u v K ξ : ℝ} (hh : 0 < h)
    (hK : 1 ≤ K) (hξ : 0 ≤ ξ) (hv : |v| ≤ K)
    (hcoeff : ∀ b, |(packetPolynomial F a h u v).coeff b| ≤ 48 * K)
    (z z' : Fin 2 → ℝ) (hz : ∀ e, |z e| ≤ K) (hz' : ∀ e, |z' e| ≤ K)
    (hnear : ∀ e, |z e - z' e| ≤ (K + 2) * ξ) :
    ∀ e, |eval (packetPoint a h u v z) (pderiv e F) -
      eval (packetPoint a h u v z') (pderiv e F)| ≤ 23040 * K ^ 4 * ξ / h := by
  let Q := packetPolynomial F a h u v
  have hQ : Q.totalDegree ≤ 2 := (packetPolynomial_degree _ _ _ _ _).trans hF
  have hc (e : Fin 2) (b : Fin 2 →₀ ℕ) : |(pderiv e Q).coeff b| ≤ 96 * K := by
    convert Submission.Obl.k4_quadratic_atlas_normalization.quadratic_pderiv_coeff_bound
      Q hQ e (by positivity : 0 ≤ 48 * K) hcoeff b using 1 <;> ring
  have hd (e : Fin 2) : (pderiv e Q).totalDegree ≤ 2 :=
    (Submission.Obl.k4_eligibility_sign_description.degree_pderiv_le Q e).trans hQ
  have hsum : |z 0 - z' 0| + |z 1 - z' 1| ≤ 2 * (K + 2) * ξ := by
    linarith [hnear 0, hnear 1]
  have hconstant : 10 * (96 * K) * (1 + K) * (2 * (K + 2)) ≤ 11520 * K ^ 3 := by
    calc
      _ ≤ 10 * (96 * K) * (2 * K) * (2 * (3 * K)) := by gcongr <;> linarith
      _ = _ := by ring
  have hp (e : Fin 2) : |eval z (pderiv e Q) - eval z' (pderiv e Q)| ≤
      11520 * K ^ 3 * ξ := by
    calc
      _ ≤ 10 * (96 * K) * (1 + K) * (|z 0 - z' 0| + |z 1 - z' 1|) :=
        Submission.Obl.k4_scalar_candidate_original_return.Cells.quad_lipschitz
          (pderiv e Q) (hd e) (hc e) z z' hz hz'
      _ ≤ 10 * (96 * K) * (1 + K) * (2 * (K + 2) * ξ) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hconstant hξ]
  have hchain (w : Fin 2 → ℝ) :
      eval w (pderiv 0 Q) = h * (eval (packetPoint a h u v w) (pderiv 0 F) +
        v * eval (packetPoint a h u v w) (pderiv 1 F)) ∧
      eval w (pderiv 1 Q) = h * eval (packetPoint a h u v w) (pderiv 1 F) := by
    have hw : (![w 0, w 1] : Fin 2 → ℝ) = w := by ext e; fin_cases e <;> rfl
    simpa only [hw, packetPoint] using eval_packetPolynomial_partials F a h u v (w 0) (w 1)
  have h₁ : eval (packetPoint a h u v z) (pderiv 1 F) -
      eval (packetPoint a h u v z') (pderiv 1 F) =
      (eval z (pderiv 1 Q) - eval z' (pderiv 1 Q)) / h := by
    rw [(hchain z).2, (hchain z').2]
    field_simp
    <;> ring
  have h₀ : eval (packetPoint a h u v z) (pderiv 0 F) -
      eval (packetPoint a h u v z') (pderiv 0 F) =
      ((eval z (pderiv 0 Q) - eval z' (pderiv 0 Q)) -
        v * (eval z (pderiv 1 Q) - eval z' (pderiv 1 Q))) / h := by
    rw [(hchain z).1, (hchain z').1, (hchain z).2, (hchain z').2]
    field_simp
    <;> ring
  have hlarge : (1 + K) * (11520 * K ^ 3 * ξ) ≤ 23040 * K ^ 4 * ξ := by
    calc
      _ ≤ (2 * K) * (11520 * K ^ 3 * ξ) := by gcongr; linarith
      _ = _ := by ring
  intro e
  fin_cases e
  · change |eval (packetPoint a h u v z) (pderiv 0 F) -
      eval (packetPoint a h u v z') (pderiv 0 F)| ≤ 23040 * K ^ 4 * ξ / h
    rw [h₀, abs_div, abs_of_pos hh]
    apply (div_le_div_iff_of_pos_right hh).mpr
    calc
      _ ≤ |eval z (pderiv 0 Q) - eval z' (pderiv 0 Q)| +
          |v * (eval z (pderiv 1 Q) - eval z' (pderiv 1 Q))| := abs_sub _ _
      _ ≤ 11520 * K ^ 3 * ξ + K * (11520 * K ^ 3 * ξ) := by
        rw [abs_mul]
        exact add_le_add (hp 0) (mul_le_mul hv (hp 1) (abs_nonneg _) (by linarith))
      _ = (1 + K) * (11520 * K ^ 3 * ξ) := by ring
      _ ≤ _ := hlarge
  · change |eval (packetPoint a h u v z) (pderiv 1 F) -
      eval (packetPoint a h u v z') (pderiv 1 F)| ≤ 23040 * K ^ 4 * ξ / h
    rw [h₁, abs_div, abs_of_pos hh]
    apply (div_le_div_iff_of_pos_right hh).mpr
    apply (hp 1).trans
    calc
      _ ≤ (1 + K) * (11520 * K ^ 3 * ξ) := by
        apply le_mul_of_one_le_left (by positivity)
        linarith
      _ ≤ _ := hlarge

theorem packetPoint_inverse (a h u v t y : ℝ) (hh : h ≠ 0) :
    packetPoint a h u v ![(t - a) / h, (y - u - t * v) / h] = ![t, y] := by
  funext e
  fin_cases e <;> simp [packetPoint] <;> field_simp <;> ring

/-- Two original packet points in one sufficiently small unsheared base cell have close gradients. -/
theorem packet_gradient_cell_variation (F : MvPolynomial (Fin 2) ℝ)
    (hF : F.totalDegree ≤ 2) {a h u v K t t' y y' ξ : ℝ}
    (hh : 0 < h) (hK : 1 ≤ K) (hξ : 0 ≤ ξ) (hv : |v| ≤ K)
    (hbound : ∀ t ∈ Set.Icc a (a + h), ∀ w ∈ Set.Icc (-1 : ℝ) 1,
      |eval ![t, u + t * v + h * w] F| ≤ K)
    (ht : t ∈ Set.Icc a (a + h)) (ht' : t' ∈ Set.Icc a (a + h))
    (hy : |y - u - t * v| ≤ K * h) (hy' : |y' - u - t' * v| ≤ K * h)
    (hdt : |t - t'| ≤ h * ξ) (hdy : |y - y'| ≤ h * ξ) :
    ∀ e, |eval ![t, y] (pderiv e F) - eval ![t', y'] (pderiv e F)| ≤
      23040 * K ^ 4 * ξ / h := by
  let z : Fin 2 → ℝ := ![(t - a) / h, (y - u - t * v) / h]
  let z' : Fin 2 → ℝ := ![(t' - a) / h, (y' - u - t' * v) / h]
  have hc (t₀ y₀ : ℝ) (ht₀ : t₀ ∈ Set.Icc a (a + h))
      (hy₀ : |y₀ - u - t₀ * v| ≤ K * h) :
      ∀ e, |(![(t₀ - a) / h, (y₀ - u - t₀ * v) / h] : Fin 2 → ℝ) e| ≤ K := by
    intro e
    fin_cases e
    · change |(t₀ - a) / h| ≤ K
      rw [abs_div, abs_of_pos hh, abs_of_nonneg (by linarith [ht₀.1])]
      exact ((div_le_one hh).mpr (by linarith [ht₀.2])).trans hK
    · change |(y₀ - u - t₀ * v) / h| ≤ K
      rw [abs_div, abs_of_pos hh]
      exact (div_le_iff₀ hh).mpr hy₀
  have hnear : ∀ e, |z e - z' e| ≤ (K + 2) * ξ := by
    intro e
    fin_cases e
    · change |(t - a) / h - (t' - a) / h| ≤ (K + 2) * ξ
      rw [show (t - a) / h - (t' - a) / h = (t - t') / h by ring,
        abs_div, abs_of_pos hh]
      apply (div_le_iff₀ hh).mpr
      have hmul := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ K + 2 by linarith)
        (mul_nonneg hh.le hξ)
      nlinarith
    · change |(y - u - t * v) / h - (y' - u - t' * v) / h| ≤ (K + 2) * ξ
      rw [show (y - u - t * v) / h - (y' - u - t' * v) / h =
        ((y - y') - v * (t - t')) / h by ring, abs_div, abs_of_pos hh]
      apply (div_le_iff₀ hh).mpr
      have hraw : |(y - y') - v * (t - t')| ≤ (1 + K) * (h * ξ) := by
        calc
          _ ≤ |y - y'| + |v * (t - t')| := abs_sub _ _
          _ ≤ h * ξ + K * (h * ξ) := by
            rw [abs_mul]
            exact add_le_add hdy (mul_le_mul hv hdt (abs_nonneg _) (by linarith))
          _ = _ := by ring
      nlinarith [mul_nonneg hh.le hξ]
  have hout := packet_gradient_variation F hF hh hK hξ hv
    (packetPolynomial_coeff_bound F hF hh (by linarith : 0 ≤ K) hbound)
    z z' (hc t y ht hy) (hc t' y' ht' hy') hnear
  simpa only [z, z', packetPoint_inverse a h u v t y hh.ne',
    packetPoint_inverse a h u v t' y' hh.ne'] using hout

end Submission.Obl.k4_scalar_grid_cartesian_field
