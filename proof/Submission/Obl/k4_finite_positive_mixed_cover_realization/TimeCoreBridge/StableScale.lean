-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/StableScale.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/StableScale.lean (namespace renamed).

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.StableNormalization
import Submission.Obl.k4_stable_quadratic_hidden_sheets

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MvPolynomial
open Submission.Obl.k4_stable_quadratic_hidden_sheets

/-- The root derivative square differs from the anchor derivative square by a uniformly
small discriminant error. -/
theorem stable_root_square_error {A a_fit a : ℝ} (hA : 2 ≤ A)
    (b c : MvPolynomial (Fin 3) ℝ) (hb : b.totalDegree ≤ 1) (hc : c.totalDegree ≤ 2)
    (hcoeff : ∀ e, |(b * b - MvPolynomial.C (4 * a) * c).coeff e| ≤ A)
    (hsmall : |a| * a_fit ≤ A ^ (-20 : ℝ))
    (u0 u : Real3) (w0 φ : ℝ) (hu0 : ‖u0‖ ≤ A)
    (hu : ‖u - u0‖ < (A ^ 20)⁻¹)
    (hvalue : |a * w0 ^ 2 + eval (fun j => u0 j) b * w0 + eval (fun j => u0 j) c| ≤ a_fit * A)
    (hroot : a * φ ^ 2 + eval (fun j => u j) b * φ + eval (fun j => u j) c = 0) :
    |(2 * a * φ + eval (fun j => u j) b) ^ 2 -
      (2 * a * w0 + eval (fun j => u0 j) b) ^ 2| ≤ 1 / (2 * A ^ 2) := by
  have hApos : 0 < A := by linarith
  have hAone : 1 ≤ A := by linarith
  have hsmall' : |a| * a_fit ≤ (A ^ 20)⁻¹ := by
    have he : A ^ (-20 : ℝ) = (A ^ 20)⁻¹ := by
      rw [show (-20 : ℝ) = -((20 : ℕ) : ℝ) by norm_num,
        Real.rpow_neg hApos.le, Real.rpow_natCast]
    simpa only [he] using hsmall
  let D := b * b - MvPolynomial.C (4 * a) * c
  let σ := 2 * a * w0 + eval (fun j => u0 j) b
  have hDdeg : D.totalDegree ≤ 2 := by
    apply (totalDegree_sub _ _).trans
    apply max_le
    · exact (totalDegree_mul b b).trans (by omega)
    · exact (totalDegree_mul _ c).trans (by simpa only [totalDegree_C, zero_add] using hc)
  have hvar : |eval (fun j => u j) D - eval (fun j => u0 j) D| ≤ 1 / (4 * A ^ 2) := by
    have hh := eval₂_sub_le D hDdeg A hcoeff A ((A ^ 20)⁻¹) hAone
      (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ hAone))
      (fun j => (u0 j : ℂ)) (fun j => (u j : ℂ))
      (coord_le_of_norm_le u0 A hu0)
      (fun i => (coord_lt_of_norm_sub_lt u0 u _ hu i).le)
    rw [eval₂_ofReal, eval₂_ofReal, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hh
    exact hh.trans (num_ball A hA)
  have hcorr : |4 * a *
      (a * w0 ^ 2 + eval (fun j => u0 j) b * w0 + eval (fun j => u0 j) c)| ≤ 1 / (4 * A ^ 2) := by
    calc
      _ = 4 * (|a| * |a * w0 ^ 2 + eval (fun j => u0 j) b * w0 + eval (fun j => u0 j) c|) := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
        ring
      _ ≤ 4 * (|a| * (a_fit * A)) := by gcongr
      _ = 4 * ((|a| * a_fit) * A) := by ring
      _ ≤ 4 * ((A ^ 20)⁻¹ * A) := by gcongr
      _ ≤ _ := num_disc0 A hA
  have hD0 : eval (fun j => u0 j) D = σ ^ 2 - 4 * a *
      (a * w0 ^ 2 + eval (fun j => u0 j) b * w0 + eval (fun j => u0 j) c) := by
    dsimp only [D, σ]
    rw [eval_disc]
    ring
  have hq : (2 * a * φ + eval (fun j => u j) b) ^ 2 = eval (fun j => u j) D := by
    dsimp only [D]
    rw [eval_disc]
    linear_combination 4 * a * hroot
  have he : (2 * a * φ + eval (fun j => u j) b) ^ 2 - σ ^ 2 =
      (eval (fun j => u j) D - eval (fun j => u0 j) D) - 4 * a *
        (a * w0 ^ 2 + eval (fun j => u0 j) b * w0 + eval (fun j => u0 j) c) := by
    rw [hq, hD0]
    ring
  change |(2 * a * φ + eval (fun j => u j) b) ^ 2 - σ ^ 2| ≤ _
  rw [he]
  calc
    _ ≤ |eval (fun j => u j) D - eval (fun j => u0 j) D| +
        |4 * a * (a * w0 ^ 2 + eval (fun j => u0 j) b * w0 + eval (fun j => u0 j) c)| :=
      abs_sub _ _
    _ ≤ 1 / (4 * A ^ 2) + 1 / (4 * A ^ 2) := add_le_add hvar hcorr
    _ = _ := by ring

/-- Every exact root in the stable comparison ball has derivative within a fixed
factor of the original anchor derivative, as required by representative normalization. -/
theorem stable_root_derivative_scale {A a_fit a : ℝ} (hA : 2 ≤ A)
    (b c : MvPolynomial (Fin 3) ℝ) (hb : b.totalDegree ≤ 1) (hc : c.totalDegree ≤ 2)
    (hcoeff : ∀ e, |(b * b - MvPolynomial.C (4 * a) * c).coeff e| ≤ A)
    (hsmall : |a| * a_fit ≤ A ^ (-20 : ℝ))
    (u0 u : Real3) (w0 φ : ℝ) (hu0 : ‖u0‖ ≤ A)
    (hu : ‖u - u0‖ < (A ^ 20)⁻¹)
    (hvalue : |a * w0 ^ 2 + eval (fun j => u0 j) b * w0 + eval (fun j => u0 j) c| ≤ a_fit * A)
    (hslo : A ^ (-1 : ℝ) ≤ |2 * a * w0 + eval (fun j => u0 j) b|)
    (hroot : a * φ ^ 2 + eval (fun j => u j) b * φ + eval (fun j => u j) c = 0) :
    |2 * a * w0 + eval (fun j => u0 j) b| / 2 ≤ |2 * a * φ + eval (fun j => u j) b| ∧
      |2 * a * φ + eval (fun j => u j) b| ≤ 2 * |2 * a * w0 + eval (fun j => u0 j) b| := by
  have hApos : 0 < A := by linarith
  let σ := 2 * a * w0 + eval (fun j => u0 j) b
  have hσsq : 1 / A ^ 2 ≤ σ ^ 2 := by
    rw [Real.rpow_neg_one] at hslo
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ A⁻¹) hslo 2
    simpa only [inv_pow, sq_abs, one_div] using hh
  have herr := stable_root_square_error hA b c hb hc hcoeff hsmall u0 u w0 φ hu0 hu hvalue hroot
  change |(2 * a * φ + eval (fun j => u j) b) ^ 2 - σ ^ 2| ≤ 1 / (2 * A ^ 2) at herr
  have hhalf : 1 / A ^ 2 = 2 * (1 / (2 * A ^ 2)) := by ring
  obtain ⟨hlo, hhi⟩ := abs_le.mp herr
  have hlow : σ ^ 2 / 2 ≤ (2 * a * φ + eval (fun j => u j) b) ^ 2 := by nlinarith
  have hhigh : (2 * a * φ + eval (fun j => u j) b) ^ 2 ≤ (3 / 2 : ℝ) * σ ^ 2 := by nlinarith
  change |σ| / 2 ≤ _ ∧ _ ≤ 2 * |σ|
  constructor
  · by_contra! hh
    nlinarith [sq_abs σ, sq_abs (2 * a * φ + eval (fun j => u j) b),
      abs_nonneg σ, abs_nonneg (2 * a * φ + eval (fun j => u j) b)]
  · by_contra! hh
    nlinarith [sq_abs σ, sq_abs (2 * a * φ + eval (fun j => u j) b),
      abs_nonneg σ, abs_nonneg (2 * a * φ + eval (fun j => u j) b)]

/-- A slightly stronger anchor floor leaves room for the finite endpoint derivative
windows used to define geometric output assignments. -/
theorem stable_root_derivative_window {A a_fit a : ℝ} (hA : 2 ≤ A)
    (b c : MvPolynomial (Fin 3) ℝ) (hb : b.totalDegree ≤ 1) (hc : c.totalDegree ≤ 2)
    (hcoeff : ∀ e, |(b * b - MvPolynomial.C (4 * a) * c).coeff e| ≤ A)
    (hsmall : |a| * a_fit ≤ A ^ (-20 : ℝ))
    (u0 u : Real3) (w0 φ : ℝ) (hu0 : ‖u0‖ ≤ A)
    (hu : ‖u - u0‖ < (A ^ 20)⁻¹)
    (hvalue : |a * w0 ^ 2 + eval (fun j => u0 j) b * w0 + eval (fun j => u0 j) c| ≤ a_fit * A)
    (hslo : 4 * A ^ (-1 : ℝ) ≤ |2 * a * w0 + eval (fun j => u0 j) b|)
    (hroot : a * φ ^ 2 + eval (fun j => u j) b * φ + eval (fun j => u j) c = 0) :
    19 / 20 * |2 * a * w0 + eval (fun j => u0 j) b| ≤ |2 * a * φ + eval (fun j => u j) b| ∧
      |2 * a * φ + eval (fun j => u j) b| ≤ 21 / 20 * |2 * a * w0 + eval (fun j => u0 j) b| := by
  have hApos : 0 < A := by linarith
  let σ := 2 * a * w0 + eval (fun j => u0 j) b
  have hσsq : 16 * (1 / A ^ 2) ≤ σ ^ 2 := by
    rw [Real.rpow_neg_one] at hslo
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 4 * A⁻¹) hslo 2
    have he : (4 * A⁻¹) ^ 2 = 16 * (1 / A ^ 2) := by ring
    simpa only [he, sq_abs] using hh
  have herr := stable_root_square_error hA b c hb hc hcoeff hsmall u0 u w0 φ hu0 hu hvalue hroot
  change |(2 * a * φ + eval (fun j => u j) b) ^ 2 - σ ^ 2| ≤ 1 / (2 * A ^ 2) at herr
  have hhalf : 1 / A ^ 2 = 2 * (1 / (2 * A ^ 2)) := by ring
  obtain ⟨hlo, hhi⟩ := abs_le.mp herr
  have hlow : (31 / 32 : ℝ) * σ ^ 2 ≤ (2 * a * φ + eval (fun j => u j) b) ^ 2 := by nlinarith
  have hhigh : (2 * a * φ + eval (fun j => u j) b) ^ 2 ≤ (33 / 32 : ℝ) * σ ^ 2 := by nlinarith
  change 19 / 20 * |σ| ≤ _ ∧ _ ≤ 21 / 20 * |σ|
  constructor
  · by_contra! hh
    nlinarith [sq_abs σ, sq_abs (2 * a * φ + eval (fun j => u j) b),
      abs_nonneg σ, abs_nonneg (2 * a * φ + eval (fun j => u j) b)]
  · by_contra! hh
    nlinarith [sq_abs σ, sq_abs (2 * a * φ + eval (fun j => u j) b),
      abs_nonneg σ, abs_nonneg (2 * a * φ + eval (fun j => u j) b)]

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
