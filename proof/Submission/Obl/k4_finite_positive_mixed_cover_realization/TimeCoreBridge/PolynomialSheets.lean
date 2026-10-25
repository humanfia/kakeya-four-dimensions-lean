-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/PolynomialSheets.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/PolynomialSheets.lean (namespace renamed).

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.LocalSheets
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.PolynomialRemez
import Submission.Obl.k4_stable_quadratic_hidden_sheets.Sheet

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open Set Metric MvPolynomial

/-- A real polynomial graph on an arbitrary local comparison box. -/
noncomputable def localPolynomialSheet {D : ℕ} (P : MvPolynomial (Fin 3) ℝ)
    (hPD : P.totalDegree ≤ D) (a : Real3) (r : ℝ) (hr : 0 < r) : RealSheet (max 1 D) := by
  let f : Complex3 → ℂ := fun z => eval₂ (algebraMap ℝ ℂ) (fun j => z j) P
  let Q := polynomialGraphRelation (P.map (algebraMap ℝ ℂ))
  have hQ : Q ≠ 0 := polynomialGraphRelation_ne_zero _
  have hQD : Q.totalDegree ≤ max 1 D :=
    (polynomialGraphRelation_degree _).trans
      (max_le_max_left 1 ((totalDegree_map_le _ P).trans hPD))
  have hf : DifferentiableOn ℂ f (ball (emb a) r) :=
    (Submission.Obl.k4_stable_quadratic_hidden_sheets.differentiable_eval₂ P).differentiableOn
  have heq (z : Complex3) (_hz : z ∈ ball (emb a) r) :
      eval (Fin.snoc (fun j : Fin 3 => z j) (f z)) Q = 0 := by
    simp only [Q, polynomialGraphRelation, map_sub, eval_X, Fin.snoc_last,
      MvPolynomial.eval_rename, Function.comp_def, Fin.snoc_castSucc, eval_map, f, sub_self]
  have hreal (x : Real3) (_hx : ‖x - a‖ < r) : (f (emb x)).im = 0 := by
    change (eval₂ (algebraMap ℝ ℂ) (fun j : Fin 3 => (x j : ℂ)) P).im = 0
    rw [Submission.Obl.k4_stable_quadratic_hidden_sheets.eval₂_ofReal]
    rfl
  exact localRealSheet a r hr f Q hQ hQD hf heq hreal

theorem localPolynomialSheet_re {D : ℕ} (P : MvPolynomial (Fin 3) ℝ)
    (hPD : P.totalDegree ≤ D) (a : Real3) (r : ℝ) (hr : 0 < r) (x : Real3) :
    ((localPolynomialSheet P hPD a r hr).f (emb x)).re =
      eval (fun j => (a + (r / 8) • x) j) P := by
  change (eval₂ (algebraMap ℝ ℂ)
    (fun j : Fin 3 => (emb a + ((r / 8 : ℝ) : ℂ) • emb x) j) P).re = _
  rw [← Submission.Obl.k4_algebraic_real_jet_comparison.realEmbedding_line]
  change (eval₂ (algebraMap ℝ ℂ)
    (fun j : Fin 3 => ((a + (r / 8) • x) j : ℂ)) P).re = _
  rw [Submission.Obl.k4_stable_quadratic_hidden_sheets.eval₂_ofReal]
  rfl

noncomputable def quadraticCenterPolynomial (a : ℝ) (b : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ := C (-(2 * a)⁻¹) * b

theorem quadraticCenterPolynomial_degree (a : ℝ) (b : MvPolynomial (Fin 3) ℝ)
    (hb : b.totalDegree ≤ 1) : (quadraticCenterPolynomial a b).totalDegree ≤ 1 :=
  (totalDegree_mul _ b).trans (by simpa only [totalDegree_C, zero_add] using hb)

/-- The high-curvature alternative is the affine center, viewed as a real algebraic sheet. -/
noncomputable def quadraticCenterSheet (a : ℝ) (b : MvPolynomial (Fin 3) ℝ)
    (hb : b.totalDegree ≤ 1) (u0 : Real3) (r : ℝ) (hr : 0 < r) : RealSheet 2 :=
  localPolynomialSheet (quadraticCenterPolynomial a b)
    ((quadraticCenterPolynomial_degree a b hb).trans (by norm_num : 1 ≤ 2)) u0 r hr

theorem quadraticCenterSheet_re (a : ℝ) (b : MvPolynomial (Fin 3) ℝ)
    (hb : b.totalDegree ≤ 1) (u0 : Real3) (r : ℝ) (hr : 0 < r) (x : Real3) :
    ((quadraticCenterSheet a b hb u0 r hr).f (emb x)).re =
      -eval (fun j => (u0 + (r / 8) • x) j) b / (2 * a) := by
  rw [quadraticCenterSheet, localPolynomialSheet_re]
  simp only [quadraticCenterPolynomial, map_mul, eval_C, div_eq_mul_inv]
  ring

/-- A whole-block derivative upper bound controls distance to the affine center. -/
theorem quadraticCenterSheet_fit (a : ℝ) (b : MvPolynomial (Fin 3) ℝ)
    (hb : b.totalDegree ≤ 1) (u0 : Real3) (r : ℝ) (hr : 0 < r) (x : Real3)
    {v U β : ℝ} (hβ : 0 < β) (ha : β ≤ |a|)
    (hder : |2 * a * v + eval (fun j => (u0 + (r / 8) • x) j) b| ≤ U) :
    |v - ((quadraticCenterSheet a b hb u0 r hr).f (emb x)).re| ≤ U / (2 * β) := by
  rw [quadraticCenterSheet_re]
  have hane : a ≠ 0 := abs_pos.mp (hβ.trans_le ha)
  have he : v - -eval (fun j => (u0 + (r / 8) • x) j) b / (2 * a) =
      (2 * a * v + eval (fun j => (u0 + (r / 8) • x) j) b) / (2 * a) := by
    field_simp
    <;> ring
  rw [he, abs_div, abs_mul, abs_two]
  exact div_le_div₀ ((abs_nonneg _).trans hder) hder (by positivity)
    (mul_le_mul_of_nonneg_left ha (by norm_num))

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
