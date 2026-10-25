-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/TensorFieldError.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/- Adapted from this LOT tree, o285, session x1022, commit 3118a01b648b6fe31c1ad302109f3ffc3507ef6f,
Submission/Obl/k4_original_interpolated_field_source/Cart/TensorFieldError.lean.
This is the signal-independent interpolation kernel, not the refuted o285 theorem.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, obligation o106 (k4_isotropic_path_improvement), session x0358 (as merged
-- on branch x0352 at commit 1e57792e, file Submission/Obl/k4_isotropic_path_improvement/TensorFieldError.lean;
-- only the namespace and module paths were renamed into o285's Cart namespace.
-- Existing source attributions of that file are preserved below.

import Mathlib
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.TensorField
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.TensorInterpolation

/-!
# Error of the tensor interpolant from one-axis polynomial fits

Paper `tex-06-isotropic.tex`, Section 6, "Cartesian interpolation of the physical field": if
the field is, along each of the needed axis-parallel fibers, within `ε` of a polynomial of
degree at most `D` at its target and at all anchors, then the tensor Lagrange interpolant
`tensorPoly a b c V` of the anchor values approximates the field at the target up to
`3 (1 + Λ)^3 ε`, where `Λ = (D + 1) ((R + A)/δ)^D` bounds the sums of the absolute Lagrange
weights for targets with `|x v| ≤ R`.

* `lag_reproduces`: degree-`D` polynomials are reproduced by the Lagrange weights;
* `abs_sub_lagrange_combination_le`: the one-axis error `(1 + Σ|lag|) ε`;
* `sum_abs_lag_le`: `Σ_i |lag a i t| ≤ (D + 1) ((|t| + A)/δ)^D`;
* `abs_sub_eval_tensorPoly_le`: the three-axis error, through x0352's
  `norm_tensorInterpolation3_error_le` (`TensorInterpolation.lean`, o106 branch x0352).

Fibers: the `x`-fiber through the target `(y, z)`, every `y`-fiber through
`(anchor x, target z)`, every `z`-fiber through `(anchor x, anchor y)`; `f` indexes a target
coordinate by `none` and an anchor by `some`.
-/

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

open MvPolynomial

noncomputable section

variable {D : ℕ}

/-- Lagrange weights reproduce polynomials of degree at most `D`. -/
theorem lag_reproduces (a : Fin (D + 1) → ℝ) (ha : Function.Injective a) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ D) (t : ℝ) :
    p.eval t = ∑ i, lag a i t * p.eval (a i) := by
  classical
  have hdeg : p.degree < ((Finset.univ : Finset (Fin (D + 1))).card : WithBot ℕ) := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hp) (by exact_mod_cast Nat.lt_succ_self D)
  have h := Lagrange.eq_interpolate (s := Finset.univ) (v := a) (f := p)
    (fun i _ j _ hij => ha hij) hdeg
  conv_lhs => rw [h]
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_C, lag_eq_eval_basis, mul_comm]

/-- **One-axis error.**  If `g` is within `ε` of a polynomial of degree at most `D` at the
target `t` and at the anchors, the Lagrange combination of its anchor values misses `g t` by
at most `(1 + Σ |lag a i t|) ε`. -/
theorem abs_sub_lagrange_combination_le (a : Fin (D + 1) → ℝ) (ha : Function.Injective a)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ D) (t gt : ℝ) (g : Fin (D + 1) → ℝ) (ε : ℝ)
    (ht : |gt - p.eval t| ≤ ε) (hg : ∀ i, |g i - p.eval (a i)| ≤ ε) :
    |gt - ∑ i, lag a i t * g i| ≤ (1 + ∑ i, |lag a i t|) * ε := by
  rw [lag_reproduces a ha p hp t] at ht
  have hsplit : gt - ∑ i, lag a i t * g i =
      (gt - ∑ i, lag a i t * p.eval (a i)) + ∑ i, lag a i t * (p.eval (a i) - g i) := by
    have : ∑ i, lag a i t * (p.eval (a i) - g i) =
        ∑ i, lag a i t * p.eval (a i) - ∑ i, lag a i t * g i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    ring
  rw [hsplit]
  calc |(gt - ∑ i, lag a i t * p.eval (a i)) + ∑ i, lag a i t * (p.eval (a i) - g i)|
      ≤ |gt - ∑ i, lag a i t * p.eval (a i)| + |∑ i, lag a i t * (p.eval (a i) - g i)| :=
        abs_add_le _ _
    _ ≤ ε + ∑ i, |lag a i t| * ε := by
        gcongr
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [abs_mul]
        gcongr
        rw [abs_sub_comm]
        exact hg i
    _ = (1 + ∑ i, |lag a i t|) * ε := by rw [← Finset.sum_mul]; ring

/-- The sum of the absolute Lagrange weights. -/
theorem sum_abs_lag_le (a : Fin (D + 1) → ℝ) (A δ : ℝ) (hδ : 0 < δ) (hA : ∀ j, |a j| ≤ A)
    (hsep : ∀ i j, i ≠ j → δ ≤ |a i - a j|) (t : ℝ) :
    ∑ i, |lag a i t| ≤ ((D : ℝ) + 1) * ((|t| + A) / δ) ^ D := by
  calc ∑ i, |lag a i t| ≤ ∑ _i : Fin (D + 1), ((|t| + A) / δ) ^ D :=
        Finset.sum_le_sum fun i _ => abs_lag_le a A δ hδ hA hsep i t
    _ = ((D : ℝ) + 1) * ((|t| + A) / δ) ^ D := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Three-axis error of the tensor interpolant.** -/
theorem abs_sub_eval_tensorPoly_le (a b c : Fin (D + 1) → ℝ) (ha : Function.Injective a)
    (hb : Function.Injective b) (hc : Function.Injective c)
    (A δ R ε : ℝ) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hA : ∀ j, |a j| ≤ A) (hB : ∀ j, |b j| ≤ A) (hC : ∀ j, |c j| ≤ A)
    (hsa : ∀ i j, i ≠ j → δ ≤ |a i - a j|) (hsb : ∀ i j, i ≠ j → δ ≤ |b i - b j|)
    (hsc : ∀ i j, i ≠ j → δ ≤ |c i - c j|)
    (x : Fin 3 → ℝ) (hR : ∀ v, |x v| ≤ R)
    (f : Option (Fin (D + 1)) → Option (Fin (D + 1)) → Option (Fin (D + 1)) → ℝ)
    (hx : ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧ |f none none none - p.eval (x 0)| ≤ ε ∧
      ∀ i, |f (some i) none none - p.eval (a i)| ≤ ε)
    (hy : ∀ i, ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧
      |f (some i) none none - p.eval (x 1)| ≤ ε ∧
      ∀ j, |f (some i) (some j) none - p.eval (b j)| ≤ ε)
    (hz : ∀ i j, ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧
      |f (some i) (some j) none - p.eval (x 2)| ≤ ε ∧
      ∀ k, |f (some i) (some j) (some k) - p.eval (c k)| ≤ ε) :
    |f none none none - eval x (tensorPoly a b c (fun i j k => f (some i) (some j) (some k)))| ≤
      3 * (1 + ((D : ℝ) + 1) * ((R + A) / δ) ^ D) ^ 3 * ε := by
  set Λ := ((D : ℝ) + 1) * ((R + A) / δ) ^ D with hΛ
  have hR0 : 0 ≤ R := (abs_nonneg (x 0)).trans (hR 0)
  have hA0 : 0 ≤ A := (abs_nonneg (a 0)).trans (hA 0)
  have hΛ0 : 0 ≤ Λ := by positivity
  -- the sums of absolute weights at the target
  have hsum : ∀ (n : Fin (D + 1) → ℝ), (∀ j, |n j| ≤ A) →
      (∀ i j, i ≠ j → δ ≤ |n i - n j|) → ∀ v, ∑ i, |lag n i (x v)| ≤ Λ := by
    intro n hn hsn v
    refine (sum_abs_lag_le n A δ hδ hn hsn (x v)).trans ?_
    rw [hΛ]
    gcongr
    exact hR v
  -- the three one-axis errors
  obtain ⟨p₀, hp₀, hp₀t, hp₀a⟩ := hx
  have h₀ := abs_sub_lagrange_combination_le a ha p₀ hp₀ (x 0) (f none none none)
    (fun i => f (some i) none none) ε hp₀t hp₀a
  have h₁ : ∀ i, |f (some i) none none - ∑ j, lag b j (x 1) * f (some i) (some j) none| ≤
      (1 + Λ) * ε := by
    intro i
    obtain ⟨p, hp, hpt, hpa⟩ := hy i
    refine (abs_sub_lagrange_combination_le b hb p hp (x 1) _ _ ε hpt hpa).trans ?_
    gcongr
    exact hsum b hB hsb 1
  have h₂ : ∀ i j, |f (some i) (some j) none -
      ∑ k, lag c k (x 2) * f (some i) (some j) (some k)| ≤ (1 + Λ) * ε := by
    intro i j
    obtain ⟨p, hp, hpt, hpa⟩ := hz i j
    refine (abs_sub_lagrange_combination_le c hc p hp (x 2) _ _ ε hpt hpa).trans ?_
    gcongr
    exact hsum c hC hsc 2
  have h₀' : |f none none none - ∑ i, lag a i (x 0) * f (some i) none none| ≤ (1 + Λ) * ε :=
    h₀.trans (by gcongr; exact hsum a hA hsa 0)
  -- telescoping through the intermediate vertices (x0352's tensor stability lemma)
  have htel := norm_tensorInterpolation3_error_le (E := ℝ) (fun i => lag a i (x 0))
    (fun j => lag b j (x 1)) (fun k => lag c k (x 2)) f ((1 + Λ) * ε) ((1 + Λ) * ε)
    ((1 + Λ) * ε) (by simpa [Real.norm_eq_abs, smul_eq_mul] using h₀')
    (fun i => by simpa [Real.norm_eq_abs, smul_eq_mul] using h₁ i)
    (fun i j => by simpa [Real.norm_eq_abs, smul_eq_mul] using h₂ i j)
  have hinterp : tensorInterpolation3 (fun i => lag a i (x 0)) (fun j => lag b j (x 1))
      (fun k => lag c k (x 2)) (fun i j k => f (some i) (some j) (some k)) =
      eval x (tensorPoly a b c (fun i j k => f (some i) (some j) (some k))) := by
    rw [eval_tensorPoly, tensorInterpolation3]
    simp only [smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hinterp, Real.norm_eq_abs] at htel
  refine htel.trans ?_
  have hsa' := hsum a hA hsa 0
  have hsb' := hsum b hB hsb 1
  have hε' : 0 ≤ (1 + Λ) * ε := by positivity
  calc (1 + Λ) * ε + (∑ i, |lag a i (x 0)|) * ((1 + Λ) * ε) +
        (∑ i, |lag a i (x 0)|) * (∑ j, |lag b j (x 1)|) * ((1 + Λ) * ε)
      ≤ (1 + Λ) * ε + Λ * ((1 + Λ) * ε) + Λ * Λ * ((1 + Λ) * ε) := by
        gcongr
    _ ≤ 3 * (1 + Λ) ^ 3 * ε := by nlinarith [mul_nonneg hΛ0 hΛ0, mul_nonneg hΛ0 hε]

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
