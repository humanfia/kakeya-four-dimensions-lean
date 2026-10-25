-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.ObservationIntercept, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/ObservationIntercept.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/ObservationIntercept.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.DirectPackaging
import Submission.Obl.k4_polynomial_variation_tube.LineVariation

/-!
# Intercepts are continuous at the fine observation

Let `F = R_b - P` with `P` depending on the base coordinates only, and suppose every retained
trajectory `l` keeps `F` within `εfit` of its own intercept `c l` throughout the block.  Two
points that differ only in the hidden coordinate differ in `R_b` by at most the hidden distance
times the larger of the two hidden derivatives: along a hidden segment `R_b` is a quadratic `q`,
and `q a - q b = (a - b) (q' a + q' b) / 2` exactly.  Two incidences with the same observation
at width `a` (same time and base position, same hidden bin of width `a / B`) therefore have own
intercepts within `2 εfit + κ a`, using the chart's hidden-derivative bound `κ B` at both.

So every incidence observed in the same fine cell as an incidence of an intercept group belongs
to a slightly enlarged group: group mass can be read off the observation law, with no count of
groups.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad

open MvPolynomial

noncomputable section

/-- The two-point identity for quadratics. -/
lemma quadratic_two_point (q : Polynomial ℝ) (hq : q.natDegree ≤ 2) (a b : ℝ) :
    q.eval a - q.eval b = (a - b) * (q.derivative.eval a + q.derivative.eval b) / 2 := by
  have hd : q.derivative.natDegree ≤ 1 := by
    have := Polynomial.natDegree_derivative_le q
    omega
  have he : ∀ s, q.eval s = q.coeff 0 + q.coeff 1 * s + q.coeff 2 * s ^ 2 := by
    intro s
    rw [Polynomial.eval_eq_sum_range' (n := 3) (by omega)]
    simp [Finset.sum_range_succ]
  have hde : ∀ s, q.derivative.eval s = q.coeff 1 + 2 * q.coeff 2 * s := by
    intro s
    rw [Polynomial.eval_eq_sum_range' (n := 2) (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Polynomial.coeff_derivative]
    push_cast
    ring
  rw [he, he, hde, hde]
  ring

/-- The hidden line through `z'`, as a base point and a direction in `EuclideanSpace`. -/
def hiddenBase (z' : Fin 4 → ℝ) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 (Function.update z' 3 0)

/-- The hidden unit direction. -/
def hiddenDir : EuclideanSpace ℝ (Fin 4) := WithLp.toLp 2 (Pi.single (3 : Fin 4) (1 : ℝ))

lemma hidden_line_eq (z' : Fin 4 → ℝ) (s : ℝ) :
    (fun j => (hiddenBase z' + s • hiddenDir) j) = Function.update z' 3 s := by
  funext i
  by_cases hi : i = 3
  · subst hi; simp [hiddenBase, hiddenDir]
  · simp [hiddenBase, hiddenDir, hi]

/-- **Hidden mean value bound for quadratics.** -/
lemma abs_eval_sub_le_of_hidden {Rb : MvPolynomial (Fin 4) ℝ} (hR : Rb.totalDegree ≤ 2)
    (z z' : Fin 4 → ℝ) (hzz : ∀ i : Fin 4, i ≠ 3 → z i = z' i) {D : ℝ}
    (hD : |MvPolynomial.eval z (pderiv 3 Rb)| ≤ D)
    (hD' : |MvPolynomial.eval z' (pderiv 3 Rb)| ≤ D) :
    |MvPolynomial.eval z Rb - MvPolynomial.eval z' Rb| ≤ D * |z 3 - z' 3| := by
  set q := Submission.Obl.k4_polynomial_variation_tube.lineRestrict Rb (hiddenBase z') hiddenDir
    with hqdef
  have hqeval : ∀ s, q.eval s = MvPolynomial.eval (Function.update z' 3 s) Rb := by
    intro s
    rw [hqdef, Submission.Obl.k4_polynomial_variation_tube.eval_lineRestrict, hidden_line_eq]
  have hqdeg : q.natDegree ≤ 2 :=
    (Submission.Obl.k4_polynomial_variation_tube.natDegree_lineRestrict_le _ _ _).trans hR
  have hqder : ∀ s, q.derivative.eval s =
      MvPolynomial.eval (Function.update z' 3 s) (pderiv 3 Rb) := by
    intro s
    set e : Fin 4 → ℝ := Pi.single (3 : Fin 4) (1 : ℝ) with he
    have hcurve : ∀ i, HasDerivAt (fun u => Function.update z' 3 u i) (e i) s := by
      intro i
      by_cases hi : i = 3
      · subst hi; simpa [he] using hasDerivAt_id' s
      · simpa [Function.update_of_ne hi, he, Pi.single_apply, hi] using hasDerivAt_const s (z' i)
    have h2 := Submission.Lib.K4CubicTests.hasDerivAt_eval_finite_polynomial_curve Rb
      (fun u => Function.update z' 3 u) e s hcurve
    have h1 := q.hasDerivAt s
    have heq : (fun u => q.eval u) = fun u => MvPolynomial.eval (Function.update z' 3 u) Rb := by
      funext u; exact hqeval u
    rw [heq] at h1
    rw [h1.unique h2]
    simp [he, Pi.single_apply, Finset.sum_ite_eq']
  have hz : z = Function.update z' 3 (z 3) := by
    funext i
    by_cases hi : i = 3
    · subst hi; simp
    · simp [Function.update_of_ne hi, hzz i hi]
  have hz' : z' = Function.update z' 3 (z' 3) := by simp
  have key := quadratic_two_point q hqdeg (z 3) (z' 3)
  rw [hqeval, hqeval, ← hz, ← hz', hqder, hqder, ← hz, ← hz'] at key
  rw [key, abs_div, abs_mul, abs_two]
  have hsum : |MvPolynomial.eval z (pderiv 3 Rb) + MvPolynomial.eval z' (pderiv 3 Rb)| ≤ 2 * D :=
    (abs_add_le _ _).trans (by linarith)
  have hab : 0 ≤ |z 3 - z' 3| := abs_nonneg _
  calc |z 3 - z' 3| * |MvPolynomial.eval z (pderiv 3 Rb) + MvPolynomial.eval z' (pderiv 3 Rb)| / 2
      ≤ |z 3 - z' 3| * (2 * D) / 2 := by gcongr
    _ = D * |z 3 - z' 3| := by ring

/-- **Intercept continuity at the fine observation.**  Two points of retained trajectories of
the block, with equal base coordinates and hidden coordinates within `η`, have own intercepts
within `2 εfit + κ B η`. -/
theorem intercept_close_of_same_base {Rb : MvPolynomial (Fin 4) ℝ} (hR : Rb.totalDegree ≤ 2)
    (P : MvPolynomial (Fin 3) ℝ) (cpt : Ln → ℝ) {εfit κ Bv η : ℝ} {l l' : Ln} {t t' : ℝ}
    (hfit : |MvPolynomial.eval (xp l t) Rb - MvPolynomial.eval (fun i => xp l t i.castSucc) P -
      cpt l| ≤ εfit)
    (hfit' : |MvPolynomial.eval (xp l' t') Rb -
      MvPolynomial.eval (fun i => xp l' t' i.castSucc) P - cpt l'| ≤ εfit)
    (hbase : ∀ i : Fin 3, xp l t i.castSucc = xp l' t' i.castSucc)
    (hhidden : |xp l t 3 - xp l' t' 3| ≤ η)
    (hder : |MvPolynomial.eval (xp l t) (pderiv 3 Rb)| ≤ κ * Bv)
    (hder' : |MvPolynomial.eval (xp l' t') (pderiv 3 Rb)| ≤ κ * Bv) (hκB : 0 ≤ κ * Bv) :
    |cpt l - cpt l'| ≤ 2 * εfit + κ * Bv * η := by
  have hzz : ∀ i : Fin 4, i ≠ 3 → xp l t i = xp l' t' i := by
    intro i hi
    have : i = (⟨i.val, by omega⟩ : Fin 3).castSucc := by
      ext; simp
    rw [this]
    exact hbase _
  have hP : MvPolynomial.eval (fun i => xp l t i.castSucc) P =
      MvPolynomial.eval (fun i => xp l' t' i.castSucc) P := by
    rw [show (fun i : Fin 3 => xp l t i.castSucc) = (fun i => xp l' t' i.castSucc) from
      funext hbase]
  have hRdiff := abs_eval_sub_le_of_hidden hR (xp l t) (xp l' t') hzz hder hder'
  have hRdiff' : |MvPolynomial.eval (xp l t) Rb - MvPolynomial.eval (xp l' t') Rb| ≤
      κ * Bv * η :=
    hRdiff.trans (mul_le_mul_of_nonneg_left hhidden hκB)
  rw [hP] at hfit
  calc |cpt l - cpt l'|
      = |(MvPolynomial.eval (xp l' t') Rb - MvPolynomial.eval (fun i => xp l' t' i.castSucc) P -
            cpt l') - (MvPolynomial.eval (xp l t) Rb -
            MvPolynomial.eval (fun i => xp l' t' i.castSucc) P - cpt l) +
          (MvPolynomial.eval (xp l t) Rb - MvPolynomial.eval (xp l' t') Rb)| := by ring_nf
    _ ≤ εfit + εfit + κ * Bv * η := by
        refine (abs_add_le _ _).trans ?_
        refine add_le_add ((abs_sub _ _).trans (add_le_add hfit' hfit)) hRdiff'
    _ = 2 * εfit + κ * Bv * η := by ring

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad
