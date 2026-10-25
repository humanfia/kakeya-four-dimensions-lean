-- Adapted from this LOT tree o194, session x0672, commit 69d09a7b,
-- Submission/Obl/k4_greedy_cover_graph_atlas/CandidateMarginal.lean. Earlier attributions follow.

-- Adapted from this LOT tree, o173, session x0598, commit 6ded8016fe11,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/CandidateMarginal.lean.

import Submission.Obl.k4_clean_cover_graph_atlas.HiddenBins
import Submission.Lib.K4ListedExceptions.ObservationCaps
import Submission.Obl.k4_clean_cover_graph_atlas.Interface
import Submission.Obl.k4_quadratic_slope_volume.PolynomialSlices
import Submission.Lib.K4QuadraticSheets.QuadTest

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory Set MvPolynomial

/-- The exact-base support of a regular quadratic hidden fit at hidden bin width `δ`. -/
def polynomialBinSupport {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℝ) (ε β δ : ℝ) :
    Set (EuclideanSpace ℝ (Fin n) × ℤ) :=
  closedBinSupport
    (fun u w => eval (Fin.snoc (fun j : Fin n => u j) w) P)
    (fun u w => eval (Fin.snoc (fun j : Fin n => u j) w) (pderiv (Fin.last n) P)) ε β δ

theorem continuous_eval_snoc {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℝ) :
    Continuous (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      eval (Fin.snoc (fun j : Fin n => p.1 j) p.2) P) := by
  apply P.continuous_eval.comp
  exact (by fun_prop : Continuous (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
    fun j : Fin n => p.1 j)).finSnoc continuous_snd

theorem measurableSet_polynomialBinSupport {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℝ) (ε β δ : ℝ) :
    MeasurableSet (polynomialBinSupport P ε β δ) :=
  measurableSet_closedBinSupport (continuous_eval_snoc P)
    (continuous_eval_snoc (pderiv (Fin.last n) P)) ε β δ

/-- A quadratic test with a regular hidden derivative has uniformly bounded vertical
observation fibers, independently of its coefficients. -/
theorem count_polynomialBinSupport {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℝ)
    (hP : P.totalDegree ≤ 2) {ε β δ : ℝ} (hε : 0 ≤ ε) (hβ : 0 < β) (hδ : 0 < δ)
    (u : EuclideanSpace ℝ (Fin n)) :
    (Measure.count : Measure ℤ) {b | (u, b) ∈ polynomialBinSupport P ε β δ} ≤
      ENNReal.ofReal (16 * (1 + ε / (β * δ))) := by
  classical
  let q := Submission.Obl.k4_quadratic_slope_volume.coordinatePolynomialHom
    (Fin.snoc (fun j : Fin n => u j) 0) (Fin.last n) P
  have hq : q.natDegree ≤ 2 := by
    apply le_trans (Submission.Obl.k4_quadratic_slope_volume.natDegree_eval₂_affine_le P _ ?_) hP
    intro j
    split_ifs <;> simp
  have hvalue (w : ℝ) : q.eval w = eval (Fin.snoc (fun j : Fin n => u j) w) P := by
    rw [Submission.Obl.k4_quadratic_slope_volume.eval_coordinatePolynomialHom,
      ← Submission.Lib.K4QuadraticSheets.snoc_eq_update]
  have hslope (w : ℝ) : q.derivative.eval w =
      eval (Fin.snoc (fun j : Fin n => u j) w) (pderiv (Fin.last n) P) := by
    rw [Submission.Obl.k4_quadratic_slope_volume.derivative_coordinatePolynomialHom,
      Submission.Obl.k4_quadratic_slope_volume.eval_coordinatePolynomialHom,
      ← Submission.Lib.K4QuadraticSheets.snoc_eq_update]
  obtain ⟨hfin, hcard⟩ := regularClosedBins_finite_card q hq hε hβ hδ
  have heq : {b | (u, b) ∈ polynomialBinSupport P ε β δ} = regularClosedBins q ε β δ := by
    ext b
    simp only [polynomialBinSupport, closedBinSupport, regularClosedBins, mem_ofPred_eq,
      hvalue, hslope]
  rw [heq, Measure.count_apply_finite _ hfin]
  have hc := ENNReal.ofReal_le_ofReal hcard
  simpa only [ncard_eq_toFinset_card _ hfin, ENNReal.ofReal_natCast] using hc

/-- Every counted regular fit lies in the measurable closed-bin support. -/
theorem mem_polynomialBinSupport {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℝ)
    {ε β δ w : ℝ} (hδ : 0 < δ) (u : EuclideanSpace ℝ (Fin n))
    (hv : |eval (Fin.snoc (fun j : Fin n => u j) w) P| ≤ ε)
    (hs : β ≤ |eval (Fin.snoc (fun j : Fin n => u j) w) (pderiv (Fin.last n) P)|) :
    (u, ⌊w / δ⌋) ∈ polynomialBinSupport P ε β δ := by
  refine ⟨w, ⟨?_, ?_⟩, hv, hs⟩
  · have hh := (le_div_iff₀ hδ).mp (Int.floor_le (w / δ))
    nlinarith
  · have hh := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (w / δ))
    nlinarith

/-- The count at the natural candidate scales costs only the square of the slack. -/
theorem count_candidate_support (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    {δ B U : ℝ} (hδ : 0 < δ) (hB : 0 < B) (hU : 0 < U)
    (u : EuclideanSpace ℝ (Fin 3)) :
    (Measure.count : Measure ℤ) {b | (u, b) ∈ polynomialBinSupport P (U * δ) (B / U) (δ / B)} ≤
      ENNReal.ofReal (16 * (1 + U ^ 2)) := by
  have hh := count_polynomialBinSupport P hP (mul_nonneg hU.le hδ.le)
    (div_pos hB hU) (div_pos hδ hB) u
  have heq : U * δ / (B / U * (δ / B)) = U ^ 2 := by
    field_simp
    <;> ring
  simpa only [heq] using hh

/-- The candidate incidence observation has exactly the support used in the fiber count. -/
theorem original_obs_mem_candidate_support (P : MvPolynomial (Fin 4) ℝ)
    {δ B U : ℝ} (hδ : 0 < δ) (hB : 0 < B) (p : (ℕ × (Fin 6 → ℝ)) × ℝ)
    (hv : |eval (x p.1 p.2) P| ≤ U * δ)
    (hs : B / U ≤ |eval (x p.1 p.2) (pderiv (3 : Fin 4) P)|) :
    obs B δ p ∈ polynomialBinSupport P (U * δ) (B / U) (δ / B) := by
  have heq : Fin.snoc (fun j : Fin 3 => (obs B δ p).1 j) ((x p.1 p.2) 3) = x p.1 p.2 := by
    ext j
    fin_cases j <;> simp [obs, x, Submission.Lib.K4XInterface.gobs,
      Submission.Lib.K4XInterface.gx]
  have hm := mem_polynomialBinSupport (n := 3) P
    (ε := U * δ) (β := B / U) (w := (x p.1 p.2) 3) (div_pos hδ hB) (obs B δ p).1
    (by rw [heq]; exact hv) (by rw [heq]; exact hs)
  have hbin : (x p.1 p.2) 3 / (δ / B) = B * (x p.1 p.2) 3 / δ := by
    field_simp
    <;> ring
  simpa only [hbin, obs, Submission.Lib.K4XInterface.gobs] using hm

/-- A truncated candidate observation density therefore has a bounded exact-base marginal. -/
theorem candidate_base_marginal (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    {δ B U : ℝ} (hδ : 0 < δ) (hB : 0 < B) (hU : 0 < U)
    (ν : Measure (EuclideanSpace ℝ (Fin 3) × ℤ)) (H : ENNReal)
    (hν : ν ≤ H • (volume.prod Measure.count))
    (hsupport : ν (polynomialBinSupport P (U * δ) (B / U) (δ / B))ᶜ = 0)
    (A : Set (EuclideanSpace ℝ (Fin 3))) (hA : MeasurableSet A) :
    ν (A ×ˢ univ) ≤ (H * ENNReal.ofReal (16 * (1 + U ^ 2))) * volume A := by
  simpa only [Set.prod_univ] using
    Submission.Lib.K4ListedExceptions.supported_product_first_marginal_bound
      ν volume Measure.count _ (measurableSet_polynomialBinSupport P _ _ _) hsupport
      hν (count_candidate_support P hP hδ hB hU) A hA

end Submission.Obl.k4_clean_cover_graph_atlas
