import Submission.Obl.k4_scalar_guarded_tangent_preparation.GraphNorm
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.MassBounds

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open MeasureTheory Set
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction
open scoped ENNReal

/-- The current restricted packet obeys the original pure-density cap.
Only its numerator is restricted; all original densities stay fixed. -/
theorem current_packet_base_cap
    {μ ρ : Measure (Coeff × ℝ)} (hρ : ρ ≤ μ)
    {g : (Fin 2 → ℝ) × ℤ → ℝ≥0∞} (hg : Measurable g)
    {a : ℝ} (ha : 0 < a)
    (hmap : μ.map (obsL a) = (volume.prod Measure.count).withDensity g)
    {P : MvPolynomial (Fin 2) ℝ} (hP : P.totalDegree ≤ 2)
    {A : Set Coeff} {t₀ q u v w Λ K : ℝ} (hΛ : 0 ≤ Λ)
    (hconf : ∀ l ∈ A, ∀ t ∈ Icc t₀ (t₀ + q),
      |spatial l t - (u + v * t)| ≤ w ∧
      |hidden l t - MvPolynomial.eval ![t, spatial l t] P| ≤ Λ * a)
    (hval : ∀ l ∈ A, ∀ t ∈ Icc t₀ (t₀ + q),
      |MvPolynomial.eval ![t, spatial l t] P| ≤ K)
    (θ : ℝ≥0∞) (hhigh : ρ {p | θ < g (obsL a p)} = 0) :
    ρ (A ×ˢ Icc t₀ (t₀ + q)) ≤
      θ * (ENNReal.ofReal (2 * Λ + 3) * volume (graphGoodRegion P t₀ q u v w K)) := by
  calc
    ρ (A ×ˢ Icc t₀ (t₀ + q)) =
        ρ ((A ×ˢ Icc t₀ (t₀ + q)) \ {p | θ < g (obsL a p)}) :=
      (measure_sdiff_null hhigh).symm
    _ ≤ μ ((A ×ˢ Icc t₀ (t₀ + q)) \ {p | θ < g (obsL a p)}) := hρ _
    _ ≤ _ := thin_packet_diff_le hg ha hmap (isQuad2_eval P hP) hΛ hconf hval θ

/-- On the whole original time block, a scalar trajectory with bounded
coefficients has bounded hidden coordinate. -/
theorem hidden_bound_on_unit_interval {l : Coeff} {K t : ℝ}
    (_hK : 0 ≤ K) (hl : ∀ e, |l.2 e| ≤ K) (ht : t ∈ Icc (0 : ℝ) 1) :
    |hidden l t| ≤ 3 * K := by
  have h1 : |t * l.2 3| ≤ K := by
    rw [abs_mul, abs_of_nonneg ht.1]
    exact (mul_le_mul ht.2 (hl 3) (abs_nonneg _) (by norm_num)).trans_eq (one_mul K)
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  have h2 : |t ^ 2 * l.2 4| ≤ K := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg t)]
    exact (mul_le_mul ht2 (hl 4) (abs_nonneg _) (by norm_num)).trans_eq (one_mul K)
  unfold Submission.Obl.k4_scalar_terminal_chart_packet_extraction.hidden
  calc
    |l.2 2 + t * l.2 3 + t ^ 2 * l.2 4| ≤
        |l.2 2| + |t * l.2 3| + |t ^ 2 * l.2 4| := abs_add_three _ _ _
    _ ≤ 3 * K := by linarith [hl 2]

/-- Whole-block fitting and the unchanged coefficient bounds give the
bounded values used in quadratic graph comparison. -/
theorem graph_value_bound_of_fit {l : Coeff} {P : MvPolynomial (Fin 2) ℝ}
    {K a Λ t : ℝ} (hK : 0 ≤ K) (hl : ∀ e, |l.2 e| ≤ K)
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hfit : |hidden l t - MvPolynomial.eval ![t, spatial l t] P| ≤ Λ * a) :
    |MvPolynomial.eval ![t, spatial l t] P| ≤ 3 * K + Λ * a := by
  have hhidden := hidden_bound_on_unit_interval hK hl ht
  calc
    |MvPolynomial.eval ![t, spatial l t] P| ≤
        |hidden l t| + |hidden l t - MvPolynomial.eval ![t, spatial l t] P| := by
      calc
        |MvPolynomial.eval ![t, spatial l t] P| =
            |hidden l t - (hidden l t - MvPolynomial.eval ![t, spatial l t] P)| := by
          congr 1
          ring
        _ ≤ _ := abs_sub _ _
    _ ≤ _ := add_le_add hhidden hfit

/-- A floor on the current packet mass, compared with its original
pure ceiling, supplies the whole-block norm bound. No cap on the earlier
witness measure is inferred from a cap on the current submeasure. -/
theorem graph_norm_of_current_mass
    {μ ρ : Measure (Coeff × ℝ)} (hρ : ρ ≤ μ)
    {g : (Fin 2 → ℝ) × ℤ → ℝ≥0∞} (hg : Measurable g)
    {a : ℝ} (ha : 0 < a)
    (hmap : μ.map (obsL a) = (volume.prod Measure.count).withDensity g)
    {P : MvPolynomial (Fin 2) ℝ} (hP : P.totalDegree ≤ 2)
    {A : Set Coeff} {t₀ q u v w Λ K : ℝ}
    (hK : 1 ≤ K) (hq : 0 < q) (hw : 0 < w) (hwidth : q ≤ K * w) (hΛ : 0 ≤ Λ)
    (hconf : ∀ l ∈ A, ∀ t ∈ Icc t₀ (t₀ + q),
      |spatial l t - (u + v * t)| ≤ w ∧
      |hidden l t - MvPolynomial.eval ![t, spatial l t] P| ≤ Λ * a)
    (hval : ∀ l ∈ A, ∀ t ∈ Icc t₀ (t₀ + q),
      |MvPolynomial.eval ![t, spatial l t] P| ≤ K)
    (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ⊤)
    (hhigh : ρ {p | θ < g (obsL a p)} = 0)
    (hmass : θ * ENNReal.ofReal (2 * Λ + 3) * ENNReal.ofReal ((q * (2 * w)) / K) ≤
      ρ (A ×ˢ Icc t₀ (t₀ + q)))
    {t z : ℝ} (ht : t ∈ Icc t₀ (t₀ + q)) (hz : z ∈ Icc (-2 : ℝ) 2) :
    |MvPolynomial.eval ![t, u + t * v + z * q] P| ≤ 4665600 * K ^ 7 := by
  have hcap := current_packet_base_cap hρ hg ha hmap hP hΛ hconf hval θ hhigh
  have hcount : ENNReal.ofReal (2 * Λ + 3) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hfactor0 : θ * ENNReal.ofReal (2 * Λ + 3) ≠ 0 := mul_ne_zero hθ0 hcount
  have hfactortop : θ * ENNReal.ofReal (2 * Λ + 3) ≠ ⊤ :=
    ENNReal.mul_ne_top hθtop ENNReal.ofReal_ne_top
  have hvolume : ENNReal.ofReal ((q * (2 * w)) / K) ≤
      volume (graphGoodRegion P t₀ q u v w K) := by
    apply (ENNReal.mul_le_mul_iff_left hfactor0 hfactortop).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hmass.trans hcap
  exact graph_norm_on_block hP hK hq hw hwidth hvolume ht hz

end Submission.Obl.k4_scalar_guarded_tangent_preparation
