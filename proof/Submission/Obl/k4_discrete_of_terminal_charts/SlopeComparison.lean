import Mathlib

/-!
# The mass comparison for a terminal chart

The slope-volume hypothesis is used on the original trajectory prior.  None of the
sets of geometrically eligible slopes in this file need to be measurable: all bounds
are bounds for outer measure.
-/

namespace Submission.Obl.k4_discrete_of_terminal_charts

open Set MeasureTheory
open scoped ENNReal

abbrev E2 := EuclideanSpace ℝ (Fin 2)
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- Slopes for which some intercept satisfies the geometric chart tests. -/
def eligibleSlopes (P : MvPolynomial (Fin 4) ℝ)
    (D : Matrix (Fin 2) (Fin 2) ℝ) (c u : E2) (t₀ q a K R : ℝ) : Set E3 :=
  {s | ‖s‖ ≤ R ∧ ∃ b : E3, ‖b‖ ≤ R ∧
    (∀ t ∈ Icc t₀ (t₀ + q),
      ‖Matrix.toEuclideanLin (D⁻¹)
        (WithLp.toLp 2 (fun i : Fin 2 => (b + t • s) i.castSucc - c i - t * u i))‖ ≤ K ∧
      |MvPolynomial.eval ![t, (b + t • s) 0, (b + t • s) 1, (b + t • s) 2] P| ≤ K * a) ∧
    ∃ t ∈ Icc t₀ (t₀ + q), K⁻¹ ≤
      |MvPolynomial.eval ![t, (b + t • s) 0, (b + t • s) 1, (b + t • s) 2]
        (MvPolynomial.pderiv (3 : Fin 4) P)|}

/-- The second antecedent of the obligation, with a specified constant. -/
def SlopeVolumeBound (C : ℝ) : Prop :=
  ∀ (P : MvPolynomial (Fin 4) ℝ) (D : Matrix (Fin 2) (Fin 2) ℝ)
    (c u : E2) (t₀ q a K R : ℝ),
    P.totalDegree ≤ 2 → Matrix.det D ≠ 0 → 0 < q → 0 < a → 1 ≤ K → 1 ≤ R →
    volume (eligibleSlopes P D c u t₀ q a K R) ≤
      ENNReal.ofReal (C * K ^ 4 * a * |Matrix.det D| / q ^ 3)

/-- A slope cap and an interval bound control selected incidence mass. -/
theorem incidence_mass_le_of_slope_cap {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (s : α → E3) (H : ℝ≥0∞)
    (hcap : ∀ S : Set E3, ν (s ⁻¹' S) ≤ H * volume S)
    (F : Set (α × ℝ)) (S : Set E3) {t₀ q : ℝ}
    (hF : ∀ p ∈ F, s p.1 ∈ S ∧ p.2 ∈ Icc t₀ (t₀ + q)) :
    (ν.prod volume) F ≤ H * volume S * ENNReal.ofReal q := by
  calc
    (ν.prod volume) F ≤ (ν.prod volume) ((s ⁻¹' S) ×ˢ Icc t₀ (t₀ + q)) :=
      measure_mono hF
    _ ≤ ν (s ⁻¹' S) * volume (Icc t₀ (t₀ + q)) := Measure.prod_prod_le _ _
    _ ≤ (H * volume S) * volume (Icc t₀ (t₀ + q)) := by
      gcongr
      exact hcap S
    _ = H * volume S * ENNReal.ofReal q := by rw [Real.volume_Icc]; congr 2; ring

/-- A measurable slope marginal dominated by Lebesgue measure gives an outer cap. -/
theorem slope_cap_of_map_le {α : Type*} [MeasurableSpace α]
    (ν : Measure α) {s : α → E3} (hs : AEMeasurable s ν) (H : ℝ≥0∞)
    (hcap : ν.map s ≤ H • volume) (S : Set E3) :
    ν (s ⁻¹' S) ≤ H * volume S := by
  calc
    ν (s ⁻¹' S) ≤ ν.map s S := Measure.le_map_apply hs S
    _ ≤ (H • volume) S := hcap S
    _ = H * volume S := by simp

/-- Geometric eligibility bounds the mass of a chart before any conditioning. -/
theorem chart_incidence_mass_le {α : Type*} [MeasurableSpace α]
    {C H : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H) (hvol : SlopeVolumeBound C)
    (ν : Measure α) (s : α → E3)
    (hcap : ∀ S : Set E3, ν (s ⁻¹' S) ≤ ENNReal.ofReal H * volume S)
    (P : MvPolynomial (Fin 4) ℝ) (D : Matrix (Fin 2) (Fin 2) ℝ)
    (c u : E2) {t₀ q a K R : ℝ}
    (hP : P.totalDegree ≤ 2) (hD : Matrix.det D ≠ 0)
    (hq : 0 < q) (ha : 0 < a) (hK : 1 ≤ K) (hR : 1 ≤ R)
    (F : Set (α × ℝ))
    (hF : ∀ p ∈ F, s p.1 ∈ eligibleSlopes P D c u t₀ q a K R ∧
      p.2 ∈ Icc t₀ (t₀ + q)) :
    (ν.prod volume) F ≤
      ENNReal.ofReal (H * C * K ^ 4 * a * |Matrix.det D| / q ^ 2) := by
  calc
    (ν.prod volume) F ≤ ENNReal.ofReal H *
        volume (eligibleSlopes P D c u t₀ q a K R) * ENNReal.ofReal q :=
      incidence_mass_le_of_slope_cap ν s _ hcap F _ hF
    _ ≤ ENNReal.ofReal H *
        ENNReal.ofReal (C * K ^ 4 * a * |Matrix.det D| / q ^ 3) *
          ENNReal.ofReal q := by
      gcongr
      exact hvol P D c u t₀ q a K R hP hD hq ha hK hR
    _ = ENNReal.ofReal (H * C * K ^ 4 * a * |Matrix.det D| / q ^ 2) := by
      rw [← ENNReal.ofReal_mul hH, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp

/-- Cancelling a positive spatial Jacobian against the true chart floor. -/
theorem density_le_of_chart_mass_bounds {n H C K a J q : ℝ} {mass : ℝ≥0∞}
    (hH : 0 ≤ H) (hC : 0 ≤ C) (hK : 0 < K) (ha : 0 ≤ a)
    (hJ : 0 < J) (hq : 0 < q)
    (hfloor : ENNReal.ofReal (n * J * q / K) ≤ mass)
    (hupper : mass ≤ ENNReal.ofReal (H * C * K ^ 4 * a * J / q ^ 2)) :
    n ≤ H * C * K ^ 5 * a / q ^ 3 := by
  have h : n * J * q / K ≤ H * C * K ^ 4 * a * J / q ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hfloor.trans hupper)
  calc
    n = (n * J * q / K) / (J * q / K) := by field_simp
    _ ≤ (H * C * K ^ 4 * a * J / q ^ 2) / (J * q / K) :=
      div_le_div_of_nonneg_right h (by positivity)
    _ = H * C * K ^ 5 * a / q ^ 3 := by field_simp

/-- A true terminal system carrying positive total selected mass contains a chart. -/
theorem nonempty_of_terminal_mass {ι : Type*} [Fintype ι]
    (w mass : ι → ℝ≥0∞) {K : ℝ} (hK : 0 < K)
    (htotal : ENNReal.ofReal K⁻¹ ≤ ∑ i, w i * mass i) : Nonempty ι := by
  classical
  by_contra hi
  let : IsEmpty ι := not_nonempty_iff.mp hi
  have hz : (∑ i, w i * mass i) = 0 := Finset.sum_eq_zero (fun i _ => isEmptyElim i)
  rw [hz, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at htotal
  exact (inv_pos.mpr hK).not_ge htotal

end Submission.Obl.k4_discrete_of_terminal_charts
