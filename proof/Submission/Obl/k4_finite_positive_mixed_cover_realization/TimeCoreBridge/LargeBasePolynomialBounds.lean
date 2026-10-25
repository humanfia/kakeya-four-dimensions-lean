-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/LargeBasePolynomialBounds.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.OriginalPolynomialBounds
import Submission.Lib.K4CubicTests.FinitePolynomialBounds
import Submission.Obl.k4_quadratic_atlas_normalization.RefinementFormat

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MeasureTheory Set MvPolynomial

/-- Original-law polynomial coefficient bounds on a larger base ball. Rescaling
uses the exact radius cubed in the cap, and preserves the original source mass. -/
theorem exists_original_law_large_ball_coefficient_bound (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 3) ℝ), P.totalDegree ≤ D →
      ∀ (X : Type*) [MeasurableSpace X] (μ : Measure X)
        (base : X → EuclideanSpace ℝ (Fin 3)) (H q V S : ℝ),
        Measurable base → 0 < H → 0 < q → q ≤ 1 → 0 ≤ V → 1 ≤ S →
        μ.map base ≤ ENNReal.ofReal H • volume →
        ENNReal.ofReal (H * q) ≤ μ univ →
        (∀ᵐ x ∂μ, ‖base x‖ ≤ S / 8 ∧ |eval (fun i => base x i) P| ≤ V) →
        ∀ d, |P.coeff d| ≤ C * (32 * ((D : ℝ) + 1) / (q / S ^ 3)) ^ (3 * D) * V := by
  obtain ⟨C₁, hC₁, hsmall⟩ := exists_original_law_polynomial_coefficient_bound D
  obtain ⟨C₂, hC₂, hcoeff⟩ :=
    Submission.Lib.K4PolynomialRemezThree.exists_coefficient_bound_on_small_ball D
  refine ⟨C₂ * ((D + 1 : ℕ) : ℝ) * 3 ^ D * C₁, by positivity, ?_⟩
  intro P hP X inst μ base H q V S hb hH hq hq1 hV hS hcap hmass hpoint
  have hS0 : 0 < S := by linarith
  let Z : X → EuclideanSpace ℝ (Fin 3) := fun x => S⁻¹ • base x
  let f : Fin 3 → MvPolynomial (Fin 3) ℝ := fun i => C S * MvPolynomial.X i
  let Q := aeval f P
  have hQ : Q.totalDegree ≤ D := by
    apply le_trans ?_ hP
    have hh := Submission.Obl.k4_quadratic_atlas_normalization.degree_aeval_le_mul P f 1
      (fun i => (totalDegree_mul _ _).trans (by simp [f]))
    simpa only [one_mul] using hh
  have hev (z : Fin 3 → ℝ) : eval z Q = eval (fun i => S * z i) P := by
    simpa only [Q, aeval_def, algebraMap_eq, Function.comp_def, f, map_mul, eval_C, eval_X]
      using (eval_assoc f z P).symm
  have hZ : Measurable Z := by dsimp only [Z]; fun_prop
  let g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) := fun z => S⁻¹ • z
  have hg : Measurable g := by dsimp only [g]; fun_prop
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin 3))).map g =
      ENNReal.ofReal (S ^ 3) • volume := by
    rw [show g = fun z : EuclideanSpace ℝ (Fin 3) => S⁻¹ • z from rfl,
      Measure.map_addHaar_smul volume (inv_ne_zero hS0.ne')]
    simp only [finrank_euclideanSpace_fin, inv_pow, inv_inv,
      abs_of_nonneg (pow_nonneg hS0.le 3)]
  have hZcap : μ.map Z ≤ ENNReal.ofReal (H * S ^ 3) • volume := by
    change μ.map (g ∘ base) ≤ _
    rw [← Measure.map_map hg hb]
    calc
      _ ≤ (ENNReal.ofReal H • (volume : Measure (EuclideanSpace ℝ (Fin 3)))).map g :=
        Measure.map_mono hcap hg
      _ = ENNReal.ofReal H • (volume : Measure (EuclideanSpace ℝ (Fin 3))).map g :=
        Measure.map_smul _ hg.aemeasurable
      _ = _ := by rw [hvol, smul_smul, ← ENNReal.ofReal_mul hH.le]
  have hqS : 0 < q / S ^ 3 := by positivity
  have hqS1 : q / S ^ 3 ≤ 1 := (div_le_one (by positivity)).mpr
    (hq1.trans (one_le_pow₀ hS))
  have hmass' : ENNReal.ofReal ((H * S ^ 3) * (q / S ^ 3)) ≤ μ univ := by
    convert hmass using 1
    congr 1
    field_simp
  have hpoint' : ∀ᵐ x ∂μ, ‖Z x‖ ≤ 1 / 8 ∧ |eval (fun i => Z x i) Q| ≤ V := by
    filter_upwards [hpoint] with x hx
    constructor
    · dsimp only [Z]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hS0.le)]
      calc
        _ ≤ S⁻¹ * (S / 8) := mul_le_mul_of_nonneg_left hx.1 (by positivity)
        _ = 1 / 8 := by field_simp
    · rw [hev]
      have he : (fun i => S * Z x i) = fun i => base x i := by
        funext i
        simp only [Z, PiLp.smul_apply, smul_eq_mul]
        field_simp
      rw [he]
      exact hx.2
  let K := C₁ * (32 * ((D : ℝ) + 1) / (q / S ^ 3)) ^ (3 * D) * V
  have hK0 : 0 ≤ K := by dsimp only [K]; positivity
  have hQcoeff : ∀ d, |Q.coeff d| ≤ K :=
    hsmall Q hQ X μ Z (H * S ^ 3) (q / S ^ 3) V hZ (by positivity) hqS hqS1 hV
      hZcap hmass' hpoint'
  have hPbound (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ ≤ 1 / 8) :
      |eval (fun i => x i) P| ≤ ((D + 1 : ℕ) : ℝ) * 3 ^ D * K := by
    let z : Fin 3 → ℝ := fun i => x i / S
    have hz : ∀ i, |z i| ≤ 1 := by
      intro i
      dsimp only [z]
      rw [abs_div, abs_of_pos hS0]
      apply (div_le_one hS0).mpr
      have hh := PiLp.norm_apply_le x i
      rw [Real.norm_eq_abs] at hh
      exact hh.trans (hx.trans (by linarith))
    have hh := Submission.Lib.K4CubicTests.finite_polynomial_eval_abs_le Q D hQ 1 K
      (by norm_num) hK0 hQcoeff z hz
    have he : eval z Q = eval (fun i => x i) P := by
      rw [hev]
      apply congrArg (fun z : Fin 3 → ℝ => eval z P)
      funext i
      dsimp only [z]
      field_simp
    rw [he] at hh
    norm_num at hh
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  intro d
  have hh := hcoeff P hP (((D + 1 : ℕ) : ℝ) * 3 ^ D * K) (by positivity) hPbound d
  dsimp only [K] at hh
  convert hh using 1 <;> ring

/-- Discriminant control in the whole old moving frame. The base may have radius
`S/8`; the radius cost is explicit and does not involve any new subbox mass floor. -/
theorem exists_original_law_large_ball_discriminant_coefficient_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 4) ℝ), P.totalDegree ≤ 2 →
      ∀ (X : Type*) [MeasurableSpace X] (μ : Measure X)
        (base : X → EuclideanSpace ℝ (Fin 3)) (hidden : X → ℝ)
        (H q K a S : ℝ),
        Measurable base → 0 < H → 0 < q → q ≤ 1 → 2 ≤ K → 0 < a → 1 ≤ S →
        μ.map base ≤ ENNReal.ofReal H • volume →
        ENNReal.ofReal (H * q) ≤ μ univ →
        |Submission.Obl.k4_quadratic_atlas_normalization.curvature P (Fin.last 3)| ≤ K / a →
        (∀ᵐ x ∂μ, ‖base x‖ ≤ S / 8 ∧
          |eval (Fin.snoc (fun i => base x i) (hidden x)) P| ≤ K * a ∧
          |eval (Fin.snoc (fun i => base x i) (hidden x)) (pderiv (Fin.last 3) P)| ≤ K) →
        ∀ d, |(Submission.Obl.k4_stable_native_signal_oscillation.baseDiscriminant P).coeff d| ≤
          C * (96 / (q / S ^ 3)) ^ 6 * K ^ 4 := by
  obtain ⟨C, hC, hbound⟩ := exists_original_law_large_ball_coefficient_bound 2
  refine ⟨C, hC, ?_⟩
  intro P hP X inst μ base hidden H q K a S hb hH hq hq1 hK ha hS hcap hmass hcurv hpoint
  have hpoly := Submission.Obl.k4_stable_native_signal_oscillation.baseDiscriminant_degree P hP
  have hpointD : ∀ᵐ x ∂μ, ‖base x‖ ≤ S / 8 ∧
      |eval (fun i => base x i)
        (Submission.Obl.k4_stable_native_signal_oscillation.baseDiscriminant P)| ≤ K ^ 4 := by
    filter_upwards [hpoint] with x hx
    refine ⟨hx.1, ?_⟩
    rw [Submission.Obl.k4_stable_native_signal_oscillation.eval_baseDiscriminant
      P hP (fun i => base x i) (hidden x)]
    exact Submission.Obl.k4_stable_native_signal_oscillation.discriminant_bound
      P _ _ hK ha hcurv hx.2.1 hx.2.2
  have hh := hbound _ hpoly X μ base H q (K ^ 4) S hb hH hq hq1 (by positivity) hS hcap hmass hpointD
  norm_num at hh
  exact hh

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
