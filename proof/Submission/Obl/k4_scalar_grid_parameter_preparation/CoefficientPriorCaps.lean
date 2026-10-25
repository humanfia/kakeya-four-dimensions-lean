/- Adapted from this LOT tree, o092, session x0317, commit d881f97f20e4.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/CoefficientPriorCaps.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.SnapshotCaps
import Submission.Obl.k4_scalar_coefficient_clustering.Evaluation

/-! Mixed coefficient-bin ceilings for a long-duration original subprior. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped Classical BigOperators ENNReal

def scalarMixedCoefficientTag (ξ ζ : ℝ) (a : Fin 5 → ℝ) : Fin 5 → ℤ :=
  fun e => ⌊a e / (if e.val < 2 then ξ else ζ)⌋

theorem measurable_scalarMixedCoefficientTag (ξ ζ : ℝ) :
    Measurable (scalarMixedCoefficientTag ξ ζ) := by
  apply Measurable.of_eval
  intro e
  exact ((measurable_pi_apply e).div_const _).floor

/-- Use the accepted scalar evaluation and coefficient-code estimates on the two
groups of coefficients. Additional trajectory labels play no role. -/
theorem scalar_mixed_coefficient_position_diameter (a b : Fin 5 → ℝ)
    (ξ ζ t : ℝ) (hξ : 0 < ξ) (hζ : 0 < ζ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hab : scalarMixedCoefficientTag ξ ζ a = scalarMixedCoefficientTag ξ ζ b) :
    dist (a 0 + t * a 1) (b 0 + t * b 1) ≤ 9 * ξ ∧
      dist (a 2 + t * a 3 + t ^ 2 * a 4) (b 2 + t * b 3 + t ^ 2 * b 4) ≤ 9 * ζ := by
  let ay : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![a 0, a 1, 0]
  let by' : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![b 0, b 1, 0]
  let ax : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![a 2, a 3, a 4]
  let bx : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![b 2, b 3, b 4]
  have hcodeY : Submission.Obl.k4_scalar_coefficient_clustering.coefficientCode ξ ay =
      Submission.Obl.k4_scalar_coefficient_clustering.coefficientCode ξ by' := by
    ext e
    fin_cases e
    · simpa [ay, by', Submission.Obl.k4_scalar_coefficient_clustering.coefficientCode,
        scalarMixedCoefficientTag] using congrFun hab 0
    · simpa [ay, by', Submission.Obl.k4_scalar_coefficient_clustering.coefficientCode,
        scalarMixedCoefficientTag] using congrFun hab 1
    · rfl
  have hcodeX : Submission.Obl.k4_scalar_coefficient_clustering.coefficientCode ζ ax =
      Submission.Obl.k4_scalar_coefficient_clustering.coefficientCode ζ bx := by
    ext e
    fin_cases e
    · simpa [ax, bx, Submission.Obl.k4_scalar_coefficient_clustering.coefficientCode,
        scalarMixedCoefficientTag] using congrFun hab 2
    · simpa [ax, bx, Submission.Obl.k4_scalar_coefficient_clustering.coefficientCode,
        scalarMixedCoefficientTag] using congrFun hab 3
    · simpa [ax, bx, Submission.Obl.k4_scalar_coefficient_clustering.coefficientCode,
        scalarMixedCoefficientTag] using congrFun hab 4
  have hy := (Submission.Obl.k4_scalar_coefficient_clustering.quadratic_difference_le
    (a := ay) (b := by') ht).trans
    (mul_le_mul_of_nonneg_left
      (Submission.Obl.k4_scalar_coefficient_clustering.coefficient_dist_of_code_eq hξ hcodeY)
      (by norm_num : (0 : ℝ) ≤ 3))
  have hx := (Submission.Obl.k4_scalar_coefficient_clustering.quadratic_difference_le
    (a := ax) (b := bx) ht).trans
    (mul_le_mul_of_nonneg_left
      (Submission.Obl.k4_scalar_coefficient_clustering.coefficient_dist_of_code_eq hζ hcodeX)
      (by norm_num : (0 : ℝ) ≤ 3))
  constructor
  · simpa [ay, by', Submission.Obl.k4_scalar_coefficient_clustering.quadratic,
      Real.dist_eq, show 3 * (3 * ξ) = 9 * ξ by ring] using hy
  · simpa [ax, bx, Submission.Obl.k4_scalar_coefficient_clustering.quadratic,
      Real.dist_eq, show 3 * (3 * ζ) = 9 * ζ by ring] using hx

/-- Fixed-time trace caps plus the retained duration give a coefficient-bin prior cap.
The same exact original velocity bin occurs on both sides. -/
theorem mixed_coefficient_prior_cap {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] (θ : Measure X) (ρ : Measure (X × ℝ))
    (a : X → Fin 5 → ℝ) (ha : Measurable a)
    (Z : Set (X × ℝ)) (hZ : MeasurableSet Z)
    (hunit : Z ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1)
    (K τ ξ ζ : ℝ) (_hK : 0 ≤ K) (hτ : 0 < τ) (hξ : 0 < ξ) (hζ : 0 < ζ)
    (hdom : ρ ≤ ENNReal.ofReal K • ν.prod volume)
    (hduration : ∀ C : Set X, MeasurableSet C →
      ENNReal.ofReal τ * θ C ≤ (ρ.restrict Z) (C ×ˢ Set.univ))
    (π : Measure ℝ) (q : Fin 5 → ℤ) (B : ℝ≥0∞)
    (hcap : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i j : ℤ,
      ν {l | (l,t) ∈ Z ∧ a l 0 + t * a l 1 ∈ scalarVelocityBin ξ i ∧
        a l 2 + t * a l 3 + t ^ 2 * a l 4 ∈ scalarVelocityBin ζ j ∧
        a l 1 ∈ scalarVelocityBin ξ (q 1)} ≤ B * π (scalarVelocityBin ξ (q 1))) :
    θ {l | scalarMixedCoefficientTag ξ ζ (a l) = q} ≤
      ENNReal.ofReal (400 * K / τ) * B * π (scalarVelocityBin ξ (q 1)) := by
  let C := {l | scalarMixedCoefficientTag ξ ζ (a l) = q}
  have hC : MeasurableSet C :=
    (measurable_scalarMixedCoefficientTag ξ ζ |>.comp ha) (measurableSet_singleton q)
  have hsnapshot (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ν {l | (l,t) ∈ Z ∧ l ∈ C} ≤ 400 * (B * π (scalarVelocityBin ξ (q 1))) := by
    apply two_coordinate_grid_mass_le ν (fun l => a l 0 + t * a l 1)
      (fun l => a l 1) (fun l => a l 2 + t * a l 3 + t ^ 2 * a l 4)
      {l | (l,t) ∈ Z ∧ l ∈ C} (scalarVelocityBin ξ (q 1)) ξ ζ hξ hζ
      (B * π (scalarVelocityBin ξ (q 1)))
    · intro l hl l' hl'
      exact (scalar_mixed_coefficient_position_diameter (a l) (a l') ξ ζ t hξ hζ ht
        (hl.2.trans hl'.2.symm)).1
    · intro l hl l' hl'
      exact (scalar_mixed_coefficient_position_diameter (a l) (a l') ξ ζ t hξ hζ ht
        (hl.2.trans hl'.2.symm)).2
    · intro l hl
      simpa [scalarMixedCoefficientTag, scalarVelocityBin] using congrFun hl.2 1
    · intro i j
      exact (measure_mono (by
        intro l hl
        exact ⟨hl.1.1, hl.2⟩)).trans (hcap t ht i j)
  have hintegral := integrated_snapshot_mass_le ν Z hZ hunit C hC
    (400 * (B * π (scalarVelocityBin ξ (q 1)))) hsnapshot
  have hmass := (hduration C hC).trans
    ((Measure.restrict_mono_measure hdom Z) (C ×ˢ Set.univ))
  rw [Measure.restrict_smul, Measure.smul_apply, smul_eq_mul] at hmass
  have hfloor : ENNReal.ofReal τ * θ C ≤
      ENNReal.ofReal K * (400 * (B * π (scalarVelocityBin ξ (q 1)))) :=
    hmass.trans (mul_le_mul le_rfl hintegral bot_le bot_le)
  have hτ0 : ENNReal.ofReal τ ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hτ
  have hτtop : ENNReal.ofReal τ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hdiv : θ C ≤ ENNReal.ofReal K * (400 * (B * π (scalarVelocityBin ξ (q 1)))) /
      ENNReal.ofReal τ := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hτ0) (Or.inl hτtop)).mpr
    rw [mul_comm]
    exact hfloor
  have heq : ENNReal.ofReal K * (400 * (B * π (scalarVelocityBin ξ (q 1)))) /
      ENNReal.ofReal τ = ENNReal.ofReal (400 * K / τ) * B * π (scalarVelocityBin ξ (q 1)) := by
    rw [ENNReal.ofReal_div_of_pos hτ, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 400)]
    norm_num only [ENNReal.ofReal_ofNat]
    simp only [div_eq_mul_inv]
    ring
  exact hdiv.trans_eq heq

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
