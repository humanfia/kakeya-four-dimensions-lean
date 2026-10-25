import Submission.Obl.k4_pair_bin_atlas_assembly.Kernel
import Submission.Obl.k4_quadratic_discriminant_safe_paths.Measurability

namespace Submission.Obl.k4_pair_bin_atlas_assembly

open Set Metric MeasureTheory
open scoped ENNReal

abbrev AnchorParameter := EuclideanSpace ℝ (Fin 3) × ℂ

def anchorDomain : Set AnchorParameter :=
  closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 8) ×ˢ
    closedBall (1 / 2 : ℂ) (1 / 4)

noncomputable def anchorLaw : Measure AnchorParameter :=
  ProbabilityTheory.cond (volume.prod volume) anchorDomain

theorem measurableSet_anchorDomain : MeasurableSet anchorDomain :=
  measurableSet_closedBall.prod measurableSet_closedBall

theorem anchorDomain_volume_pos : 0 < (volume.prod volume) anchorDomain := by
  rw [anchorDomain, Measure.prod_prod]
  exact pos_iff_ne_zero.mpr (mul_ne_zero
    (measure_closedBall_pos volume _ (by norm_num)).ne'
    (measure_closedBall_pos volume _ (by norm_num)).ne')

theorem anchorDomain_volume_ne_top : (volume.prod volume) anchorDomain ≠ ∞ := by
  rw [anchorDomain, Measure.prod_prod]
  exact ENNReal.mul_ne_top measure_closedBall_lt_top.ne measure_closedBall_lt_top.ne

theorem anchorLaw_probability : IsProbabilityMeasure anchorLaw :=
  ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    anchorDomain_volume_pos.ne' anchorDomain_volume_ne_top

theorem anchorLaw_outside : anchorLaw anchorDomainᶜ = 0 := by
  rw [anchorLaw, ProbabilityTheory.cond_apply measurableSet_anchorDomain]
  simp

theorem not_safeFor_iff (ρ : ℝ) (P P' : MvPolynomial (Fin 3) ℝ)
    (z₀ α : EuclideanSpace ℝ (Fin 3)) (σ : ℂ) :
    ¬ SafeFor ρ P P' z₀ α σ ↔
      ∃ z ∈ thickening ρ (safePath z₀ α σ),
        ‖MvPolynomial.eval (fun i => z i) (P.map (algebraMap ℝ ℂ))‖ < ρ ∨
          ‖MvPolynomial.eval (fun i => z i) (P'.map (algebraMap ℝ ℂ))‖ < ρ := by
  simp only [SafeFor, not_forall, not_and_or, not_le, exists_prop]

/-- Failure of the safe-path condition is open even when the source moves. -/
theorem isOpen_unsafe (ρ : ℝ) (P P' : MvPolynomial (Fin 3) ℝ) :
    IsOpen {p : EuclideanSpace ℝ (Fin 3) × AnchorParameter |
      ¬ SafeFor ρ P P' p.1 p.2.1 p.2.2} := by
  let U : Set (EuclideanSpace ℂ (Fin 3)) :=
    {z | ‖MvPolynomial.eval (fun i => z i) (P.map (algebraMap ℝ ℂ))‖ < ρ ∨
      ‖MvPolynomial.eval (fun i => z i) (P'.map (algebraMap ℝ ℂ))‖ < ρ}
  let a : EuclideanSpace ℝ (Fin 3) × AnchorParameter → EuclideanSpace ℂ (Fin 3) :=
    fun p => emb p.1
  let b : EuclideanSpace ℝ (Fin 3) × AnchorParameter → EuclideanSpace ℂ (Fin 3) :=
    fun p => emb p.1 + p.2.2 • (emb p.2.1 - emb p.1)
  let c : EuclideanSpace ℝ (Fin 3) × AnchorParameter → EuclideanSpace ℂ (Fin 3) :=
    fun p => emb p.2.1
  have ha : Continuous a := by dsimp [a, emb]; fun_prop
  have hb : Continuous b := by dsimp [b, emb]; fun_prop
  have hc : Continuous c := by dsimp [c, emb]; fun_prop
  have h₁ := Submission.Obl.k4_quadratic_discriminant_safe_paths.isOpen_tube_hits
    a b ha hb ρ U
  have h₂ := Submission.Obl.k4_quadratic_discriminant_safe_paths.isOpen_tube_hits
    b c hb hc ρ U
  convert h₁.union h₂ using 1
  ext p
  rw [mem_ofPred_eq, not_safeFor_iff]
  change (∃ z ∈ thickening ρ (safePath p.1 p.2.1 p.2.2), z ∈ U) ↔
    (∃ z ∈ thickening ρ (segment ℝ (a p) (b p)), z ∈ U) ∨
      ∃ z ∈ thickening ρ (segment ℝ (b p) (c p)), z ∈ U
  change (∃ z ∈ thickening ρ
      (segment ℝ (a p) (b p) ∪ segment ℝ (b p) (c p)), z ∈ U) ↔ _
  rw [thickening_union]
  constructor
  · rintro ⟨z, hz | hz, hzU⟩
    · exact Or.inl ⟨z, hz, hzU⟩
    · exact Or.inr ⟨z, hz, hzU⟩
  · rintro (⟨z, hz, hzU⟩ | ⟨z, hz, hzU⟩)
    · exact ⟨z, Or.inl hz, hzU⟩
    · exact ⟨z, Or.inr hz, hzU⟩

theorem measurableSet_unsafe (ρ : ℝ) (P P' : MvPolynomial (Fin 3) ℝ) :
    MeasurableSet {p : EuclideanSpace ℝ (Fin 3) × AnchorParameter |
      ¬ SafeFor ρ P P' p.1 p.2.1 p.2.2} :=
  (isOpen_unsafe ρ P P').measurableSet

/-- A normalized version of the supplied safe-path estimate at one exponent. -/
def SafeProbability (Cs : ℕ) : Prop :=
    ∀ A : ℝ, 2 ≤ A →
      ∀ P P' : MvPolynomial (Fin 3) ℝ,
      P.totalDegree ≤ 2 → P'.totalDegree ≤ 2 →
      (∀ d, |P.coeff d| ≤ A) → (∀ d, |P'.coeff d| ≤ A) →
      ∀ z₀ : EuclideanSpace ℝ (Fin 3), ‖z₀‖ ≤ 1 / 8 →
      A⁻¹ ≤ |MvPolynomial.eval (fun i => z₀ i) P| →
      A⁻¹ ≤ |MvPolynomial.eval (fun i => z₀ i) P'| →
      anchorLaw {θ | ¬ SafeFor (A ^ (-(Cs : ℝ))) P P' z₀ θ.1 θ.2} ≤
        ENNReal.ofReal A⁻¹

/-- Normalize the supplied volume estimate once, on a fixed parameter law. -/
theorem safePaths_probability (hsafe : SafePaths) :
    ∃ Cs : ℕ, 0 < Cs ∧ SafeProbability Cs := by
  obtain ⟨Cs, hCs, h⟩ := hsafe
  refine ⟨Cs, hCs, ?_⟩
  intro A hA P P' hP hP' hc hc' z₀ hz hval hval'
  have hv := (h A hA P P' hP hP' hc hc' z₀ hz hval hval').2
  have heq : anchorDomain ∩
      {θ | ¬ SafeFor (A ^ (-(Cs : ℝ))) P P' z₀ θ.1 θ.2} =
      Submission.Obl.k4_quadratic_discriminant_safe_paths.badSet
        z₀ P P' (A ^ (-(Cs : ℝ))) := by
    ext θ
    simp only [anchorDomain, mem_inter_iff, mem_prod, mem_ofPred_eq, SafeFor,
      safePath, not_forall, not_and_or, not_le,
      Submission.Obl.k4_quadratic_discriminant_safe_paths.badSet,
      Submission.Obl.k4_quadratic_discriminant_safe_paths.brokenPath,
      Submission.Obl.k4_quadratic_discriminant_safe_paths.emb, emb]
    simp only [exists_prop, and_assoc]
  rw [anchorLaw, ProbabilityTheory.cond_apply measurableSet_anchorDomain, heq]
  calc
    _ ≤ ((volume.prod volume) anchorDomain)⁻¹ *
        (ENNReal.ofReal A⁻¹ * (volume.prod volume) anchorDomain) := by
      gcongr
      exact hv
    _ = ENNReal.ofReal A⁻¹ := by
      rw [mul_left_comm,
        ENNReal.inv_mul_cancel anchorDomain_volume_pos.ne' anchorDomain_volume_ne_top,
        mul_one]

end Submission.Obl.k4_pair_bin_atlas_assembly
