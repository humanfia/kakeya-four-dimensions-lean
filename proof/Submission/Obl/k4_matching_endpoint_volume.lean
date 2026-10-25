import Mathlib
import ChallengeDeps
import Submission.Obl.k4_matching_endpoint_volume.EndpointVolume

set_option linter.unusedVariables false

/-!
# Polynomial endpoint pullback-volume bound

This is the endpoint estimate in the supplied paper's Lemma 3.3. The proof
uses its Vandermonde Jacobian, quantitative local injectivity, a finite grid
bound for regular fibers, the accepted area inequality, and Fubini. All helper
code was developed in this workspace by session x0047 for o015.
-/

theorem Submission.k4_matching_endpoint_volume : ∀ m : ℕ, 1 ≤ m → ∃ A : ℕ, 1 ≤ A ∧ ∀ K : ℝ, 2 ≤ K → ∀ (U : Fin (m + 1) → ℝ) (s₀ : ℝ) (T : Set (ℝ × (Fin m → ℝ))), (∀ p : Fin (m + 1), |U p| ≤ K) → |s₀| ≤ 1 → (∀ p : Fin m, K⁻¹ ≤ |U p.succ - U p.castSucc|) → MeasurableSet T → (fun Φ : (ℝ × (Fin m → ℝ)) → (ℝ × (Fin m → ℝ)) => MeasureTheory.volume {x : ℝ × (Fin m → ℝ) | |x.1| ≤ 1 ∧ (∀ p : Fin m, |x.2 p| ≤ 1) ∧ (∀ p q : Fin m, p ≠ q → K⁻¹ ≤ |x.2 p - x.2 q|) ∧ Φ x ∈ T} ≤ ENNReal.ofReal (K ^ A) * MeasureTheory.volume T) (fun x => (x.1, fun j : Fin m => (U 0 * (x.1 - s₀) ^ ((j : ℕ) + 1) + ∑ p : Fin m, (U p.succ - U p.castSucc) * (x.1 - x.2 p) ^ ((j : ℕ) + 1)) / (((j : ℕ) + 1).factorial : ℝ))) := by
  intro m hm
  obtain ⟨A, hA, hbound⟩ := Submission.Obl.k4_matching_endpoint_volume.endpoint_volume_power_bound m hm
  refine ⟨A, hA, ?_⟩
  intro K hK U s₀ T hU hs₀ hgap hT
  dsimp only
  have h := hbound K hK U hU hgap s₀ T hT
  change MeasureTheory.volume {x : ℝ × (Fin m → ℝ) | |x.1| ≤ 1 ∧
    (∀ p : Fin m, |x.2 p| ≤ 1) ∧
    (∀ p q : Fin m, p ≠ q → K⁻¹ ≤ |x.2 p - x.2 q|) ∧
    Submission.Obl.k4_matching_endpoint_volume.fullEndpoint U s₀ x ∈ T} ≤ _
  have heq : {x : ℝ × (Fin m → ℝ) | |x.1| ≤ 1 ∧
      (∀ p : Fin m, |x.2 p| ≤ 1) ∧
      (∀ p q : Fin m, p ≠ q → K⁻¹ ≤ |x.2 p - x.2 q|) ∧
      Submission.Obl.k4_matching_endpoint_volume.fullEndpoint U s₀ x ∈ T} =
      (Set.Icc (-1 : ℝ) 1 ×ˢ Submission.Obl.k4_matching_endpoint_volume.separatedUnitCube m K⁻¹) ∩
        (Submission.Obl.k4_matching_endpoint_volume.fullEndpoint U s₀) ⁻¹' T := by
    ext x
    change (_ ∧ _ ∧ _ ∧ _) ↔ ((_ ∧ _) ∧ _)
    constructor
    · rintro ⟨ht, hcoord, hsep, hT⟩
      refine ⟨⟨abs_le.mp ht, ?_⟩, hT⟩
      refine ⟨(pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr hcoord, ?_⟩
      intro p q hpq
      exact hsep q p hpq.symm
    · rintro ⟨⟨ht, hnorm, hsep⟩, hT⟩
      refine ⟨abs_le.mpr ht, ?_, ?_, hT⟩
      · exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mp hnorm
      · intro p q hpq
        exact hsep q p hpq.symm
  rw [heq]
  exact h
