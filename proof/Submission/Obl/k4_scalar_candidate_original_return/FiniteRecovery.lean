import Submission.Obl.k4_scalar_candidate_original_return.ListRecovery
import Submission.Obl.k4_scalar_candidate_original_return.FiniteLists
import Submission.Obl.k4_scalar_candidate_original_return.RecordSupport

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4ModelReduction

noncomputable section

/-- Original-law list recovery produces an actual finite observer table whose
selected predicates have degree three and an explicit finite record count. -/
theorem recover_finite_original_scalar_lists {W m : ℕ}
    (ω : Fin W → ℝ) (hω : ∀ a, 0 ≤ ω a) (hωsum : ∑ a, ω a = 1)
    (γ : Fin m → Fin W) (R δ ρ : ℝ) (hδ : 0 < δ) (hρ : 0 < ρ)
    (μ : Fin m → Measure Inc) (C : Fin m → Set Inc)
    (f g : Fin m → (Fin 6 → ℝ) → ℝ)
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hfi : ∀ i, Integrable (f i) volume) (hsupport : ∀ i, supportedInCube (f i) R)
    (hf0 : ∀ i w, 0 ≤ f i w) (hg0 : ∀ i w, 0 ≤ g i w)
    (hsource : ∀ i, ((μ i).restrict (C i)).map fullSourceCoordinates =
      volume.withDensity (fun w => ENNReal.ofReal (f i w)))
    (hcell : ∀ i w w', (∀ j ∉ ([0, 1] : List (Fin 6)), w j = w' j) →
      (∀ j ∈ ([0, 1] : List (Fin 6)), ⌊w j / ρ⌋ = ⌊w' j / ρ⌋) → g i w = g i w')
    (D : ℕ) (L : Fin W → (Base × ℤ) → Finset (Fin m))
    (hLmeas : ∀ a i, MeasurableSet {z | i ∈ L a z})
    (hLcard : ∀ a z, (L a z).card ≤ D) :
    let F := originalRecordCodes R ρ δ
    ∃ table : Fin W → Option F → Finset (Fin m),
      (∀ a c, (table a c).card ≤ D) ∧
      (∀ a i, MeasurableSet {z | i ∈ table a (observationMeshCode ρ F z)}) ∧
      (∀ a i z, Format 6 (6 * (F.card : ℝ) + 1) 3
        {w | i ∈ table a (observationMeshCode ρ F
          (originalObservation δ ((z, fun e : Fin 5 => w e.castSucc), w 5)))}) ∧
      (∑ i, ENNReal.ofReal (ω (γ i)) * μ i
        {q | q ∈ C i ∧ i ∈ L (γ i) (originalObservation δ q)}) ≤
      (∑ i, ENNReal.ofReal (ω (γ i)) * μ i
        {q | q ∈ C i ∧ i ∈ table (γ i) (observationMeshCode ρ F (originalObservation δ q))}) +
        2 * ∑ i, densityL1Distance volume (g i) (f i) := by
  classical
  let F := originalRecordCodes R ρ δ
  obtain ⟨table₀, htable₀, hsuccess⟩ := recover_original_scalar_lists ω hω hωsum γ δ ρ hρ
    μ C f g hf hg hfi hf0 hg0 hsource hcell D L hLmeas hLcard
  let table : Fin W → Option F → Finset (Fin m) := fun a => restrictTable F (table₀ a)
  refine ⟨table, ?_, ?_, ?_, ?_⟩
  · intro a c
    exact restrictTable_card F (table₀ a) (htable₀ a) c
  · intro a i
    exact meshLists_measurable ρ F (table a) i
  · intro a i z
    exact meshLists_format ρ δ F (table a) i z
  · have heq : (∑ i, ENNReal.ofReal (ω (γ i)) * μ i
        {q | q ∈ C i ∧ i ∈ table₀ (γ i) (observationMeshTag ρ (originalObservation δ q))}) =
        ∑ i, ENNReal.ofReal (ω (γ i)) * μ i
          {q | q ∈ C i ∧ i ∈ table (γ i) (observationMeshCode ρ F (originalObservation δ q))} := by
      apply Finset.sum_congr rfl
      intro i _
      apply congrArg (fun a : ℝ≥0∞ => ENNReal.ofReal (ω (γ i)) * a)
      exact restrictTable_success (μ i) (C i) F
        (fun q => observationMeshTag ρ (originalObservation δ q)) (table₀ (γ i)) i
        (original_record_support hρ hδ (μ i) (C i) (f i) (hsource i) (hsupport i))
    rw [heq] at hsuccess
    exact hsuccess

end

end Submission.Obl.k4_scalar_candidate_original_return
