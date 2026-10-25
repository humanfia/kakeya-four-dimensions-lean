/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.ProductSectionMass
import Submission.Lib.K4PolynomialNorming.NormingCoordinates

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

/-- A positive joint mass under an original product ceiling forces a
substantial section, without a loss from the number of control tuples. -/
theorem exists_substantial_product_section {Ω Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Y]
    (μ : Measure Ω) [SFinite μ] (ν : Measure Y) [SFinite ν]
    (P : Measure (Ω × Y)) (K b : ENNReal) (hP : P ≤ K • μ.prod ν)
    (E : Set (Ω × Y)) (hE : MeasurableSet E)
    (hmass : K * μ univ * b < P E) :
    ∃ ω, b < ν (Prod.mk ω ⁻¹' E) := by
  by_contra! hn
  have h := dominated_product_section_mass_bound μ ν P K 1 b hP E hE
    (fun ω => by simpa only [one_mul] using hn ω)
  simp only [one_mul] at h
  exact (not_le_of_gt hmass) h

/-- Convert the selected duration section to ordinary six signed
coordinates with its exact Lebesgue volume. -/
theorem exists_substantial_six_parameter_family {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ]
    (P : Measure (Ω × ((Fin 5 → ℝ) × ℝ))) (K b : ENNReal)
    (hP : P ≤ K • μ.prod volume)
    (E : Set (Ω × ((Fin 5 → ℝ) × ℝ))) (hE : MeasurableSet E)
    (hmass : K * μ univ * b < P E) :
    ∃ ω, ∃ S : Set (Fin 6 → ℝ), MeasurableSet S ∧ b < volume S ∧
      ∀ δ ∈ S, (ω,splitHeadCoordinates 5 δ) ∈ E := by
  obtain ⟨ω,hω⟩ := exists_substantial_product_section μ volume P K b hP E hE hmass
  let S := (splitHeadCoordinates 5) ⁻¹' (Prod.mk ω ⁻¹' E)
  have hsection : MeasurableSet (Prod.mk ω ⁻¹' E) := hE.preimage measurable_prodMk_left
  have hS : MeasurableSet S := (splitHeadCoordinates 5).measurable hsection
  refine ⟨ω,S,hS,?_,fun _ hδ => hδ⟩
  simpa only [S,(splitHeadCoordinates_measurePreserving 5).measure_preimage
    hsection.nullMeasurableSet] using hω

/-- The original retained-mass budget and its observed product ceiling
supply a substantial actual six-parameter family whenever every retained
observation satisfies the successful endpoint event. -/
theorem retained_observation_substantial_six_parameter_family {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω]
    (θ : Measure X) (f : X → Ω × ((Fin 5 → ℝ) × ℝ)) (hf : Measurable f)
    (μ : Measure Ω) [SFinite μ] (K b m loss : ENNReal)
    (hdom : θ.map f ≤ K • μ.prod volume)
    (hbudget : m ≤ θ univ + loss)
    (E : Set (Ω × ((Fin 5 → ℝ) × ℝ))) (hE : MeasurableSet E)
    (hsupport : ∀ᵐ x ∂θ, f x ∈ E)
    (hpositive : K * μ univ * b + loss < m) :
    ∃ ω, ∃ S : Set (Fin 6 → ℝ), MeasurableSet S ∧ b < volume S ∧
      ∀ δ ∈ S, (ω,splitHeadCoordinates 5 δ) ∈ E := by
  have hmass : (θ.map f) E = θ univ := by
    rw [Measure.map_apply hf hE]
    apply measure_congr
    filter_upwards [hsupport] with x hx
    simp only [Set.mem_preimage, Set.mem_univ, hx]
  have hlarge : K * μ univ * b < (θ.map f) E := by
    by_contra hn
    have hh : (θ.map f) E ≤ K * μ univ * b := le_of_not_gt hn
    have hle : m ≤ K * μ univ * b + loss := by
      rw [← hmass] at hbudget
      exact hbudget.trans (add_le_add hh le_rfl)
    exact (not_le_of_gt hpositive) hle
  exact exists_substantial_six_parameter_family μ (θ.map f) K b hdom E hE hlarge

end Submission.Lib.K4PolynomialNorming
