/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.RectangularTargetEnlargement
import Submission.Lib.K4PolynomialNorming.StationaryWeightedSupport
import Mathlib.MeasureTheory.Group.Prod

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

/-- Express a physical target in displacement and height-increment
coordinates relative to the original start of each row. -/
def translatedPhysicalEndpointTarget {Ω : Type*} (n : ℕ)
    (start : Ω → (Fin n → ℝ) × ℝ) (T : Set ((Fin n → ℝ) × ℝ)) :
    Set (Ω × ((Fin n → ℝ) × ℝ)) := {z | z.2 + start z.1 ∈ T}

theorem translatedPhysicalEndpointTarget_measurable {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (start : Ω → (Fin n → ℝ) × ℝ) (hstart : Measurable start)
    (T : Set ((Fin n → ℝ) × ℝ)) (hT : MeasurableSet T) :
    MeasurableSet (translatedPhysicalEndpointTarget n start T) :=
  hT.preimage (measurable_snd.add (hstart.comp measurable_fst))

theorem translatedPhysicalEndpointTarget_section_volume {Ω : Type*}
    (n : ℕ) (start : Ω → (Fin n → ℝ) × ℝ) (T : Set ((Fin n → ℝ) × ℝ)) (ω : Ω) :
    volume (Prod.mk ω ⁻¹' translatedPhysicalEndpointTarget n start T) = volume T := by
  change ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ))
    ((fun z => z+start ω) ⁻¹' T) = _
  exact measure_preimage_add_right
    ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ)) (start ω) T

/-- Enlarge the original counted physical cells once. A simulated endpoint
near the actual last incidence lies in the corresponding translated target
under the same retained original path law. -/
theorem exists_original_rectangular_endpoint_support {X Ω Y ι : Type*}
    [MeasurableSpace X] (n : ℕ)
    (P : Measure X) [IsProbabilityMeasure P] (K : ℕ → Kernel X X)
    [∀ k, IsMarkovKernel (K k)] (hK : ∀ k, K k ∘ₘ P = P)
    (w : (ℕ → X) → ENNReal) (N : ℕ)
    (point : X → (Fin n → ℝ) × ℝ) (T : Set ((Fin n → ℝ) × ℝ))
    (hsupport : ∀ᵐ z ∂P, point z ∈ T)
    (I : Finset ι) (c : ι → Fin (n+1) → ℝ) (r : Fin (n+1) → ℝ)
    (η : ℝ) (hη : 0 ≤ η) (hηr : ∀ j, η ≤ r j)
    (hcover : ∀ y ∈ T, ∃ i ∈ I, ∀ j,
      |(splitHeadCoordinates n).symm y j-c i j| ≤ r j)
    (f : (ℕ → X) → Ω × Y) (start : Ω → (Fin n → ℝ) × ℝ)
    (endpoint : Ω × Y → (Fin n → ℝ) × ℝ)
    (herror : ∀ᵐ x ∂(kernelPathMeasure P K).withDensity w,
      ‖endpoint (f x)+start (f x).1-point (x N)‖ ≤ η) :
    ∃ Tplus : Set ((Fin n → ℝ) × ℝ), MeasurableSet Tplus ∧
      volume Tplus ≤ (I.card : ENNReal)*∏ j, ENNReal.ofReal (4*r j) ∧
      (∀ ω, volume (Prod.mk ω ⁻¹' translatedPhysicalEndpointTarget n start Tplus) =
        volume Tplus) ∧
      ∀ᵐ x ∂(kernelPathMeasure P K).withDensity w,
        ((f x).1,endpoint (f x)) ∈ translatedPhysicalEndpointTarget n start Tplus := by
  obtain ⟨Tplus,hTplus,henlarge,hvol⟩ := exists_rectangular_target_enlargement n
    I c r T η hη hηr hcover
  refine ⟨Tplus,hTplus,hvol,
    fun ω => translatedPhysicalEndpointTarget_section_volume n start Tplus ω,?_⟩
  filter_upwards [kernelPathMeasure_weighted_ae_states P K hK w
    (fun _ z => point z ∈ T) (fun _ => hsupport),herror] with x hx he
  exact henlarge _ _ (hx N) he

/-- Physical base and height errors give their separate rectangular
coordinate margins, with height in the head coordinate of the split. -/
theorem splitHeadCoordinates_error_of_base_height (n : ℕ)
    (x y : (Fin n → ℝ) × ℝ) (ηbase ηheight : ℝ)
    (hb : ‖x.1-y.1‖ ≤ ηbase) (hh : |x.2-y.2| ≤ ηheight) :
    ∀ j, |(splitHeadCoordinates n).symm x j-(splitHeadCoordinates n).symm y j| ≤
      (Fin.cons ηheight (fun _ : Fin n => ηbase) : Fin (n+1) → ℝ) j := by
  rcases x with ⟨xb,xh⟩
  rcases y with ⟨yb,yh⟩
  intro j
  simp only [splitHeadCoordinates_symm_apply]
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa only [Fin.cons_zero] using hh
  · simp only [Fin.cons_succ]
    have hi : |xb i-yb i| ≤ ‖xb-yb‖ := by
      simpa only [Real.norm_eq_abs,Pi.sub_apply] using norm_le_pi_norm (xb-yb) i
    exact hi.trans hb

/-- Enlarge the original counted physical cells once. A simulated endpoint
near the actual last incidence lies in the corresponding translated target
under the same retained original path law. -/
theorem exists_original_rectangular_endpoint_support_of_coordinate_error {X Ω Y ι : Type*}
    [MeasurableSpace X] (n : ℕ)
    (P : Measure X) [IsProbabilityMeasure P] (K : ℕ → Kernel X X)
    [∀ k, IsMarkovKernel (K k)] (hK : ∀ k, K k ∘ₘ P = P)
    (w : (ℕ → X) → ENNReal) (N : ℕ)
    (point : X → (Fin n → ℝ) × ℝ) (T : Set ((Fin n → ℝ) × ℝ))
    (hsupport : ∀ᵐ z ∂P, point z ∈ T)
    (I : Finset ι) (c : ι → Fin (n+1) → ℝ) (r : Fin (n+1) → ℝ)
    (η : Fin (n+1) → ℝ) (hηr : ∀ j, η j ≤ r j)
    (hcover : ∀ y ∈ T, ∃ i ∈ I, ∀ j,
      |(splitHeadCoordinates n).symm y j-c i j| ≤ r j)
    (f : (ℕ → X) → Ω × Y) (start : Ω → (Fin n → ℝ) × ℝ)
    (endpoint : Ω × Y → (Fin n → ℝ) × ℝ)
    (herror : ∀ᵐ x ∂(kernelPathMeasure P K).withDensity w,
      ∀ j, |(splitHeadCoordinates n).symm (endpoint (f x)+start (f x).1) j-
        (splitHeadCoordinates n).symm (point (x N)) j| ≤ η j) :
    ∃ Tplus : Set ((Fin n → ℝ) × ℝ), MeasurableSet Tplus ∧
      volume Tplus ≤ (I.card : ENNReal)*∏ j, ENNReal.ofReal (4*r j) ∧
      (∀ ω, volume (Prod.mk ω ⁻¹' translatedPhysicalEndpointTarget n start Tplus) =
        volume Tplus) ∧
      ∀ᵐ x ∂(kernelPathMeasure P K).withDensity w,
        ((f x).1,endpoint (f x)) ∈ translatedPhysicalEndpointTarget n start Tplus := by
  obtain ⟨Tplus,hTplus,henlarge,hvol⟩ := exists_rectangular_target_enlargement_of_coordinate_error n
    I c r T η hηr hcover
  refine ⟨Tplus,hTplus,hvol,
    fun ω => translatedPhysicalEndpointTarget_section_volume n start Tplus ω,?_⟩
  filter_upwards [kernelPathMeasure_weighted_ae_states P K hK w
    (fun _ z => point z ∈ T) (fun _ => hsupport),herror] with x hx he
  exact henlarge _ _ (hx N) he


end Submission.Lib.K4PolynomialNorming
