/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/MarkedPredictorPair.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeComparisonFrames
import Submission.Obl.k4_horizontal_strict_parameter_step.MarkedComparisonDensity
import Submission.Obl.k4_horizontal_strict_parameter_step.MarkedJitterTransfer
import Submission.Obl.k4_horizontal_strict_parameter_step.PredictorPair

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps

noncomputable section

/-- Data for a comparison obtained by redistributing the original marked cell
masses. Source and witness caps use the same original colour coefficient. -/
structure MarkedComparison (Ω M ι Λ : Type*) [MeasurableSpace Ω]
    [Fintype M] [MeasurableSpace M] [MeasurableSingletonClass M]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] where
  original : Measure Ω
  finite : IsFiniteMeasure original
  mark : Ω → M
  mark_measurable : Measurable mark
  base : Ω → Fin 3 → ℝ
  base_measurable : Measurable base
  mesh : ℝ
  mesh_pos : 0 < mesh
  cells : Finset (Fin 3 → ℤ)
  cells_cover : ∀ᵐ p ∂original, baseMesh mesh (base p) ∈ cells
  source : M → ι
  witness : M → ι
  colour : ι → Λ
  same_colour : ∀ m, colour (source m) = colour (witness m)
  frame : Λ → ComparisonFrame
  time_pos : ∀ l, 0 < (frame l).timeScale
  parameter_pos : ∀ l, 0 < (frame l).parameterScale
  coefficients : ι → Fin 6 → ℝ
  error : ℝ
  error_pos : 0 < error
  ceiling : Λ → ℝ
  ceiling_nonneg : ∀ l, 0 ≤ ceiling l
  source_cells : ∀ i q, q ∈ cells →
    original {p | baseMesh mesh (base p) = q ∧ source (mark p) = i} ≤
      ENNReal.ofReal (ceiling (colour i)) * ENNReal.ofReal (mesh ^ 3)
  witness_cells : ∀ i q, q ∈ cells →
    original {p | baseMesh mesh (base p) = q ∧ witness (mark p) = i} ≤
      ENNReal.ofReal (ceiling (colour i)) * ENNReal.ofReal (mesh ^ 3)
  cell_good : ∀ᵐ p ∂original, ∀ z, baseMesh mesh z = baseMesh mesh (base p) →
    let x := (frame (colour (source (mark p)))).coordinates z
    ‖x‖ ≤ 1 / 2 ∧
      |predictor (coefficients (source (mark p))) (x 0) (x 1) (x 2) -
        predictor (coefficients (witness (mark p))) (x 0) (x 1) (x 2)| ≤ error

namespace MarkedComparison

variable {Ω M ι Λ : Type*} [MeasurableSpace Ω]
    [Fintype M] [MeasurableSpace M] [MeasurableSingletonClass M]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (C : MarkedComparison Ω M ι Λ)

def law : Measure (M × (Fin 3 → ℝ)) :=
  indexedBaseLaw (fun m => meshJitter C.mesh C.cells
    (fun q => (C.original.restrict {p | C.mark p = m})
      {p | baseMesh C.mesh (C.base p) = q}))

def coordinates : M × (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3) :=
  ComparisonFrame.markedCoordinates (fun m => C.frame (C.colour (C.source m)))

def density (l : Λ) : ℝ :=
  C.ceiling l * ((C.frame l).timeScale * (C.frame l).parameterScale ^ 2)

/-- Every cell-stable test is charged to its original pre-jitter event. -/
theorem event_bound (A : Set Ω) (hA : MeasurableSet A)
    (B : M → Set (Fin 3 → ℝ)) (hB : ∀ m, MeasurableSet (B m))
    (htransport : ∀ᵐ p ∂C.original, ∀ z,
      baseMesh C.mesh z = baseMesh C.mesh (C.base p) → z ∈ B (C.mark p) → p ∈ A) :
    C.law {p | p.2 ∈ B p.1} ≤ C.original A :=
  markedJitter_event_bound C.original C.mark C.mark_measurable C.base C.base_measurable
    C.mesh_pos C.cells A hA B hB htransport

theorem finite_law : IsFiniteMeasure C.law := by
  letI := C.finite
  exact markedJitter_finite C.original C.mark C.mark_measurable C.base C.base_measurable
    C.mesh_pos C.cells C.cells_cover

theorem source_density (i : ι) (U : Set (EuclideanSpace ℝ (Fin 3)))
    (hU : MeasurableSet U) :
    C.law {p | C.source p.1 = i ∧ C.coordinates p ∈ U} ≤
      ENNReal.ofReal (C.density (C.colour i)) * volume U := by
  have hb := markedJitter_comparison_density C.original C.mark C.mark_measurable C.source
    C.base C.base_measurable C.mesh_pos C.cells
    (fun i => ENNReal.ofReal (C.ceiling (C.colour i))) C.source_cells
    (fun i => (C.frame (C.colour i)).velocity)
    (fun i => (C.frame (C.colour i)).timeCenter)
    (fun i => (C.frame (C.colour i)).timeScale)
    (fun i => (C.frame (C.colour i)).pCenter)
    (fun i => (C.frame (C.colour i)).qCenter)
    (fun i => (C.frame (C.colour i)).parameterScale)
    (fun i => C.time_pos _) (fun i => C.parameter_pos _) i U hU
  simpa only [law, coordinates, ComparisonFrame.markedCoordinates,
    ComparisonFrame.coordinates, density, ENNReal.ofReal_mul (C.ceiling_nonneg _)] using hb

theorem witness_density (i : ι) (U : Set (EuclideanSpace ℝ (Fin 3)))
    (hU : MeasurableSet U) :
    C.law {p | C.witness p.1 = i ∧ C.coordinates p ∈ U} ≤
      ENNReal.ofReal (C.density (C.colour i)) * volume U := by
  have hb := markedJitter_comparison_density C.original C.mark C.mark_measurable C.witness
    C.base C.base_measurable C.mesh_pos C.cells
    (fun i => ENNReal.ofReal (C.ceiling (C.colour i))) C.witness_cells
    (fun i => (C.frame (C.colour i)).velocity)
    (fun i => (C.frame (C.colour i)).timeCenter)
    (fun i => (C.frame (C.colour i)).timeScale)
    (fun i => (C.frame (C.colour i)).pCenter)
    (fun i => (C.frame (C.colour i)).qCenter)
    (fun i => (C.frame (C.colour i)).parameterScale)
    (fun i => C.time_pos _) (fun i => C.parameter_pos _) i U hU
  have hevent : {p : M × (Fin 3 → ℝ) | C.witness p.1 = i ∧ C.coordinates p ∈ U} =
      {p | C.witness p.1 = i ∧
        (C.frame (C.colour (C.witness p.1))).coordinates p.2 ∈ U} := by
    ext p
    simp only [coordinates, ComparisonFrame.markedCoordinates, Set.mem_ofPred_eq]
    rw [C.same_colour p.1]
  rw [hevent]
  simpa only [law, ComparisonFrame.coordinates, density,
    ENNReal.ofReal_mul (C.ceiling_nonneg _)] using hb

/-- Every event determined by the original finite pair mark returns with its
exact original mass. Polynomial discrepancy events are such mark events. -/
theorem original_mark_mass (P : M → Prop) :
    C.law {p | P p.1} = C.original {p | P (C.mark p)} :=
  markedJitter_original_mass C.original C.mark C.mark_measurable C.base C.base_measurable
    C.mesh_pos C.cells C.cells_cover P

/-- The continuously distributed law is a genuine matching input. Its reference
densities contain precisely the original cell ceiling and the chart Jacobian. -/
def predictorPair : PredictorPair ι Λ (M × (Fin 3 → ℝ)) where
  μ := C.law
  finite := C.finite_law
  lab := C.colour
  h := C.coefficients
  src := fun p => C.source p.1
  wit := fun p => C.witness p.1
  src_measurable := (measurable_of_countable C.source).comp measurable_fst
  wit_measurable := (measurable_of_countable C.witness).comp measurable_fst
  x := C.coordinates
  x_measurable := ComparisonFrame.measurable_markedCoordinates _
  w := fun p => predictor (C.coefficients (C.source p.1))
    (C.coordinates p 0) (C.coordinates p 1) (C.coordinates p 2)
  w_measurable := by
    have hx : Measurable C.coordinates := ComparisonFrame.measurable_markedCoordinates _
    have hh : Measurable (fun p : M × (Fin 3 → ℝ) => C.coefficients (C.source p.1)) :=
      (measurable_of_countable C.coefficients).comp
        ((measurable_of_countable C.source).comp measurable_fst)
    have hx' (i : Fin 3) : Measurable (fun p => C.coordinates p i) :=
      (measurable_pi_apply i).comp ((WithLp.measurable_ofLp 2 (Fin 3 → ℝ)).comp hx)
    have hh' (i : Fin 6) : Measurable (fun p : M × (Fin 3 → ℝ) =>
        C.coefficients (C.source p.1) i) := (measurable_pi_apply i).comp hh
    exact (((hh' 0).add ((hh' 1).mul (hx' 0))).add
      (((hh' 2).add ((hh' 3).mul (hx' 0))).mul (hx' 1))).add
      (((hh' 4).add ((hh' 5).mul (hx' 0))).mul (hx' 2))
  Δ := C.error
  Δ_pos := C.error_pos
  ρ := C.density
  ρ_nonneg := fun l => mul_nonneg (C.ceiling_nonneg l)
    (mul_nonneg (C.time_pos l).le (sq_nonneg _))
  good := by
    have hg : ∀ᵐ p ∂C.law,
        ‖C.coordinates p‖ ≤ 1 / 2 ∧
          |predictor (C.coefficients (C.source p.1))
            (C.coordinates p 0) (C.coordinates p 1) (C.coordinates p 2) -
            predictor (C.coefficients (C.witness p.1))
              (C.coordinates p 0) (C.coordinates p 1) (C.coordinates p 2)| ≤ C.error := by
      apply markedJitter_transport_ae C.original C.mark C.mark_measurable
        C.base C.mesh C.cells C.cell_good
      intro p hp z hz
      exact hp z hz
    filter_upwards [hg] with p hp
    refine ⟨C.same_colour _, hp.1, ?_, ?_⟩
    · simpa using C.error_pos.le
    · simpa only [abs_sub_comm] using hp.2
  density_src := C.source_density
  density_wit := C.witness_density

end MarkedComparison

end

end Submission.Obl.k4_horizontal_strict_parameter_step
