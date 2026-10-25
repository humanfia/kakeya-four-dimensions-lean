/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file GlobalStripFilling.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.BreadthFromFloors
import Submission.Obl.k4_scalar_graph_residual_discovery.LongEntryFilling
import Submission.Obl.k4_scalar_graph_residual_discovery.StripEntries

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal NNReal
open Submission.Lib.K4CommonLocalChoice
open Submission.Lib.K4ContinuousKakeya
open Submission.Obl.k4_initial_horizon_bound

noncomputable section

/-- The simultaneous final original-state and strip floors give actual
global strip filling. Breadth is derived from the original graph palette
caps; the long durations refer to the earlier `P`, and the filling counts
the final `R` across ALL coefficient worlds. -/
theorem global_assigned_filling_of_original_floors
    (θ : Measure ScalarLine) [IsFiniteMeasure θ]
    (μ oldGraph : Measure ScalarIncidence) [IsFiniteMeasure μ]
    (π : Measure ℤ) {P R : Set ScalarIncidence}
    (hP : MeasurableSet P) (hR : MeasurableSet R) (hRP : R ⊆ P)
    {b p ρ H K C vsep L a δ : ℝ}
    (hb : 0 < b) (hp : 0 < p) (hbp : b ≤ p) (hp₁ : p ≤ 1) (hρ : 0 < ρ)
    (hH : 1 ≤ H) (hK : 0 < K) (hC : 0 ≤ C) (hMK : FiniteMK 2 C)
    (hvsep : 0 < vsep) (hL : 0 < L) (ha : 0 < a) (hδ : 0 < δ)
    (U : ℝ≥0) (hU : 3 * (U : ℝ) ≤ K) (hdom : μ.restrict R ≤ U • θ.prod volume)
    (hcur : μ.restrict R ≤ oldGraph)
    (hcoeff : ∀ z ∈ P, ∀ e, |z.1.2 e| ≤ H)
    (htime : ∀ z ∈ P, z.2 ∈ Icc (0 : ℝ) 1)
    (hprod : ∀ A : Set ScalarIncidence, MeasurableSet A → A ⊆ P →
      (θ.prod volume) A ≤ ENNReal.ofReal H * μ A)
    (Cg η pmax : ℝ≥0∞) (hη₀ : η ≠ 0) (hηt : η ≠ ∞)
    (hgraphcap : ∀ (w : Fin 3 → ℤ) (c : ℤ),
      oldGraph {z | cell b (scalarPosition z) = w ∧ (⌊z.1.2 1 / vsep⌋ : ℤ) = c} ≤
        Cg * oldGraph ((fun z => cell b (scalarPosition z)) ⁻¹' {w}) * π {c})
    (hstatefloor : ∀ w, R ∩ (fun z => cell b (scalarPosition z)) ⁻¹' {w} = ∅ ∨
      η * oldGraph ((fun z => cell b (scalarPosition z)) ⁻¹' {w}) <
        μ (R ∩ (fun z => cell b (scalarPosition z)) ⁻¹' {w}))
    (hπ : ∀ c, π {c} ≤ pmax) (hsmall : 5 * (Cg / η) * pmax ≤ 1 / 2)
    (row : (Fin 3 → ℤ) → Fin 2 → ℝ)
    (hlong : ∀ z ∈ R, ENNReal.ofReal (a * ρ) ≤
      incidenceDuration (P ∩ stripRecord b ρ p row ⁻¹' {stripRecord b ρ p row z}) z.1)
    (hstripfloor : ∀ vj, R ∩ stripRecord b ρ p row ⁻¹' {vj} = ∅ ∨
      ENNReal.ofReal δ * μ (P ∩ stripRecord b ρ p row ⁻¹' {vj}) <
        μ (R ∩ stripRecord b ρ p row ⁻¹' {vj}))
    (hpriorbudget : H / (a * δ) ≤ K)
    (hbudget : 200 * C * K ^ 4 * (1 + H) ^ 2 ≤ L * vsep) :
    ∀ v j, (∃ z ∈ R, stripRecord b ρ p row z = (v, j)) →
      (ρ / p) ^ 2 / L ≤
        ((normalStripPhysicalCells (assignedPosition b) {z ∈ R | assignedCell ρ b z = v}
          (row v) p j).ncard : ℝ) := by
  have hstate : Measurable (fun z : ScalarIncidence => cell b (scalarPosition z)) :=
    measurable_cell b measurable_scalarPosition
  have hvelocity : Measurable (fun z : ScalarIncidence => z.1.2 1) :=
    (measurable_pi_apply 1).comp (measurable_snd.comp measurable_fst)
  have hcurrentfloor (w : Fin 3 → ℤ) :
      (μ.restrict R) ((fun z => cell b (scalarPosition z)) ⁻¹' {w}) = 0 ∨
        η * oldGraph ((fun z => cell b (scalarPosition z)) ⁻¹' {w}) ≤
          (μ.restrict R) ((fun z => cell b (scalarPosition z)) ⁻¹' {w}) := by
    rw [Measure.restrict_apply (hstate (measurableSet_singleton w)), inter_comm]
    rcases hstatefloor w with he | hf
    · exact Or.inl (by rw [he, measure_empty])
    · exact Or.inr hf.le
  have hstates := velocity_breadth_of_final_state_floors oldGraph (μ.restrict R) hcur
    (fun z => cell b (scalarPosition z)) hstate (fun z => z.1.2 1) hvelocity hvsep π
    (fun w => oldGraph ((fun z => cell b (scalarPosition z)) ⁻¹' {w})) Cg η pmax
    hη₀ hηt hgraphcap hcurrentfloor hπ hsmall
  intro v j hoccupied
  let S : Set (Fin 3 → ℤ) := {w | stripLabel b ρ p row w = (v, j)}
  have hentry (A : Set ScalarIncidence) :
      A ∩ (fun z => cell b (scalarPosition z)) ⁻¹' S =
        A ∩ stripRecord b ρ p row ⁻¹' {(v, j)} := rfl
  have hnonempty : R ∩ stripRecord b ρ p row ⁻¹' {(v, j)} ≠ ∅ := by
    obtain ⟨z, hz, hrecord⟩ := hoccupied
    exact Set.nonempty_iff_ne_empty.mp ⟨z, hz, hrecord⟩
  have hfloor := (hstripfloor (v, j)).resolve_left hnonempty
  have hpositive : μ (R ∩ (fun z => cell b (scalarPosition z)) ⁻¹' S) ≠ 0 := by
    rw [hentry]
    exact ne_of_gt (lt_of_le_of_lt zero_le hfloor)
  have hlong' : ∀ z ∈ R, cell b (scalarPosition z) ∈ S → ENNReal.ofReal (a * ρ) ≤
      incidenceDuration (P ∩ (fun z => cell b (scalarPosition z)) ⁻¹' S) z.1 := by
    intro z hz hs
    have hh := hlong z hz
    change stripRecord b ρ p row z = (v, j) at hs
    rw [hs, ← hentry P] at hh
    exact hh
  have hprod' : (θ.prod volume) (P ∩ (fun z => cell b (scalarPosition z)) ⁻¹' S) ≤
      ENNReal.ofReal H * μ (P ∩ (fun z => cell b (scalarPosition z)) ⁻¹' S) :=
    hprod _ (hP.inter (hstate (to_countable S).measurableSet)) inter_subset_left
  have hfloor' : ENNReal.ofReal δ * μ (P ∩ (fun z => cell b (scalarPosition z)) ⁻¹' S) ≤
      μ (R ∩ (fun z => cell b (scalarPosition z)) ⁻¹' S) := by
    simpa only [hentry] using hfloor.le
  have hfilling := global_filling_of_long_original_entries θ μ hP hR hRP hb hp hbp hp₁ hρ
    hH hK hC hMK hvsep hL ha hδ U hU hdom hcoeff htime hstates S
    hlong' hprod' hfloor' hpositive hpriorbudget hbudget
  have hsets : ((fun z => cell p (assignedPosition b z)) ''
      (R ∩ (fun z => cell b (scalarPosition z)) ⁻¹' S)) =
      normalStripPhysicalCells (assignedPosition b) {z ∈ R | assignedCell ρ b z = v}
        (row v) p j := by
    ext w
    constructor
    · rintro ⟨z, ⟨hz, hrec⟩, hw⟩
      change stripRecord b ρ p row z = (v, j) at hrec
      have hv := congrArg Prod.fst hrec
      change assignedCell ρ b z = v at hv
      have hj := congrArg Prod.snd hrec
      change ⌊normalCoordinate (row (assignedCell ρ b z)) (assignedPosition b z) / p⌋ = j at hj
      rw [hv] at hj
      exact ⟨z, ⟨hz, hv⟩, hw, hj⟩
    · rintro ⟨z, ⟨hz, hv⟩, hw, hj⟩
      refine ⟨z, ⟨hz, ?_⟩, hw⟩
      change stripRecord b ρ p row z = (v, j)
      change (assignedCell ρ b z,
        ⌊normalCoordinate (row (assignedCell ρ b z)) (assignedPosition b z) / p⌋) = (v, j)
      rw [hv, hj]
  simpa only [hsets] using hfilling

end

end Submission.Obl.k4_scalar_graph_residual_discovery
