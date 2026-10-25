/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file GlobalPreparation.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalReferenceFloors
import Submission.Obl.k4_scalar_graph_residual_discovery.GlobalPosteriorRecords
import Submission.Obl.k4_scalar_graph_residual_discovery.PriorIntersectionCut
import Submission.Obl.k4_scalar_graph_residual_discovery.LongStripCut

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice
open Submission.Obl.k4_scalar_grid_parameter_preparation
open Submission.Obl.k4_initial_horizon_bound

namespace Zoom

noncomputable section

/-- Actual global preparation, before choosing a coefficient world:
prior-intersection cut, simultaneous earlier long entries, then ONE
simultaneous current-floor pruning. Every deletion is charged to the
original measures. The intermediate `P` is the earlier strip law. -/
theorem prepare_global_original_law {σ : Type*} [Fintype σ]
    (θ : Measure ScalarLine) [IsFiniteMeasure θ]
    (μ oldGraph : Measure ScalarIncidence) [IsFiniteMeasure μ]
    (π : Measure ℤ) {c : ℝ≥0∞} (hdom : μ ≤ c • θ.prod volume)
    {E : Set ScalarIncidence} (hE : MeasurableSet E)
    {ρ b H A D : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hb : 0 < b) (hbρ : b ≤ ρ) (hH : 1 ≤ H)
    (β h Ac : σ → ℝ) (hβ : ∀ s, 0 < β s) (hscale : ∀ s, β s ≤ ρ * h s)
    (hh : ∀ s, 0 < h s) (hh₁ : ∀ s, h s ≤ 1) (hAc : ∀ s, 0 < Ac s)
    (ηint : σ → ℝ≥0∞) (ηdur : σ → ℝ) (hηdur : ∀ s, 0 ≤ ηdur s)
    (ηstate : ℝ≥0∞) (ηstrip ηpost Dpost : σ → ℝ≥0∞)
    (row : (Fin 3 → ℤ) → Fin 2 → ℝ)
    (hcoeff : ∀ z ∈ E, ∀ e, |z.1.2 e| ≤ H)
    (htime : ∀ z ∈ E, z.2 ∈ Icc (0 : ℝ) 1)
    (hA : ∀ q, 1 + |row q 0| + |row q 1| ≤ A) (hD : 0 ≤ D)
    (hderiv : ∀ z ∈ E,
      |(normalPolynomial
        (row (cell ρ (leftCorner b (cell b (scalarPosition z))))) z.1).derivative.eval z.2| ≤ D)
    (hvariation : ∀ s, D * (ρ + 2 * b) + 2 * A * b ≤ ρ * h s)
    (lists : σ → ((Fin 3 → ℤ) × ℤ) → Finset ((Fin 5 → ℤ) × (Fin 3 → ℤ)))
    (hlistcard : ∀ s wc, ((lists s wc).card : ℝ≥0∞) ≤ Dpost s)
    (hlisted : ∀ s z, z ∈ E →
      (posteriorEntryRecord ρ b (h s) z).1 ∈ lists s (posteriorEntryRecord ρ b (h s) z).2) :
    ∃ P R : Set ScalarIncidence, MeasurableSet P ∧ P ⊆ E ∧ MeasurableSet R ∧ R ⊆ P ∧
      μ (E \ R) ≤ c * (32 * ∑ s, ηint s) * θ univ +
        (c * (∑ s, ENNReal.ofReal (6860 * H * ηdur s)) * θ univ +
          ((ηstate * oldGraph univ +
            ((∑ s, ηstrip s * μ E) + ∑ s, ηpost s * (Dpost s * (oldGraph univ * π univ)))) +
              (∑ s, ENNReal.ofReal ((5000 * 111 ^ 3) / Ac s)) * θ univ)) ∧
      (∀ z ∈ R, ∀ s, ηint s * θ {l | cell (β s) l.2 = cell (β s) z.1.2} ≤
        θ {l | cell ρ l.2 = cell ρ z.1.2 ∧ cell (β s) l.2 = cell (β s) z.1.2}) ∧
      (∀ z ∈ R, ∀ s, ENNReal.ofReal (ηdur s * ρ) ≤
        incidenceDuration (P ∩ stripRecord b ρ (ρ * h s) row ⁻¹' {stripRecord b ρ (ρ * h s) row z}) z.1) ∧
      (∀ w : Fin 3 → ℤ, R ∩ (fun z => cell b (scalarPosition z)) ⁻¹' {w} = ∅ ∨
        ηstate * oldGraph ((fun z => cell b (scalarPosition z)) ⁻¹' {w}) <
          μ (R ∩ (fun z => cell b (scalarPosition z)) ⁻¹' {w})) ∧
      (∀ s q, R ∩ stripRecord b ρ (ρ * h s) row ⁻¹' {q} = ∅ ∨
        ηstrip s * μ (P ∩ stripRecord b ρ (ρ * h s) row ⁻¹' {q}) <
          μ (R ∩ stripRecord b ρ (ρ * h s) row ⁻¹' {q})) ∧
      (∀ s e, R ∩ posteriorEntryRecord ρ b (h s) ⁻¹' {e} = ∅ ∨
        ηpost s * oldGraph ((fun z => cell b (scalarPosition z)) ⁻¹' {e.2.1}) * π {e.2.2} <
          μ (R ∩ posteriorEntryRecord ρ b (h s) ⁻¹' {e})) ∧
      ∀ s q b' z,
        R ∩ coefficientPhysicalEntry (normalizedCoeff ρ) (parameterPiece ρ (β s) q b') (h s) z = ∅ ∨
        ENNReal.ofReal (h s / Ac s) * θ (parameterPiece ρ (β s) q b') <
          μ (R ∩ coefficientPhysicalEntry (normalizedCoeff ρ) (parameterPiece ρ (β s) q b') (h s) z) := by
  classical
  have hβρ (s : σ) : β s ≤ ρ := (hscale s).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hh₁ s) hρ.le)
  obtain ⟨P, hP, hPE, hmassP, hprior⟩ := exists_simultaneous_prior_intersection_cut θ μ hdom
    β hβ hβρ ηint hE htime
  obtain ⟨E₂, hE₂, hE₂P, hmass₂, hlong⟩ := exists_simultaneous_long_strip_cut θ μ hdom hP row
    hH hb hρ hρ₁ hbρ (fun s => ρ * h s) ηdur (fun s => mul_pos hρ (hh s)) hηdur
    (fun z hz => hcoeff z (hPE hz)) (fun z hz => htime z (hPE hz)) hA hD
    (fun z hz => hderiv z (hPE hz)) hvariation
  have hE₂E : E₂ ⊆ E := hE₂P.trans hPE
  have hcoef₂ : ∀ z ∈ E₂, ∀ e, |z.1.2 e| ≤ H := fun z hz => hcoeff z (hE₂E hz)
  have htime₂ : ∀ z ∈ E₂, z.2 ∈ Icc (0 : ℝ) 1 := fun z hz => htime z (hE₂E hz)
  have habstime₂ : ∀ z ∈ E₂, |z.2| ≤ 1 := by
    intro z hz
    rw [abs_of_nonneg (htime₂ z hz).1]
    exact (htime₂ z hz).2
  have hfstate := finite_original_physical_records E₂ hH hb hcoef₂ habstime₂
  have hfstrip (s : σ) : (stripRecord b ρ (ρ * h s) row '' E₂).Finite := by
    change ((fun z => stripLabel b ρ (ρ * h s) row (cell b (scalarPosition z))) '' E₂).Finite
    simpa only [image_image, Function.comp_def] using
      hfstate.image (stripLabel b ρ (ρ * h s) row)
  have hfpost (s : σ) : (posteriorEntryRecord ρ b (h s) '' E₂).Finite :=
    posteriorEntryRecord_finite E₂ hρ hb hH (h s) hcoef₂ habstime₂ (lists s)
      (fun z hz => hlisted s z (hE₂E hz))
  obtain ⟨R, hR, hRE₂, hmassR, hstatefloor, hstripfloor, hpostfloor, hcoefloor⟩ :=
    prepare_original_reference_floors μ oldGraph (μ.restrict P) θ π hρ (by linarith : 0 ≤ H)
      β h Ac hβ hscale hh hh₁ hAc
      (fun z => cell b (scalarPosition z)) (measurable_cell b measurable_scalarPosition)
      (fun s => stripRecord b ρ (ρ * h s) row) (fun s => measurable_stripRecord b ρ (ρ * h s) row)
      (fun s => posteriorEntryRecord ρ b (h s)) (fun s => measurable_posteriorEntryRecord ρ b (h s))
      lists Dpost ηstrip ηpost ηstate hlistcard hE₂ htime₂ hcoef₂ hfstate hfstrip hfpost
      (fun s z hz => hlisted s z (hE₂E hz))
  simp only [Measure.restrict_apply_univ] at hmassR
  have hstripsum : (∑ s, ηstrip s * μ P) ≤ ∑ s, ηstrip s * μ E :=
    Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (measure_mono hPE) zero_le)
  have hmassR' := hmassR.trans
    (add_le_add (add_le_add le_rfl (add_le_add hstripsum le_rfl)) le_rfl)
  have hRPE : R ⊆ P := hRE₂.trans hE₂P
  refine ⟨P, R, hP, hPE, hR, hRPE, ?_,
    (fun z hz => hprior z (hRPE hz)), (fun z hz => hlong z (hRE₂ hz)), hstatefloor, ?_,
    hpostfloor, hcoefloor⟩
  · have hcover : E \ R ⊆ (E \ P) ∪ ((P \ E₂) ∪ (E₂ \ R)) := by
      intro z hz
      by_cases hpP : z ∈ P
      · right
        by_cases hp₂ : z ∈ E₂
        · exact Or.inr ⟨hp₂, hz.2⟩
        · exact Or.inl ⟨hpP, hp₂⟩
      · exact Or.inl ⟨hz.1, hpP⟩
    calc
      μ (E \ R) ≤ μ ((E \ P) ∪ ((P \ E₂) ∪ (E₂ \ R))) := measure_mono hcover
      _ ≤ μ (E \ P) + (μ (P \ E₂) + μ (E₂ \ R)) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
      _ ≤ _ := add_le_add hmassP (add_le_add hmass₂ hmassR')
  · intro s q
    have heq : (μ.restrict P) (stripRecord b ρ (ρ * h s) row ⁻¹' {q}) =
        μ (P ∩ stripRecord b ρ (ρ * h s) row ⁻¹' {q}) := by
      rw [Measure.restrict_apply ((measurable_stripRecord b ρ (ρ * h s) row) (measurableSet_singleton q)),
        inter_comm]
    simpa only [heq] using hstripfloor s q

end

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
