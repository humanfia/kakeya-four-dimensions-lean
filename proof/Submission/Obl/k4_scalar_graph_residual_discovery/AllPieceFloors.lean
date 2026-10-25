/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file AllPieceFloors.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.GlobalFloors
import Submission.Obl.k4_scalar_graph_residual_discovery.FiniteRecords

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice
open Submission.Obl.k4_scalar_grid_parameter_preparation

namespace Zoom

noncomputable section

/-- Restore entries for ALL original coarse/fine coefficient boxes and
all old-reference record systems in ONE final law. The finite box family
is constructed from the actual bounded original incidences, and its size
does not enter the deletion budget. -/
theorem global_entry_and_reference_floors {σ ι Q : Type*}
    [Fintype σ] [Fintype ι] [MeasurableSpace Q]
    [MeasurableSingletonClass Q] [Countable Q]
    (μ : Measure ScalarIncidence) (θ : Measure ScalarLine)
    {ρ H : ℝ} (hρ : 0 < ρ) (hH : 0 ≤ H) (β h A : σ → ℝ)
    (hβ : ∀ s, 0 < β s) (hscale : ∀ s, β s ≤ ρ * h s)
    (hh : ∀ s, 0 < h s) (hh₁ : ∀ s, h s ≤ 1) (hA : ∀ s, 0 < A s)
    (record : ι → ScalarIncidence → Q) (hrecord : ∀ i, Measurable (record i))
    (old : ι → Q → ℝ≥0∞) (η B : ι → ℝ≥0∞)
    (hbudget : ∀ i, (∑' c, old i c) ≤ B i)
    {E : Set ScalarIncidence} (hE : MeasurableSet E)
    (htime : ∀ p ∈ E, p.2 ∈ Icc (0 : ℝ) 1)
    (hcoeff : ∀ p ∈ E, ∀ e, |p.1.2 e| ≤ H)
    (hfinite : ∀ i, (record i '' E).Finite) :
    ∃ R : Set ScalarIncidence, MeasurableSet R ∧ R ⊆ E ∧
      μ (E \ R) ≤ (∑ i, η i * B i) +
        (∑ s, ENNReal.ofReal ((5000 * 111 ^ 3) / A s)) * θ univ ∧
      (∀ i c, R ∩ record i ⁻¹' {c} = ∅ ∨
        η i * old i c < μ (R ∩ record i ⁻¹' {c})) ∧
      ∀ s q b z,
        R ∩ coefficientPhysicalEntry (normalizedCoeff ρ)
          (parameterPiece ρ (β s) q b) (h s) z = ∅ ∨
        ENNReal.ofReal (h s / A s) * θ (parameterPiece ρ (β s) q b) <
          μ (R ∩ coefficientPhysicalEntry (normalizedCoeff ρ)
            (parameterPiece ρ (β s) q b) (h s) z) := by
  classical
  let P (s : σ) : Set ((Fin 5 → ℤ) × (Fin 5 → ℤ)) :=
    (fun p : ScalarIncidence => (cell ρ p.1.2, cell (β s) p.1.2)) '' E
  have hP (s : σ) : (P s).Finite := by
    have hcoarse := finite_original_coefficient_records E hH hρ hcoeff
    have hfine := finite_original_coefficient_records E hH (hβ s) hcoeff
    apply (hcoarse.prod hfine).subset
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩
  letI (s : σ) : Fintype (P s) := (hP s).fintype
  let n (s : σ) := Fintype.card (P s)
  let e (s : σ) : Fin (n s) ≃ P s := (Fintype.equivFin (P s)).symm
  let coarse (s : σ) (j : Fin (n s)) := (e s j).1.1
  let fine (s : σ) (j : Fin (n s)) := (e s j).1.2
  have hinj (s : σ) : Function.Injective (fun j => (coarse s j, fine s j)) := by
    intro j j' hj
    apply (e s).injective
    apply Subtype.ext
    exact hj
  obtain ⟨R, hR, hRE, hmass, hrecords, hentries⟩ :=
    multiscale_zoom_entry_and_record_floors n μ θ hρ β h A hβ hscale hh hh₁ hA
      coarse fine hinj record hrecord old η B hbudget hE htime hfinite
  refine ⟨R, hR, hRE, hmass, hrecords, ?_⟩
  intro s q b z
  by_cases hpair : (q, b) ∈ P s
  · let j : Fin (n s) := (e s).symm ⟨(q, b), hpair⟩
    have hcoarse : coarse s j = q := by
      exact congrArg (fun a : P s => a.1.1) ((e s).apply_symm_apply ⟨(q, b), hpair⟩)
    have hfine : fine s j = b := by
      exact congrArg (fun a : P s => a.1.2) ((e s).apply_symm_apply ⟨(q, b), hpair⟩)
    simpa only [hcoarse, hfine] using hentries s j z
  · left
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    apply hpair
    exact ⟨p, hRE hp.1, Prod.ext hp.2.1.1 hp.2.1.2⟩

end

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
