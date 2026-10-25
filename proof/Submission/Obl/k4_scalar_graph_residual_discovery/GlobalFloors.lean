/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file GlobalFloors.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.ZoomEntryPreparation
import Submission.Obl.k4_scalar_graph_residual_discovery.RecordPruning

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Obl.k4_scalar_grid_parameter_preparation

namespace Zoom

noncomputable section

/-- Coefficient-entry floors and summable old-reference record floors
are restored by ONE pruning. Thus later restrictions do not invalidate
floors proved at an earlier intermediate stage. -/
theorem multiscale_zoom_entry_and_record_floors {σ ι Q : Type*}
    [Fintype σ] [Fintype ι] [MeasurableSpace Q]
    [MeasurableSingletonClass Q] [Countable Q]
    (n : σ → ℕ) (μ : Measure ScalarIncidence) (θ : Measure ScalarLine)
    {ρ : ℝ} (hρ : 0 < ρ) (β h A : σ → ℝ)
    (hβ : ∀ s, 0 < β s) (hscale : ∀ s, β s ≤ ρ * h s)
    (hh : ∀ s, 0 < h s) (hh₁ : ∀ s, h s ≤ 1) (hA : ∀ s, 0 < A s)
    (q b : (s : σ) → Fin (n s) → Fin 5 → ℤ)
    (hinj : ∀ s, Function.Injective (fun j => (q s j, b s j)))
    (record : ι → ScalarIncidence → Q) (hrecord : ∀ i, Measurable (record i))
    (old : ι → Q → ℝ≥0∞) (η B : ι → ℝ≥0∞)
    (hbudget : ∀ i, (∑' c, old i c) ≤ B i)
    {E : Set ScalarIncidence} (hE : MeasurableSet E)
    (htime : ∀ p ∈ E, p.2 ∈ Icc (0 : ℝ) 1)
    (hfinite : ∀ i, (record i '' E).Finite) :
    ∃ R : Set ScalarIncidence, MeasurableSet R ∧ R ⊆ E ∧
      μ (E \ R) ≤ (∑ i, η i * B i) +
        (∑ s, ENNReal.ofReal ((5000 * 111 ^ 3) / A s)) * θ univ ∧
      (∀ i c, R ∩ record i ⁻¹' {c} = ∅ ∨
        η i * old i c < μ (R ∩ record i ⁻¹' {c})) ∧
      ∀ s j z,
        R ∩ coefficientPhysicalEntry (normalizedCoeff ρ)
          (parameterPiece ρ (β s) (q s j) (b s j)) (h s) z = ∅ ∨
        ENNReal.ofReal (h s / A s) * θ (parameterPiece ρ (β s) (q s j) (b s j)) <
          μ (R ∩ coefficientPhysicalEntry (normalizedCoeff ρ)
            (parameterPiece ρ (β s) (q s j) (b s j)) (h s) z) := by
  classical
  let L (i : ι) := (hfinite i).toFinset
  let J := Σ i, L i
  let F (j : J) : Set ScalarIncidence := record j.1 ⁻¹' {j.2.1}
  let τ (j : J) := η j.1 * old j.1 j.2.1
  have hF (j : J) : MeasurableSet (F j) := hrecord j.1 (measurableSet_singleton _)
  obtain ⟨R, hR, hRE, hmass, hrecords, hcoeff⟩ :=
    multiscale_zoom_entry_and_floors n μ θ hρ β h A hβ hscale hh hh₁ hA q b hinj
      F hF τ hE htime
  have hsum : (∑ j : J, τ j) ≤ ∑ i, η i * B i := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_le_sum
    intro i _
    dsimp only [τ]
    rw [Finset.sum_coe_sort (L i) (fun c => η i * old i c)]
    exact (ENNReal.sum_le_tsum (L i)).trans (by
      rw [ENNReal.tsum_mul_left]
      exact mul_le_mul_of_nonneg_left (hbudget i) zero_le)
  refine ⟨R, hR, hRE, hmass.trans (add_le_add hsum le_rfl), ?_, hcoeff⟩
  intro i c
  by_cases hc : c ∈ L i
  · exact hrecords ⟨i, ⟨c, hc⟩⟩
  · left
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hcode : record i p = c := hp.2
    apply hc
    exact (hfinite i).mem_toFinset.mpr ⟨p, hRE hp.1, hcode⟩

end

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
