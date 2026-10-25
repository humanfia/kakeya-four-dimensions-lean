/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file OriginalMeshCore.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.ParameterRefinement
import Submission.Obl.k4_scalar_graph_residual_discovery.Assembly

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice

namespace ScalarData

noncomputable section

/-- One measurable conull core makes EVERY original preparation-mesh
physical pair and physical/coefficient entry containing a retained point
positive. There is no loss proportional to the preparation mesh size. -/
theorem exists_original_mesh_positive_core (D : ScalarData) (k M : ℕ)
    (μ : Measure ScalarIncidence) :
    ∃ C : Set ScalarIncidence, MeasurableSet C ∧ μ Cᶜ = 0 ∧
      (∀ r r₀ : ℝ, (∃ m : ℕ, r = (m : ℝ) / (M : ℝ)) →
        (∃ m : ℕ, r₀ = (m : ℝ) / (M : ℝ)) → ∀ z ∈ C,
          μ {p | D.phys k r p = D.phys k r z ∧ D.phys k r₀ p = D.phys k r₀ z} ≠ 0) ∧
      ∀ r : ℝ, (∃ m : ℕ, r = (m : ℝ) / (M : ℝ)) → ∀ z ∈ C,
        μ {p | D.phys k r p = D.phys k r z ∧ D.coeff k r p.1 = D.coeff k r z.1} ≠ 0 := by
  let pairs (ij : ℕ × ℕ) (p : ScalarIncidence) :=
    (D.phys k ((ij.1 : ℝ) / (M : ℝ)) p, D.phys k ((ij.2 : ℝ) / (M : ℝ)) p)
  let parameter (i : ℕ) (p : ScalarIncidence) :=
    (D.phys k ((i : ℝ) / (M : ℝ)) p, D.coeff k ((i : ℝ) / (M : ℝ)) p.1)
  have hpairs (ij : ℕ × ℕ) : Measurable (pairs ij) :=
    (D.measurable_phys k _).prodMk (D.measurable_phys k _)
  have hparameter (i : ℕ) : Measurable (parameter i) := by
    have hc : Measurable (fun p : ScalarIncidence =>
        cell (D.N k ^ (-((i : ℝ) / (M : ℝ)))) p.1.2) :=
      measurable_cell _ (measurable_snd.comp measurable_fst)
    exact (D.measurable_phys k _).prodMk hc
  let C := positiveRecordCore μ pairs ∩ positiveRecordCore μ parameter
  have hC : MeasurableSet C :=
    (measurableSet_positiveRecordCore μ pairs hpairs).inter
      (measurableSet_positiveRecordCore μ parameter hparameter)
  have hconull : μ Cᶜ = 0 := by
    have hh := (ae_mem_positiveRecordCore μ pairs).and (ae_mem_positiveRecordCore μ parameter)
    exact (ae_iff).mp hh
  refine ⟨C, hC, hconull, ?_, ?_⟩
  · intro r r₀ hr hr₀ z hz
    obtain ⟨i, hi⟩ := hr
    obtain ⟨j, hj⟩ := hr₀
    have hpos := hz.1 (i, j)
    have heq : pairs (i, j) ⁻¹' {pairs (i, j) z} =
        {p | D.phys k r p = D.phys k r z ∧ D.phys k r₀ p = D.phys k r₀ z} := by
      ext p
      simp only [mem_preimage, mem_singleton_iff, pairs, Prod.mk.injEq, mem_ofPred_eq, hi, hj]
    simpa only [heq] using hpos
  · intro r hr z hz
    obtain ⟨i, hi⟩ := hr
    have hpos := hz.2 i
    have heq : parameter i ⁻¹' {parameter i z} =
        {p | D.phys k r p = D.phys k r z ∧ D.coeff k r p.1 = D.coeff k r z.1} := by
      ext p
      simp only [mem_preimage, mem_singleton_iff, parameter, Prod.mk.injEq, mem_ofPred_eq, hi]
    simpa only [heq] using hpos

end

end ScalarData

end Submission.Obl.k4_scalar_graph_residual_discovery
