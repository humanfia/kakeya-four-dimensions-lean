-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.EStages
import Submission.Obl.k4_stable_native_signal_oscillation

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory MvPolynomial
open Submission.Obl.k4_stable_native_signal_oscillation
open Submission.Obl.k4_quadratic_atlas_normalization

noncomputable section

/-- Native geometric points keep the original trajectory labels in their source. -/
def pointS {α : Type} (b : α → Fin 6 → ℝ) (p : α × ℝ) : NativePoint :=
  WithLp.toLp 2 (exS b p.1 p.2)

theorem measurable_pointS {α : Type} [MeasurableSpace α] {b : α → Fin 6 → ℝ}
    (hb : Measurable b) : Measurable (pointS b) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro i
  fin_cases i <;> simp [exS] <;> fun_prop

/-- The accepted quadratic oscillation partition applies on the unchanged
source probability, by pulling its groups back through the native point map. -/
theorem exists_native_partition_pullback (A : ℕ) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (Ω : Type) [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (point : Ω → NativePoint) (hp : Measurable point)
      (K a : ℝ) (P S : MvPolynomial (Fin 4) ℝ),
      2 ≤ K → 0 < a → a ≤ 1 → P.totalDegree ≤ 2 → S.totalDegree ≤ 2 →
      μ.map (nativeBase ∘ point) ≤ ENNReal.ofReal K • volume →
      (∀ᵐ p ∂μ, point p ∈ goodSet K a P S) →
      ∃ (n : ℕ) (E : Fin n → Set Ω), (n : ℝ) ≤ K ^ C ∧
        (∀ i, MeasurableSet (E i)) ∧
        (∀ i j, i ≠ j → Disjoint (E i) (E j)) ∧
        μ (⋃ i, E i)ᶜ ≤ ENNReal.ofReal ((K ^ A)⁻¹) ∧
        ∀ i p, p ∈ E i → ∀ q, q ∈ E i →
          |value S (point p) - value S (point q)| ≤
            K ^ C * (a + ‖nativeBase (point p) - nativeBase (point q)‖) := by
  obtain ⟨C, hC, hpartition⟩ := Submission.k4_stable_native_signal_oscillation A
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ _ point hp K a P S hK ha ha1 hP hS hbase hgood
  have hbase' : (μ.map point).map nativeBase ≤ ENNReal.ofReal K • volume := by
    rwa [Measure.map_map measurable_nativeBase hp]
  have hgood' : ∀ᵐ p ∂μ.map point, p ∈ goodSet K a P S :=
    (ae_map_iff hp.aemeasurable (measurableSet_goodSet K a P S)).mpr hgood
  have hjets : ∀ᵐ p ∂μ.map point, ‖nativeBase p‖ ≤ K ∧
      |eval (fun j => p j) P| ≤ K * a ∧
      K⁻¹ ≤ |eval (fun j => p j) (pderiv (3 : Fin 4) P)| ∧
      |eval (fun j => p j) (pderiv (3 : Fin 4) P)| ≤ K ∧
      |eval (fun j => p j) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P))| ≤ K / a ∧
      |eval (fun j => p j) S| ≤ K ∧
      |eval (fun j => p j) (pderiv (3 : Fin 4) S)| ≤ K ∧
      |eval (fun j => p j) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) S))| ≤ K := by
    simpa only [goodSet, value, Set.mem_ofPred_eq,
      second_pderiv_eq_curvature P hP 3, second_pderiv_eq_curvature S hS 3, eval_C] using hgood'
  obtain ⟨n, E, hn, hEm, hEd, hmass, hosc⟩ :=
    hpartition K a P S (μ.map point) hK ha ha1 hP hS inferInstance hbase' hjets
  refine ⟨n, fun i => point ⁻¹' E i, hn, fun i => hp (hEm i), ?_, ?_, ?_⟩
  · intro i j hij
    exact Set.disjoint_left.mpr fun p hpi hpj => Set.disjoint_left.mp (hEd i j hij) hpi hpj
  · have heq : μ (⋃ i, point ⁻¹' E i)ᶜ = (μ.map point) (⋃ i, E i)ᶜ := by
      rw [Measure.map_apply hp (MeasurableSet.iUnion hEm).compl,
        Set.preimage_compl, Set.preimage_iUnion]
    exact heq.symm ▸ hmass
  · intro i p hp q hq
    exact hosc i (point p) hp (point q) hq

end

end Submission.Obl.k4_finite_affine_parent_sources
