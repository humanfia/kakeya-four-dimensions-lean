-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Velocity.MeasureBasis, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Velocity/MeasureBasis.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Velocity/MeasureBasis.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit d78c43c7c261;
-- source Submission/Obl/k4_isotropic_path_improvement/MeasureBasis.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Filling.DeterminantBreadth
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry.PlaneGraph

/-!
Spanning witnesses remain available after a small original-law loss.
The source can be any finite measure space, with no atomicity assumption.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity

open MeasureTheory Set Module
open SourceGeometry
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Filling

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- Renew a quantitatively transverse tuple inside a captured set. The
loss budget uses the original measure, rather than a normalized conditional. -/
theorem exists_good_tuple_after_loss {d : ℕ}
    (μ : Measure X) [IsFiniteMeasure μ] (e : X → EuclideanSpace ℝ (Fin d))
    (ρ c : ℝ) (Q : Set X) (hQ : μ.real Qᶜ < c * μ.real univ)
    (hbroad : ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin d)), finrank ℝ V < d →
      c * μ.real univ ≤ μ.real {x | ρ ≤ Metric.infDist (e x) (V : Set _)}) :
    ∃ T : Fin d → X, (∀ i, T i ∈ Q) ∧ Breadth.Good e ρ T := by
  classical
  have hstep : ∀ k : ℕ, k ≤ d →
      ∃ T : Fin k → X, (∀ i, T i ∈ Q) ∧ Breadth.Good e ρ T := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨Fin.elim0, (fun i => Fin.elim0 i), (fun i => Fin.elim0 i)⟩
    | succ k ih =>
      intro hk
      obtain ⟨T, hTQ, hT⟩ := ih (by omega)
      let V := Submodule.span ℝ (Set.range fun i => e (T i))
      have hV : finrank ℝ V < d := by
        have h := finrank_range_le_card (R := ℝ) (fun i => e (T i))
        simp only [Fintype.card_fin] at h
        exact h.trans_lt (by omega)
      have hex : ∃ x ∈ Q, ρ ≤ Metric.infDist (e x) (V : Set _) := by
        by_contra hno
        have hsub : {x | ρ ≤ Metric.infDist (e x) (V : Set _)} ⊆ Qᶜ := by
          intro x hx hqx
          exact hno ⟨x, hqx, hx⟩
        have hle := (hbroad V hV).trans (measureReal_mono hsub)
        exact (not_lt_of_ge hle) hQ
      obtain ⟨x, hxQ, hx⟩ := hex
      refine ⟨Fin.snoc T x, ?_, (Breadth.good_snoc_iff e ρ T x).mpr ⟨hT, hx⟩⟩
      intro i
      induction i using Fin.lastCases with
      | last => simpa only [Fin.snoc_last] using hxQ
      | cast i => simpa only [Fin.snoc_castSucc] using hTQ i
  exact hstep d le_rfl

/-- The renewed actual witnesses have a determinant at least `rho^d`. -/
theorem exists_determinant_tuple_after_loss {d : ℕ}
    (μ : Measure X) [IsFiniteMeasure μ] (e : X → EuclideanSpace ℝ (Fin d))
    (ρ c : ℝ) (hρ : 0 ≤ ρ) (Q : Set X) (hQ : μ.real Qᶜ < c * μ.real univ)
    (hbroad : ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin d)), finrank ℝ V < d →
      c * μ.real univ ≤ μ.real {x | ρ ≤ Metric.infDist (e x) (V : Set _)}) :
    ∃ T : Fin d → X, (∀ i, T i ∈ Q) ∧
      ρ ^ d ≤ |(Matrix.of fun i j : Fin d => e (T i) j).det| := by
  obtain ⟨T, hTQ, hT⟩ := exists_good_tuple_after_loss μ e ρ c Q hQ hbroad
  refine ⟨T, hTQ, ?_⟩
  have hprod := Finset.prod_le_prod₀ (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hρ)
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hT i)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
  exact hprod.trans (Breadth.abs_det_ge_prod_infDist d (fun i => e (T i)))

/-- Base breadth renews a basis inside the plane's captured fraction, so the
nearby plane gives an actual bounded scalar velocity row on that fraction. -/
theorem exists_row_on_captured_broad_law
    (μ : Measure X) [IsFiniteMeasure μ]
    (e : X → EuclideanSpace ℝ (Fin 3)) (w : X → ℝ)
    (ρ c K ε : ℝ) (hρ : 0 ≤ ρ) (hK : 1 ≤ K) (hε : 0 ≤ ε)
    (Q : Set X) (hQ : μ.real Qᶜ < c * μ.real univ)
    (hbroad : ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 3)), finrank ℝ V < 3 →
      c * μ.real univ ≤ μ.real {x | ρ ≤ Metric.infDist (e x) (V : Set _)})
    (he : ∀ x ∈ Q, ∀ j, |e x j| ≤ K) (hw : ∀ x ∈ Q, |w x| ≤ K)
    (hcondition : 1 ≤ K * ρ ^ 3)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin 4))) (hV : finrank ℝ V < 4)
    (hnear : ∀ x ∈ Q, Metric.infDist (liftedVector (e x) (w x)) (V : Set _) ≤ ε)
    (hsmall : 36 * K ^ 3 * ε ≤ 1) :
    ∃ G : Fin 3 → ℝ, (∀ j, |G j| ≤ 28 * K ^ 6) ∧
      ∀ x ∈ Q, |w x - ∑ j, G j * e x j| ≤ 80 * K ^ 6 * ε := by
  obtain ⟨T, hTQ, hdet⟩ := exists_determinant_tuple_after_loss μ e ρ c hρ Q hQ hbroad
  let A : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j => e (T i) j
  have hK0 : 0 ≤ K := by linarith
  have hd : 1 ≤ K * |A.det| := hcondition.trans (mul_le_mul_of_nonneg_left hdet hK0)
  obtain ⟨G, hG, hres⟩ := subspace_graph_row V hV A (fun i => w (T i)) K ε hK hε
    (fun i j => he (T i) (hTQ i) j) hd (fun i => hw (T i) (hTQ i))
    (fun i => hnear (T i) (hTQ i)) hsmall
  refine ⟨G, hG, ?_⟩
  intro x hx
  exact (hres (e x) (w x)).trans (mul_le_mul_of_nonneg_left (hnear x hx) (by positivity))

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
