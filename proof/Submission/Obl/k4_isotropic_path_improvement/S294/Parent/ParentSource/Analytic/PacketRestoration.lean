-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Analytic.PacketRestoration, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Analytic/PacketRestoration.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/PacketRestoration.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/PacketRestoration.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/PacketRestoration.lean
-- Earlier source attributions below are retained.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.RestoredBounds
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.WitnessExtension

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

noncomputable section

open MvPolynomial MeasureTheory

/-- One common loss controls quadratic values and affine hidden derivatives. -/
def restorationRemezFactor (η : ℝ) : ℝ := (24 / η) ^ 2

lemma restorationRemezFactor_bounds {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    1 ≤ restorationRemezFactor η ∧ 16 / η ≤ restorationRemezFactor η := by
  have h24 : 24 ≤ (24 : ℝ) / η := (le_div_iff₀ hη).mpr (by linarith)
  have h16 : (16 : ℝ) / η ≤ 24 / η := by gcongr; norm_num
  dsimp [restorationRemezFactor]
  constructor <;> nlinarith

/-- Restoration on long witnesses supplies all whole-block upper bounds, while
its lower derivative is retained on the counted observations themselves. -/
theorem restore_packet_bounds {C : ℕ} (D : LocalBranchData C)
    (Q : Poly) (hQ : D.restored Q) (c : Fin 3 → ℝ)
    (M : Matrix (Fin 3) (Fin 3) ℝ) {B K η : ℝ} (hB : 0 < B)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hbudget : restorationRemezFactor η * D.A ^ C ≤ K)
    (a v : Fin 4 → ℝ) (S : Set ℝ) (hS : S ⊆ Set.Icc (0 : ℝ) 1)
    (hmass : ENNReal.ofReal η ≤ volume S)
    (hwitness : ∀ t ∈ S,
      pointOfCoordinates (coordinateMap c M B (fun i => a i + t * v i)) ∈ D.region) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      |eval (fun i => a i + t * v i) (transportPolynomial c M B Q)| ≤ K * D.b ∧
      |eval (fun i => a i + t * v i) (pderiv 3 (transportPolynomial c M B Q))| ≤ K * B ∧
      |eval (fun i => a i + t * v i) (pderiv 3 (pderiv 3 (transportPolynomial c M B Q)))| ≤
        K * B ^ 2 / D.b) ∧
    (∀ x : Fin 4 → ℝ, pointOfCoordinates (coordinateMap c M B x) ∈ D.region →
      B / K ≤ |eval x (pderiv 3 (transportPolynomial c M B Q))|) := by
  have hA : 0 < D.A := lt_of_lt_of_le (by norm_num) D.two_le_A
  have hb : 0 < D.b := D.b_pos
  have hAC : 0 < D.A ^ C := pow_pos hA C
  obtain ⟨hfac, hfac16⟩ := restorationRemezFactor_bounds hη hη1
  have hlocal : D.A ^ C ≤ K := by
    exact (le_mul_of_one_le_left hAC.le hfac).trans hbudget
  let R := transportPolynomial c M B Q
  have hdeg : R.totalDegree ≤ 2 :=
    (totalDegree_transportPolynomial_le _ _ _ _).trans hQ.1
  have hpoint (t : ℝ) (ht : t ∈ S) :=
    restored_bounds_in_original_coordinates D Q hQ c M (K := D.A ^ C)
      hB (le_refl _) _ (hwitness t ht)
  have hvalue := affine_trajectory_witness_extension a v R hdeg S hη hη1
    (by positivity : 0 ≤ D.A ^ C * D.b) hS hmass (fun t ht => (hpoint t ht).1)
  have hderiv := quadratic_hidden_derivative_witness_extension a v R hdeg S hη hη1
    (by positivity : 0 ≤ D.A ^ C * B) hS hmass (fun t ht => (hpoint t ht).2.2.1)
  have hcurv := quadratic_hidden_curvature_witness_extension a v R hdeg S hη hη1
    (by positivity : 0 ≤ D.A ^ C * B ^ 2 / D.b) hS hmass (fun t ht => (hpoint t ht).2.2.2)
  constructor
  · intro t ht
    refine ⟨?_, ?_, ?_⟩
    · calc
        |eval (fun i => a i + t * v i) R|
            ≤ restorationRemezFactor η * (D.A ^ C * D.b) := by
          convert hvalue t ht using 1 <;> norm_num [restorationRemezFactor]
        _ = (restorationRemezFactor η * D.A ^ C) * D.b := by ring
        _ ≤ K * D.b := mul_le_mul_of_nonneg_right hbudget D.b_pos.le
    · calc
        |eval (fun i => a i + t * v i) (pderiv 3 R)|
            ≤ (16 / η) * (D.A ^ C * B) := hderiv t ht
        _ ≤ restorationRemezFactor η * (D.A ^ C * B) :=
          mul_le_mul_of_nonneg_right hfac16 (by positivity)
        _ = (restorationRemezFactor η * D.A ^ C) * B := by ring
        _ ≤ K * B := mul_le_mul_of_nonneg_right hbudget hB.le
    · exact (hcurv t ht).trans (by gcongr)
  · intro x hx
    exact (restored_bounds_in_original_coordinates D Q hQ c M hB hlocal x hx).2.1

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
