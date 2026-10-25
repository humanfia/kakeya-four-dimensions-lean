-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.OriginalParentInputs, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/OriginalParentInputs.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/OriginalParentInputs.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.ParentSignal
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Problem

/-! # Literal global-parent inputs for the physical gradient source -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set MvPolynomial Native

noncomputable section

/-- Every event in the original problem has original time in the unit block. -/
theorem original_event_time {d : ProblemData} (hd : d.Valid) (k : ℕ)
    (w : Fin (d.W k)) {z : Ev} (hz : z ∈ d.E k w) : z.2 ∈ Icc (0 : ℝ) 1 := by
  rcases hd with ⟨_, _, _, _, _, _, _, _, hformat, _⟩
  obtain ⟨M, D, hformat⟩ := hformat
  rcases (hformat k).2.2.2.1 w with ⟨_, _, _, _, _, _, _, _, htime, _⟩
  exact (htime hz).2

/-- Global parent data are extracted from the original problem, on every subsequent
source subset. Exceptional original lines are the only removed set. -/
theorem original_parent_source_inputs {d : ProblemData} (hd : d.Valid) (k : ℕ)
    (w : Fin (d.W k)) {K : ℝ} (hK : d.K k ≤ K) (H : Set Ev) (hH : H ⊆ d.E k w) :
    let P := d.P k w
    let G := ParentSignal.goodLines P (d.K k) (d.B k w)
    P.totalDegree ≤ 2 ∧ MeasurableSet G ∧ (∀ᵐ l ∂d.ν k w, l ∈ G) ∧
    (∀ z ∈ H, z.1 ∈ G →
      |eval (xp z.1 z.2) (pderiv 3 P)| ≤ K * d.B k w ∧
      |eval (xp z.1 z.2) (pderiv 3 (pderiv 3 P))| ≤ K * (d.B k w) ^ 2) ∧
    (∀ z ∈ H, ∀ z' ∈ H, z.1 ∈ G → z'.1 = z.1 →
      |eval (xp z'.1 z'.2) P - eval (xp z.1 z.2) P| ≤ 24 * K * |z'.2 - z.2|) := by
  have hpb : pb d.N d.K d.L d.d d.S d.η d.W d.ω d.ν d.E d.P d.B d.f d.g d.G := hd
  have hb := ParentSignal.original_parent_bounds hpb k w
  have hB : 0 < d.B k w := by
    rcases hd with ⟨_, _, _, _, _, _, _, _, hformat, _⟩
    obtain ⟨M, D, hformat⟩ := hformat
    exact ((hformat k).2.2.2.1 w).2.1
  refine ⟨hb.1, ParentSignal.measurableSet_goodLines _ _ _, hb.2.2.1, ?_, ?_⟩
  · intro z hz hgood
    have hj := hgood z.2 (original_event_time hd k w (hH hz))
    exact ⟨hj.2.1.trans (mul_le_mul_of_nonneg_right hK hB.le),
      hj.2.2.trans (mul_le_mul_of_nonneg_right hK (sq_nonneg _))⟩
  · intro z hz z' hz' hgood hline
    have hdiff := ParentSignal.signal_variation hb.1
      (fun t ht => (hgood t ht).1)
      (original_event_time hd k w (hH hz)) (original_event_time hd k w (hH hz'))
    rw [hline]
    exact hdiff.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hK (by norm_num)) (abs_nonneg _))

/-- Every nonnegative depth has dyadic width at most one. -/
theorem physical_parent_fine_width_le_one {N r : ℝ} (hN : 1 ≤ N) (hr : 0 ≤ r) :
    δ N r ≤ 1 := by
  unfold δ
  rw [← zpow_zero (2 : ℝ)]
  apply zpow_le_zpow_right₀ (by norm_num)
  have hf : (0 : ℤ) ≤ ⌊r * Real.log N / Real.log 2⌋ :=
    Int.floor_nonneg.mpr (div_nonneg (mul_nonneg hr (Real.log_nonneg hN))
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)
  omega

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
