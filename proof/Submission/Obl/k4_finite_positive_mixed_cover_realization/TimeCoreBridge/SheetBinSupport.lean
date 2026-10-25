-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/SheetBinSupport.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/SheetBinSupport.lean (namespace renamed).

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.ObservationSheets

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open Set MeasureTheory Metric

/-- A sheet's closed hidden-bin support is measurable despite its holomorphy being
local. Only values on the comparison half-ball are used. -/
theorem measurableSet_sheet_bin_bounds {D : ℕ} {X : Type*} [MeasurableSpace X]
    (F : RealSheet D) (base : X → Real3) (hb : Measurable base)
    (bin : X → ℤ) (hbin : Measurable bin) (δ η : ℝ) :
    MeasurableSet {o | ‖base o‖ ≤ (1 : ℝ) / 2 ∧
      δ * (bin o : ℝ) - η ≤ (F.f (emb (base o))).re ∧
      (F.f (emb (base o))).re ≤ δ * ((bin o : ℝ) + 1) + η} := by
  have hmaps : MapsTo emb (closedBall (0 : Real3) (1 / 2)) (ball (0 : Complex3) 4) := by
    intro x hx
    rw [mem_ball_zero_iff, emb.norm_map]
    have hh := mem_closedBall_zero_iff.mp hx
    linarith
  have hcont : ContinuousOn (fun x : Real3 => (F.f (emb x)).re) (closedBall 0 (1 / 2)) :=
    Complex.continuous_re.comp_continuousOn
      (F.holomorphic.continuousOn.comp emb.continuous.continuousOn hmaps)
  let A (k : ℤ) : Set Real3 := {x | ‖x‖ ≤ (1 : ℝ) / 2 ∧
    δ * (k : ℝ) - η ≤ (F.f (emb x)).re ∧ (F.f (emb x)).re ≤ δ * ((k : ℝ) + 1) + η}
  have hA (k : ℤ) : MeasurableSet (A k) := by
    have hlo : MeasurableSet {x : Real3 | x ∈ closedBall 0 (1 / 2) ∧
        δ * (k : ℝ) - η ≤ (F.f (emb x)).re} :=
      (isClosed_closedBall.isClosed_le continuousOn_const hcont).measurableSet
    have hhi : MeasurableSet {x : Real3 | x ∈ closedBall 0 (1 / 2) ∧
        (F.f (emb x)).re ≤ δ * ((k : ℝ) + 1) + η} :=
      (isClosed_closedBall.isClosed_le hcont continuousOn_const).measurableSet
    have he : A k =
        {x : Real3 | x ∈ closedBall 0 (1 / 2) ∧ δ * (k : ℝ) - η ≤ (F.f (emb x)).re} ∩
        {x : Real3 | x ∈ closedBall 0 (1 / 2) ∧ (F.f (emb x)).re ≤ δ * ((k : ℝ) + 1) + η} := by
      ext x
      simp only [A, mem_ofPred_eq, mem_inter_iff, mem_closedBall_zero_iff]
      tauto
    rw [he]
    exact hlo.inter hhi
  let S : Set (Real3 × ℤ) := {q | ‖q.1‖ ≤ (1 : ℝ) / 2 ∧
    δ * (q.2 : ℝ) - η ≤ (F.f (emb q.1)).re ∧ (F.f (emb q.1)).re ≤ δ * ((q.2 : ℝ) + 1) + η}
  have hS : MeasurableSet S := by
    have he : S = ⋃ k : ℤ, A k ×ˢ ({k} : Set ℤ) := by
      ext q
      simp only [S, mem_ofPred_eq, mem_iUnion, mem_prod, mem_singleton_iff]
      constructor
      · intro hq
        exact ⟨q.2, hq, rfl⟩
      · rintro ⟨k, hk, hq⟩
        simpa only [A, hq, Set.mem_ofPred_eq] using hk
    rw [he]
    exact MeasurableSet.iUnion fun k => (hA k).prod (measurableSet_singleton k)
  have he : {o : X | ‖base o‖ ≤ (1 : ℝ) / 2 ∧
      δ * (bin o : ℝ) - η ≤ (F.f (emb (base o))).re ∧
      (F.f (emb (base o))).re ≤ δ * ((bin o : ℝ) + 1) + η} =
        (fun o => (base o, bin o)) ⁻¹' S := by
    ext o
    rfl
  rw [he]
  exact hS.preimage (hb.prodMk hbin)

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
