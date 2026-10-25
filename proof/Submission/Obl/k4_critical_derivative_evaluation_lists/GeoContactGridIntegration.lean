import Submission.Obl.k4_critical_derivative_evaluation_lists.GeoContactGrid

/- Adapted from this LOT tree, obligation o107, session x0353, commit 96bcaa7b51cc,
   file Submission/Obl/k4_finite_narrowness_path_improvement/ContactGridIntegration.lean (namespace and imports renamed only). -/

/-! Integrating original cell ceilings over a contact rectangle. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

theorem contactGrid_count_volume_le {δ : ℝ} (hδ : 0 < δ)
    (F : Finset (Fin 3 → ℤ)) (E : Set (Fin 3 → ℝ))
    (hsub : ∀ j ∈ F, contactGridCell δ j ⊆ E) :
    ENNReal.ofReal ((F.card : ℝ) * δ ^ 3) ≤ volume E := by
  have hu : (⋃ j ∈ F, contactGridCell δ j) ⊆ E := by
    intro q hq
    rcases Set.mem_iUnion₂.mp hq with ⟨j, hj, hq⟩
    exact hsub j hj hq
  have hvol := measure_mono (μ := (volume : Measure (Fin 3 → ℝ))) hu
  rw [measure_biUnion_finset (fun j _ k _ hjk => contactGridCell_disjoint δ hjk)
    (fun j _ => measurableSet_contactGridCell δ j)] at hvol
  simp only [volume_contactGridCell hδ, Finset.sum_const, nsmul_eq_mul] at hvol
  rwa [ENNReal.ofReal_mul (Nat.cast_nonneg F.card), ENNReal.ofReal_natCast]

theorem contactGridCell_subset_doubled_box {m H A B K δ : ℝ} {p : Fin 3 → ℝ}
    (hK : 1 ≤ K) (hδ : 0 < δ) (hδH : δ ≤ H / 2)
    (hδA : 2 * K * δ ≤ A) (hδB : 3 * K * δ ≤ B)
    (hm : |m| ≤ 1) (hv : |p 2| ≤ K) (hcenter : |p 0 + m * p 2| ≤ K)
    {j : Fin 3 → ℤ} {r : Fin 3 → ℝ} (hr : r ∈ contactGridCell δ j)
    (hrbox : r ∈ contactOuterBox m p H A B) :
    contactGridCell δ j ⊆ contactOuterBox m p (2 * H) (2 * A) (2 * B) := by
  intro q hq
  have hrb := (mem_contactOuterBox_iff _ _ _ _ _ _).mp hrbox
  have hgap := contactCoordinates_mesh_gap m K δ p q r hK hm hv hcenter
    (contactGridCell_coordinate_gap hδ hq hr)
  apply (mem_contactOuterBox_iff _ _ _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · have ht := abs_sub_le (q 0) (r 0) m
    linarith [contactGridCell_coordinate_gap hδ hq hr 0, hrb.1]
  · have hZ := abs_sub_le (q 1 - referenceZ p (q 0)) (r 1 - referenceZ p (r 0)) 0
    simp only [sub_zero] at hZ
    linarith [hgap.1, hrb.2.1]
  · have hY := abs_sub_le (contactTransverse m p q) (contactTransverse m p r) 0
    simp only [sub_zero] at hY
    linarith [hgap.2, hrb.2.2]

/-- A time-horizontal cell of widths H and A with transverse range B costs
O(H*A*B/delta^3) original fine cells. The fine mesh can be chosen afterwards. -/
theorem contactGrid_count_rectangle {m H A B K δ : ℝ} {p : Fin 3 → ℝ}
    (hH : 0 ≤ H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hK : 1 ≤ K) (hδ : 0 < δ) (hδH : δ ≤ H / 2)
    (hδA : 2 * K * δ ≤ A) (hδB : 3 * K * δ ≤ B)
    (hm : |m| ≤ 1) (hv : |p 2| ≤ K) (hcenter : |p 0 + m * p 2| ≤ K)
    (F : Finset (Fin 3 → ℤ))
    (hF : ∀ j ∈ F, (contactGridCell δ j ∩ contactOuterBox m p H A B).Nonempty) :
    (F.card : ℝ) * δ ^ 3 ≤ 32 * H * A * B := by
  have hcount := contactGrid_count_volume_le hδ F (contactOuterBox m p (2 * H) (2 * A) (2 * B))
    (by
      intro j hj
      rcases hF j hj with ⟨r, hr, hrbox⟩
      exact contactGridCell_subset_doubled_box hK hδ hδH hδA hδB hm hv hcenter hr hrbox)
  rw [volume_contactOuterBox _ _ _ _ _ (by positivity) (by positivity) (by positivity)] at hcount
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity :
    0 ≤ 4 * (2 * H) * (2 * A) * (2 * B))).mp hcount
  convert hreal using 1 <;> ring

end

end Submission.Obl.k4_critical_derivative_evaluation_lists
