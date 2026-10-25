-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.CoefficientRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.CoefficientCover

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

/-- Refine a coefficient cluster to any fixed relative diameter. The
number of pieces depends only on that relative diameter, uniformly in
both the coefficient scale and the cardinality of the original family. -/
theorem exists_coefficient_refinement {n : ℕ}
    (F : Finset (Fin n)) (q : Fin n → EuclideanSpace ℝ (Fin 3)) {D θ : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hdiam : ∀ i ∈ F, ∀ j ∈ F, dist (q i) (q j) ≤ D) :
    ∃ k : ℕ, (k:ℝ) ≤ 27648/θ^3 ∧ ∃ G : Fin k → Finset (Fin n),
      (∀ a, G a ⊆ F) ∧ (∀ a, (G a).Nonempty) ∧
      (∀ i ∈ F, ∃ a, i ∈ G a) ∧
      (∀ a, ∀ i ∈ G a, ∀ j ∈ G a, dist (q i) (q j) ≤ θ*D) := by
  classical
  have hρ : 0 < θ*D/2 := by positivity
  have hρD : θ*D/2 ≤ D := by nlinarith [mul_nonneg hD.le (sub_nonneg.mpr hθ1)]
  obtain ⟨C, hCF, hcard, hcover⟩ := exists_coefficient_cluster_cover F q hρ hρD hdiam
  let e := (Finset.equivFin C).symm
  let G : Fin C.card → Finset (Fin n) := fun a =>
    F.filter (fun i => dist (q i) (e a) ≤ θ*D/2)
  refine ⟨C.card, ?_, G, ?_, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ (pow_pos hθ 3)).mpr
    apply (mul_le_mul_iff_left₀ (pow_pos hD 3)).mp
    nlinarith only [hcard]
  · intro a
    exact Finset.filter_subset _ _
  · intro a
    obtain ⟨i, hi, hqi⟩ := Finset.mem_image.mp (hCF (e a).property)
    refine ⟨i, Finset.mem_filter.mpr ⟨hi, ?_⟩⟩
    rw [hqi, dist_self]
    exact hρ.le
  · intro i hi
    obtain ⟨c, hc, hci⟩ := hcover i hi
    refine ⟨e.symm ⟨c, hc⟩, Finset.mem_filter.mpr ⟨hi, ?_⟩⟩
    simpa only [Equiv.apply_symm_apply] using hci
  · intro a i hi j hj
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    have ht := dist_triangle (q i) (e a) (q j)
    rw [dist_comm (e a : EuclideanSpace ℝ (Fin 3)) (q j)] at ht
    linarith

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
