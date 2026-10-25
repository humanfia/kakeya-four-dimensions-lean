-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.FactoredFineBall.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.FineBall
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.Structure
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file FactoredFineBall.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set

/-- `factored_fine_prism` with the fine estimate of o065: every occupied prism packet of a
factored family of tubes in the unit ball, for `a ≤ 1/100`. -/
theorem factored_fine_prism_ball {σ ω : ℝ} (hFine : FinePrismEstimateBall σ ω)
    (e : ℝ) (he : 0 < e) :
    ∃ A : ℝ, 0 < A ∧ ∃ η : ℝ, 0 < η ∧ ∃ d : ℝ, 0 < d ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d → ∀ a b : ℝ, δ ≤ a → a ≤ b → b ≤ 1 → a ≤ 1 / 100 →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space), 0 < n →
    (∀ i, ‖v i‖ = 1) → (∀ i, tube δ (x i) (v i) ⊆ Metric.ball 0 1) →
    (∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) →
    (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
    (∀ i, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ volume (Y i)) →
    ∀ (p : ℕ) (c e₁ e₂ e₃ : Fin p → Space),
    (∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j]) →
    Factored (δ ^ (-η)) b (fun i => tube δ (x i) (v i))
      (fun j => prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) →
    ∀ j, ENNReal.ofReal (A * δ ^ e * (δ / a) ^ ω *
      ((Set.ncard {i | tube δ (x i) (v i) ⊆ prism a b (c j) (e₁ j) (e₂ j) (e₃ j)} : ℝ) *
        (δ ^ 2 / (a * b)) ^ 2) ^ (σ / 2)) *
      volume (prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) ≤
      volume (prism a b (c j) (e₁ j) (e₂ j) (e₃ j) ∩ ⋃ i, Y i) := by
  classical
  obtain ⟨A, hA, η, hη, d, hd, hlocal⟩ := hFine e he
  refine ⟨A, hA, η, hη, d, hd, ?_⟩
  intro δ hδ hδd a b hδa hab hb ha100 n x v Y hn hv hball hover hYm hYT hden p c e₁ e₂ e₃
    he hf j
  let P := prism a b (c j) (e₁ j) (e₂ j) (e₃ j)
  let S := {i | tube δ (x i) (v i) ⊆ P}
  let g : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  have hS : 0 < Fintype.card S := by
    rw [Set.fintypeCard_eq_ncard]
    exact hf.count_pos hn j
  have hcount (U : Set Space) (hU : Convex ℝ U) :
      ENNReal.ofReal (Set.ncard {i | tube δ (x (g i)) (v (g i)) ⊆ U} : ℝ) * volume P ≤
        ENNReal.ofReal (δ ^ (-η) * Fintype.card S) * volume U := by
    have hcard : Set.ncard {i | tube δ (x (g i)) (v (g i)) ⊆ U} =
        Set.ncard {i | tube δ (x i) (v i) ⊆ P ∧ tube δ (x i) (v i) ⊆ U} := by
      calc
        _ = Set.ncard {i : S | tube δ (x i) (v i) ⊆ U} :=
          Set.ncard_preimage_of_injective_subset_range g.injective
            (by simp [g.surjective.range_eq])
        _ = Set.ncard ({i | tube δ (x i) (v i) ⊆ U} ∩ S) :=
          Set.ncard_subtype (fun i => tube δ (x i) (v i) ⊆ P)
            {i | tube δ (x i) (v i) ⊆ U}
        _ = _ := by congr 1; ext i; exact and_comm
    rw [hcard, Set.fintypeCard_eq_ncard]
    exact hf.2.2.2.1 j U hU
  have hbound := hlocal δ a b hδ hδd hδa hab hb ha100 (c j) (e₁ j) (e₂ j) (e₃ j) (he j)
    (Fintype.card S) (fun i => x (g i)) (fun i => v (g i)) (fun i => Y (g i)) hS
    (fun i => hv (g i)) (fun i => hball (g i)) (fun i => (g i).property)
    (fun i k hik => hover (g i) (g k) (by
      intro heq
      exact hik (g.injective (Subtype.ext heq))))
    (fun i => hYm (g i)) (fun i => hYT (g i)) (fun i => hden (g i)) hcount
  have hsub : (⋃ i : Fin (Fintype.card S), Y (g i)) ⊆ P ∩ ⋃ i, Y i :=
    Set.iUnion_subset (fun i y hy =>
      ⟨(g i).property (hYT (g i) hy), Set.mem_iUnion.mpr ⟨(g i).val, hy⟩⟩)
  have hfinal := hbound.trans (measure_mono hsub)
  simpa only [Set.fintypeCard_eq_ncard] using hfinal

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
