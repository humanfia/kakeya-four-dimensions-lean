-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.FactoredThickening.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.LocalThickening
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.Structure
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file FactoredThickening.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set Metric

/-- The local planar estimate applies simultaneously to every occupied prism of
an indexed Frostman factorization. -/
theorem factored_prism_thickening_restricted (e : ℝ) (he : 0 < e) :
    ∃ A : ℝ, 0 < A ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ a b : ℝ, δ ≤ a → a ≤ b → b ≤ 1 →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space), 0 < n →
      (∀ i, ‖v i‖ = 1) → (∀ i, MeasurableSet (Y i)) →
      (∀ i, Y i ⊆ tube δ (x i) (v i)) →
      (∀ i, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ volume (Y i)) →
    ∀ (p : ℕ) (c e₁ e₂ e₃ : Fin p → Space),
      (∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j]) →
      Factored (δ ^ (-η)) b (fun i => tube δ (x i) (v i))
        (fun j => prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) →
      ∀ j, ENNReal.ofReal (A * δ ^ e) * volume (prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) ≤
        volume (prism a b (c j) (e₁ j) (e₂ j) (e₃ j) ∩
          thickening a (prism a b (c j) (e₁ j) (e₂ j) (e₃ j) ∩ ⋃ i, Y i)) := by
  classical
  obtain ⟨A, hA, η, hη, hlocal⟩ := local_prism_thickening e he
  refine ⟨A, hA, η, hη, ?_⟩
  intro δ hδ hδ1 a b hδa hab hb n x v Y hn hv hYm hYT hden p c e₁ e₂ e₃ he hf j
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
          Set.ncard_preimage_of_injective_subset_range g.injective (by simp [g.surjective.range_eq])
        _ = Set.ncard ({i | tube δ (x i) (v i) ⊆ U} ∩ S) :=
          Set.ncard_subtype (fun i => tube δ (x i) (v i) ⊆ P)
            {i | tube δ (x i) (v i) ⊆ U}
        _ = _ := by
          congr 1
          ext i
          exact and_comm
    rw [hcard, Set.fintypeCard_eq_ncard]
    exact hf.2.2.2.1 j U hU
  have h := hlocal δ hδ hδ1 a b hδa hab hb (c j) (e₁ j) (e₂ j) (e₃ j) (he j)
    (Fintype.card S) (fun i => x (g i)) (fun i => v (g i)) (fun i => Y (g i)) hS
    (fun i => hv (g i)) (fun i => (g i).property) (fun i => hYm (g i))
    (fun i => hYT (g i)) (fun i => hden (g i)) hcount
  apply h.trans
  apply measure_mono
  apply Set.inter_subset_inter_right
  apply thickening_subset_of_subset
  refine Set.iUnion_subset fun i y hy => ?_
  exact ⟨(g i).property (hYT (g i) hy), Set.mem_iUnion.mpr ⟨(g i).val, hy⟩⟩

/-- The version with the unrestricted physical shading union. -/
theorem factored_prism_thickening (e : ℝ) (he : 0 < e) :
    ∃ A : ℝ, 0 < A ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ a b : ℝ, δ ≤ a → a ≤ b → b ≤ 1 →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space), 0 < n →
      (∀ i, ‖v i‖ = 1) → (∀ i, MeasurableSet (Y i)) →
      (∀ i, Y i ⊆ tube δ (x i) (v i)) →
      (∀ i, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ volume (Y i)) →
    ∀ (p : ℕ) (c e₁ e₂ e₃ : Fin p → Space),
      (∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j]) →
      Factored (δ ^ (-η)) b (fun i => tube δ (x i) (v i))
        (fun j => prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) →
      ∀ j, ENNReal.ofReal (A * δ ^ e) * volume (prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) ≤
        volume (prism a b (c j) (e₁ j) (e₂ j) (e₃ j) ∩ thickening a (⋃ i, Y i)) := by
  obtain ⟨A, hA, η, hη, h⟩ := factored_prism_thickening_restricted e he
  refine ⟨A, hA, η, hη, ?_⟩
  intro δ hδ hδ1 a b hδa hab hb n x v Y hn hv hYm hYT hden p c e₁ e₂ e₃ he hf j
  exact (h δ hδ hδ1 a b hδa hab hb n x v Y hn hv hYm hYT hden p c e₁ e₂ e₃ he hf j).trans
    (measure_mono (Set.inter_subset_inter_right _
      (thickening_subset_of_subset _ Set.inter_subset_right)))

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
