-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.WeightedPruning.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Regularize

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory Set
open scoped Classical

noncomputable section

/-- Prune finitely many weighted cells, charging each deleted cell only its
threshold. This is the discrete version of the accepted density-pruning lemma. -/
theorem finite_weighted_pruning {α β : Type*} [Fintype α]
    (S : Finset α) (B : β → Finset α) (F : Finset β)
    (w : α → ENNReal) (cost : β → ENNReal) :
    ∃ T : Finset α, T ⊆ S ∧
      (∑ a ∈ S, w a) ≤ (∑ a ∈ T, w a) + ∑ i ∈ F, cost i ∧
      ∀ i ∈ F, (T ∩ B i).Nonempty → cost i ≤ ∑ a ∈ T ∩ B i, w a := by
  classical
  letI : MeasurableSpace α := ⊤
  let μ : Measure α := ∑ a, w a • Measure.dirac a
  have hmeasure (E : Set α) : μ E = ∑ a ∈ E.toFinset, w a := by
    have he : E.toFinset = Finset.univ.filter (fun a => a ∈ E) := by ext a; simp
    rw [he, Finset.sum_filter]
    simp only [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      Measure.dirac_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a ∈ E <;> simp [Set.indicator, ha]
  obtain ⟨H, _, hHS, hmass, hdense⟩ :=
    WangZahlLot.Obl.wz_regular_transverse_affine_cells.finite_density_pruning
      μ (fun i => (B i : Set α)) cost F (fun _ _ => MeasurableSet.of_discrete)
      (Y := S) MeasurableSet.of_discrete
  refine ⟨H.toFinset, ?_, ?_, ?_⟩
  · intro a ha
    exact hHS (Set.mem_toFinset.mp ha)
  · simpa only [hmeasure, Finset.toFinset_coe] using hmass
  · intro i hi hmeet
    have hmeet' : (H ∩ (B i : Set α)).Nonempty := by
      obtain ⟨a, ha⟩ := hmeet
      exact ⟨a, Set.mem_toFinset.mp (Finset.mem_inter.mp ha).1,
        (Finset.mem_inter.mp ha).2⟩
    have hh := hdense i hi hmeet'
    simpa only [hmeasure, Set.toFinset_inter, Finset.toFinset_coe] using hh

/-- Two simultaneous incidence thresholds cost the sum of their row and column
budgets. No repeated loss is paid when one deletion forces another. -/
theorem weighted_bipartite_core {α ι κ : Type*} [Fintype α] [Fintype ι] [Fintype κ]
    (S : Finset α) (row : α → ι) (col : α → κ) (w : α → ENNReal)
    (r : ι → ENNReal) (c : κ → ENNReal) :
    ∃ T : Finset α, T ⊆ S ∧
      (∑ a ∈ S, w a) ≤ (∑ a ∈ T, w a) + (∑ i, r i) + ∑ j, c j ∧
      (∀ i, (T.filter fun a => row a = i).Nonempty →
        r i ≤ ∑ a ∈ T with row a = i, w a) ∧
      (∀ j, (T.filter fun a => col a = j).Nonempty →
        c j ≤ ∑ a ∈ T with col a = j, w a) := by
  classical
  let B : ι ⊕ κ → Finset α := Sum.elim
    (fun i => Finset.univ.filter fun a => row a = i)
    (fun j => Finset.univ.filter fun a => col a = j)
  obtain ⟨T, hTS, hmass, hdense⟩ := finite_weighted_pruning S B Finset.univ w (Sum.elim r c)
  have hrow (i : ι) : T ∩ B (Sum.inl i) = T.filter (fun a => row a = i) := by
    ext a
    simp [B]
  have hcol (j : κ) : T ∩ B (Sum.inr j) = T.filter (fun a => col a = j) := by
    ext a
    simp [B]
  refine ⟨T, hTS, ?_, ?_, ?_⟩
  · simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, ← add_assoc] using hmass
  · intro i hi
    simpa only [hrow, Sum.elim_inl] using hdense (Sum.inl i) (Finset.mem_univ _) (hrow i ▸ hi)
  · intro j hj
    simpa only [hcol, Sum.elim_inr] using hdense (Sum.inr j) (Finset.mem_univ _) (hcol j ▸ hj)

end

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
