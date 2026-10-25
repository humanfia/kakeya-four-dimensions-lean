import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.AtomTable
import Submission.Obl.k4_marked_scalar_grid_selection.MassTrimming

namespace Submission.Obl.k4_marked_scalar_grid_selection

open MeasureTheory Set Filter Scalar
open scoped ENNReal

theorem markOf_markedAtoms {H J : ℕ} (mark : Fin H → Fin J → Bool) :
    markOf (markedAtoms mark) = mark := by
  classical
  funext j z
  cases h : mark j z <;> simp [markOf, markedAtoms, h]

theorem tableMeasure_finset {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (I T : Finset α) (hTI : T ⊆ I) (w : α → ℝ) (hw : ∀ a ∈ I, 0 ≤ w a) :
    tableMeasure I w (T : Set α) = ENNReal.ofReal (tableMass T w) := by
  classical
  rw [tableMeasure_restrict_mass I w _ T.finite_toSet.measurableSet hw]
  congr 2
  ext a
  simp only [Finset.mem_filter, Finset.mem_coe]
  exact and_iff_right_of_imp (fun h => hTI h)

/-- Tiny atoms may be removed before type selection, with only a constant
factor in the mass loss. The finite exceptional prefix keeps its old atoms. -/
theorem trimmed_tables (N K : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k)
    (hNt : Tendsto N atTop atTop) (hK : Subpower N K)
    (m : ℝ) (M : ℕ) (H J : ℕ → ℕ)
    (b : (k : ℕ) → Fin (H k) → Fin 5 → ℝ)
    (w : (k : ℕ) → Fin (H k) → ℝ)
    (mark : (k : ℕ) → Fin (H k) → Fin (J k) → Bool)
    (htables : ∀ k, tables (N k) (K k) m M (H k) (J k) (b k) (w k) (mark k)) :
    ∃ I : (k : ℕ) → Finset (AtomIndex (H k) (J k)),
      (∀ k, I k ⊆ markedAtoms (mark k)) ∧
      (∀ k, ENNReal.ofReal ((2 * K k)⁻¹) ≤
        ENNReal.ofReal (tableMass (I k) (cellWeight (J k) (w k)))) ∧
      ∀ᶠ k in atTop, ∀ a ∈ I k,
        N k ^ (-(2 * (M : ℝ) + 2)) ≤ cellWeight (J k) (w k) a := by
  classical
  let S (k : ℕ) := markedAtoms (mark k)
  let δ (k : ℕ) := N k ^ (-(2 * (M : ℝ) + 2))
  let T (k : ℕ) := (S k).filter (fun a => δ k ≤ cellWeight (J k) (w k) a)
  let μ (k : ℕ) := tableMeasure (S k) (cellWeight (J k) (w k))
  have hw (k : ℕ) (a : AtomIndex (H k) (J k)) : 0 ≤ cellWeight (J k) (w k) a :=
    div_nonneg ((htables k).2.2.2.2.2.1 a.1) (Nat.cast_nonneg _)
  have hμ (k : ℕ) (F : Finset (AtomIndex (H k) (J k))) (hF : F ⊆ S k) :
      μ k (F : Set _) = ENNReal.ofReal (tableMass F (cellWeight (J k) (w k))) :=
    tableMeasure_finset (S k) F hF _ (fun a _ => hw k a)
  have hlower (k : ℕ) : ENNReal.ofReal (K k)⁻¹ ≤ μ k (S k : Set _) := by
    rw [hμ k (S k) Subset.rfl]
    have hσ : 0 < N k ^ (-m) := Real.rpow_pos_of_pos (by linarith [hN k]) _
    have hj : 0 < J k := by have := (htables k).1; omega
    have heq := law_mass_markOf hσ hj (b k) (w k)
      ((htables k).2.2.2.2.2.1) (S k)
    rw [show markOf (S k) = mark k from markOf_markedAtoms _] at heq
    rw [← heq]
    exact (htables k).2.2.2.2.2.2.2.2
  have hdiscard (k : ℕ) : μ k (S k : Set _) ≤ μ k (T k : Set _) +
      ENNReal.ofReal (N k ^ (-1 : ℝ)) := by
    rw [hμ k (S k) Subset.rfl, hμ k (T k) (Finset.filter_subset _ _)]
    have hprune := tableMass_prune (S k) (cellWeight (J k) (w k)) (δ k)
      (Real.rpow_nonneg (by linarith [hN k]) _)
    have hcard : ((S k).card : ℝ) ≤ N k ^ (2 * (M : ℝ)) := by
      have hc : ((S k).card : ℝ) ≤ (H k : ℝ) * (J k : ℝ) := by
        have hnat : (S k).card ≤ H k * J k := by
          simpa only [AtomIndex, Fintype.card_prod, Fintype.card_fin] using
            (Finset.card_le_univ (s := S k))
        exact_mod_cast hnat
      refine hc.trans ?_
      calc
        (H k : ℝ) * (J k : ℝ) ≤ N k ^ (M : ℝ) * N k ^ (M : ℝ) :=
          mul_le_mul (htables k).2.1 (htables k).2.2.1 (Nat.cast_nonneg _)
            (Real.rpow_nonneg (by linarith [hN k]) _)
        _ = N k ^ (2 * (M : ℝ)) := by
          rw [← Real.rpow_add (by linarith [hN k])]; congr 1; ring
    have herr : ((S k).card : ℝ) * δ k ≤ N k ^ (-1 : ℝ) := by
      calc
        ((S k).card : ℝ) * δ k ≤ N k ^ (2 * (M : ℝ)) * δ k :=
          mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg (by linarith [hN k]) _)
        _ = N k ^ (-2 : ℝ) := by
          dsimp only [δ]
          rw [← Real.rpow_add (by linarith [hN k])]; congr 1; ring
        _ ≤ N k ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le
          (by linarith [hN k]) (by norm_num)
    have hmass : tableMass (S k) (cellWeight (J k) (w k)) ≤
        tableMass (T k) (cellWeight (J k) (w k)) + N k ^ (-1 : ℝ) := by
      exact hprune.trans (add_le_add le_rfl herr)
    have hnonneg : 0 ≤ tableMass (T k) (cellWeight (J k) (w k)) :=
      Finset.sum_nonneg (fun a _ => hw k a)
    rw [← ENNReal.ofReal_add hnonneg
      (Real.rpow_nonneg (by linarith [hN k]) _)]
    exact ENNReal.ofReal_le_ofReal hmass
  obtain ⟨_, A, hAS, hAT, hAlower⟩ := dense_active_sets N K hN hNt hK μ
    (fun k => (S k : Set _)) (fun k => (T k : Set _))
    (fun k => Finset.filter_subset _ _) hlower 1 (by norm_num)
    (Eventually.of_forall hdiscard)
  let I (k : ℕ) := (S k).filter (fun a => a ∈ A k)
  refine ⟨I, (fun k => Finset.filter_subset _ _), ?_, ?_⟩
  · intro k
    have hh := hAlower k
    rw [tableMeasure_restrict_mass (S k) _ _ (Set.to_countable (A k)).measurableSet
      (fun a _ => hw k a)] at hh
    exact hh
  · filter_upwards [hAT] with k hk a ha
    have hmem := (Finset.mem_filter.mp ha).2
    rw [hk] at hmem
    exact (Finset.mem_filter.mp hmem).2

end Submission.Obl.k4_marked_scalar_grid_selection
