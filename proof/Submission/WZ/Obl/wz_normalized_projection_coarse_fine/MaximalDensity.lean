-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.MaximalDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.DyadicCells

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Selecting a cell of maximum normalized occupancy provides local Frostman counts
without regularizing the entire hierarchy. -/
theorem maximal_dyadic_density_cell {α : Type*} [DecidableEq α] {d j₀ L : ℕ}
    (U : Finset α) (hU : U.Nonempty) (p : α → EuclideanSpace ℝ (Fin d))
    (hjL : j₀ ≤ L) (s : ℝ)
    (hroot : ∀ a ∈ U, ∀ b ∈ U, dyadicLabel j₀ (p a) = dyadicLabel j₀ (p b)) :
    ∃ j, j₀ ≤ j ∧ j ≤ L ∧ ∃ a ∈ U,
      let Q := U.filter (fun b => dyadicLabel j (p b) = dyadicLabel j (p a))
      Q.Nonempty ∧
      (U.card : ℝ) * (((2 : ℝ) ^ j)⁻¹) ^ s ≤
        (Q.card : ℝ) * (((2 : ℝ) ^ j₀)⁻¹) ^ s ∧
      ∀ k, j₀ ≤ k → k ≤ L → ∀ l : Fin d → ℤ,
        ((Q.filter (fun b => dyadicLabel k (p b) = l)).card : ℝ) ≤
          (Q.card : ℝ) * ((((2 : ℝ) ^ k)⁻¹ / ((2 : ℝ) ^ j)⁻¹) ^ s) := by
  classical
  let I := (Finset.Icc j₀ L) ×ˢ U
  let C (i : ℕ × α) := U.filter (fun b => dyadicLabel i.1 (p b) = dyadicLabel i.1 (p i.2))
  let density (i : ℕ × α) := (C i).card / ((((2 : ℝ) ^ i.1)⁻¹) ^ s)
  obtain ⟨a₀, ha₀⟩ := hU
  have hI : I.Nonempty := ⟨(j₀, a₀), Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨le_rfl, hjL⟩, ha₀⟩⟩
  obtain ⟨i, hi, hmax⟩ := I.exists_max_image density hI
  obtain ⟨hij, hia⟩ := Finset.mem_product.mp hi
  obtain ⟨hij₀, hiL⟩ := Finset.mem_Icc.mp hij
  have hcomp {k : ℕ} (hk₀ : j₀ ≤ k) (hkL : k ≤ L) {b : α} (hb : b ∈ U) :
      ((C (k, b)).card : ℝ) * ((((2 : ℝ) ^ i.1)⁻¹) ^ s) ≤
        ((C i).card : ℝ) * ((((2 : ℝ) ^ k)⁻¹) ^ s) := by
    have hm := hmax (k, b) (Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hk₀, hkL⟩, hb⟩)
    exact (div_le_div_iff₀ (by positivity) (by positivity)).mp hm
  have hCroot : C (j₀, a₀) = U := by
    apply Finset.filter_eq_self.mpr
    intro b hb
    exact hroot b hb a₀ ha₀
  refine ⟨i.1, hij₀, hiL, i.2, hia, ?_, ?_, ?_⟩
  · exact ⟨i.2, Finset.mem_filter.mpr ⟨hia, rfl⟩⟩
  · have hh := hcomp le_rfl hjL ha₀
    simpa only [hCroot] using hh
  · intro k hk₀ hkL l
    let V := (C i).filter (fun b => dyadicLabel k (p b) = l)
    rcases V.eq_empty_or_nonempty with he | hV
    · change (V.card : ℝ) ≤ _
      rw [he, Finset.card_empty, Nat.cast_zero]
      positivity
    obtain ⟨b, hb⟩ := hV
    obtain ⟨hbC, hbl⟩ := Finset.mem_filter.mp hb
    have hbU := (Finset.mem_filter.mp hbC).1
    have hVC : V ⊆ C (k, b) := by
      intro a ha
      obtain ⟨haC, hal⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp haC).1, hal.trans hbl.symm⟩
    have hcard : (V.card : ℝ) ≤ (C (k, b)).card := by exact_mod_cast Finset.card_le_card hVC
    have hh := hcomp hk₀ hkL hbU
    have hden : 0 < (((2 : ℝ) ^ i.1)⁻¹) ^ s := by positivity
    have hratio : (((2 : ℝ) ^ k)⁻¹ / ((2 : ℝ) ^ i.1)⁻¹) ^ s =
        (((2 : ℝ) ^ k)⁻¹) ^ s / (((2 : ℝ) ^ i.1)⁻¹) ^ s :=
      Real.div_rpow (by positivity) (by positivity) s
    change (V.card : ℝ) ≤ (C i).card * _
    rw [hratio, ← mul_div_assoc]
    exact (le_div_iff₀ hden).mpr
      ((mul_le_mul_of_nonneg_right hcard hden.le).trans hh)

/-- Repeated nonempty selections give disjoint good cells, leaving at most a prescribed
number of indices. No weighted or cardinality loss is incurred on the selected cells. -/
theorem disjoint_selection_partition {α : Type*} [DecidableEq α]
    (U : Finset α) (P : Finset α → Prop) {M : ℝ} (hM : 0 ≤ M)
    (hselect : ∀ S ⊆ U, M < (S.card : ℝ) → ∃ Q ⊆ S, Q.Nonempty ∧ P Q) :
    ∃ F : Finset (Finset α),
      (∀ Q ∈ F, Q ⊆ U ∧ Q.Nonempty ∧ P Q) ∧
      (F : Set (Finset α)).PairwiseDisjoint id ∧
      ((U \ F.biUnion id).card : ℝ) ≤ M := by
  classical
  have go : ∀ S : Finset α, S ⊆ U → ∃ F : Finset (Finset α),
      (∀ Q ∈ F, Q ⊆ S ∧ Q.Nonempty ∧ P Q) ∧
      (F : Set (Finset α)).PairwiseDisjoint id ∧
      ((S \ F.biUnion id).card : ℝ) ≤ M := by
    intro S
    refine Finset.strongInductionOn S ?_
    intro S ih hSU
    by_cases hsmall : (S.card : ℝ) ≤ M
    · exact ⟨∅, by simp, by simp, by simpa using hsmall⟩
    obtain ⟨Q, hQS, hQ, hPQ⟩ := hselect S hSU (not_le.mp hsmall)
    have hproper : S \ Q ⊂ S := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
      intro he
      obtain ⟨a, ha⟩ := hQ
      have ham : a ∈ S \ Q := he.symm ▸ hQS ha
      exact (Finset.mem_sdiff.mp ham).2 ha
    obtain ⟨G, hG, hGdisj, hrem⟩ := ih (S \ Q) hproper (Finset.sdiff_subset.trans hSU)
    have hQG : ∀ V ∈ G, Disjoint Q V := by
      intro V hV
      apply Finset.disjoint_left.mpr
      intro a haQ haV
      exact (Finset.mem_sdiff.mp ((hG V hV).1 haV)).2 haQ
    refine ⟨insert Q G, ?_, ?_, ?_⟩
    · intro V hV
      rcases Finset.mem_insert.mp hV with rfl | hV
      · exact ⟨hQS, hQ, hPQ⟩
      · exact ⟨(hG V hV).1.trans Finset.sdiff_subset, (hG V hV).2⟩
    · intro V hV W hW hne
      rcases Finset.mem_insert.mp hV with hVQ | hVG
      · rcases Finset.mem_insert.mp hW with hWQ | hWG
        · exact False.elim (hne (hVQ.trans hWQ.symm))
        · subst V
          exact hQG W hWG
      · rcases Finset.mem_insert.mp hW with hWQ | hWG
        · subst W
          exact (hQG V hVG).symm
        · exact hGdisj hVG hWG hne
    · simpa only [Finset.biUnion_insert, id_eq, Finset.sdiff_union_distrib,
        Finset.sdiff_sdiff_left'] using hrem
  exact go U (Finset.Subset.refl _)

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
