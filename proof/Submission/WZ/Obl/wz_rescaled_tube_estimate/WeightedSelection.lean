-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_tube_estimate.WeightedSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_rescaled_tube_estimate

/-- Greedy selection retains at least a reciprocal-degree share of arbitrary
nonnegative weights. The relation includes each vertex itself. -/
theorem weighted_separated_subfamily {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ι → ι → Prop) [DecidableRel R] (hrefl : ∀ i, R i i) (hsymm : ∀ {i j}, R i j → R j i)
    (D : ℕ) (hdegree : ∀ i, (Finset.univ.filter (R i)).card ≤ D)
    (w : ι → ENNReal) (F : Finset ι) :
    ∃ S : Finset ι, S ⊆ F ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → ¬R i j) ∧
      ∑ i ∈ F, w i ≤ (D : ENNReal) * ∑ i ∈ S, w i := by
  classical
  refine Finset.strongInductionOn F ?_
  intro F ih
  rcases F.eq_empty_or_nonempty with rfl | hF
  · exact ⟨∅, by simp, by simp, by simp⟩
  obtain ⟨i, hi, hmax⟩ := F.exists_max_image w hF
  let L := F.filter (R i)
  let G := F.filter (fun j => ¬R i j)
  have hGsub : G ⊆ F := Finset.filter_subset _ _
  have hiG : i ∉ G := by simp [G, hrefl i]
  have hGproper : G ⊂ F := Finset.ssubset_iff_subset_ne.mpr
    ⟨hGsub, fun heq => hiG (heq.symm ▸ hi)⟩
  obtain ⟨S, hSG, hsep, hmass⟩ := ih G hGproper
  have hiS : i ∉ S := fun hiS => hiG (hSG hiS)
  refine ⟨insert i S, Finset.insert_subset hi (hSG.trans hGsub), ?_, ?_⟩
  · intro j hj k hk hjk
    rcases Finset.mem_insert.mp hj with hji | hjS
    · subst j
      have hkS : k ∈ S := (Finset.mem_insert.mp hk).resolve_left hjk.symm
      exact (Finset.mem_filter.mp (hSG hkS)).2
    · rcases Finset.mem_insert.mp hk with hki | hkS
      · subst k
        exact fun hji => (Finset.mem_filter.mp (hSG hjS)).2 (hsymm hji)
      · exact hsep j hjS k hkS hjk
  · have hLcard : L.card ≤ D :=
      (Finset.card_le_card (Finset.filter_subset_filter (R i) (Finset.subset_univ F))).trans
        (hdegree i)
    have hLmass : ∑ j ∈ L, w j ≤ (D : ENNReal) * w i := by
      calc
        ∑ j ∈ L, w j ≤ ∑ _ ∈ L, w i :=
          Finset.sum_le_sum fun j hj => hmax j (Finset.mem_filter.mp hj).1
        _ = (L.card : ENNReal) * w i := by simp
        _ ≤ (D : ENNReal) * w i := mul_le_mul_left (by exact_mod_cast hLcard) _
    calc
      ∑ j ∈ F, w j = (∑ j ∈ L, w j) + ∑ j ∈ G, w j :=
        (Finset.sum_filter_add_sum_filter_not F (R i) w).symm
      _ ≤ (D : ENNReal) * w i + (D : ENNReal) * ∑ j ∈ S, w j :=
        add_le_add hLmass hmass
      _ = (D : ENNReal) * ∑ j ∈ insert i S, w j := by
        rw [Finset.sum_insert hiS, mul_add]

end WangZahlLot.Obl.wz_rescaled_tube_estimate
