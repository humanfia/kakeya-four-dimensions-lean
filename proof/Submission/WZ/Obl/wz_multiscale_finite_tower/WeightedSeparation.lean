-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.WeightedSeparation.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.DistinctGeometry
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.DenseNet

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal
attribute [local instance] Classical.propDecidable

/-- Greedy weighted selection for a symmetric relation of bounded local cardinality. -/
theorem weighted_independent {α : Type*} [DecidableEq α]
    (R : α → α → Prop) (hrefl : ∀ i, R i i) (hsymm : ∀ i j, R i j → R j i)
    {K : ℝ} (hK : 0 ≤ K) (w : α → ℝ) (U : Finset α) :
    (∀ i ∈ U, ((U.filter fun j => R i j).card : ℝ) ≤ K) →
    (∀ i ∈ U, 0 ≤ w i) →
    ∃ S : Finset α, S ⊆ U ∧ (∑ i ∈ U, w i) ≤ K * ∑ i ∈ S, w i ∧
      (S : Set α).Pairwise (fun i j => ¬R i j) := by
  classical
  induction U using Finset.strongInductionOn with
  | _ U ih =>
    intro hbound hw
    rcases U.eq_empty_or_nonempty with rfl | hU
    · exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
    obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image U w hU
    let A := U.filter fun i => ¬R p i
    let D := U.filter fun i => R p i
    have hAU : A ⊆ U := Finset.filter_subset _ _
    have hpA : p ∉ A := by simp [A, hrefl p]
    have hlt : A ⊂ U :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hAU, fun he => hpA (he.symm ▸ hp)⟩
    have hAbound : ∀ i ∈ A, ((A.filter fun j => R i j).card : ℝ) ≤ K := by
      intro i hi
      exact (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hAU))).trans
        (hbound i (hAU hi))
    obtain ⟨S, hSA, hmass, hind⟩ := ih A hlt hAbound (fun i hi => hw i (hAU hi))
    have hpS : p ∉ S := fun hpS => hpA (hSA hpS)
    have hDmass : (∑ i ∈ D, w i) ≤ K * w p := by
      calc
        _ ≤ ∑ _i ∈ D, w p := Finset.sum_le_sum fun i hi => hmax i (Finset.mem_filter.mp hi).1
        _ = (D.card : ℝ) * w p := by simp
        _ ≤ K * w p := mul_le_mul_of_nonneg_right (hbound p hp) (hw p hp)
    have hsplit : (∑ i ∈ D, w i) + (∑ i ∈ A, w i) = ∑ i ∈ U, w i :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    refine ⟨insert p S, Finset.insert_subset hp (hSA.trans hAU), ?_, ?_⟩
    · rw [Finset.sum_insert hpS, mul_add]
      linarith
    · intro i hi j hj hij
      by_cases hip : i = p
      · have hjp : j ≠ p := fun hjp => hij (hip.trans hjp.symm)
        have hjS := (Finset.mem_insert.mp hj).resolve_left hjp
        simpa only [hip] using (Finset.mem_filter.mp (hSA hjS)).2
      · have hiS := (Finset.mem_insert.mp hi).resolve_left hip
        by_cases hjp : j = p
        · intro hR
          have hR' := hsymm i j hR
          rw [hjp] at hR'
          exact (Finset.mem_filter.mp (hSA hiS)).2 hR'
        · exact hind hiS ((Finset.mem_insert.mp hj).resolve_left hjp) hij

def TubeNear (d : ℝ) (x v y w : Space) : Prop :=
  (Tube d x v ∩ Tube d y w).Nonempty ∧ min ‖v - w‖ ‖v + w‖ ≤ 16384 * d

lemma TubeNear.symm {d : ℝ} {x v y w : Space} (h : TubeNear d x v y w) :
    TubeNear d y w x v := by
  refine ⟨by simpa only [inter_comm] using h.1, ?_⟩
  simpa only [norm_sub_rev, add_comm] using h.2

lemma overlapContainer_convex (d : ℝ) (x v : Space) : Convex ℝ (OverlapContainer d x v) := by
  exact (WangZahlLot.Obl.wz_rescaled_fibre_alternatives.tube_convex (20000 * d) (x - v) v).affine_image
    (AffineMap.homothety (x - v) (3 : ℝ))

/-- A convex-count bound is sufficient for a quantitatively weighted essentially
distinct subfamily. This applies after the initial longitudinal shifts. -/
theorem weighted_distinct_selection {d L : ℝ} (hd : 0 < d) (hd1 : d ≤ 1 / 100000)
    (hL : 0 ≤ L) {n : ℕ} (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (hK : KatzTao d L n x v) (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hmass : 0 < ∑ i, w i) :
    ∃ S : Finset (Fin n), S.Nonempty ∧
      (∑ i, w i) ≤ (10000000000000 * L) * ∑ i ∈ S, w i ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
        volume (Tube d (x i) (v i) ∩ Tube d (x j) (v j)) ≤
          (1 / 2 : ℝ≥0∞) * volume (Tube d (x i) (v i)) := by
  classical
  let R := fun i j => TubeNear d (x i) (v i) (x j) (v j)
  have hrefl (i : Fin n) : R i i := by
    refine ⟨⟨x i, ?_, ?_⟩, ?_⟩
    · exact self_subset_thickening hd _ (left_mem_segment ℝ _ _)
    · exact self_subset_thickening hd _ (left_mem_segment ℝ _ _)
    · simp only [sub_self, norm_zero, min_eq_left (norm_nonneg _)]
      positivity
  have hbound (i : Fin n) : ((Finset.univ.filter fun j => R i j).card : ℝ) ≤ 10000000000000 * L := by
    apply WangZahlLot.Obl.wz_rescaled_fibre_alternatives.card_le_of_container hd hL
      (by norm_num) (by simpa only [WangZahlLot.Obl.wz_rescaled_fibre_alternatives.ConvexCount,
        KatzTao, true_and] using hK) _ (overlapContainer_convex d (x i) (v i))
      (overlapContainer_volume hd hd1 (x i) (v i) (hv i))
    intro j hj
    have hij : TubeNear d (x i) (v i) (x j) (v j) := (Finset.mem_filter.mp hj).2
    exact near_intersecting_tube_subset hd hij.symm.2 hij.1
  obtain ⟨S, hS, hweight, hind⟩ := weighted_independent R hrefl (fun i j hij => hij.symm)
    (by positivity : 0 ≤ 10000000000000 * L) w Finset.univ
    (fun i _ => hbound i) (fun i _ => hw i)
  have hSne : S.Nonempty := by
    by_contra hn
    simp only [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty, mul_zero] at hweight
    linarith
  refine ⟨S, hSne, hweight, ?_⟩
  intro i hi j hj hij
  by_contra hover
  have hang := angle_le_of_large_overlap hd (by linarith : d ≤ 1 / 1024) (hv i) (hv j) hover
  have hne : (Tube d (x i) (v i) ∩ Tube d (x j) (v j)).Nonempty := by
    by_contra hn
    have he := Set.not_nonempty_iff_eq_empty.mp hn
    simp only [he, measure_empty, not_le, not_lt_zero] at hover
  exact hind hi hj hij ⟨hne, hang⟩

end WangZahlLot.Obl.wz_multiscale_finite_tower
