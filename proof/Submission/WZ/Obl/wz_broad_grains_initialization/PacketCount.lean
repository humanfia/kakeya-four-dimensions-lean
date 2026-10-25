-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.PacketCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.AngularMax

namespace WangZahlLot.Obl.wz_broad_grains_initialization

/-- Disjoint angular packets, each large relative to the original incidence
count, have bounded pointwise multiplicity. -/
theorem angular_packet_count {n : ℕ} {θ β : ℝ} (hθ : 0 < θ)
    (S : Finset (Fin n)) (P : Finset (Finset (Fin n)))
    (hne : ∀ W ∈ P, W.Nonempty) (hsub : ∀ W ∈ P, W ⊆ S)
    (hdis : (P : Set (Finset (Fin n))).Pairwise Disjoint)
    (hsize : ∀ W ∈ P, ((S.card : ℝ) / 2) * θ ^ β ≤ W.card) :
    (P.card : ℝ) ≤ 2 * θ ^ (-β) := by
  classical
  by_cases hS : S.Nonempty
  · have hSpos : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hS)
    have hbound : ∑ W ∈ P, (W.card : ℝ) ≤ S.card := by
      have he : (P.biUnion id).card = ∑ W ∈ P, W.card := Finset.card_biUnion hdis
      have hh : (P.biUnion id).card ≤ S.card :=
        Finset.card_le_card (Finset.biUnion_subset.mpr hsub)
      rw [he] at hh
      exact_mod_cast hh
    have hlo : (P.card : ℝ) * (((S.card : ℝ) / 2) * θ ^ β) ≤ S.card := by
      calc
        _ = ∑ _ ∈ P, (((S.card : ℝ) / 2) * θ ^ β) := by simp
        _ ≤ ∑ W ∈ P, (W.card : ℝ) := Finset.sum_le_sum hsize
        _ ≤ S.card := hbound
    have hcancel : (P.card : ℝ) * θ ^ β ≤ 2 := by nlinarith
    rw [Real.rpow_neg hθ.le]
    exact (le_mul_inv_iff₀ (Real.rpow_pos_of_pos hθ β)).mpr hcancel
  · have hP : P = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro W hW
      exact hS ((hne W hW).mono (hsub W hW))
    simp only [hP, Finset.card_empty, Nat.cast_zero]
    positivity


/-- Combining disjoint packets at one scale preserves their angular broadness. -/
theorem angular_packet_union {E : Type*} [NormedAddCommGroup E] {n : ℕ}
    (v : Fin n → E) (P : Finset (Finset (Fin n))) {β δ θ C : ℝ}
    (hdis : (P : Set (Finset (Fin n))).Pairwise Disjoint)
    (hrob : ∀ W ∈ P, ∀ u r, δ ≤ r →
      ((W.filter (fun i => wz_measurable_angular_selection.pd (v i) u ≤ r)).card : ℝ) ≤
        C * (r / θ) ^ β * (W.card : ℝ)) :
    ∀ u r, δ ≤ r →
      (((P.biUnion id).filter (fun i => wz_measurable_angular_selection.pd (v i) u ≤ r)).card : ℝ) ≤
        C * (r / θ) ^ β * ((P.biUnion id).card : ℝ) := by
  classical
  intro u r hr
  have hc : ((P.biUnion id).card : ℝ) = ∑ W ∈ P, (W.card : ℝ) := by
    exact_mod_cast Finset.card_biUnion hdis
  calc
    _ ≤ ∑ W ∈ P,
        ((W.filter (fun i => wz_measurable_angular_selection.pd (v i) u ≤ r)).card : ℝ) := by
      rw [Finset.filter_biUnion]
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ W ∈ P, C * (r / θ) ^ β * (W.card : ℝ) :=
      Finset.sum_le_sum (fun W hW => hrob W hW u r hr)
    _ = C * (r / θ) ^ β * ((P.biUnion id).card : ℝ) := by
      rw [hc, Finset.mul_sum]

end WangZahlLot.Obl.wz_broad_grains_initialization
