-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.AngularPartition.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_measurable_angular_selection

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open wz_measurable_angular_selection (pd)

/-- One nonempty group of directions, at one of the allowed angular scales. -/
def AngularPacket {E : Type*} [NormedAddCommGroup E] {n : ℕ}
    (v : Fin n → E) (β δ : ℝ) (K : ℕ) (W : Finset (Fin n)) : Prop :=
  W.Nonempty ∧ ∃ k : ℕ, k ≤ K ∧ ∃ j : Fin n,
    (∀ i ∈ W, pd (v i) (v j) ≤ 2 * (1 / 2 : ℝ) ^ k) ∧
    ∀ u r, δ ≤ r →
      ((W.filter (fun i => pd (v i) u ≤ r)).card : ℝ) ≤
        2 * (r / (1 / 2 : ℝ) ^ k) ^ β * (W.card : ℝ)

/-- A nonempty residual collection contains a nonempty robust angular packet. -/
theorem angular_packet_exists {E : Type*} [NormedAddCommGroup E] {n : ℕ}
    (v : Fin n → E) (hv : ∀ i, ‖v i‖ = 1) {β δ : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hδ : 0 < δ) {K : ℕ}
    (hK1 : δ ≤ (1 / 2 : ℝ) ^ K) (hK2 : (1 / 2 : ℝ) ^ K < 2 * δ)
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    ∃ W : Finset (Fin n), W ⊆ S ∧ AngularPacket v β δ K W := by
  classical
  obtain ⟨j₀, hj₀⟩ := hS
  obtain ⟨k, j, hk, hmass, hrob⟩ :=
    wz_measurable_angular_selection.local_select v hv hβ hβ1 hδ hK1 hK2 j₀ S
  let W := S.filter (fun i => pd (v i) (v j) ≤ 2 * (1 / 2 : ℝ) ^ k)
  have hW : W.Nonempty := by
    apply Finset.card_pos.mp
    have hpos : (0 : ℝ) < W.card :=
      lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hδ β)
        (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨j₀, hj₀⟩))) hmass
    exact_mod_cast hpos
  exact ⟨W, Finset.filter_subset _ _, hW, k, hk, j,
    fun i hi => (Finset.mem_filter.mp hi).2, hrob⟩

/-- Repeated local selection partitions every direction multiset into broad
packets. In particular, no incidence mass is lost before selecting a scale. -/
theorem finite_angular_partition {E : Type*} [NormedAddCommGroup E] {n : ℕ}
    (v : Fin n → E) (hv : ∀ i, ‖v i‖ = 1) {β δ : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hδ : 0 < δ) {K : ℕ}
    (hK1 : δ ≤ (1 / 2 : ℝ) ^ K) (hK2 : (1 / 2 : ℝ) ^ K < 2 * δ)
    (S : Finset (Fin n)) :
    ∃ P : Finset (Finset (Fin n)),
      (∀ W ∈ P, AngularPacket v β δ K W) ∧
      (∀ W ∈ P, W ⊆ S) ∧ (P : Set (Finset (Fin n))).Pairwise Disjoint ∧ P.biUnion id = S := by
  classical
  refine Finset.strongInductionOn S ?_
  intro S ih
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst S
    exact ⟨∅, by simp, by simp, by simp, by simp⟩
  obtain ⟨W, hWS, hW⟩ := angular_packet_exists v hv hβ hβ1 hδ hK1 hK2 S hS
  have hlt : S \ W ⊂ S := Finset.sdiff_ssubset hWS hW.1
  obtain ⟨P, hgood, hsub, hdis, hcover⟩ := ih (S \ W) hlt
  have hd (U : Finset (Fin n)) (hU : U ∈ P) : Disjoint W U := by
    apply Finset.disjoint_left.mpr
    intro i hiW hiU
    exact (Finset.mem_sdiff.mp (hsub U hU hiU)).2 hiW
  refine ⟨insert W P, ?_, ?_, ?_, ?_⟩
  · intro U hU
    rcases Finset.mem_insert.mp hU with rfl | hU
    · exact hW
    · exact hgood U hU
  · intro U hU
    rcases Finset.mem_insert.mp hU with rfl | hU
    · exact hWS
    · exact (hsub U hU).trans Finset.sdiff_subset
  · rw [Finset.coe_insert]
    exact hdis.insert (fun U hU _ => ⟨hd U hU, (hd U hU).symm⟩)
  · rw [Finset.biUnion_insert, hcover]
    exact Finset.union_sdiff_of_subset hWS

end WangZahlLot.Obl.wz_broad_grains_initialization
