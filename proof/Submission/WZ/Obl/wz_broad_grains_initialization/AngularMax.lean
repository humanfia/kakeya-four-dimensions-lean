-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.AngularMax.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_measurable_angular_selection
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Dyadic

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open wz_measurable_angular_selection (pd G cnt)

/-- The maximal normalized cap has mass proportional to its own radius,
rather than merely to the bottom angular scale. This is the quantitative
input for retaining many packets at a common scale. -/
theorem large_angular_packet {E : Type*} [NormedAddCommGroup E] {n : ℕ}
    (v : Fin n → E) (hv : ∀ i, ‖v i‖ = 1) {β δ : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hδ : 0 < δ) {K : ℕ}
    (hK2 : (1 / 2 : ℝ) ^ K < 2 * δ)
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    ∃ k : ℕ, k ≤ K ∧ ∃ j : Fin n, ∃ W : Finset (Fin n),
      W.Nonempty ∧ W ⊆ S ∧
      (∀ i ∈ W, pd (v i) (v j) ≤ 2 * (1 / 2 : ℝ) ^ k) ∧
      ((1 / 2 : ℝ) ^ k) ^ β * (S.card : ℝ) ≤ W.card ∧
      ∀ u r, δ ≤ r →
        ((W.filter (fun i => pd (v i) u ≤ r)).card : ℝ) ≤
          2 * (r / (1 / 2 : ℝ) ^ k) ^ β * (W.card : ℝ) := by
  classical
  let radius : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k
  have hradius (k : ℕ) : 0 < radius k := by dsimp [radius]; positivity
  let score : ℕ → ℝ := fun k => (G v S (2 * radius k) : ℝ) / (radius k) ^ β
  obtain ⟨k, hk, hkmax⟩ := Finset.exists_max_image (Finset.range (K + 1)) score
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos K)⟩
  have hkK : k ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  obtain ⟨j, hj, hjmax⟩ := Finset.exists_mem_eq_sup S hS (fun j => cnt v S j (2 * radius k))
  let W := S.filter (fun i => pd (v i) (v j) ≤ 2 * radius k)
  have hWsub : W ⊆ S := Finset.filter_subset _ _
  have hG : G v S (2 * radius k) = W.card := hjmax
  have hmax (l : ℕ) (hl : l ≤ K) :
      (G v S (2 * radius l) : ℝ) * (radius k) ^ β ≤ (W.card : ℝ) * (radius l) ^ β := by
    have hh := hkmax l (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))
    dsimp [score] at hh
    rw [hG] at hh
    exact (div_le_div_iff₀ (Real.rpow_pos_of_pos (hradius l) β)
      (Real.rpow_pos_of_pos (hradius k) β)).mp hh
  have hmass : (radius k) ^ β * (S.card : ℝ) ≤ W.card := by
    have hh := hmax 0 (Nat.zero_le K)
    simp only [radius, pow_zero, mul_one, Real.one_rpow] at hh
    have hc : (S.card : ℝ) ≤ G v S 2 := by
      exact_mod_cast wz_measurable_angular_selection.card_le_G v hv S
    exact (mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg (hradius k).le β)).trans
      (by simpa only [mul_comm] using hh)
  have hWne : W.Nonempty := by
    apply Finset.card_pos.mp
    have hh : (0 : ℝ) < W.card :=
      (mul_pos (Real.rpow_pos_of_pos (hradius k) β)
        (Nat.cast_pos.mpr (Finset.card_pos.mpr hS))).trans_le hmass
    exact_mod_cast hh
  refine ⟨k, hkK, j, W, hWne, hWsub,
    fun i hi => (Finset.mem_filter.mp hi).2, hmass, ?_⟩
  intro u r hr
  have hrpos : 0 < r := hδ.trans_le hr
  have hcard : ((W.filter (fun i => pd (v i) u ≤ r)).card : ℝ) ≤ W.card := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun i => pd (v i) u ≤ r) W)
  by_cases hkr : radius k ≤ r
  · have hone : 1 ≤ (r / radius k) ^ β :=
      Real.one_le_rpow ((one_le_div (hradius k)).mpr hkr) hβ.le
    exact hcard.trans (by nlinarith [show (0 : ℝ) ≤ W.card from Nat.cast_nonneg _])
  · have hr1 : r ≤ 1 := (le_of_not_ge hkr).trans
      (pow_le_one₀ (by norm_num) (by norm_num) : radius k ≤ 1)
    obtain ⟨l, hlK, hrl, hlr⟩ :=
      wz_regular_transverse_affine_cells.exists_dyadic_between hδ hK2 hr hr1
    have hGmono : G v S (2 * r) ≤ G v S (2 * radius l) :=
      wz_measurable_angular_selection.G_mono v S (by dsimp [radius]; linarith)
    have hlocal : ((W.filter (fun i => pd (v i) u ≤ r)).card : ℝ) ≤
        G v S (2 * radius l) := by
      exact_mod_cast (wz_measurable_angular_selection.cap_le_G v S W hWsub u r).trans hGmono
    have hbound : (G v S (2 * radius l) : ℝ) ≤
        (radius l / radius k) ^ β * (W.card : ℝ) := by
      rw [Real.div_rpow (hradius l).le (hradius k).le]
      calc
        _ ≤ (W.card : ℝ) * (radius l) ^ β / (radius k) ^ β :=
          (le_div_iff₀ (Real.rpow_pos_of_pos (hradius k) β)).mpr (hmax l hlK)
        _ = _ := by ring
    have hp : (radius l / radius k) ^ β ≤ 2 * (r / radius k) ^ β := by
      calc
        _ ≤ (2 * (r / radius k)) ^ β :=
          Real.rpow_le_rpow (by positivity)
            (by simpa only [mul_div_assoc] using
              div_le_div_of_nonneg_right hlr.le (hradius k).le) hβ.le
        _ = (2 : ℝ) ^ β * (r / radius k) ^ β :=
          Real.mul_rpow (by norm_num) (by positivity)
        _ ≤ 2 * (r / radius k) ^ β := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hβ1
    exact hlocal.trans (hbound.trans (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _)))


/-- A broad packet whose size is measured against a fixed reference mass. -/
def DenseAngularPacket {E : Type*} [NormedAddCommGroup E] {n : ℕ}
    (v : Fin n → E) (β δ : ℝ) (K : ℕ) (M : ℝ) (W : Finset (Fin n)) : Prop :=
  W.Nonempty ∧ ∃ k : ℕ, k ≤ K ∧ ∃ j : Fin n,
    (∀ i ∈ W, pd (v i) (v j) ≤ 2 * (1 / 2 : ℝ) ^ k) ∧
    M * ((1 / 2 : ℝ) ^ k) ^ β ≤ W.card ∧
    ∀ u r, δ ≤ r →
      ((W.filter (fun i => pd (v i) u ≤ r)).card : ℝ) ≤
        2 * (r / (1 / 2 : ℝ) ^ k) ^ β * (W.card : ℝ)

/-- Greedy extraction stops once at most `M` directions remain. Every selected
packet has the corresponding scale-dependent lower cardinality. -/
theorem partial_angular_partition {E : Type*} [NormedAddCommGroup E] {n : ℕ}
    (v : Fin n → E) (hv : ∀ i, ‖v i‖ = 1) {β δ : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hδ : 0 < δ) {K : ℕ}
    (hK2 : (1 / 2 : ℝ) ^ K < 2 * δ) (M : ℝ) (hM : 0 ≤ M)
    (S : Finset (Fin n)) :
    ∃ P : Finset (Finset (Fin n)),
      (∀ W ∈ P, DenseAngularPacket v β δ K M W) ∧
      (∀ W ∈ P, W ⊆ S) ∧ (P : Set (Finset (Fin n))).Pairwise Disjoint ∧
      (S.card : ℝ) ≤ M + (P.biUnion id).card := by
  classical
  refine Finset.strongInductionOn S ?_
  intro S ih
  by_cases hsmall : (S.card : ℝ) ≤ M
  · exact ⟨∅, by simp, by simp, by simp, by simpa using hsmall⟩
  have hS : S.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (hM.trans_lt (lt_of_not_ge hsmall))
  obtain ⟨k, hk, j, W, hWne, hWS, hcap, hsize, hrob⟩ :=
    large_angular_packet v hv hβ hβ1 hδ hK2 S hS
  have hW : DenseAngularPacket v β δ K M W := by
    refine ⟨hWne, k, hk, j, hcap, ?_, hrob⟩
    exact (mul_le_mul_of_nonneg_right (le_of_not_ge hsmall) (by positivity)).trans
      (by simpa only [mul_comm] using hsize)
  obtain ⟨P, hgood, hsub, hdis, hcount⟩ :=
    ih (S \ W) (Finset.sdiff_ssubset hWS hWne)
  have hd (U : Finset (Fin n)) (hU : U ∈ P) : Disjoint W U := by
    apply Finset.disjoint_left.mpr
    intro i hiW hiU
    exact (Finset.mem_sdiff.mp (hsub U hU hiU)).2 hiW
  have hdall : Disjoint W (P.biUnion id) :=
    (Finset.disjoint_biUnion_right _ _ _).mpr hd
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
  · rw [Finset.biUnion_insert, id_eq, Finset.card_union_of_disjoint hdall, Nat.cast_add]
    have hcards : ((S \ W).card : ℝ) + W.card = S.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hWS
    linarith

end WangZahlLot.Obl.wz_broad_grains_initialization
