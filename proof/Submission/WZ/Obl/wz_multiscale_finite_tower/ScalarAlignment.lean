-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.ScalarAlignment.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_tower_balanced_refinement.Regularize
import Submission.WZ.Obl.wz_multiscale_finite_tower.Basic
import Submission.WZ.Obl.kakeya_three_le_dimH_of_tube_estimate.Packing

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open scoped ENNReal
open Set Metric LeanEval.Analysis.WangZahlKakeya

lemma weighted_fintype_color {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype β] [Nonempty β]
    (U : Finset α) (c : α → β) (w : α → ℝ≥0∞) :
    ∃ b : β, (∑ i ∈ U, w i) ≤ (Fintype.card β : ℝ≥0∞) *
      ∑ i ∈ U.filter (fun i => c i = b), w i := by
  classical
  let e := Fintype.equivFin β
  obtain ⟨b, hb⟩ := WangZahlLot.Obl.wz_tower_balanced_refinement.weighted_color
    (Fintype.card_pos) U (fun i => e (c i)) w
  refine ⟨e.symm b, ?_⟩
  simpa only [Equiv.apply_eq_iff_eq_symm_apply] using hb

/-- A bounded scalar family can be moved to one common value toward zero,
using shifts at most b and losing at most the factor b/4 in arbitrary weights. -/
theorem select_inward_scalar {α : Type*} [DecidableEq α] {b : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (U : Finset α) (h : α → ℝ)
    (hh : ∀ i, |h i| ≤ 1) (w : α → ℝ≥0∞) (hmass : 0 < ∑ i ∈ U, w i) :
    ∃ S : Finset α, S ⊆ U ∧ S.Nonempty ∧ ∃ h₀ : ℝ,
      ENNReal.ofReal (b / 4) * (∑ i ∈ U, w i) ≤ ∑ i ∈ S, w i ∧
      ∀ i ∈ S, |h₀| ≤ |h i| ∧ |h₀ - h i| ≤ b := by
  classical
  let M := Nat.floor (1 / b) + 1
  let C := Fin M × Bool
  have hM : 0 < M := Nat.succ_pos _
  haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  let c : α → C := fun i =>
    (⟨Nat.floor (|h i| / b), Nat.lt_succ_of_le (Nat.floor_mono
      ((div_le_div_iff_of_pos_right hb).mpr (hh i)))⟩, decide (h i < 0))
  let val : C → ℝ := fun z => if z.2 then -((z.1.val : ℝ) * b) else (z.1.val : ℝ) * b
  have hval (i : α) : |val (c i)| ≤ |h i| ∧ |val (c i) - h i| ≤ b := by
    have hx0 : 0 ≤ |h i| / b := div_nonneg (abs_nonneg _) hb.le
    have hlo : (Nat.floor (|h i| / b) : ℝ) * b ≤ |h i| :=
      (le_div_iff₀ hb).mp (Nat.floor_le hx0)
    have hhi : |h i| < ((Nat.floor (|h i| / b) : ℝ) + 1) * b :=
      (div_lt_iff₀ hb).mp (Nat.lt_floor_add_one (|h i| / b))
    have hp : 0 ≤ (Nat.floor (|h i| / b) : ℝ) * b := mul_nonneg (Nat.cast_nonneg _) hb.le
    by_cases hs : h i < 0
    · simp only [val, c, decide_eq_true hs, Bool.true_eq, ↓reduceIte, abs_neg, abs_of_nonneg hp]
      rw [abs_of_neg hs] at hlo hhi ⊢
      exact ⟨hlo, abs_le.mpr ⟨by linarith, by linarith⟩⟩
    · have hs' : 0 ≤ h i := le_of_not_gt hs
      simp only [val, c, decide_eq_false hs, Bool.false_eq_true, ↓reduceIte, abs_of_nonneg hp]
      rw [abs_of_nonneg hs'] at hlo hhi ⊢
      exact ⟨hlo, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  obtain ⟨z, hz⟩ := weighted_fintype_color U c w
  let S := U.filter fun i => c i = z
  have hSne : S.Nonempty := by
    by_contra hn
    have hem : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    change (∑ i ∈ U, w i) ≤ (Fintype.card C : ℝ≥0∞) * ∑ i ∈ S, w i at hz
    simp only [hem, Finset.sum_empty, mul_zero] at hz
    exact (not_lt_of_ge hz) hmass
  have hq : (b / 4) * (Fintype.card C : ℝ) ≤ 1 := by
    have hf := (le_div_iff₀ hb).mp (Nat.floor_le (show 0 ≤ (1 : ℝ) / b by positivity))
    simp only [C, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.cast_mul,
      Nat.cast_ofNat, M, Nat.cast_add, Nat.cast_one]
    nlinarith
  refine ⟨S, Finset.filter_subset _ _, hSne, val z, ?_, ?_⟩
  · calc
      _ ≤ ENNReal.ofReal (b / 4) * ((Fintype.card C : ℝ≥0∞) * ∑ i ∈ S, w i) :=
        mul_le_mul' le_rfl hz
      _ = ENNReal.ofReal ((b / 4) * (Fintype.card C : ℝ)) * ∑ i ∈ S, w i := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, mul_assoc]
      _ ≤ 1 * ∑ i ∈ S, w i := mul_le_mul' (by simpa using ENNReal.ofReal_le_ofReal hq) le_rfl
      _ = _ := one_mul _
  · intro i hi
    simpa only [(Finset.mem_filter.mp hi).2] using hval i

theorem direction_cap_selection : ∃ K : ℝ, 1 ≤ K ∧
    ∀ {α : Type} [DecidableEq α] (U : Finset α) (v : α → Space)
      (hv : ∀ i, ‖v i‖ = 1) (w : α → ℝ≥0∞), 0 < ∑ i ∈ U, w i →
    ∃ S : Finset α, S ⊆ U ∧ S.Nonempty ∧ ∃ u : Space, ‖u‖ = 1 ∧
      (∑ i ∈ U, w i) ≤ ENNReal.ofReal K * ∑ i ∈ S, w i ∧
      ∀ i ∈ S, ‖v i - u‖ ≤ 1 / 10 := by
  classical
  obtain ⟨F, hF, hsep, hcover⟩ :=
    WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.exists_finset_separated_cover
      (isCompact_sphere (0 : Space) 1).totallyBounded (by norm_num : (0 : ℝ) < 1 / 10)
  refine ⟨(F.card : ℝ) + 1, by linarith [Nat.cast_nonneg (α := ℝ) F.card], ?_⟩
  intro α _ U v hv w hmass
  have hex (i : α) : ∃ u ∈ F, ‖v i - u‖ ≤ 1 / 10 := by
    have hh := hcover (show v i ∈ sphere (0 : Space) 1 by simpa only [mem_sphere, dist_zero_right] using hv i)
    obtain ⟨u, hu, hiu⟩ := mem_iUnion₂.mp hh
    exact ⟨u, hu, by simpa only [mem_closedBall, dist_eq_norm] using hiu⟩
  have hUne : U.Nonempty := by
    by_contra hn
    simp only [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty, lt_self_iff_false] at hmass
  obtain ⟨i₀, hi₀⟩ := hUne
  obtain ⟨u₀, hu₀, _⟩ := hex i₀
  haveI : Nonempty F := ⟨⟨u₀, hu₀⟩⟩
  let c : α → F := fun i => ⟨(hex i).choose, (hex i).choose_spec.1⟩
  obtain ⟨z, hz⟩ := weighted_fintype_color U c w
  let S := U.filter fun i => c i = z
  have hs : (∑ i ∈ U, w i) ≤ ENNReal.ofReal ((F.card : ℝ) + 1) * ∑ i ∈ S, w i := by
    apply hz.trans
    apply mul_le_mul' _ le_rfl
    simp only [Fintype.card_coe]
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hSne : S.Nonempty := by
    by_contra hn
    simp only [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty, mul_zero] at hs
    exact (not_lt_of_ge hs) hmass
  refine ⟨S, Finset.filter_subset _ _, hSne, z, ?_, hs, ?_⟩
  · simpa only [mem_sphere, dist_zero_right] using hF z.property
  · intro i hi
    have he : (c i).val = z.val := congrArg Subtype.val (Finset.mem_filter.mp hi).2
    rw [← he]
    exact (hex i).choose_spec.2

end WangZahlLot.Obl.wz_multiscale_finite_tower
