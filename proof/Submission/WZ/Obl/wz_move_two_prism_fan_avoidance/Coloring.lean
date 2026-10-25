-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_prism_fan_avoidance.Coloring.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# A local-optimum colouring for symmetric edge weights, and a numeric cutoff
-/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_prism_fan_avoidance

open Finset

/-- The total weight of monochromatic ordered pairs of a colouring `col`. -/
private def wzColEnergy {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ℕ} (w : ι → ι → ℝ)
    (col : ι → Fin K) : ℝ :=
  ∑ a, ∑ b, if b ≠ a ∧ col b = col a then w a b else 0

/-- The monochromatic pairs avoiding a vertex `i`. -/
private def wzColRest {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ℕ} (w : ι → ι → ℝ)
    (col : ι → Fin K) (i : ι) : ℝ :=
  ∑ a ∈ univ.erase i, ∑ b ∈ univ.erase i, if b ≠ a ∧ col b = col a then w a b else 0

/-- Splitting off the pairs through a vertex `i`: they contribute twice its own-colour weight. -/
private lemma wzColEnergy_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ℕ}
    (w : ι → ι → ℝ) (hsymm : ∀ i j, w i j = w j i) (col : ι → Fin K) (i : ι) :
    wzColEnergy w col =
      wzColRest w col i + 2 * ∑ j ∈ univ.filter (fun j => j ≠ i ∧ col j = col i), w i j := by
  unfold wzColEnergy wzColRest
  have hown : ∑ j ∈ univ.filter (fun j => j ≠ i ∧ col j = col i), w i j =
      ∑ b, (if b ≠ i ∧ col b = col i then w i b else 0) := Finset.sum_filter _ _
  have hcol : ∑ a ∈ univ.erase i, (if i ≠ a ∧ col i = col a then w a i else 0) =
      ∑ b, (if b ≠ i ∧ col b = col i then w i b else 0) := by
    rw [← Finset.add_sum_erase _ _ (mem_univ i)]
    simp only [ne_eq, not_true_eq_false, false_and, ite_false, zero_add]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    have hai : a ≠ i := Finset.ne_of_mem_erase ha
    by_cases hc : col a = col i
    · have h1 : (¬i = a ∧ col i = col a) := ⟨Ne.symm hai, hc.symm⟩
      have h2 : (¬a = i ∧ col a = col i) := ⟨hai, hc⟩
      rw [ite_eq_left h1, ite_eq_left h2, hsymm]
    · have h1 : ¬(¬i = a ∧ col i = col a) := fun h => hc h.2.symm
      have h2 : ¬(¬a = i ∧ col a = col i) := fun h => hc h.2
      rw [ite_eq_right h1, ite_eq_right h2]
  have hsplit : ∀ a ∈ univ.erase i, (∑ b, if b ≠ a ∧ col b = col a then w a b else 0) =
      (if i ≠ a ∧ col i = col a then w a i else 0) +
        ∑ b ∈ univ.erase i, (if b ≠ a ∧ col b = col a then w a b else 0) :=
    fun a _ => (Finset.add_sum_erase _ _ (mem_univ i)).symm
  rw [← Finset.add_sum_erase _ _ (mem_univ i), Finset.sum_congr rfl hsplit,
    Finset.sum_add_distrib, hcol, hown]
  ring

/-- Recolouring `i` does not change the pairs avoiding `i`. -/
private lemma wzColRest_update {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ℕ}
    (w : ι → ι → ℝ) (col : ι → Fin K) (i : ι) (κ : Fin K) :
    wzColRest w (Function.update col i κ) i = wzColRest w col i := by
  unfold wzColRest
  refine Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => ?_))
  rw [Function.update_of_ne (Finset.ne_of_mem_erase ha),
    Function.update_of_ne (Finset.ne_of_mem_erase hb)]

/-- After recolouring `i` with `κ`, its own-colour weight is its weight towards colour `κ`. -/
private lemma wzColOwn_update {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ℕ}
    (w : ι → ι → ℝ) (col : ι → Fin K) (i : ι) (κ : Fin K) :
    ∑ j ∈ univ.filter (fun j => j ≠ i ∧ Function.update col i κ j = Function.update col i κ i),
        w i j =
      ∑ j ∈ univ.filter (fun j => j ≠ i ∧ col j = κ), w i j := by
  refine Finset.sum_congr (Finset.filter_congr (fun j _ => ?_)) (fun _ _ => rfl)
  constructor
  · rintro ⟨hj, hc⟩
    rw [Function.update_of_ne hj, Function.update_self] at hc
    exact ⟨hj, hc⟩
  · rintro ⟨hj, hc⟩
    rw [Function.update_of_ne hj, Function.update_self]
    exact ⟨hj, hc⟩

theorem local_opt_coloring {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ℕ) (hK : 0 < K)
    (w : ι → ι → ℝ) (hsymm : ∀ i j, w i j = w j i) :
    ∃ col : ι → Fin K, ∀ i (κ : Fin K),
      ∑ j ∈ Finset.univ.filter (fun j => j ≠ i ∧ col j = col i), w i j ≤
      ∑ j ∈ Finset.univ.filter (fun j => j ≠ i ∧ col j = κ), w i j := by
  have : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  obtain ⟨col, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (ι → Fin K))
    (fun col => wzColEnergy w col) Finset.univ_nonempty
  refine ⟨col, fun i κ => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have h := hmin (Function.update col i κ) (mem_univ _)
  rw [wzColEnergy_eq w hsymm (Function.update col i κ) i, wzColEnergy_eq w hsymm col i,
    wzColRest_update, wzColOwn_update] at h
  linarith

theorem coloring_own_le {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ℕ) (hK : 0 < K)
    (w : ι → ι → ℝ) (hsymm : ∀ i j, w i j = w j i) :
    ∃ col : ι → Fin K, ∀ i,
      (K : ℝ) * ∑ j ∈ Finset.univ.filter (fun j => j ≠ i ∧ col j = col i), w i j ≤
      ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), w i j := by
  obtain ⟨col, hcol⟩ := local_opt_coloring K hK w hsymm
  refine ⟨col, fun i => ?_⟩
  have h1 : ∑ _κ : Fin K, ∑ j ∈ univ.filter (fun j => j ≠ i ∧ col j = col i), w i j ≤
      ∑ κ : Fin K, ∑ j ∈ univ.filter (fun j => j ≠ i ∧ col j = κ), w i j :=
    Finset.sum_le_sum (fun κ _ => hcol i κ)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  have h2 : ∑ κ : Fin K, ∑ j ∈ univ.filter (fun j => j ≠ i ∧ col j = κ), w i j =
      ∑ j ∈ univ.filter (fun j => j ≠ i), w i j := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hj : j = i
    · simp [hj]
    · simp only [hj, ne_eq, not_false_eq_true, true_and, ite_true]
      rw [Finset.sum_ite_eq]
      simp
  linarith

theorem small_delta_log {s C : ℝ} (hs : 0 < s) (hC : 0 ≤ C) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
      C * (Real.logb 2 (1 / δ) + 2) ≤ δ ^ (-s) := by
  set ε : ℝ := s / 2 with hε_def
  have hε : 0 < ε := by positivity
  set L : ℝ := Real.log 2 with hL_def
  have hL : 0 < L := Real.log_pos (by norm_num)
  set C' : ℝ := C * (1 / (ε * L) + 2) with hC'_def
  have hC' : 0 ≤ C' := by positivity
  set M : ℝ := C' + 1 with hM_def
  have hM : 0 < M := by positivity
  have hMe : 0 < M ^ ε⁻¹ := Real.rpow_pos_of_pos hM _
  refine ⟨min 1 (M ^ ε⁻¹)⁻¹, lt_min one_pos (inv_pos.mpr hMe), min_le_left _ _, ?_⟩
  intro δ hδ hδd
  have hδ1 : δ ≤ 1 := hδd.trans (min_le_left _ _)
  have hδM : δ ≤ (M ^ ε⁻¹)⁻¹ := hδd.trans (min_le_right _ _)
  set t : ℝ := δ⁻¹ with ht_def
  have ht0 : 0 < t := inv_pos.mpr hδ
  have ht1 : 1 ≤ t := (one_le_inv₀ hδ).mpr hδ1
  have htM : M ^ ε⁻¹ ≤ t := (le_inv_comm₀ hδ hMe).mp hδM
  set u : ℝ := t ^ ε with hu_def
  have hu1 : 1 ≤ u := Real.one_le_rpow ht1 hε.le
  have huM : M ≤ u := by
    have := Real.rpow_le_rpow hMe.le htM hε.le
    rwa [Real.rpow_inv_rpow hM.le hε.ne'] at this
  have hlog : Real.log t ≤ u / ε := Real.log_le_rpow_div ht0.le hε
  have hlogb : Real.logb 2 (1 / δ) = Real.log t / L := by
    rw [one_div]
    rfl
  have hrhs : δ ^ (-s) = u * u := by
    rw [Real.rpow_neg_eq_inv_rpow, ← ht_def, hu_def, ← Real.rpow_add ht0]
    congr 1
    rw [hε_def]
    ring
  rw [hlogb, hrhs]
  have h1 : Real.log t / L ≤ u / (ε * L) := by
    rw [← div_div]
    exact div_le_div_of_nonneg_right hlog hL.le
  have h2 : Real.log t / L + 2 ≤ u * (1 / (ε * L) + 2) := by
    have : u * (1 / (ε * L) + 2) = u / (ε * L) + 2 * u := by ring
    rw [this]
    linarith
  have h3 : C * (Real.log t / L + 2) ≤ C' * u := by
    calc C * (Real.log t / L + 2) ≤ C * (u * (1 / (ε * L) + 2)) :=
          mul_le_mul_of_nonneg_left h2 hC
      _ = C' * u := by rw [hC'_def]; ring
  have h4 : C' * u ≤ u * u :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  linarith

end WangZahlLot.Obl.wz_move_two_prism_fan_avoidance
