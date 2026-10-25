-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.Selection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Basic

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open scoped BigOperators

theorem power_bin {ρ s : ℝ} (_hρ : 0 < ρ) {K : ℕ} (hK : 0 < K)
    (hl : ρ ^ K ≤ s) (hu : s ≤ 1) :
    ∃ j : Fin K, ρ ^ (j.val + 1) ≤ s ∧ s ≤ ρ ^ j.val := by
  induction K with
  | zero => omega
  | succ K ih =>
    by_cases hk : K = 0
    · subst K
      exact ⟨⟨0, by omega⟩, by simpa using hl, by simpa using hu⟩
    · by_cases hs : ρ ^ K ≤ s
      · obtain ⟨j, hj, hj'⟩ := ih (Nat.pos_of_ne_zero hk) hs
        exact ⟨⟨j.val, by omega⟩, hj, hj'⟩
      · exact ⟨⟨K, Nat.lt_succ_self K⟩, hl, (not_le.mp hs).le⟩

theorem weighted_color_real {α : Type*} [DecidableEq α] {K : ℕ} (hK : 0 < K)
    (s : Finset α) (c : α → Fin K) (w : α → ℝ) {H : ℝ}
    (hH : H ≤ ∑ i ∈ s, w i) :
    ∃ j : Fin K, H / K ≤ ∑ i ∈ s.filter (fun i => c i = j), w i := by
  classical
  have : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  have hK' : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hK.ne'
  have he : (K : ℝ) * (H / K) = H := by field_simp
  have hsum : (∑ _j : Fin K, H / K) ≤ ∑ j : Fin K,
      ∑ i ∈ s.filter (fun i => c i = j), w i := by
    rw [Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) w]
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, he] using hH
  obtain ⟨j, _, hj⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨j, hj⟩

theorem density_selection {α : Type*} [DecidableEq α] (s : Finset α)
    (d w : α → ℝ) {ρ H : ℝ} (hρ : 0 < ρ) {K : ℕ} (hK : 0 < K)
    (hd : ∀ i ∈ s, d i ≤ 1) (hH : H ≤ ∑ i ∈ s, w i)
    (hlow : (∑ i ∈ s.filter (fun i => d i < ρ ^ K), w i) ≤ H / 2) :
    ∃ s' : Finset α, s' ⊆ s ∧ H / (2 * K) ≤ ∑ i ∈ s', w i ∧
      ∃ t : ℝ, 0 < t ∧ ∀ i ∈ s', t ≤ d i ∧ ρ * d i ≤ t := by
  classical
  let good := s.filter (fun i => ρ ^ K ≤ d i)
  have hmass : H / 2 ≤ ∑ i ∈ good, w i := by
    have he := Finset.sum_filter_add_sum_filter_not s (fun i => ρ ^ K ≤ d i) w
    have hlo : (∑ i ∈ s.filter (fun i => ¬ρ ^ K ≤ d i), w i) ≤ H / 2 := by
      simpa only [not_le] using hlow
    dsimp [good]
    linarith
  have hbins (i : α) : ∃ j : Fin K, i ∈ good →
      ρ ^ (j.val + 1) ≤ d i ∧ d i ≤ ρ ^ j.val := by
    by_cases hi : i ∈ good
    · obtain ⟨j, hj⟩ := power_bin hρ hK (Finset.mem_filter.mp hi).2
        (hd i (Finset.mem_filter.mp hi).1)
      exact ⟨j, fun _ => hj⟩
    · exact ⟨⟨0, hK⟩, fun h => False.elim (hi h)⟩
  choose c hc using hbins
  obtain ⟨j, hj⟩ := weighted_color_real hK good c w hmass
  refine ⟨good.filter (fun i => c i = j),
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _), ?_,
    ρ ^ (j.val + 1), pow_pos hρ _, ?_⟩
  · convert hj using 1 <;> field_simp
  · intro i hi
    obtain ⟨hig, hij⟩ := Finset.mem_filter.mp hi
    have hh := hc i hig
    rw [hij] at hh
    refine ⟨hh.1, ?_⟩
    rw [pow_succ]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh.2 hρ.le

theorem dense_indices {n : ℕ} (f : Fin n → ℝ) {t U : ℝ} (ht : 0 ≤ t)
    (hU : ∀ i, f i ≤ U) (hmass : 2 * n * t ≤ ∑ i, f i) :
    let s := Finset.univ.filter (fun i => t ≤ f i)
    (n : ℝ) * t ≤ ∑ i ∈ s, f i ∧ (n : ℝ) * t ≤ (s.card : ℝ) * U := by
  classical
  dsimp only
  let s := Finset.univ.filter (fun i => t ≤ f i)
  have hlo : (∑ i ∈ Finset.univ.filter (fun i => ¬t ≤ f i), f i) ≤ n * t := by
    calc
      _ ≤ ∑ _i ∈ Finset.univ.filter (fun i => ¬t ≤ f i), t :=
        Finset.sum_le_sum fun i hi => (not_le.mp (Finset.mem_filter.mp hi).2).le
      _ ≤ ∑ _i : Fin n, t := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ => ht)
      _ = _ := by simp
  have hsum := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => t ≤ f i) f
  have hs : (n : ℝ) * t ≤ ∑ i ∈ s, f i := by dsimp [s]; linarith
  refine ⟨hs, hs.trans ?_⟩
  calc
    _ ≤ ∑ _i ∈ s, U := Finset.sum_le_sum (fun i _ => hU i)
    _ = _ := by simp [s]

theorem dense_index_subfamily {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ)
    {t U : ℝ} (ht : 0 < t) (hU : 0 < U) (hf : ∀ i, f i ≤ U)
    (hmass : 2 * n * t ≤ ∑ i, f i) :
    ∃ (N : ℕ) (j : Fin N → Fin n), 0 < N ∧ Function.Injective j ∧
      (t / U) * n ≤ N ∧ ∀ i, t ≤ f (j i) := by
  classical
  let s := Finset.univ.filter (fun i => t ≤ f i)
  have hsize : (n : ℝ) * t ≤ (s.card : ℝ) * U := (dense_indices f ht.le hf hmass).2
  have hspos : 0 < s.card := by
    by_contra hh
    have he : s.card = 0 := Nat.eq_zero_of_not_pos hh
    have hnt : 0 < (n : ℝ) * t := mul_pos (Nat.cast_pos.mpr hn) ht
    rw [he, Nat.cast_zero, zero_mul] at hsize
    linarith
  let j : Fin s.card → Fin n := fun i => (s.equivFin.symm i).val
  refine ⟨s.card, j, hspos, ?_, ?_, ?_⟩
  · intro i k h
    exact s.equivFin.symm.injective (Subtype.ext h)
  · rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hU).mpr (by simpa only [mul_comm] using hsize)
  · intro i
    exact (Finset.mem_filter.mp (s.equivFin.symm i).property).2

end WangZahlLot.Obl.wz_nonflat_factored_improvement
