-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.TwoEndsPrune.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# From pair counts at dyadic scales to pointwise Frostman counts

`two_ends_prune`: points `H` with real positions `pos`, whose numbers of pairs at distance
at most `r 2 ^ k` are at most `B (r 2 ^ k) ^ σ #H ^ 2` for `k ≤ K₀`, contain `H' ⊆ H` with
`#H ≤ 2 #H'` in which every point has at most `2 (K₀ + 1) B (r 2 ^ k) ^ σ #H` points of `H`
within `r 2 ^ k`, for every `k ≤ K₀` (Chebyshev at each scale, union bound over the scales).

`two_ends_frostman`: the same `H'` satisfies the window bound
`#{p ∈ H' : |pos p - x| ≤ ρ} ≤ 2 (K₀ + 1) B (4 ρ) ^ σ #H` for `r ≤ ρ` with `4 ρ ≤ r 2 ^ K₀`.

Used for the 1/2-Frostman pins on the rich line (`line_frostman` of `SP.HalfConfig`).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

open scoped BigOperators

/-- Number of points of `H` within `d` of the position of `p`. -/
noncomputable def nearCount {α : Type*} (H : Finset α) (pos : α → ℝ) (d : ℝ) (p : α) : ℕ :=
  (H.filter (fun p' => |pos p - pos p'| ≤ d)).card

theorem sum_nearCount {α : Type*} (H : Finset α) (pos : α → ℝ) (d : ℝ) :
    ∑ p ∈ H, nearCount H pos d p =
      ((H ×ˢ H).filter (fun q => |pos q.1 - pos q.2| ≤ d)).card := by
  classical
  rw [Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p _
  rw [nearCount, Finset.card_filter]

theorem two_ends_prune {α : Type*} [DecidableEq α] (H : Finset α) (pos : α → ℝ)
    {r σ B : ℝ} (K₀ : ℕ) (hB : 0 < B) (hr : 0 < r)
    (hpairs : ∀ k ≤ K₀,
      (((H ×ˢ H).filter (fun q => |pos q.1 - pos q.2| ≤ r * 2 ^ k)).card : ℝ) ≤
        B * (r * 2 ^ k) ^ σ * (H.card : ℝ) ^ 2) :
    ∃ H' ⊆ H, (H.card : ℝ) ≤ 2 * (H'.card : ℝ) ∧
      ∀ p ∈ H', ∀ k ≤ K₀,
        (nearCount H pos (r * 2 ^ k) p : ℝ) ≤
          2 * (K₀ + 1) * B * (r * 2 ^ k) ^ σ * (H.card : ℝ) := by
  classical
  set bad : ℕ → Finset α := fun k => H.filter (fun p =>
    2 * (K₀ + 1) * B * (r * 2 ^ k) ^ σ * (H.card : ℝ) < (nearCount H pos (r * 2 ^ k) p : ℝ))
    with hbad
  -- each bad set is small
  have hbadsmall : ∀ k ≤ K₀, 2 * (K₀ + 1) * ((bad k).card : ℝ) ≤ (H.card : ℝ) := by
    intro k hk
    have hdpos : 0 < (r * 2 ^ k) ^ σ := Real.rpow_pos_of_pos (by positivity) σ
    by_cases hH : H.card = 0
    · have : bad k = ∅ := by
        rw [Finset.card_eq_zero] at hH
        simp [hbad, hH]
      rw [this]; simp
    have hHpos : (0 : ℝ) < H.card := by exact_mod_cast Nat.pos_of_ne_zero hH
    set T : ℝ := 2 * (K₀ + 1) * B * (r * 2 ^ k) ^ σ * (H.card : ℝ) with hT
    have hTpos : 0 < T := by positivity
    have h1 : ((bad k).card : ℝ) * T ≤ ∑ p ∈ bad k, (nearCount H pos (r * 2 ^ k) p : ℝ) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_le_sum
      intro p hp
      exact (Finset.mem_filter.mp hp).2.le
    have h2 : ∑ p ∈ bad k, (nearCount H pos (r * 2 ^ k) p : ℝ) ≤
        ∑ p ∈ H, (nearCount H pos (r * 2 ^ k) p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.cast_nonneg _)
    have h3 : ∑ p ∈ H, (nearCount H pos (r * 2 ^ k) p : ℝ) ≤
        B * (r * 2 ^ k) ^ σ * (H.card : ℝ) ^ 2 := by
      have := hpairs k hk
      rw [← sum_nearCount] at this
      exact_mod_cast this
    have h4 : ((bad k).card : ℝ) * T ≤ B * (r * 2 ^ k) ^ σ * (H.card : ℝ) ^ 2 :=
      h1.trans (h2.trans h3)
    have h5 : ((bad k).card : ℝ) * T = (2 * (K₀ + 1) * ((bad k).card : ℝ)) *
        (B * (r * 2 ^ k) ^ σ * (H.card : ℝ)) := by rw [hT]; ring
    have h6 : B * (r * 2 ^ k) ^ σ * (H.card : ℝ) ^ 2 =
        (H.card : ℝ) * (B * (r * 2 ^ k) ^ σ * (H.card : ℝ)) := by ring
    rw [h5, h6] at h4
    exact le_of_mul_le_mul_right h4 (by positivity)
  -- remove all bad points
  set allbad : Finset α := (Finset.range (K₀ + 1)).biUnion bad with hallbad
  refine ⟨H \ allbad, Finset.sdiff_subset, ?_, ?_⟩
  · have hU : (allbad.card : ℝ) ≤ ∑ k ∈ Finset.range (K₀ + 1), ((bad k).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    have hsum : ∑ k ∈ Finset.range (K₀ + 1), ((bad k).card : ℝ) ≤
        ∑ k ∈ Finset.range (K₀ + 1), (H.card : ℝ) / (2 * (K₀ + 1)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k ≤ K₀ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [le_div_iff₀ (by positivity)]
      linarith [hbadsmall k hk']
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hhalf : ((K₀ + 1 : ℕ) : ℝ) * ((H.card : ℝ) / (2 * (K₀ + 1))) = (H.card : ℝ) / 2 := by
      push_cast; field_simp
    rw [hhalf] at hsum
    have hcard : (H.card : ℝ) ≤ ((H \ allbad).card : ℝ) + (allbad.card : ℝ) := by
      have h := Finset.card_le_card_sdiff_add_card (s := H) (t := allbad)
      exact_mod_cast h
    linarith
  · intro p hp k hk
    have hpH := (Finset.mem_sdiff.mp hp).1
    have hpnb := (Finset.mem_sdiff.mp hp).2
    by_contra hcon
    push Not at hcon
    apply hpnb
    rw [hallbad, Finset.mem_biUnion]
    exact ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), Finset.mem_filter.mpr ⟨hpH, hcon⟩⟩

/-- Window bounds on the pruned set. -/
theorem two_ends_frostman {α : Type*} [DecidableEq α] (H : Finset α) (pos : α → ℝ)
    {r σ B : ℝ} (K₀ : ℕ) (hB : 0 < B) (hr : 0 < r) (hσ : 0 ≤ σ)
    (hpairs : ∀ k ≤ K₀,
      (((H ×ˢ H).filter (fun q => |pos q.1 - pos q.2| ≤ r * 2 ^ k)).card : ℝ) ≤
        B * (r * 2 ^ k) ^ σ * (H.card : ℝ) ^ 2) :
    ∃ H' ⊆ H, (H.card : ℝ) ≤ 2 * (H'.card : ℝ) ∧
      ∀ x ρ : ℝ, r ≤ ρ → 4 * ρ ≤ r * 2 ^ K₀ →
        ((H'.filter (fun p => |pos p - x| ≤ ρ)).card : ℝ) ≤
          2 * (K₀ + 1) * B * (4 * ρ) ^ σ * (H.card : ℝ) := by
  classical
  obtain ⟨H', hH'H, hcard, hnear⟩ := two_ends_prune H pos K₀ hB hr hpairs
  refine ⟨H', hH'H, hcard, ?_⟩
  intro x ρ hρ hρK
  set W := H'.filter (fun p => |pos p - x| ≤ ρ) with hW
  by_cases hWe : W = ∅
  · rw [hWe, Finset.card_empty, Nat.cast_zero]
    have : 0 ≤ (4 * ρ) ^ σ := Real.rpow_nonneg (by linarith) σ
    positivity
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hWe
  have hpH' := (Finset.mem_filter.mp hp).1
  have hpx := (Finset.mem_filter.mp hp).2
  -- a dyadic scale between 2ρ and 4ρ
  have hex : ∃ k : ℕ, 2 * ρ ≤ r * 2 ^ k := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (2 * ρ / r) (by norm_num : (1 : ℝ) < 2)
    exact ⟨k, by rw [div_lt_iff₀ hr] at hk; linarith⟩
  let k := Nat.find hex
  have hk : 2 * ρ ≤ r * 2 ^ k := Nat.find_spec hex
  have hρ0 : 0 < ρ := hr.trans_le hρ
  have hk0 : k ≠ 0 := by
    intro h0
    have := hk
    rw [show k = 0 from h0, pow_zero, mul_one] at this
    linarith
  have hkmin : r * 2 ^ (k - 1) < 2 * ρ := by
    have := Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero hk0) one_pos)
    exact lt_of_not_ge this
  have hkup : r * 2 ^ k ≤ 4 * ρ := by
    have h2 : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [h2]; nlinarith
  have hkK : k ≤ K₀ := by
    by_contra hcon
    push Not at hcon
    have h1 : (2 : ℝ) ^ K₀ < 2 ^ k := pow_lt_pow_right₀ (by norm_num) hcon
    have h2 : r * 2 ^ K₀ < r * 2 ^ k := mul_lt_mul_of_pos_left h1 hr
    linarith
  have hsub : W ⊆ H.filter (fun p' => |pos p - pos p'| ≤ r * 2 ^ k) := by
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    refine Finset.mem_filter.mpr ⟨hH'H hq'.1, ?_⟩
    have h1 := hq'.2
    calc |pos p - pos q| = |(pos p - x) - (pos q - x)| := by ring_nf
      _ ≤ |pos p - x| + |pos q - x| := abs_sub _ _
      _ ≤ ρ + ρ := add_le_add hpx h1
      _ ≤ r * 2 ^ k := by linarith
  have hW1 : (W.card : ℝ) ≤ (nearCount H pos (r * 2 ^ k) p : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  refine hW1.trans ((hnear p hpH' k hkK).trans ?_)
  have hmono : (r * 2 ^ k) ^ σ ≤ (4 * ρ) ^ σ :=
    Real.rpow_le_rpow (by positivity) hkup hσ
  have hc : 0 ≤ 2 * ((K₀ : ℝ) + 1) * B := by positivity
  calc 2 * ((K₀ : ℝ) + 1) * B * (r * 2 ^ k) ^ σ * (H.card : ℝ)
      = (2 * ((K₀ : ℝ) + 1) * B) * (r * 2 ^ k) ^ σ * (H.card : ℝ) := by ring
    _ ≤ (2 * ((K₀ : ℝ) + 1) * B) * (4 * ρ) ^ σ * (H.card : ℝ) := by gcongr
    _ = _ := by ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
