-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_cover_refinement.Arithmetic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_separated_cover_refinement

/-- A geometric net needs a number of levels depending only on its exponent gap. -/
theorem exists_net_size {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ)⁻¹ ≤ η := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hη
  refine ⟨n + 1, by omega, ?_⟩
  simpa only [Nat.cast_add, Nat.cast_one, one_div] using hn.le

/-- Consecutive powers bracket every intermediate radius. -/
theorem exists_power_bracket {b r : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (N : ℕ) (hr : b ^ N ≤ r) (hr1 : r ≤ 1) :
    ∃ j : ℕ, j ≤ N ∧ r ≤ b ^ j ∧ b ^ j ≤ b⁻¹ * r := by
  induction N with
  | zero =>
      refine ⟨0, le_rfl, by simpa using hr1, ?_⟩
      have hr' : 1 ≤ r := by simpa using hr
      have hbinv : 1 ≤ b⁻¹ := (one_le_inv₀ hb).mpr hb1
      simpa using (one_le_mul_of_one_le_of_one_le hbinv hr')
  | succ N ih =>
      by_cases h : b ^ N ≤ r
      · obtain ⟨j, hj, hjr, hjb⟩ := ih h
        exact ⟨j, hj.trans (Nat.le_succ _), hjr, hjb⟩
      · refine ⟨N, Nat.le_succ _, (lt_of_not_ge h).le, ?_⟩
        rw [inv_mul_eq_div, le_div_iff₀ hb, ← pow_succ]
        exact hr

/-- Small positive powers absorb all fixed constants. -/
theorem exists_rpow_cutoff {η c : ℝ} (hη : 0 < η) (hc : 0 < c) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → δ ^ η ≤ c := by
  refine ⟨c ^ η⁻¹, Real.rpow_pos_of_pos hc _, ?_⟩
  intro δ hδ hδd
  calc δ ^ η ≤ (c ^ η⁻¹) ^ η := Real.rpow_le_rpow hδ.le hδd hη.le
    _ = c := Real.rpow_inv_rpow hc.le hη.ne'

/-- A fixed finite net of scales with multiplicative gap at most `δ⁻η`. -/
theorem power_net {δ η : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {N : ℕ} (hN : 0 < N) (hgap : (N : ℝ)⁻¹ ≤ η) :
    ∃ s : Fin (N + 1) → ℝ, (∀ j, δ ≤ s j ∧ s j ≤ 1) ∧
      ∀ r : ℝ, δ ≤ r → r ≤ 1 → ∃ j, r ≤ s j ∧ s j ≤ δ ^ (-η) * r := by
  let b := δ ^ (N : ℝ)⁻¹
  have hb : 0 < b := Real.rpow_pos_of_pos hδ _
  have hb1 : b ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by positivity)
  have hbN : b ^ N = δ := Real.rpow_inv_natCast_pow hδ.le hN.ne'
  have hbinv : b⁻¹ ≤ δ ^ (-η) := by
    rw [show b⁻¹ = δ ^ (-(N : ℝ)⁻¹) from (Real.rpow_neg hδ.le _).symm]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  refine ⟨fun j => b ^ j.val, ?_, ?_⟩
  · intro j
    refine ⟨?_, pow_le_one₀ hb.le hb1⟩
    rw [← hbN]
    exact pow_le_pow_of_le_one hb.le hb1 (by omega)
  · intro r hr hr1
    obtain ⟨j, hj, hjr, hjb⟩ := exists_power_bracket hb hb1 N (by rwa [hbN]) hr1
    exact ⟨⟨j, by omega⟩, hjr, hjb.trans (mul_le_mul_of_nonneg_right hbinv (hδ.le.trans hr))⟩

/-- The fixed losses in selection and pruning fit within the exponent margin. -/
theorem weight_budget {a C L : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hC : 0 < C) (hL : 1 ≤ L) (hsmall : a ≤ 1 / (1000 * C * L)) :
    a ^ 4 ≤ a / C - 384 * a ^ 2 * L := by
  have hL0 : 0 < L := by linarith
  have hprod : a * (1000 * C * L) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp hsmall
  have hCL : a * C ≤ a * C * L := by
    exact le_mul_of_one_le_right (by positivity) hL
  have hfactor : C * a * (1 + 384 * L) ≤ 1 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hfactor ha.le
  have hdiv : a ^ 2 + 384 * a ^ 2 * L ≤ a / C := by
    apply (le_div_iff₀ hC).mpr
    nlinarith
  have hpow : a ^ 4 ≤ a ^ 2 := pow_le_pow_of_le_one ha.le ha1 (by norm_num)
  linarith

end WangZahlLot.Obl.wz_separated_cover_refinement
