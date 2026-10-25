-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.ShortLength.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.PrismMass
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.LargePrism

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, ShortLength.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V A)

/-- A fixed power separation between coarse and fine radii forces a
uniformly short prism length, directly from the frozen hypotheses. -/
theorem short_length_at_separated_scale {ω ζ τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hβ : 0 < ω * ζ / 100) (hβ1 : ω * ζ / 100 ≤ 1) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧ ∀ δ h : ℝ,
      0 < δ → δ ≤ d₀ → h ≤ τ * (ω * ζ / 100) / 12 →
      ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
        A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
        ∀ (ρ c : ℝ) (D : PrismData n) (o : ℕ),
          D.Valid ω ζ δ h ρ c x v Y o → δ ^ (1 - τ) ≤ ρ →
          c < δ ^ (τ * (ω * ζ / 100) / 8) := by
  let β := ω * ζ / 100
  have hb : 0 < τ * β := mul_pos hτ hβ
  have hb1 : τ * β ≤ 1 := by
    calc τ * β ≤ 1 * 1 := mul_le_mul hτ1 hβ1 hβ.le zero_le_one
         _ = 1 := one_mul _
  obtain ⟨d₁, hd₁, hsmall₁⟩ := WangZahlLot.Obl.wz_move_two_long_grains_gain.small_rpow
    (p := τ * β / 2) (by positivity) (K := 1 / 2985984) (by norm_num)
  obtain ⟨d₂, hd₂, hsmall₂⟩ := WangZahlLot.Obl.wz_move_two_long_grains_gain.small_rpow
    (p := 1 - τ * β / 8) (by linarith) (K := 1 / 4) (by norm_num)
  refine ⟨min 1 (min d₁ d₂), lt_min zero_lt_one (lt_min hd₁ hd₂), min_le_left _ _, ?_⟩
  intro δ h hδ hδd hh n x v Y hA ρ c D o H hρ
  have hδ1 : δ ≤ 1 := hδd.trans (min_le_left _ _)
  have hd1 : δ ≤ d₁ := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hd2 : δ ≤ d₂ := hδd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hρ0 : 0 < ρ := (Real.rpow_pos_of_pos hδ (1 - τ)).trans_le hρ
  have hc0 : 0 < c := hδ.trans_le (H.1.trans (H.2.1.trans H.2.2.1))
  by_cases h4 : 4 * δ ≤ c
  · have hL := valid_prism_count_pos D hδ hA H
    have hbase := prism_length_budget D hδ (Real.rpow_nonneg hδ.le _) h4
      (fun i => (hA.2.1 i).1) (fun i => (hA.2.1 i).2.2.2) hA.2.2.2.2.1 H ⟨0, hL⟩
    change δ ^ (2 * h) * (ρ / δ) ^ β * c ^ 2 ≤ 1492992 * δ ^ (-h) at hbase
    have hratio : δ ^ (-τ) ≤ ρ / δ := by
      rw [show -τ = (1 - τ) - 1 by ring, Real.rpow_sub hδ, Real.rpow_one]
      exact div_le_div_of_nonneg_right hρ hδ.le
    have hpρ : δ ^ (-τ * β) ≤ (ρ / δ) ^ β := by
      rw [Real.rpow_mul hδ.le]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hδ.le _) hratio hβ.le
    by_contra hn
    have hc : δ ^ (τ * β / 8) ≤ c := le_of_not_gt hn
    have hcsq : δ ^ (τ * β / 4) ≤ c ^ 2 := by
      have hp := pow_le_pow_left₀ (Real.rpow_nonneg hδ.le _) hc 2
      rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le] at hp
      norm_num at hp
      convert hp using 1 <;> congr 1 <;> ring
    have hbound : δ ^ (2 * h - τ * β + τ * β / 4) ≤ 1492992 * δ ^ (-h) := by
      rw [Real.rpow_add hδ, Real.rpow_sub hδ, div_eq_mul_inv, ← Real.rpow_neg hδ.le]
      have hp := mul_le_mul
        (mul_le_mul_of_nonneg_left hpρ (Real.rpow_nonneg hδ.le (2 * h))) hcsq
        (Real.rpow_nonneg hδ.le _) (by positivity)
      convert hp.trans hbase using 1 <;> congr 2 <;> ring
    have hb' := mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hδ.le h)
    have hid : δ ^ (-h) * δ ^ h = 1 := by rw [← Real.rpow_add hδ]; simp
    rw [mul_assoc, hid, mul_one, ← Real.rpow_add hδ] at hb'
    have hexp : 2 * h - τ * β + τ * β / 4 + h ≤ -(τ * β / 2) := by
      change h ≤ τ * β / 12 at hh
      linarith
    have hlower := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hexp
    have hneg : δ ^ (-(τ * β / 2)) ≤ 1492992 := hlower.trans hb'
    have hfin := mul_le_mul_of_nonneg_right hneg (Real.rpow_nonneg hδ.le (τ * β / 2))
    rw [← Real.rpow_add hδ, neg_add_cancel, Real.rpow_zero] at hfin
    have hs := hsmall₁ δ hδ hd1
    nlinarith
  · have hc : c < 4 * δ := lt_of_not_ge h4
    have hs := hsmall₂ δ hδ hd2
    have he : δ = δ ^ (1 - τ * β / 8) * δ ^ (τ * β / 8) := by
      rw [← Real.rpow_add hδ, sub_add_cancel, Real.rpow_one]
    have hd : 4 * δ ≤ δ ^ (τ * β / 8) := by
      have hp := mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hδ.le (τ * β / 8))
      nlinarith
    exact hc.trans_le hd

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
