-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.QuarterScale.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.HeavyRelation

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

open Set Metric

attribute [local instance] Classical.propDecidable

theorem quarter_power_four {r : ℝ} (hr : 0 ≤ r) : (r ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = r := by
  rw [← Real.rpow_mul_natCast hr]
  norm_num

theorem quarter_heavy_scale_bound {r K : ℝ} (hr : 0 < r) (hK : 0 < K)
    (hheavy : K * r ^ (1 / 4 : ℝ) ≤ 1) : r ≤ 1 / K ^ (4 : ℕ) := by
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ K * r ^ (1 / 4 : ℝ)) hheavy 4
  rw [mul_pow, quarter_power_four hr.le, one_pow] at hpow
  apply (le_div_iff₀ (by positivity : 0 < K ^ (4 : ℕ))).mpr
  nlinarith only [hpow]

theorem quarter_heavy_cost_bound {r K C q s : ℝ}
    (hr : 0 < r) (hK : 0 < K) (hC : 0 ≤ C) (hq : 0 < q) (hs : 0 < s)
    (hheavy : K * r ^ (1 / 4 : ℝ) ≤ 1) :
    (25 / (K * r ^ (1 / 4 : ℝ))) ^ 2 * C * (4096 * r / (q * s)) ≤
      2560000 * C / (K ^ (4 : ℕ) * q * s) := by
  let z : ℝ := r ^ (1 / 4 : ℝ)
  have hz : 0 < z := by dsimp [z]; positivity
  have hz4 : z ^ (4 : ℕ) = r := quarter_power_four hr.le
  have hsq : (K * z) ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ K * z) hheavy 2
  have hscale : K ^ 2 * r ≤ z ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hsq (sq_nonneg z)
    nlinarith only [hh, hz4]
  have hscale' := mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ 2560000 * C)
  change (25 / (K * z)) ^ 2 * C * (4096 * r / (q * s)) ≤ _
  field_simp
  nlinarith only [hscale']

/-- Uniform bad-pair estimate at every scale. A cap heavier than its entire
ambient set is impossible; all remaining scales lie below `K^(-4)`. -/
theorem quarter_heavy_relation_card_lt {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (f : I → Plane) (g : J → Plane)
    {δ C q s r K B d : ℝ}
    (hF : IndexedFrostman δ C f) (hG : IndexedFrostman δ C g)
    (hδ : 0 < δ) (hC : 0 ≤ C) (hq : 0 < q) (hs : 0 < s) (hK : 0 < K)
    (hB : 0 ≤ B) (hd : 0 < d) (hδq : δ ≤ q) (hδr : δ ≤ r)
    (hqs : q * s ≤ 4096) (hsmall : 1 / K ^ (4 : ℕ) ≤ q * s / 256)
    (hpoints : ∀ i j, 1 / 4 ≤ ‖f i - g j‖ ∧ ‖f i - g j‖ ≤ 8)
    (hline : ∀ i i', f i ≠ f i' →
      ((Finset.univ.filter (fun j => |area (g j - f i) (f i' - f i)| < s * ‖f i' - f i‖)).card : ℝ) ≤
        B * (Fintype.card J : ℝ))
    (hbudget : C * q + B + 2560000 * C / (K ^ (4 : ℕ) * q * s) < d ^ 2) :
    ((Finset.univ.filter (fun p : I × J => HeavyRelation f g r (K * r ^ (1 / 4 : ℝ)) p.1 p.2)).card : ℝ) <
      d * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) := by
  classical
  have hr := hδ.trans_le hδr
  by_cases hheavy : K * r ^ (1 / 4 : ℝ) ≤ 1
  · have hδrad : δ ≤ 4096 * r / (q * s) := by
      apply (le_div_iff₀ (mul_pos hq hs)).mpr
      have hmul := mul_le_mul_of_nonneg_left hqs hδ.le
      nlinarith
    exact heavy_relation_card_lt f g hF hG hC hq hs hr (by positivity) hB hd.le hδq
      ((quarter_heavy_scale_bound hr hK hheavy).trans hsmall) hδrad hpoints hline
      ((add_le_add le_rfl (quarter_heavy_cost_bound hr hK hC hq hs hheavy)).trans_lt hbudget)
  · have hempty : Finset.univ.filter
        (fun p : I × J => HeavyRelation f g r (K * r ^ (1 / 4 : ℝ)) p.1 p.2) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hh := (Finset.mem_filter.mp hp).2
      have hcap : ((Finset.univ.filter (fun j => dist (radialDirection (f p.1) (g j))
          (radialDirection (f p.1) (g p.2)) ≤ r)).card : ℝ) ≤ (Fintype.card J : ℝ) := by
        exact_mod_cast (Finset.card_filter_le (Finset.univ : Finset J) _).trans_eq Finset.card_univ
      have hJ : (0 : ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
      exact hheavy ((mul_le_mul_iff_left₀ hJ).mp (by simpa only [one_mul] using hh.trans hcap))
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    have hI : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
    have hJ : (0 : ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
    positivity

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
