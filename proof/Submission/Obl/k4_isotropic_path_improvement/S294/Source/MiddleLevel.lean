-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.MiddleLevel, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- The middle level of the row lists (session x1088, for x1082's root stage).

`midOf i X m = i + ⌈X m⌉` is an explicit level (so it can be put into the core source's depth
family before any path data) at least `X` above the ancestor level `i` on the grid
`s j = (j+1)/m`; `midOf_spec` keeps it `Y` below a child level `ib` when `X + Y + 1/m ≤
s_ib - s_i`.  `middle_level_bounds` turns exponent budgets `A₁ ≤ N^a₁`, `A₂ ≤ N^a₂` into the two
list conditions of x1082's `ancestor_row_lists` at the middle depth:
`A₁ δ(N, r_mid)/δ(N, r_i) ≤ 2` (so with `A₁ = 16 Lp K^8/θ`: `Lp 2K^8 δ_mid/δ_a ≤ θ/4`) and
`A₂ 2^-(T_b - T_mid) ≤ 1` (so with `A₂ = 24 Lp (K^(3R+65))^J (κ+K^8) K^R comp`: the last condition
`≤ 1/4`), together with `δ_mid ≤ δ_i` and `T_mid ≤ T_b`. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.LevelRatios

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

noncomputable section

/-- The middle level: `⌈X m⌉` levels below `i`. -/
def midOf (i : ℕ) (X : ℝ) (m : ℕ) : ℕ := i + ⌈X * m⌉₊

/-- **The middle level lies between the ancestor and the child.** -/
theorem midOf_spec {m : ℕ} {s : ℕ → ℝ} (hm : 0 < m) (hs : ∀ i, s i = ((i : ℝ) + 1) / m)
    {i ib : ℕ} {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hsep : X + Y + 1 / (m : ℝ) ≤ s ib - s i) :
    i ≤ midOf i X m ∧ midOf i X m ≤ ib ∧ X ≤ s (midOf i X m) - s i ∧
      Y ≤ s ib - s (midOf i X m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set c := ⌈X * m⌉₊ with hc
  have hc_lo : X * m ≤ c := Nat.le_ceil _
  have hc_hi : (c : ℝ) < X * m + 1 := Nat.ceil_lt_add_one (by positivity)
  have hdiff : ∀ a b : ℕ, s b - s a = ((b : ℝ) - a) / m := by
    intro a b; rw [hs, hs]; ring
  have hgap : X * m + Y * m + 1 ≤ (ib : ℝ) - i := by
    have := hsep
    rw [hdiff, le_div_iff₀ hmR] at this
    have e : (X + Y + 1 / (m : ℝ)) * m = X * m + Y * m + 1 := by field_simp
    linarith
  have hle : i + c ≤ ib := by
    have : (i : ℝ) + c ≤ ib := by nlinarith
    exact_mod_cast this
  refine ⟨by unfold midOf; omega, by unfold midOf; omega, ?_, ?_⟩
  · unfold midOf; rw [hdiff, le_div_iff₀ hmR]; push_cast; linarith
  · unfold midOf
    rw [hdiff, le_div_iff₀ hmR]
    have hcast : ((ib : ℕ) : ℝ) - ((i + c : ℕ) : ℝ) = (ib : ℝ) - i - c := by push_cast; ring
    rw [hcast]
    nlinarith

/-- **The list conditions at the middle depth** from exponent budgets. -/
theorem middle_level_bounds {N L κ₁ δ₀ si smid sb ri rmid A₁ A₂ a₁ a₂ : ℝ} {Tmid Tb : ℕ}
    (hN : 1 < N) (hL : 0 < L) (hκ : 0 < κ₁) (hδ₀ : 0 ≤ δ₀)
    (hri : |ri - si * L| ≤ δ₀ * L) (hrmid : |rmid - smid * L| ≤ δ₀ * L)
    (hTmid2 : (2 : ℝ) ^ Tmid ≤ N ^ ((κ₁ * smid + δ₀) * L))
    (hTb1 : N ^ ((κ₁ * sb - δ₀) * L) ≤ (2 : ℝ) ^ Tb)
    (hA₁ : A₁ ≤ N ^ a₁) (hA₂ : A₂ ≤ N ^ a₂) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hX : a₁ / L + 2 * δ₀ ≤ smid - si) (hY : (a₂ / L + 2 * δ₀) / κ₁ ≤ sb - smid) :
    A₁ * (O204.Split.δ N rmid / O204.Split.δ N ri) ≤ 2 ∧
      Tmid ≤ Tb ∧ A₂ * ((2 : ℝ) ^ (Tb - Tmid))⁻¹ ≤ 1 ∧
      O204.Split.δ N rmid ≤ O204.Split.δ N ri := by
  have hNp : 0 < N := by linarith
  -- thickness
  have hdr := delta_ratio_le hN hL.le hri hrmid
  have hexp1 : a₁ ≤ (smid - si - 2 * δ₀) * L := by
    have := (div_le_iff₀ hL).mp (by linarith : a₁ / L ≤ smid - si - 2 * δ₀)
    linarith
  have hratio0 : 0 ≤ O204.Split.δ N rmid / O204.Split.δ N ri :=
    div_nonneg (O204.Tangent.δ_pos _ _).le (O204.Tangent.δ_pos _ _).le
  have h1 : A₁ * (O204.Split.δ N rmid / O204.Split.δ N ri) ≤ 2 := by
    by_cases hA : A₁ ≤ 0
    · have : A₁ * (O204.Split.δ N rmid / O204.Split.δ N ri) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hA hratio0
      linarith
    push Not at hA
    calc A₁ * (O204.Split.δ N rmid / O204.Split.δ N ri)
        ≤ N ^ a₁ * (2 * N ^ (-((smid - si - 2 * δ₀) * L))) := by gcongr
      _ = 2 * N ^ (a₁ - (smid - si - 2 * δ₀) * L) := by
          rw [mul_comm, mul_assoc, ← Real.rpow_add hNp]; ring_nf
      _ ≤ 2 * N ^ (0 : ℝ) := by
          gcongr
          · exact hN.le
          · linarith
      _ = 2 := by rw [Real.rpow_zero, mul_one]
  -- clock
  have hsep2 : κ₁ * smid + δ₀ ≤ κ₁ * sb - δ₀ := by
    have h := (div_le_iff₀ hκ).mp hY
    have : 0 ≤ a₂ / L := by positivity
    linarith
  have hTmb : Tmid ≤ Tb := clock_mono hN hL.le hTmid2 hTb1 hsep2
  have hcr := clock_ratio_le (N := N) (L := L) (κ₁ := κ₁) (δ₀ := δ₀) (sx := smid) (sy := sb) hN
    hTmb hTmid2 hTb1
  have hexp2 : a₂ ≤ (κ₁ * (sb - smid) - 2 * δ₀) * L := by
    have h := (div_le_iff₀ hκ).mp hY
    have h' : a₂ / L ≤ κ₁ * (sb - smid) - 2 * δ₀ := by linarith
    have := (div_le_iff₀ hL).mp h'
    linarith
  have hclock0 : 0 ≤ ((2 : ℝ) ^ (Tb - Tmid))⁻¹ := by positivity
  have h2 : A₂ * ((2 : ℝ) ^ (Tb - Tmid))⁻¹ ≤ 1 := by
    by_cases hA : A₂ ≤ 0
    · have : A₂ * ((2 : ℝ) ^ (Tb - Tmid))⁻¹ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hA hclock0
      linarith
    push Not at hA
    calc A₂ * ((2 : ℝ) ^ (Tb - Tmid))⁻¹
        ≤ N ^ a₂ * N ^ (-((κ₁ * (sb - smid) - 2 * δ₀) * L)) := by gcongr
      _ = N ^ (a₂ - (κ₁ * (sb - smid) - 2 * δ₀) * L) := by
          rw [← Real.rpow_add hNp]; ring_nf
      _ ≤ N ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)
      _ = 1 := Real.rpow_zero N
  -- monotone thickness
  have hrr : ri ≤ rmid := by
    have h1' := (abs_le.mp hri).2
    have h2' := (abs_le.mp hrmid).1
    have : 0 ≤ a₁ / L := by positivity
    nlinarith
  have h3 : O204.Split.δ N rmid ≤ O204.Split.δ N ri := by
    unfold O204.Split.δ
    apply zpow_le_zpow_right₀ (by norm_num)
    apply neg_le_neg
    apply Int.floor_le_floor
    have hlog : 0 < Real.log N / Real.log 2 := div_pos (Real.log_pos hN) (Real.log_pos (by norm_num))
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hrr hlog.le
  exact ⟨h1, hTmb, h2, h3⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
