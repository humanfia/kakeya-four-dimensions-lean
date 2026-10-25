-- From this LOT obligation o230, session x0803, commit c61a445c,
-- Submission/Obl/k4_scalar_grid_cartesian_field/CoreMain.lean.
import Submission.Obl.k4_scalar_grid_cartesian_field.CoreFinite
import Submission.Obl.k4_scalar_grid_cartesian_field.CorePolyBd

/-!
# The packet-level Cartesian field core

`cartesianCore` proves `CartesianCoreStatement M` (for `M ≥ 1`) from
`core_finite`, choosing the list budget `K`, the grid density `η` and the anchor
gap as explicit functions of the budget `Λ`; every loss is then bounded by a
fixed monomial in `Λ`.
-/

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open MeasureTheory Set

/-- The list budget. -/
noncomputable def budgetK (Cb : ℝ) (M : ℕ) (Λ : ℝ) : ℝ :=
  (Cb * ((4 * 141 + 11) ^ 3 * Λ + 2) ^ (3 * (M + 1) + (M + 1) ^ 2 * M)) ^ 2 +
    (4 * 141 + 11) ^ 3 * Λ + 1

/-- The reciprocal grid density. -/
noncomputable def budgetEtaInv (Cb : ℝ) (M : ℕ) (Λ : ℝ) : ℝ :=
  40 * (4 * Λ + 9) * Λ ^ 3 * budgetK Cb M Λ ^ 3 * (2 * coreBf Λ + 2) ^ 2

/-- The reciprocal anchor gap. -/
noncomputable def budgetGapInv (Cb : ℝ) (M : ℕ) (Λ : ℝ) : ℝ :=
  28 * ((M : ℝ) + 2) ^ 2 * budgetEtaInv Cb M Λ ^ ((M + 2) ^ 2)

/-- The Lagrange weight budget. -/
noncomputable def budgetW (Cb : ℝ) (M : ℕ) (Λ : ℝ) : ℝ :=
  ((M : ℝ) + 1) * (2 * (coreBf Λ + 2) * budgetGapInv Cb M Λ) ^ M

/-- The reciprocal relative row length. -/
noncomputable def budgetEtaRInv (Cb : ℝ) (M : ℕ) (Λ : ℝ) : ℝ :=
  32 * Λ ^ 4 * budgetK Cb M Λ ^ 3 * budgetEtaInv Cb M Λ ^ ((M + 2) ^ 2)

/-- The mesh error coefficient. -/
noncomputable def budgetE1c (Cb Cm Cu : ℝ) (M : ℕ) (Λ : ℝ) : ℝ :=
  1 + (2 + ((M : ℝ) + 1) * M * (Cu * (((M : ℝ) + 1) * Λ)) * (1 + 2 ^ (M + 1)) +
      2 * ((M : ℝ) + 1) * 2 ^ M) * (1 + 2 * budgetW Cb M Λ + budgetW Cb M Λ ^ 2) +
    2 * Cm * (1 + Λ) * budgetW Cb M Λ ^ 2

theorem polyBd_coreBf : PolyBd coreBf := by
  have h := PolyBd.mul (PolyBd.smul (PolyBd.pow (PolyBd.add PolyBd.id' (PolyBd.const 1 zero_le_one)) 2)
    2 (by norm_num)) PolyBd.id'
  exact PolyBd.congr' h fun Λ _ => by simp [coreBf]

theorem polyBd_budgetK (Cb : ℝ) (hCb : 0 ≤ Cb) (M : ℕ) : PolyBd (budgetK Cb M) := by
  have hlin : PolyBd fun Λ : ℝ => (4 * 141 + 11) ^ 3 * Λ + 2 :=
    PolyBd.add (PolyBd.smul PolyBd.id' _ (by norm_num)) (PolyBd.const 2 (by norm_num))
  have h := PolyBd.add (PolyBd.add (PolyBd.pow (PolyBd.smul (PolyBd.pow hlin (3 * (M + 1) + (M + 1) ^ 2 * M)) Cb hCb) 2)
    (PolyBd.smul PolyBd.id' ((4 * 141 + 11) ^ 3) (by norm_num))) (PolyBd.const 1 zero_le_one)
  exact PolyBd.congr' h fun Λ _ => by simp [budgetK]

theorem polyBd_budgetEtaInv (Cb : ℝ) (hCb : 0 ≤ Cb) (M : ℕ) : PolyBd (budgetEtaInv Cb M) := by
  have h4 : PolyBd fun Λ : ℝ => 4 * Λ + 9 :=
    PolyBd.add (PolyBd.smul PolyBd.id' 4 (by norm_num)) (PolyBd.const 9 (by norm_num))
  have hB : PolyBd fun Λ : ℝ => 2 * coreBf Λ + 2 :=
    PolyBd.add (PolyBd.smul polyBd_coreBf 2 (by norm_num)) (PolyBd.const 2 (by norm_num))
  have h := PolyBd.mul (PolyBd.mul (PolyBd.mul (PolyBd.smul h4 40 (by norm_num))
    (PolyBd.pow PolyBd.id' 3)) (PolyBd.pow (polyBd_budgetK Cb hCb M) 3)) (PolyBd.pow hB 2)
  exact PolyBd.congr' h fun Λ _ => by simp [budgetEtaInv, mul_assoc]

theorem polyBd_budgetGapInv (Cb : ℝ) (hCb : 0 ≤ Cb) (M : ℕ) : PolyBd (budgetGapInv Cb M) := by
  have h := PolyBd.smul (PolyBd.pow (polyBd_budgetEtaInv Cb hCb M) ((M + 2) ^ 2))
    (28 * ((M : ℝ) + 2) ^ 2) (by positivity)
  exact PolyBd.congr' h fun Λ _ => by simp [budgetGapInv]

theorem polyBd_budgetW (Cb : ℝ) (hCb : 0 ≤ Cb) (M : ℕ) : PolyBd (budgetW Cb M) := by
  have hB : PolyBd fun Λ : ℝ => 2 * (coreBf Λ + 2) :=
    PolyBd.smul (PolyBd.add polyBd_coreBf (PolyBd.const 2 (by norm_num))) 2 (by norm_num)
  have h := PolyBd.smul (PolyBd.pow (PolyBd.mul hB (polyBd_budgetGapInv Cb hCb M)) M)
    ((M : ℝ) + 1) (by positivity)
  exact PolyBd.congr' h fun Λ _ => by simp [budgetW]

theorem polyBd_budgetEtaRInv (Cb : ℝ) (hCb : 0 ≤ Cb) (M : ℕ) :
    PolyBd (budgetEtaRInv Cb M) := by
  have h := PolyBd.mul (PolyBd.mul (PolyBd.smul (PolyBd.pow PolyBd.id' 4) 32 (by norm_num))
    (PolyBd.pow (polyBd_budgetK Cb hCb M) 3)) (PolyBd.pow (polyBd_budgetEtaInv Cb hCb M) ((M + 2) ^ 2))
  exact PolyBd.congr' h fun Λ _ => by simp [budgetEtaRInv]

theorem polyBd_budgetE1c (Cb Cm Cu : ℝ) (hCb : 0 ≤ Cb) (hCm : 0 ≤ Cm) (hCu : 0 ≤ Cu) (M : ℕ) :
    PolyBd (budgetE1c Cb Cm Cu M) := by
  have hW := polyBd_budgetW Cb hCb M
  have hHp : PolyBd fun Λ : ℝ => Cu * (((M : ℝ) + 1) * Λ) :=
    PolyBd.smul (PolyBd.smul PolyBd.id' _ (by positivity)) Cu hCu
  have hEc : PolyBd fun Λ : ℝ => 2 + ((M : ℝ) + 1) * M * (Cu * (((M : ℝ) + 1) * Λ)) *
      (1 + 2 ^ (M + 1)) + 2 * ((M : ℝ) + 1) * 2 ^ M := by
    have h := PolyBd.add (PolyBd.add (PolyBd.const 2 (by norm_num))
      (PolyBd.mul (PolyBd.smul hHp (((M : ℝ) + 1) * M) (by positivity))
        (PolyBd.const (1 + 2 ^ (M + 1)) (by positivity))))
      (PolyBd.const (2 * ((M : ℝ) + 1) * 2 ^ M) (by positivity))
    exact PolyBd.congr' h fun Λ _ => by ring
  have hpoly : PolyBd fun Λ : ℝ => 1 + 2 * budgetW Cb M Λ + budgetW Cb M Λ ^ 2 :=
    PolyBd.add (PolyBd.add (PolyBd.const 1 zero_le_one) (PolyBd.smul hW 2 (by norm_num)))
      (PolyBd.pow hW 2)
  have hlast : PolyBd fun Λ : ℝ => 2 * Cm * (1 + Λ) * budgetW Cb M Λ ^ 2 := by
    have h := PolyBd.mul (PolyBd.smul (PolyBd.add (PolyBd.const 1 zero_le_one) PolyBd.id')
      (2 * Cm) (by positivity)) (PolyBd.pow hW 2)
    exact PolyBd.congr' h fun Λ _ => by ring
  have h := PolyBd.add (PolyBd.add (PolyBd.const 1 zero_le_one) (PolyBd.mul hEc hpoly)) hlast
  exact PolyBd.congr' h fun Λ _ => by simp [budgetE1c]


theorem budgetK_ge_one (Cb : ℝ) (M : ℕ) (Λ : ℝ) (hΛ : 0 ≤ Λ) : 1 ≤ budgetK Cb M Λ := by
  unfold budgetK
  have h1 : 0 ≤ (Cb * ((4 * 141 + 11) ^ 3 * Λ + 2) ^ (3 * (M + 1) + (M + 1) ^ 2 * M)) ^ 2 :=
    sq_nonneg _
  have h2 : 0 ≤ (4 * 141 + 11) ^ 3 * Λ := by positivity
  linarith

theorem budgetEtaInv_ge_one (Cb : ℝ) (M : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    1 ≤ budgetEtaInv Cb M Λ := by
  unfold budgetEtaInv
  have hK := budgetK_ge_one Cb M Λ (by linarith)
  have hK3 : 1 ≤ budgetK Cb M Λ ^ 3 := one_le_pow₀ hK
  have hΛ3 : 1 ≤ Λ ^ 3 := one_le_pow₀ hΛ
  have hB : 1 ≤ (2 * coreBf Λ + 2) ^ 2 := by
    apply one_le_pow₀
    have : 0 ≤ coreBf Λ := by unfold coreBf; positivity
    linarith
  have h4 : 1 ≤ 40 * (4 * Λ + 9) := by linarith
  calc (1 : ℝ) = 1 * 1 * 1 * 1 := by norm_num
    _ ≤ 40 * (4 * Λ + 9) * Λ ^ 3 * budgetK Cb M Λ ^ 3 * (2 * coreBf Λ + 2) ^ 2 := by
        apply mul_le_mul (mul_le_mul (mul_le_mul h4 hΛ3 (by norm_num) (by positivity)) hK3
          (by norm_num) (by positivity)) hB (by norm_num) (by positivity)

/-- The packet-level Cartesian field core. -/
theorem cartesianCore (M : ℕ) (hM : 1 ≤ M) : CartesianCoreStatement M := by
  obtain ⟨Cb, Cm, Cu, Cc, hCb, hCm, hCu, hCc, hfin⟩ := core_finite M hM
  have hp1 : PolyBd fun Λ => Cc ^ 2 * ((1 + Λ) * budgetW Cb M Λ ^ 2) :=
    PolyBd.smul (PolyBd.mul (PolyBd.add (PolyBd.const 1 zero_le_one) PolyBd.id')
      (PolyBd.pow (polyBd_budgetW Cb hCb.le M) 2)) _ (by positivity)
  have hp2 := polyBd_budgetEtaRInv Cb hCb.le M
  have hp3 : PolyBd fun Λ => (8 * (((2 * M : ℕ) : ℝ) + 3) * budgetEtaRInv Cb M Λ) ^ (2 * M + 2) *
      (1 + (1 + Λ) * budgetE1c Cb Cm Cu M Λ) :=
    PolyBd.mul (PolyBd.pow (PolyBd.smul hp2 _ (by positivity)) _)
      (PolyBd.add (PolyBd.const 1 zero_le_one) (PolyBd.mul
        (PolyBd.add (PolyBd.const 1 zero_le_one) PolyBd.id')
        (polyBd_budgetE1c Cb Cm Cu hCb.le hCm.le hCu.le M)))
  obtain ⟨c, k, hc1, hck⟩ := PolyBd.common hp1 hp2 hp3
  obtain ⟨c4, k4, hc4, hb4⟩ := polyBd_budgetGapInv Cb hCb.le M
  refine ⟨max c c4 + 1, k, k4, by positivity, ?_⟩
  intro N Λ h a y₀ εT rT B L ξ δv δs ρ θ ν π E S₀ A G
    hN hΛ hh hh1 ha hah hεT hξ hδv hδs hsmall hfitp hgraphp hlayer hcellsmall hδvξ hfine hδs1
    hδs2 hρfin hθfin hνsf hπ hEm hS₀m hAm hS₀E hS₀A hρpos hdens hmassA hθρ hρθ hcoefA hconf
    hlip hgraph hlists hbreadth hpal hqual hbase
  set C := max c c4 + 1 with hC_def
  have hC1 : 1 ≤ C := by have := le_max_left c c4; linarith
  have hΛ0 : 0 < Λ := by linarith
  have hN0 : 0 < N := by linarith
  have hεpos : 0 < εT := hεT ▸ Real.rpow_pos_of_pos hN0 _
  have hΛk : 1 ≤ Λ ^ k := one_le_pow₀ hΛ
  have hΛk4 : 1 ≤ Λ ^ k4 := one_le_pow₀ hΛ
  -- `εT ≤ 1` and `ξ ≤ gap`
  have hCΛ4 : 1 ≤ C * Λ ^ k4 := by
    calc (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ C * Λ ^ k4 := mul_le_mul hC1 hΛk4 (by norm_num) (by positivity)
  have hεT1 : εT ≤ 1 := by
    have : 1 * εT ≤ C * Λ ^ k4 * εT := mul_le_mul_of_nonneg_right hCΛ4 hεpos.le
    linarith
  have hgapinv := hb4 Λ hΛ
  have hgapinvpos : 0 < budgetGapInv Cb M Λ := by
    unfold budgetGapInv
    have := budgetEtaInv_ge_one Cb M Λ hΛ
    positivity
  have hξgap : ξ ≤ 1 / budgetGapInv Cb M Λ := by
    have hξε : ξ ≤ εT := by
      have : ξ ≤ Λ ^ 4 * ξ := le_mul_of_one_le_left hξ.le (one_le_pow₀ hΛ)
      linarith
    have h1 : budgetGapInv Cb M Λ ≤ C * Λ ^ k4 := by
      have : c4 ≤ C := by have := le_max_right c c4; linarith
      calc budgetGapInv Cb M Λ ≤ c4 * Λ ^ k4 := hgapinv.2
        _ ≤ C * Λ ^ k4 := mul_le_mul_of_nonneg_right this (by positivity)
    have h2 : εT * budgetGapInv Cb M Λ ≤ 1 := by
      calc εT * budgetGapInv Cb M Λ ≤ εT * (C * Λ ^ k4) :=
            mul_le_mul_of_nonneg_left h1 hεpos.le
        _ = C * Λ ^ k4 * εT := by ring
        _ ≤ 1 := hsmall
    rw [le_div_iff₀ hgapinvpos]
    nlinarith
  -- the parameters
  have hK1 := budgetK_ge_one Cb M Λ hΛ0.le
  have hηinv1 := budgetEtaInv_ge_one Cb M Λ hΛ
  have hηinvpos : 0 < budgetEtaInv Cb M Λ := by linarith
  have hKrow : (Cb * (max Λ ((4 * 141 + 11) ^ 3 * Λ + 2)) ^ (3 * (M + 1) + (M + 1) ^ 2 * M)) ^ 2 ≤
      budgetK Cb M Λ := by
    have hmax : max Λ ((4 * 141 + 11) ^ 3 * Λ + 2) = (4 * 141 + 11) ^ 3 * Λ + 2 :=
      max_eq_right (by nlinarith)
    rw [hmax]
    unfold budgetK
    have : 0 ≤ (4 * 141 + 11) ^ 3 * Λ := by positivity
    linarith
  have hKcell : (4 * 141 + 11) ^ 3 * Λ ≤ budgetK Cb M Λ := by
    unfold budgetK
    have := sq_nonneg (Cb * ((4 * 141 + 11) ^ 3 * Λ + 2) ^ (3 * (M + 1) + (M + 1) ^ 2 * M))
    linarith
  have hη0 : 0 < 1 / budgetEtaInv Cb M Λ := by positivity
  have hη1 : 1 / budgetEtaInv Cb M Λ ≤ 1 := by
    rw [div_le_one hηinvpos]; exact hηinv1
  have hηdef : 1 / budgetEtaInv Cb M Λ * (40 * (4 * Λ + 9) * Λ ^ 3 * budgetK Cb M Λ ^ 3 *
      (2 * coreBf Λ + 2) ^ 2) ≤ 1 := by
    have : (40 * (4 * Λ + 9) * Λ ^ 3 * budgetK Cb M Λ ^ 3 * (2 * coreBf Λ + 2) ^ 2) =
        budgetEtaInv Cb M Λ := rfl
    rw [this, one_div_mul_cancel hηinvpos.ne']
  have hgap0 : 0 < 1 / budgetGapInv Cb M Λ := by positivity
  have hloss : 14 * ((M : ℝ) + 2) ^ 2 * (1 / budgetGapInv Cb M Λ) ≤
      (1 / budgetEtaInv Cb M Λ) ^ ((M + 2) ^ 2) / 2 := by
    apply le_of_eq
    unfold budgetGapInv
    rw [one_div_pow]
    field_simp
    ring
  obtain ⟨𝒯, S₁, hS₁m, hS₁S₀, hdeg, hcoef, hmass, hres⟩ := hfin N Λ h a y₀ εT rT B L ξ δv δs
    ρ θ ν π E S₀ A G (budgetK Cb M Λ) (1 / budgetEtaInv Cb M Λ) (1 / budgetGapInv Cb M Λ)
    hN hΛ hh hh1 ha hah hεT hεT1 hξ hδv hδs hfitp hgraphp hlayer hcellsmall hδvξ hfine hδs1 hδs2
    hρfin hθfin hνsf hπ hEm hS₀m hAm hS₀E hS₀A hρpos hdens hmassA hθρ hρθ hcoefA hconf hlip
    hgraph hlists hbreadth hpal hqual hbase hK1 hKrow hKcell hη0 hη1 hηdef hgap0 hloss hξgap
  -- identify the budgets
  have hW : ((M : ℝ) + 1) * (2 * (coreBf Λ + 2) / (1 / budgetGapInv Cb M Λ)) ^ M =
      budgetW Cb M Λ := by
    unfold budgetW; rw [div_div_eq_mul_div, div_one]
  have hηr : (1 / budgetEtaInv Cb M Λ) ^ ((M + 2) ^ 2) / (32 * Λ ^ 4 * budgetK Cb M Λ ^ 3) =
      1 / budgetEtaRInv Cb M Λ := by
    unfold budgetEtaRInv
    rw [one_div_pow]
    field_simp
  obtain ⟨hb1, hb2, hb3⟩ := hck Λ hΛ
  have hCk : c * Λ ^ k ≤ C * Λ ^ k := by
    have : c ≤ C := by have := le_max_left c c4; linarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  refine ⟨𝒯, S₁, hS₁m, hS₁S₀, hdeg, ?_, ?_, ?_⟩
  · intro e b
    refine (hcoef e b).trans ?_
    rw [hW]
    have h1 : Cc ^ 2 * ((εT + Λ) * budgetW Cb M Λ ^ 2) ≤
        Cc ^ 2 * ((1 + Λ) * budgetW Cb M Λ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    linarith
  · refine le_trans ?_ hmass
    rw [hηr]
    apply mul_le_mul_of_nonneg_right _ bot_le
    apply ENNReal.ofReal_le_ofReal
    have hpos : 0 < budgetEtaRInv Cb M Λ := by
      unfold budgetEtaRInv
      have := budgetK_ge_one Cb M Λ hΛ0.le
      positivity
    rw [div_le_div_iff₀ (by positivity) hpos]
    linarith
  · intro p hp t ht
    refine (hres p hp t ht).trans ?_
    rw [hηr, hW]
    have e1 : 8 * (((2 * M : ℕ) : ℝ) + 3) / (1 / budgetEtaRInv Cb M Λ) =
        8 * (((2 * M : ℕ) : ℝ) + 3) * budgetEtaRInv Cb M Λ := by rw [div_div_eq_mul_div, div_one]
    rw [e1]
    have e2 : (1 + (2 + ((M : ℝ) + 1) * M * (Cu * (((M : ℝ) + 1) * Λ)) * (1 + 2 ^ (M + 1)) +
        2 * ((M : ℝ) + 1) * 2 ^ M) * (1 + 2 * budgetW Cb M Λ + budgetW Cb M Λ ^ 2) +
        2 * Cm * (1 + Λ) * budgetW Cb M Λ ^ 2) = budgetE1c Cb Cm Cu M Λ := rfl
    rw [e2]
    have h3 : (8 * (((2 * M : ℕ) : ℝ) + 3) * budgetEtaRInv Cb M Λ) ^ (2 * M + 2) *
        ((1 + (1 + Λ) * budgetE1c Cb Cm Cu M Λ) * εT) =
        ((8 * (((2 * M : ℕ) : ℝ) + 3) * budgetEtaRInv Cb M Λ) ^ (2 * M + 2) *
          (1 + (1 + Λ) * budgetE1c Cb Cm Cu M Λ)) * εT := by ring
    rw [h3]
    exact mul_le_mul_of_nonneg_right (hb3.trans hCk) hεpos.le

end Submission.Obl.k4_scalar_grid_cartesian_field
