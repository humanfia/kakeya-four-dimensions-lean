-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.LateOldPathScales, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/LateOldPathScales.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.LateOldScaleArithmetic
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.WidePreparationGrid
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Path
import Submission.Obl.k4_clean_cover_graph_atlas.Numerics

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Native MeasureTheory

noncomputable section

/-- A single later supplied level works for every actual path, with
the strict frozen clock margin and both qualification error budgets.
The degree and row accuracy are fixed before the gain. -/
theorem WidePreparationGrid.exists_late_old_path_scales
    {κ₁ ρ S η χ windowFactor precision accuracy : ℝ} {M : ℕ}
    (q : WidePreparationGrid κ₁ ρ S η χ windowFactor)
    (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hprecision : 1 ≤ precision)
    (hχ : 0 < χ) (hχ1 : χ ≤ 1)
    (hM : 1 ≤ (M : ℝ)*κ₁) (hχM : χ*((M : ℝ)+1) ≤ 1)
    (hfirst : (q.m : ℝ)⁻¹+2*q.δ₀ ≤ χ*q.gain)
    (hsmall : (((precision+2)/κ₁)+8)*q.gain ≤ 1/8)
    (haccuracy : ((precision+2)/κ₁)+precision+4 ≤ accuracy) :
    ∃ level : ℕ, 0 < level ∧ level < q.m ∧ transferScale q.m level ≤ 1/8 ∧
      ∀ {W : ℕ} {N L σ : ℝ} {p : PathData W}
        {ω : Fin W → ℝ} {ν : Fin W → Measure Ln} {E : Fin W → Set Ev}
        {B : Fin W → ℝ} {f : ℝ → ℝ} {Mp Dp : ℕ},
      p.Valid N L ω ν E B f κ₁ q.m (transferScale q.m) q.δ₀ Mp Dp σ →
      1 ≤ N → 0 < L →
      (((2 : ℝ)^p.T level)⁻¹ ≤ δ N (precision*q.gain*L)) ∧
      p.r level+2*q.gain*L ≤ L ∧
      N^(q.gain*L)*((2 : ℝ)^p.T level)⁻¹*
        ((((2 : ℝ)^p.T level)⁻¹)/(((2 : ℝ)^p.T 0)⁻¹))^M ≤
          δ N (p.r level)*δ N (precision*q.gain*L) ∧
      N^(q.gain*L)*((2 : ℝ)^p.T level)⁻¹*N^(-(accuracy*q.gain*L)) ≤
          δ N (p.r level)*δ N (precision*q.gain*L) := by
  have hg : 0 < q.gain := q.valid.2.1
  have hδ : 0 < q.δ₀ := q.valid.2.2.2.1
  have hχg : χ*q.gain ≤ q.gain := mul_le_of_le_one_left hg.le hχ1
  have hfirstg : (q.m : ℝ)⁻¹ ≤ q.gain := by linarith
  have hδg : q.δ₀ ≤ q.gain := by linarith [q.tolerance]
  obtain ⟨level,hl0,hlm,hlo,hhi,hl8,hclockDepth,hroom⟩ :=
    LateOldScales.exists_late_level_with_budgets q.valid.1.1 hκ hκ1 hprecision hg
      hfirstg hδg hsmall
  have hs0 : transferScale q.m 0=(q.m : ℝ)⁻¹ := by simp [transferScale,one_div]
  have hslevel : transferScale q.m level=((level : ℝ)+1)/(q.m : ℝ) := rfl
  rw [← hslevel] at hlo hhi hl8 hclockDepth hroom
  have hrootError : (M : ℝ)*κ₁*(transferScale q.m 0)+(2*(M : ℝ)+2)*q.δ₀ ≤ q.gain := by
    rw [hs0]
    exact LateOldScales.shallow_root_error_budget hκ1 hg.le (by positivity) hχM hfirst
  refine ⟨level,hl0,hlm,hl8,?_⟩
  intro W N L σ p ω ν E B f Mp Dp hp hN hL
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hc (i : ℕ) (hi : i < q.m) :
      N^(-((κ₁*transferScale q.m i+q.δ₀)*L)) ≤ ((2 : ℝ)^p.T i)⁻¹ ∧
      ((2 : ℝ)^p.T i)⁻¹ ≤ N^(-((κ₁*transferScale q.m i-q.δ₀)*L)) := by
    have hpath := hp.2.2.2.2.1 i hi
    constructor
    · rw [Real.rpow_neg hNp.le]
      exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hpath.2.2.2.1
    · rw [Real.rpow_neg hNp.le]
      exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hpath.2.2.1
  have hwidth : N^(-((transferScale q.m level+q.δ₀)*L)) ≤ δ N (p.r level) := by
    apply le_trans _ (Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hNp (p.r level)).1
    apply Real.rpow_le_rpow_of_exponent_le hN
    have hh := (abs_le.mp (hp.2.2.2.2.1 level hlm).1).2
    nlinarith only [hh]
  have hζ : N^(-(precision*q.gain*L)) ≤ δ N (precision*q.gain*L) :=
    (Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hNp _).1
  have hclock : ((2 : ℝ)^p.T level)⁻¹ ≤ δ N (precision*q.gain*L) := by
    apply (hc level hlm).2.trans
    apply le_trans _ hζ
    apply Real.rpow_le_rpow_of_exponent_le hN
    nlinarith only [mul_le_mul_of_nonneg_right hclockDepth hL.le,mul_pos hg hL]
  have hr : p.r level ≤ (transferScale q.m level+q.δ₀)*L := by
    have hh := (abs_le.mp (hp.2.2.2.2.1 level hlm).1).2
    nlinarith only [hh]
  have hrRoom : p.r level+2*q.gain*L ≤ L := by
    nlinarith only [hr,mul_le_mul_of_nonneg_right hroom hL.le]
  have hdepth : (precision+2)*q.gain ≤ κ₁*transferScale q.m level := by
    have h := mul_le_mul_of_nonneg_left hlo hκ.le
    have heq : κ₁*(((precision+2)/κ₁)*q.gain)=(precision+2)*q.gain := by
      field_simp [hκ.ne']
    rwa [heq] at h
  have hpoly := LateOldScales.polynomial_clock_error_budget hN hL.le hκ hg hprecision
    (show 0 ≤ transferScale q.m level by dsimp [transferScale]; positivity)
    hM hdepth hrootError (by positivity : (0 : ℝ) ≤ ((2 : ℝ)^p.T level)⁻¹)
    (by positivity : (0 : ℝ) < ((2 : ℝ)^p.T 0)⁻¹)
    (hc level hlm).2 (hc 0 q.valid.1.1).1 hwidth hζ
  have hclockOne : ((2 : ℝ)^p.T level)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hrow := LateOldScales.row_error_budget hN hL.le hg hhi hδg
    (show ((precision+2)/κ₁+2)+precision+2 ≤ accuracy by linarith)
    (by positivity : (0 : ℝ) ≤ ((2 : ℝ)^p.T level)⁻¹) hclockOne hwidth hζ
  exact ⟨hclock,hrRoom,hpoly,hrow⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
