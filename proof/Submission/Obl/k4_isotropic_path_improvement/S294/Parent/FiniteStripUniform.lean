-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.FiniteStripUniform, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/FiniteStripUniform.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.EarlyCaptureNarrow
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripSecondScaleBudgets

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.FiniteStripUniform

open MeasureTheory Set Filter
open ParentSource ParentSource.Native
open Submission.Lib.K4VelocityStrips

noncomputable section

/-- Original capture by a small power number of whole-parent unit strips
gives the exact narrow exit. The prediction count may depend on the path
and on N, while the output formats are fixed before the requested slack. -/
theorem eventually_narrow_of_unit_strips
    {d : ProblemData} (hd : d.Valid) {κ₁ : ℝ} (hκ : 0 < κ₁)
    (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ) (Mp Dp : ℕ)
    {ub gain u0 : ℝ} (hub : 0 < ub) (hub1 : ub ≤ 1) (hδ : δ₀ ≤ ub/800)
    (hu0 : u0 ≤ ub/8) (hubgain : ub/8 ≤ 4*gain)
    (target : ℕ) (htarget : target < m)
    (hmiddle : 1/4 ≤ s target ∧ s target ≤ 1/2)
    {α : ℝ} (hα : 0 < α) :
    let J := Mp+⌈(κ₁+δ₀)*d.L⌉₊+1
    let U := ⌈ub*d.L/4⌉₊
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ ∀ᶠ k in atTop,
      ∀ p : PathData (d.W k),
      p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
        κ₁ m s δ₀ Mp Dp σ →
      ∀ (Jpred : ℕ), (Jpred : ℝ) ≤ d.N k^σ →
      ∀ (normal : p.StripLevel target → Fin Jpred → StripSpace)
        (offset : p.StripLevel target → Fin Jpred → ℝ),
      (∀ b j, ‖normal b j‖=1) →
      (∀ b j, |offset b j| ≤ 2*p.κ+d.N k^(-(ub*d.L)/2)) →
      ∀ R H : Fin (d.W k) → Set Ev,
      (∀ w, R w⊆H w) →
      (∀ w, R w⊆{z | ∃ b : p.StripLevel target,
        p.γ b=w ∧ z∈p.F b ∧ p.normalizedVelocity b z∈
          ⋃ j, affineStrip (normal b j) (offset b j) (d.N k^(-(ub*d.L)/2))}) →
      ENNReal.ofReal (p.κ⁻¹/8) ≤
        ∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (R w) →
      ParentSource.narrow (d.N k) d.L (d.W k) (d.ω k) (d.ν k) (d.E k) (d.B k)
        m s p.r p.T p.nw gain u0 p.κ (stripMergedOutputExponent Mp J U 1 0) (max Dp 1) α
        p.C p.lev p.γ p.j p.A p.F H := by
  let J := Mp+⌈(κ₁+δ₀)*d.L⌉₊+1
  let U := ⌈ub*d.L/4⌉₊
  change ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ _
  have hL : 0 < d.L := hd.2.2.2.1
  let z := ub*d.L
  have hz : 0 < z := mul_pos hub hL
  have hδL : δ₀*d.L ≤ z/800 := by
    have hh := mul_le_mul_of_nonneg_right hδ hL.le
    dsimp only [z]
    linarith
  obtain ⟨σE,hσE,hσE1,hEnv⟩ := strip_uniform_power_envelope hd.tendsto hα
    (show 0 < z/32 by positivity)
  let σ := min (σE/2) (1/2)
  have hσ : 0 < σ := lt_min (by positivity) (by norm_num)
  have hσ1 : σ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hσE' : σ < σE := by
    have hh := min_le_left (σE/2) (1/2)
    dsimp only [σ]
    linarith
  have hcost := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hd.tendsto hσE' 5
  refine ⟨σ,hσ,hσ1,?_⟩
  filter_upwards [hEnv,hcost] with k hEnvk hcostk
  intro p hp Jpred hpred normal offset hn hoff R H hRH hcover hmass
  have hN : 1 ≤ d.N k := le_trans (by norm_num) (hd.1 k)
  have hNpos : 0 < d.N k := zero_lt_one.trans_le hN
  have hNp : 1 ≤ d.N k^σ := Real.one_le_rpow hN hσ.le
  let envelope := 3*p.κ+(Jpred : ℝ)+1
  have hpred0 : (0 : ℝ) ≤ Jpred := Nat.cast_nonneg _
  have hE1 : 1 ≤ envelope := by dsimp only [envelope]; linarith only [hp.1,hpred0]
  have hκE : 3*p.κ ≤ envelope := by dsimp only [envelope]; linarith only [hpred0]
  have hEpower : envelope ≤ d.N k^σE := by
    calc
      _ ≤ 5*d.N k^σ := by dsimp only [envelope]; linarith only [hp.2.1,hpred,hNp]
      _ ≤ _ := hcostk.le
  obtain ⟨hEN,hslack,hdet⟩ := hEnvk envelope hE1 hEpower
  have htime : (2 : ℝ)^p.T target ≤ d.N k^J := by
    have hh := (hp.2.2.2.2.1 target htarget).2.2.2.1
    apply hh.trans
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hN
    have hj : (κ₁+δ₀)*d.L ≤ (⌈(κ₁+δ₀)*d.L⌉₊ : ℝ) := Nat.le_ceil _
    have hsκ := mul_le_mul_of_nonneg_left hmiddle.2 hκ.le
    have hlev := mul_le_mul_of_nonneg_right hsκ hL.le
    have hMp : (0 : ℝ) ≤ Mp := Nat.cast_nonneg _
    dsimp only [J]
    push_cast
    nlinarith only [hj,hlev,hMp,mul_pos hκ hL]
  have hrL : p.r target ≤ d.L := by
    have hh := (hp.2.2.2.2.1 target htarget).1
    have hsL := mul_le_mul_of_nonneg_right hmiddle.2 hL.le
    have hubL : z ≤ d.L := by
      simpa only [z,one_mul] using mul_le_mul_of_nonneg_right hub1 hL.le
    have hδsmall : δ₀*d.L ≤ d.L/800 := hδL.trans (by linarith)
    have hr := (le_abs_self (p.r target-s target*d.L)).trans hh
    linarith
  have hinv : (d.N k^(-z/4))⁻¹ ≤ d.N k^U := by
    rw [← Real.rpow_neg hNpos.le,neg_div,neg_neg,← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hN (Nat.le_ceil _)
  have hcount : (Jpred : ℝ) ≤ d.N k^1 := by
    simpa only [pow_one,Real.rpow_one] using hpred.trans
      (Real.rpow_le_rpow_of_exponent_le hN hσ1)
  have hsmallCount : (Jpred : ℝ) ≤ 3*envelope^2 := by
    have hh : (Jpred : ℝ) ≤ envelope := by dsimp only [envelope]; linarith [hp.1]
    nlinarith only [hh,hE1]
  exact EarlyCaptureNarrow.narrow_of_unit_strips hp (hd.1 k)
    (fun w => (hd.parent_signal_data k w).1.le) target htarget hrL hmiddle
    (width := d.N k^(-z/2)) (radius := d.N k^(-z/4)) (β := ub/8)
    (loss := z/32) (stripExponent := z/4) (envelope := envelope)
    hu0 hubgain Jpred normal offset hn hoff J U 1 (by dsimp only [J]; omega)
    htime hEN hκE (Real.rpow_pos_of_pos hNpos _)
    (Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)) hinv
    (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) hcount hsmallCount
    R H hRH hcover hslack hdet (le_of_eq (by congr 1; ring))
    (by dsimp only [z] at hδL hz ⊢; nlinarith only [hδL,hz]) hmass

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.FiniteStripUniform
