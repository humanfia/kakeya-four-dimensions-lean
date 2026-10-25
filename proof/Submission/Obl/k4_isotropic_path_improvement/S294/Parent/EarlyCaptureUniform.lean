-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.EarlyCaptureUniform, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/EarlyCaptureUniform.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.EarlyCaptureNarrow
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripSecondScaleBudgets

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.EarlyCaptureUniform

open MeasureTheory Set Filter
open ParentSource ParentSource.Native

noncomputable section

/-- The exact early-capture narrow exit is uniform over the supplied
path. Its output format exponent is independent of the requested list
slack and of the fixed finite prediction count. -/
theorem eventually_narrow_of_early_capture {T : Type*}
    {d : ProblemData} (hd : d.Valid) {κ₁ : ℝ} (hκ : 0 < κ₁)
    (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ) (Mp Dp : ℕ)
    {ub gain u0 : ℝ} (hub : 0 < ub) (hub1 : ub ≤ 1) (hδ : δ₀ ≤ ub / 800)
    (hu0 : u0 ≤ ub / 8) (hubgain : ub / 8 ≤ 4 * gain)
    (target : ℕ) (htarget : target < m)
    (hmiddle : 1 / 4 ≤ s target ∧ s target ≤ 1 / 2)
    (Jpred : ℕ) {α : ℝ} (hα : 0 < α) :
    let J := Mp + ⌈(κ₁ + δ₀) * d.L⌉₊ + 1
    let U := ⌈ub * d.L / 4⌉₊
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ k in atTop,
      ∀ p : PathData (d.W k),
      p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
        κ₁ m s δ₀ Mp Dp σ →
      ∀ H : Fin (d.W k) → Set Ev,
      (∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b}) →
      ∀ (u : T → ℝ) (τ : ℝ) (Q : PreparedAngularPath d k p m H u τ)
        (i stop : ℕ), i ≤ stop → stop < m → stop ≤ target →
      ∀ (a A fraction : ℝ) (θ : ENNReal) (F : PaletteFamily Q i stop a A θ)
        (P : PaletteStripSaturation F (d.N k ^ (-(ub * d.L))) fraction),
      fraction⁻¹ ≤ (Jpred : ℝ) →
      ENNReal.ofReal (9 * p.κ⁻¹ / 64) ≤
        ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (P.captureResidual w) →
      ParentSource.narrow (d.N k) d.L (d.W k) (d.ω k) (d.ν k) (d.E k) (d.B k)
        m s p.r p.T p.nw gain u0 p.κ (stripMergedOutputExponent Mp J U 1 0) (max Dp 1) α
        p.C p.lev p.γ p.j p.A p.F H := by
  let J := Mp + ⌈(κ₁ + δ₀) * d.L⌉₊ + 1
  let U := ⌈ub * d.L / 4⌉₊
  change ∃ σ : ℝ, 0 < σ ∧ _
  have hL : 0 < d.L := hd.2.2.2.1
  let z := ub * d.L
  have hz : 0 < z := mul_pos hub hL
  have hδL : δ₀ * d.L ≤ z / 800 := by
    have hh := mul_le_mul_of_nonneg_right hδ hL.le
    dsimp only [z]
    linarith
  obtain ⟨σE,hσE,hσE1,hEnv⟩ := strip_uniform_power_envelope hd.tendsto hα
    (show 0 < z / 32 by positivity)
  obtain ⟨σS,hσS,hσS1,hScale⟩ := strip_uniform_monomial_bound hd.tendsto
    (show -z + 2 * δ₀ * d.L < -z / 2 by linarith) (by norm_num : (0 : ℝ) ≤ 1) 2
  let σ := min (σE / 2) σS
  have hσ : 0 < σ := lt_min (by positivity) hσS
  have hcost := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hd.tendsto (show σ < σE by have hh := min_le_left (σE / 2) σS; dsimp only [σ]; linarith)
    ((Jpred : ℝ) + 4)
  have hpred := hd.tendsto.eventually (eventually_ge_atTop (Jpred : ℝ))
  refine ⟨σ,hσ,?_⟩
  filter_upwards [hEnv,hScale,hcost,hpred] with k hEnvk hScalek hcostk hpredk
  intro p hp H hH u τ Q i stop hi hstop horder a A fraction θ F P hJpred hmass
  have hN2 := hd.1 k
  have hN : 1 ≤ d.N k := le_trans (by norm_num) hN2
  have hNpos : 0 < d.N k := zero_lt_one.trans_le hN
  let envelope := 3 * p.κ + (Jpred : ℝ) + 1
  have hpred0 : (0 : ℝ) ≤ Jpred := Nat.cast_nonneg _
  have hpκ : 1 ≤ p.κ := hp.1
  have hE1 : 1 ≤ envelope := by dsimp only [envelope]; linarith only [hpκ,hpred0]
  have hEκ : 3 * p.κ ≤ envelope := by dsimp only [envelope]; linarith only [hpred0]
  have hEpower : envelope ≤ d.N k ^ σE := by
    calc
      _ ≤ ((Jpred : ℝ) + 4) * p.κ := by
        dsimp only [envelope]
        have hh := mul_nonneg (show (0 : ℝ) ≤ (Jpred : ℝ) + 1 by linarith only [hpred0])
          (show 0 ≤ p.κ - 1 by linarith only [hpκ])
        nlinarith only [hh]
      _ ≤ ((Jpred : ℝ) + 4) * d.N k ^ σ :=
        mul_le_mul_of_nonneg_left hp.2.1 (by positivity)
      _ ≤ _ := hcostk.le
  obtain ⟨hEN,hslack,hdet⟩ := hEnvk envelope hE1 hEpower
  have hκScale : p.κ ≤ d.N k ^ σS := hp.2.1.trans
    (Real.rpow_le_rpow_of_exponent_le hN (min_le_right _ _))
  have hscale : d.N k ^ (-z) * (p.κ ^ 2 * d.N k ^ (2 * δ₀ * d.L)) ≤ d.N k ^ (-z / 2) := by
    have hh := hScalek p.κ hp.1 hκScale
    have heq : d.N k ^ (-z) * (p.κ ^ 2 * d.N k ^ (2 * δ₀ * d.L)) =
        1 * p.κ ^ 2 * d.N k ^ (-z + 2 * δ₀ * d.L) := by
      rw [Real.rpow_add hNpos]
      ring
    rw [heq]
    exact hh
  have htime : (2 : ℝ) ^ p.T target ≤ d.N k ^ J := by
    have hh := (hp.2.2.2.2.1 target htarget).2.2.2.1
    apply hh.trans
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hN
    have hj : (κ₁ + δ₀) * d.L ≤ (⌈(κ₁ + δ₀) * d.L⌉₊ : ℝ) := Nat.le_ceil _
    have hsκ := mul_le_mul_of_nonneg_left hmiddle.2 hκ.le
    have hlev := mul_le_mul_of_nonneg_right hsκ hL.le
    dsimp only [J]
    push_cast
    have hMp : (0 : ℝ) ≤ Mp := Nat.cast_nonneg _
    nlinarith only [hj,hlev,hMp,mul_pos hκ hL]
  have hrL : p.r target ≤ d.L := by
    have hh := (hp.2.2.2.2.1 target htarget).1
    have hsL := mul_le_mul_of_nonneg_right hmiddle.2 hL.le
    have hubL : z ≤ d.L := by
      simpa only [z,one_mul] using mul_le_mul_of_nonneg_right hub1 hL.le
    have hδsmall : δ₀ * d.L ≤ d.L / 800 := hδL.trans (by linarith)
    have hr := (le_abs_self (p.r target - s target * d.L)).trans hh
    linarith
  have hU : z / 4 ≤ (U : ℝ) := Nat.le_ceil _
  have hinv : (d.N k ^ (-z / 4))⁻¹ ≤ d.N k ^ U := by
    rw [← Real.rpow_neg hNpos.le,neg_div,neg_neg,← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hN hU
  have hsmallCount : (Jpred : ℝ) ≤ 3 * envelope ^ 2 := by
    have hh : (Jpred : ℝ) ≤ envelope := by dsimp only [envelope]; linarith [hp.1]
    nlinarith
  exact EarlyCaptureNarrow.narrow_of_early_capture hd P hp
    (width := d.N k ^ (-z / 2)) (radius := d.N k ^ (-z / 4))
    (β := ub / 8) (loss := z / 32) (stripExponent := z / 4) (envelope := envelope)
    hH hi hstop target htarget horder
    hrL hmiddle Jpred hJpred (Real.rpow_pos_of_pos hNpos _).le
    (Real.rpow_pos_of_pos hNpos _).le hscale hu0 hubgain J U 1 (by dsimp only [J]; omega)
    htime hEN hEκ (Real.rpow_pos_of_pos hNpos _)
    (Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)) hinv
    (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) (by simpa only [pow_one] using hpredk)
    hsmallCount hslack hdet (le_of_eq (by congr 1; ring))
    (by dsimp only [z] at hδL hz ⊢; nlinarith only [hδL,hz]) hmass

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.EarlyCaptureUniform
