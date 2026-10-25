-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.EarlyCaptureDynamic, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/EarlyCaptureDynamic.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.FiniteStripUniform
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.EarlyCaptureUniform
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.PathTolerance

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.EarlyCaptureUniform

open MeasureTheory Set Filter
open ParentSource ParentSource.Native

noncomputable section

/-- The early-capture exit is uniform in a path-dependent prediction
count. Hence its saturation fraction may decrease with the original
native envelope, while the frozen output format remains fixed. -/
theorem eventually_narrow_of_early_capture_dynamic {T : Type*}
    {d : ProblemData} (hd : d.Valid) {κ₁ : ℝ} (hκ : 0 < κ₁)
    (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ) (Mp Dp : ℕ)
    {ub gain u0 : ℝ} (hub : 0 < ub) (hub1 : ub ≤ 1) (hδ : δ₀ ≤ ub/800)
    (hu0 : u0 ≤ ub/8) (hubgain : ub/8 ≤ 4*gain)
    (target : ℕ) (htarget : target < m)
    (hmiddle : 1/4 ≤ s target ∧ s target ≤ 1/2) {α : ℝ} (hα : 0 < α) :
    let J := Mp+⌈(κ₁+δ₀)*d.L⌉₊+1
    let U := ⌈ub*d.L/4⌉₊
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ ∀ᶠ k in atTop,
      ∀ p : PathData (d.W k),
      p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
        κ₁ m s δ₀ Mp Dp σ →
      ∀ H : Fin (d.W k) → Set Ev,
      (∀ w, H w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b}) →
      ∀ (u : T → ℝ) (τ : ℝ) (Q : PreparedAngularPath d k p m H u τ)
        (i stop : ℕ), i ≤ stop → stop < m → stop ≤ target →
      ∀ (a A fraction : ℝ) (θ : ENNReal) (F : PaletteFamily Q i stop a A θ)
        (P : PaletteStripSaturation F (d.N k^(-(ub*d.L))) fraction)
        (Jpred : ℕ), fraction⁻¹ ≤ (Jpred : ℝ) → (Jpred : ℝ) ≤ d.N k^σ →
      ENNReal.ofReal (9*p.κ⁻¹/64) ≤
        ∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (P.captureResidual w) →
      ParentSource.narrow (d.N k) d.L (d.W k) (d.ω k) (d.ν k) (d.E k) (d.B k)
        m s p.r p.T p.nw gain u0 p.κ (stripMergedOutputExponent Mp J U 1 0) (max Dp 1) α
        p.C p.lev p.γ p.j p.A p.F H := by
  dsimp only
  have hL : 0 < d.L := hd.2.2.2.1
  let z := ub*d.L
  have hz : 0 < z := mul_pos hub hL
  have hδL : δ₀*d.L ≤ z/800 := by
    have hh := mul_le_mul_of_nonneg_right hδ hL.le
    dsimp only [z]
    linarith
  obtain ⟨σN,hσN,hσN1,hnarrow⟩ := FiniteStripUniform.eventually_narrow_of_unit_strips
    hd hκ m s δ₀ Mp Dp hub hub1 hδ hu0 hubgain target htarget hmiddle hα
  obtain ⟨σS,hσS,hσS1,hScale⟩ := strip_uniform_monomial_bound hd.tendsto
    (show -z+2*δ₀*d.L < -z/2 by linarith) (by norm_num : (0:ℝ) ≤ 1) 2
  let σ := min σN σS
  refine ⟨σ,lt_min hσN hσS,(min_le_left _ _).trans hσN1,?_⟩
  filter_upwards [hnarrow,hScale] with k hnarrowk hScalek
  intro p hp H hH u τ Q i stop hi hstop horder a A fraction θ F P Jpred hpred hpredCount hmass
  have hN : 1 ≤ d.N k := le_trans (by norm_num) (hd.1 k)
  have hNpos : 0 < d.N k := zero_lt_one.trans_le hN
  have hpN := PathTolerance.mono hp hN (min_le_left σN σS)
  have hκScale : p.κ ≤ d.N k^σS := hp.2.1.trans
    (Real.rpow_le_rpow_of_exponent_le hN (min_le_right σN σS))
  have hscale : d.N k^(-z)*(p.κ^2*d.N k^(2*δ₀*d.L)) ≤ d.N k^(-z/2) := by
    have hh := hScalek p.κ hp.1 hκScale
    have heq : d.N k^(-z)*(p.κ^2*d.N k^(2*δ₀*d.L))=
        1*p.κ^2*d.N k^(-z+2*δ₀*d.L) := by
      rw [Real.rpow_add hNpos]
      ring
    rw [heq]
    exact hh
  obtain ⟨normal,offset,hn,hoff,hcover⟩ := AncestorPredictions.exists_descendant_capture_strips
    P hp hN hH hi hstop target htarget horder Jpred hpred
    (Real.rpow_pos_of_pos hNpos _).le (Real.rpow_pos_of_pos hNpos _).le hscale
  have hclean : ENNReal.ofReal (p.κ⁻¹/8) ≤
      ∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (P.cleanCapture w) := by
    rw [P.cleanCapture_original_mass hp]
    have hκp : 0 < p.κ := zero_lt_one.trans_le hp.1
    exact (ENNReal.ofReal_le_ofReal (by nlinarith [inv_pos.mpr hκp])).trans hmass
  exact hnarrowk p hpN Jpred
    (hpredCount.trans (Real.rpow_le_rpow_of_exponent_le hN (min_le_left σN σS)))
    normal offset hn hoff P.cleanCapture H
    (fun w x hx => P.captureResidual_subset_H w hx.1.1) hcover hclean

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.EarlyCaptureUniform
