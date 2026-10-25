-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.NativeFractionFront, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/NativeFractionFront.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.FrontAlternativeDynamic
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.NativePredictionCount

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.FrontAlternative

open MeasureTheory Set Filter
open ParentSource ParentSource.Native

noncomputable section

/-- The actual native envelope may choose the saturation fraction after
all problem and path data arrive. It can be as small as any fixed inverse
power, with no change to the exact original narrow exit format. -/
theorem exists_narrow_or_broad_native_fraction {T : Type*} [Fintype T]
    {d : ProblemData} (hd : d.Valid) {κ₁ : ℝ} (hκ : 0 < κ₁)
    (m : ℕ) (hm : 0 < m) (s : ℕ → ℝ) (δ₀ : ℝ) (Mp Dp : ℕ)
    (u : T → ℝ) (hu : ∀ t, 0 < u t ∧ u t ≤ d.η * d.L)
    (τ εpure : ℝ) (hτ : 0 < τ) (hεpure : 0 < εpure)
    (C : ℕ) (hC : 1 ≤ C) (indices : Finset ℕ)
    (hindices : ∀ i ∈ indices, i < m ∧ i + C < m)
    (σvel ue entropy paletteExponent : ℝ) (hσvel : 0 < σvel)
    (hue : 0 ≤ ue) (hentropy : 0 ≤ entropy)
    (hgap : 2 * (C : ℝ) * (σvel + ue) < (indices.card : ℝ) * (entropy * (1 / 128)))
    (hmesh : paletteExponent + 2 * δ₀ * d.L ≤ ue)
    {ub gain u0 : ℝ} (hub : 0 < ub) (hub1 : ub ≤ 1) (hδ : δ₀ ≤ ub / 800)
    (hu0 : u0 ≤ ub / 8) (hubgain : ub / 8 ≤ 4 * gain)
    (target : ℕ) (htarget : target < m)
    (hmiddle : 1 / 4 ≤ s target ∧ s target ≤ 1 / 2)
    (hbefore : ∀ i ∈ indices, i + C ≤ target)
    {α : ℝ} (hα : 0 < α) (power : ℕ) :
    let J := Mp + ⌈(κ₁ + δ₀) * d.L⌉₊ + 1
    let U := ⌈ub * d.L / 4⌉₊
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ ∀ᶠ k in atTop, ∀ p : PathData (d.W k),
      p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
        κ₁ m s δ₀ Mp Dp σ →
      ∀ H : Fin (d.W k) → Set Ev, (∀ w, MeasurableSet (H w)) →
      (∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b}) →
      ENNReal.ofReal (p.κ⁻¹ / 2) ≤
        ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (H w) →
      ∀ Kgeom : ℝ, 1 ≤ Kgeom → Kgeom ≤ d.N k^σ →
      ParentSource.narrow (d.N k) d.L (d.W k) (d.ω k) (d.ν k) (d.E k) (d.B k)
        m s p.r p.T p.nw gain u0 p.κ (stripMergedOutputExponent Mp J U 1 0) (max Dp 1) α
        p.C p.lev p.γ p.j p.A p.F H ∨
      ∃ Q : PreparedAngularPath d k p m H u τ, Q.uniformPureBounds εpure ∧
        ENNReal.ofReal (11 * p.κ⁻¹ / 32) ≤
          ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Q.residual w) ∧
        ∃ i ∈ indices,
        ∃ F : PaletteFamily Q i (i + C) (d.N k ^ (-paletteExponent))
            (d.N k ^ entropy / palettePruningThreshold ⌈(4 * p.κ + 6) ^ 2⌉₊)
            (lightParentThreshold p.κ),
          (∃ R : BroadResidual F (d.N k ^ (-(ub * d.L))) (2 * (Kgeom^power)⁻¹),
            ENNReal.ofReal (71 * p.κ⁻¹ / 512) ≤
              ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (R.residual w)) ∧
          ∀ b, F.active b → F.U b ⊆
            likelihoodGood Q.law (labelledSupport Q.residual)
              (finitePacketHistory p.lev p.γ p.F) (labelledVelocityPalette (d.N k^(-ue)))
              i (i+C) (d.N k^entropy) := by
  obtain ⟨σF,hσF,hσF1,hfront⟩ := exists_narrow_or_broad_dynamic_fraction
    hd hκ m hm s δ₀ Mp Dp u hu τ εpure hτ hεpure C hC indices hindices
    σvel ue entropy paletteExponent hσvel hue hentropy hgap hmesh hub hub1 hδ
    hu0 hubgain target htarget hmiddle hbefore hα
  obtain ⟨σG,hσG,hσG1,hcount⟩ := eventually_native_prediction_count d.N hd.tendsto hσF power
  refine ⟨min σF σG,lt_min hσF hσG,(min_le_left _ _).trans hσF1,?_⟩
  filter_upwards [hfront,hcount] with k hfrontk hcountk
  intro p hp H hH hcover hmass Kgeom hKgeom hKpower
  have hN : 1 ≤ d.N k := le_trans (by norm_num) (hd.1 k)
  have hpF := PathTolerance.mono hp hN (min_le_left σF σG)
  have hKpow : 0 < Kgeom^power := pow_pos (zero_lt_one.trans_le hKgeom) _
  have hcount' := hcountk Kgeom hKgeom
    (hKpower.trans (Real.rpow_le_rpow_of_exponent_le hN (min_le_right σF σG)))
  exact hfrontk p hpF H hH hcover hmass (Kgeom^power)⁻¹ (inv_pos.mpr hKpow)
    ⌈Kgeom^power⌉₊ (by simpa only [inv_inv] using Nat.le_ceil (Kgeom^power)) hcount'

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.FrontAlternative
