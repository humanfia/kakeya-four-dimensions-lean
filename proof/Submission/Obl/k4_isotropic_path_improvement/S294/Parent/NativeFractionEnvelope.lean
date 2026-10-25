-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.NativeFractionEnvelope, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.NativeFractionFront

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.FrontAlternative

open MeasureTheory Set Filter
open ParentSource ParentSource.Native

noncomputable section

/-- Fix the native envelope exponent BEFORE the front entropy, palette
and pure-cap parameters. The path tolerance may subsequently shrink
without shrinking the allowed prediction budget. This lets one actual
geometric envelope pay all later finite-state refinement costs. -/
theorem exists_narrow_or_broad_fraction_envelope {T : Type*} [Fintype T]
    {d : ProblemData} (hd : d.Valid) {κ₁ : ℝ} (hκ : 0 < κ₁)
    (m : ℕ) (hm : 0 < m) (s : ℕ → ℝ) (δ₀ : ℝ) (Mp Dp : ℕ)
    {ub gain u0 : ℝ} (hub : 0 < ub) (hub1 : ub ≤ 1) (hδ : δ₀ ≤ ub / 800)
    (hu0 : u0 ≤ ub / 8) (hubgain : ub / 8 ≤ 4 * gain)
    (target : ℕ) (htarget : target < m)
    (hmiddle : 1 / 4 ≤ s target ∧ s target ≤ 1 / 2)
    {α : ℝ} (hα : 0 < α) (power : ℕ) :
    ∃ budget : ℝ, 0 < budget ∧ budget ≤ 1 ∧
    ∀
    (u : T → ℝ) (hu : ∀ t, 0 < u t ∧ u t ≤ d.η * d.L)
    (τ εpure : ℝ) (hτ : 0 < τ) (hεpure : 0 < εpure)
    (C : ℕ) (hC : 1 ≤ C) (indices : Finset ℕ)
    (hindices : ∀ i ∈ indices, i < m ∧ i + C < m)
    (σvel ue entropy paletteExponent : ℝ) (hσvel : 0 < σvel)
    (hue : 0 ≤ ue) (hentropy : 0 ≤ entropy)
    (hgap : 2 * (C : ℝ) * (σvel + ue) < (indices.card : ℝ) * (entropy * (1 / 128)))
    (hmesh : paletteExponent + 2 * δ₀ * d.L ≤ ue)
    (hbefore : ∀ i ∈ indices, i + C ≤ target),
    let J := Mp + ⌈(κ₁ + δ₀) * d.L⌉₊ + 1
    let U := ⌈ub * d.L / 4⌉₊
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ ∀ᶠ k in atTop, ∀ p : PathData (d.W k),
      p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
        κ₁ m s δ₀ Mp Dp σ →
      ∀ H : Fin (d.W k) → Set Ev, (∀ w, MeasurableSet (H w)) →
      (∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b}) →
      ENNReal.ofReal (p.κ⁻¹ / 2) ≤
        ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (H w) →
      ∀ Kgeom : ℝ, 1 ≤ Kgeom → Kgeom ≤ d.N k^budget →
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
  dsimp only
  obtain ⟨σN,hσN,hσN1,hnarrow⟩ := EarlyCaptureUniform.eventually_narrow_of_early_capture_dynamic (T := T)
    hd hκ m s δ₀ Mp Dp hub hub1 hδ hu0 hubgain target htarget hmiddle hα
  obtain ⟨budget,hbudget,hbudget1,hcount⟩ := eventually_native_prediction_count
    d.N hd.tendsto hσN power
  refine ⟨budget,hbudget,hbudget1,?_⟩
  intro u hu τ εpure hτ hεpure C hC indices hindices
    σvel ue entropy paletteExponent hσvel hue hentropy hgap hmesh hbefore
  obtain ⟨σF,hσF,hfront⟩ := FrontPreparation.exists_prepared_front hd κ₁ m hm s δ₀ Mp Dp u hu
    τ εpure hτ hεpure C hC indices hindices σvel ue entropy paletteExponent (ub*d.L)
    hσvel hue hentropy hgap hmesh
  refine ⟨min σF σN,lt_min hσF hσN,(min_le_right _ _).trans hσN1,?_⟩
  filter_upwards [hfront,hnarrow,hcount] with k hfrontk hnarrowk hcountk
  intro p hp H hH hcover hmass Kgeom hKgeom hKpower
  have hN : 1 ≤ d.N k := le_trans (by norm_num) (hd.1 k)
  have hpF := PathTolerance.mono hp hN (min_le_left σF σN)
  have hpN := PathTolerance.mono hp hN (min_le_right σF σN)
  have hKpow : 0 < Kgeom^power := pow_pos (zero_lt_one.trans_le hKgeom) _
  have hcount' := hcountk Kgeom hKgeom hKpower
  obtain ⟨Q,hpure,hbuffer,i,hi,F,hfull,hOriginal,hsaturation⟩ := hfrontk p hpF H hH hcover hmass
  obtain ⟨P,hcapture | hbroad⟩ := hsaturation (Kgeom^power)⁻¹ (inv_pos.mpr hKpow)
  · refine Or.inl (hnarrowk p hpN H hcover u τ Q i (i+C) (Nat.le_add_right i C)
      (hindices i hi).2 (hbefore i hi) _ _ _ _ F P ⌈Kgeom^power⌉₊ ?_ hcount' hcapture)
    simpa only [inv_inv] using Nat.le_ceil (Kgeom^power)
  · obtain ⟨F',hF',hOriginal'⟩ := hbroad
    exact Or.inr ⟨Q,hpure,hbuffer,i,hi,F',hF',hOriginal'⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.FrontAlternative
