-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.FrontPreparation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/FrontPreparation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.StrongPalette
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.StrongBroadResidual
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.UniformBoundsPreparation
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeWindow

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.FrontPreparation

open MeasureTheory Set Filter
open ParentSource ParentSource.Native

noncomputable section

/-- The original path supplies the pure-density masks, velocity window,
strong original palette, and saturated narrow/broad alternative. All
thresholds and the window are fixed before the actual path arrives. -/
theorem exists_prepared_front {T : Type*} [Fintype T]
    {d : ProblemData} (hd : d.Valid) (κ₁ : ℝ) (m : ℕ) (hm : 0 < m)
    (s : ℕ → ℝ) (δ₀ : ℝ) (Mp Dp : ℕ) (u : T → ℝ)
    (hu : ∀ t, 0 < u t ∧ u t ≤ d.η * d.L)
    (τ εpure : ℝ) (hτ : 0 < τ) (hεpure : 0 < εpure)
    (C : ℕ) (hC : 1 ≤ C) (indices : Finset ℕ)
    (hindices : ∀ i ∈ indices, i < m ∧ i + C < m)
    (σvel ue entropy paletteExponent stripExponent : ℝ) (hσvel : 0 < σvel)
    (hue : 0 ≤ ue) (hentropy : 0 ≤ entropy)
    (hgap : 2 * (C : ℝ) * (σvel + ue) < (indices.card : ℝ) * (entropy * (1 / 128)))
    (hmesh : paletteExponent + 2 * δ₀ * d.L ≤ ue) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ k in atTop, ∀ p : PathData (d.W k),
      p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ →
      ∀ H : Fin (d.W k) → Set Ev,
      (∀ w, MeasurableSet (H w)) →
      (∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b}) →
      ENNReal.ofReal (p.κ⁻¹ / 2) ≤
        ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (H w) →
      ∃ Q : PreparedAngularPath d k p m H u τ,
        Q.uniformPureBounds εpure ∧
        ENNReal.ofReal (11 * p.κ⁻¹ / 32) ≤
          ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Q.residual w) ∧
        ∃ i ∈ indices,
        ∃ F : PaletteFamily Q i (i + C) (d.N k ^ (-paletteExponent))
            (d.N k ^ entropy / palettePruningThreshold ⌈(4 * p.κ + 6) ^ 2⌉₊)
            (lightParentThreshold p.κ),
          ENNReal.ofReal (15 / 16 : ℝ) ≤ Q.law
            (labelledSupport (Q.packetFamilyResidual i (Q.selectedCoarseFamily F.active F.U))) ∧
          (∀ b, F.active b → F.U b ⊆
            likelihoodGood Q.law (labelledSupport Q.residual)
              (finitePacketHistory p.lev p.γ p.F) (labelledVelocityPalette (d.N k^(-ue)))
              i (i+C) (d.N k^entropy)) ∧
          ∀ fraction : ℝ, 0 < fraction →
          ∃ P : PaletteStripSaturation F (d.N k ^ (-stripExponent)) fraction,
            ENNReal.ofReal (9 * p.κ⁻¹ / 64) ≤
              ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (P.captureResidual w) ∨
            ∃ F' : PaletteFamily Q i (i + C) (d.N k ^ (-paletteExponent))
                (d.N k ^ entropy / palettePruningThreshold ⌈(4 * p.κ + 6) ^ 2⌉₊)
                (lightParentThreshold p.κ),
              (∃ R : BroadResidual F' (d.N k ^ (-stripExponent)) (2 * fraction),
                ENNReal.ofReal (71 * p.κ⁻¹ / 512) ≤
                  ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (R.residual w)) ∧
              ∀ b, F'.active b → F'.U b ⊆
                likelihoodGood Q.law (labelledSupport Q.residual)
                  (finitePacketHistory p.lev p.γ p.F) (labelledVelocityPalette (d.N k^(-ue)))
                  i (i+C) (d.N k^entropy) := by
  obtain ⟨σ,hσ,hprep⟩ := hd.prepare_native_angular_path_uniform_bounds
    κ₁ m hm s δ₀ Mp Dp u hu τ εpure hτ hεpure
  have hK := hd.2.2.1.2 σvel hσvel
  have hbudget := eventually_velocity_window_budget d.N hd.tendsto indices m C
    σvel ue entropy (1 / 128) hgap
  refine ⟨σ,hσ,?_⟩
  filter_upwards [hprep,hK,hbudget] with k hprepk hKk hbudgetk
  intro p hp H hH hcover hmass
  have hHE := hp.residual_subset_event H hcover
  have hN : 1 ≤ d.N k := le_trans (by norm_num) (hd.1 k)
  have hNpos : 0 < d.N k := zero_lt_one.trans_le hN
  obtain ⟨Q,hbuffer,hpure⟩ := hprepk p hp H hH hcover hmass
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  obtain ⟨i,hi,hgood⟩ := Q.good_velocity_window hd hHE
    (zero_lt_one.trans_le hp.1) hF m C hC indices
    (fun i hi => ⟨(hindices i hi).1,(hindices i hi).2.le⟩)
    σvel ue entropy (1 / 128) hσvel.le hue hentropy (by norm_num) hKk hbudgetk
  have hbad : Q.law (labelledSupport Q.residual \ likelihoodGood Q.law
      (labelledSupport Q.residual) (finitePacketHistory p.lev p.γ p.F)
      (labelledVelocityPalette (d.N k ^ (-ue))) i (i + C) (d.N k ^ entropy)) ≤
      ENNReal.ofReal (1 / 128 : ℝ) := by
    rw [likelihoodGood_lost_mass]
    exact hgood
  have hmesh' : d.N k ^ (-ue) * d.N k ^ (2 * δ₀ * d.L) ≤ d.N k ^ (-paletteExponent) := by
    rw [← Real.rpow_add hNpos]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  obtain ⟨coding⟩ := hp.exists_packetCoding hNpos
  obtain ⟨F,hfull,hOriginal⟩ := StrongPalette.exists_default_palette_family_with_original_likelihood Q hd hp hHE hcover coding i
    (hindices i hi).1 (i + C) (Nat.le_add_right i C)
    (Real.rpow_pos_of_pos hNpos _) (Real.rpow_pos_of_pos hNpos _)
    (Real.rpow_pos_of_pos hNpos _).le hmesh' hbad
  refine ⟨Q,hpure,hbuffer,i,hi,F,hfull,hOriginal,?_⟩
  intro fraction hfraction
  have hKpalette := (native_palette_integer_bounds hp.1).1
  obtain ⟨P⟩ := F.exists_stripSaturation hd hp hHE (d.N k ^ (-stripExponent)) fraction
    hfraction (Real.rpow_pos_of_pos hNpos _)
    (div_pos (Real.rpow_pos_of_pos hNpos _) (palettePruningThreshold_pos hKpalette))
  by_cases hlarge : ENNReal.ofReal (9*p.κ⁻¹/64) ≤
      ∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (P.captureResidual w)
  · exact ⟨P,Or.inl hlarge⟩
  · have hcap := SaturatedDichotomy.prepared_capture_le_of_small_original P hp hd hHE hbuffer hlarge
    have hremaining := SaturatedDichotomy.remaining_mass P hfull hcap
    let F' := SaturatedDichotomy.remainingPalette P hp hremaining
    have hbroad : ∃ R : BroadResidual F' (d.N k^(-stripExponent)) (2*fraction),
        ENNReal.ofReal (71 * p.κ⁻¹ / 512) ≤
          ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (R.residual w) :=
      SaturatedDichotomy.remaining_broad_strong P hp hd hHE hcover
        (hindices i hi).1 (hindices i hi).2 hfraction hbuffer hfull hcap
    refine ⟨P,Or.inr ⟨F',hbroad,?_⟩⟩
    intro b hb z hz
    exact hOriginal b hb hz.1

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.FrontPreparation
