-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativeFineHistory, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativeFineHistory.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativeFineHistory.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativeFineHistory.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/NativeFineHistory.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeWindow
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativePredictionAssembly
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativePaletteTransfer

/-! Actual fine history states are represented by ORIGINAL fine packet
witnesses under both the single prepared law and all its coarse posteriors.
The null sets precede every later discovery selection. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- Original full-measure properties survive the one weighted normalization.
No reference denominator or original world weight is changed. -/
theorem preparedResidualLaw_original_ae {W : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Fin W → Measure X) (ω : Fin W → ℝ) (H A : Fin W → Set X)
    (hA : ∀ w, MeasurableSet (A w)) (hAe : ∀ w, ∀ᵐ x ∂μ w, x ∈ A w) :
    ∀ᵐ z ∂preparedResidualLaw μ ω H, z.2 ∈ A z.1 := by
  have hD := (measurableSet_labelledSupport A hA).compl
  have hzero : preparedResidualLaw μ ω H (labelledSupport A)ᶜ = 0 := by
    rw [preparedResidualLaw_apply μ ω H _ hD]
    have hnull (w : Fin W) : μ w (H w ∩ {x | (w, x) ∈ (labelledSupport A)ᶜ}) = 0 := by
      apply measure_mono_null inter_subset_right
      exact ae_iff.mp (hAe w)
    simp only [hnull, mul_zero, Finset.sum_const_zero, ENNReal.zero_div]
  exact ae_iff.mpr hzero

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  (Q : PreparedAngularPath d k p m H u τ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

theorem PreparedAngularPath.ae_fine_packet_code
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (q : PacketCoding p (d.ν k)) (stop : ℕ) (hstop : stop < m) :
    ∀ᵐ z ∂Q.law, ∃ b, p.lev b = stop ∧ p.γ b = z.1 ∧
      finitePacketHistory p.lev p.γ p.F stop z = q.code b ∧
      z.2 ∈ p.packetWitness m stop z.1 b := by
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have hcore : ∀ᵐ z ∂Q.law, z.2 ∈ q.core z.1 :=
    preparedResidualLaw_original_ae (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual
      q.core (q.measurableSet_core hF) q.ae_core
  have hunique : ∀ᵐ z ∂Q.law, packetUnique p.lev p.γ p.F z.1 z.2 :=
    preparedResidualLaw_original_ae (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual
      (fun w => {z | packetUnique p.lev p.γ p.F w z})
      (measurableSet_packetUnique p.lev p.γ p.F hF) hp.ae_packet_unique
  have hres : ∀ᵐ z ∂Q.law, z.2 ∈ Q.residual z.1 := ae_iff.mpr
    (preparedResidualLaw_support (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual Q.residual_measurable)
  have hcover : ∀ w, Q.residual w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b} :=
    fun w => (Q.residual_subset w).trans ((Q.base_subset w).trans (hH w))
  have hcoverStop := hp.covered_at_level Q.residual stop hstop hcover
  filter_upwards [hcore, hunique, hres] with z hzcore hzunique hzres
  obtain ⟨b, hb, hbw, hzb⟩ := hcoverStop z.1 hzres
  have hcode := q.code_eq_of_mem_core z.1 hzcore b hbw hzb
  rw [hb] at hcode
  refine ⟨b, hb, hbw, hcode, ?_⟩
  obtain ⟨t, ht, htw, hzt⟩ := hcover z.1 hzres
  have hterminal : z.2 ∈ p.terminalCoverage m z.1 := ⟨t, ⟨ht, htw⟩, hzt⟩
  simpa only [PathData.packetWitness, ite_eq_left (show p.lev b = stop ∧ p.γ b = z.1 from ⟨hb, hbw⟩),
    mem_inter_iff, mem_ofPred_eq] using
      (show (z.2 ∈ p.F b ∧ packetUnique p.lev p.γ p.F z.1 z.2) ∧
        z.2 ∈ p.terminalCoverage m z.1 from ⟨⟨hzb, hzunique⟩, hterminal⟩)

/-- Every later coarse posterior uses the SAME original fine packet table. -/
theorem PreparedAngularPath.ae_coarse_fine_packet_code
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (q : PacketCoding p (d.ν k)) (stop : ℕ) (hstop : stop < m) (i c : ℕ) :
    ∀ᵐ z ∂Q.coarseLaw i c, ∃ b, p.lev b = stop ∧ p.γ b = z.1 ∧
      finitePacketHistory p.lev p.γ p.F stop z = q.code b ∧
      z.2 ∈ p.packetWitness m stop z.1 b :=
  (ProbabilityTheory.cond_absolutelyContinuous (μ := Q.law) (s := Q.coarseSupport i c)).ae_le
    (Q.ae_fine_packet_code hp hH q stop hstop)

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
