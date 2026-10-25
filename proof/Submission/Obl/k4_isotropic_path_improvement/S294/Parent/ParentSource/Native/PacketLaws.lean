-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.PacketLaws, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/PacketLaws.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/PacketLaws.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/PacketLaws.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/PacketLaws.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Frames

/-! Fixed reference priors for residual packets, before any sparse selection. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

def PathData.block {W : ℕ} (p : PathData W) (b : Fin p.C) : Set ℝ :=
  Icc ((p.j b : ℝ) / (2 : ℝ) ^ p.T (p.lev b))
    (((p.j b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b))

noncomputable def PathData.referencePrior {W : ℕ} (p : PathData W)
    (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))) (b : Fin p.C) :
    Measure (ℕ × (Fin 6 → ℝ)) :=
  ProbabilityTheory.cond (ν (p.γ b)) (p.A b)

noncomputable def PathData.referenceTime {W : ℕ} (p : PathData W) (b : Fin p.C) :
    Measure ℝ :=
  ProbabilityTheory.cond volume (p.block b)

noncomputable def PathData.residualPacketLaw {W : ℕ} (p : PathData W)
    (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ)))
    (H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (b : Fin p.C) :
    Measure ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  ProbabilityTheory.cond ((ν (p.γ b)).prod volume) (H (p.γ b) ∩ p.F b)

theorem PathData.volume_block {W : ℕ} (p : PathData W) (b : Fin p.C) :
    volume (p.block b) = ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹) := by
  rw [block, Real.volume_Icc]
  congr 1
  ring

/-- A mass floor against the full old assignment yields one conditional
packet probability, dominated by its fixed prior times uniform block time.
All later selections can restrict these three laws without renormalizing them. -/
theorem PathData.Valid.conditional_packet_laws {W : ℕ} {p : PathData W}
    {Nk L : ℝ} {ω : Fin W → ℝ} {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ} {f : ℝ → ℝ}
    {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hNk : 0 < Nk)
    (hν : ∀ w, IsProbabilityMeasure (ν w))
    (H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (b : Fin p.C)
    {c : ℝ} (hc : 0 < c)
    (hfloor : ENNReal.ofReal (c / (2 : ℝ) ^ p.T (p.lev b)) * ν (p.γ b) (p.A b) ≤
      ((ν (p.γ b)).prod volume) (H (p.γ b) ∩ p.F b)) :
    IsProbabilityMeasure (p.referencePrior ν b) ∧
      IsProbabilityMeasure (p.referenceTime b) ∧
      IsProbabilityMeasure (p.residualPacketLaw ν H b) ∧
      p.residualPacketLaw ν H b ≤
        ENNReal.ofReal c⁻¹ • (p.referencePrior ν b).prod (p.referenceTime b) := by
  have := hν (p.γ b)
  have hApos := h.assignment_mass_pos hNk b
  have hAtop : ν (p.γ b) (p.A b) ≠ ∞ := measure_ne_top _ _
  have hblockpos : 0 < volume (p.block b) := by rw [p.volume_block]; positivity
  have hblocktop : volume (p.block b) ≠ ∞ := by rw [p.volume_block]; finiteness
  have hprior : IsProbabilityMeasure (p.referencePrior ν b) :=
    ProbabilityTheory.cond_isProbabilityMeasure hApos.ne'
  have htime : IsProbabilityMeasure (p.referenceTime b) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite hblockpos.ne' hblocktop
  have hsub : H (p.γ b) ∩ p.F b ⊆ p.A b ×ˢ p.block b := by
    rcases h.2.2.2.2.2.2.2 b with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hF, _⟩
    intro z hz
    exact ⟨(hF z hz.2).2.1, (hF z hz.2).2.2.1⟩
  have hupper : ((ν (p.γ b)).prod volume) (H (p.γ b) ∩ p.F b) ≤
      ν (p.γ b) (p.A b) * volume (p.block b) := by
    calc
      _ ≤ ((ν (p.γ b)).prod volume) (p.A b ×ˢ p.block b) := measure_mono hsub
      _ = _ := Measure.prod_prod _ _
  have hpos : 0 < ((ν (p.γ b)).prod volume) (H (p.γ b) ∩ p.F b) :=
    lt_of_lt_of_le (by positivity) hfloor
  have htop : ((ν (p.γ b)).prod volume) (H (p.γ b) ∩ p.F b) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hAtop hblocktop) hupper
  have hlaw : IsProbabilityMeasure (p.residualPacketLaw ν H b) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite hpos.ne' htop
  refine ⟨hprior, htime, hlaw, ?_⟩
  have href : (p.referencePrior ν b).prod (p.referenceTime b) =
      ProbabilityTheory.cond ((ν (p.γ b)).prod volume) (p.A b ×ˢ p.block b) := by
    simp only [referencePrior, referenceTime, ProbabilityTheory.cond, Measure.prod_smul_left,
      Measure.prod_smul_right, Measure.prod_restrict, Measure.prod_prod, smul_smul]
    rw [ENNReal.mul_inv (Or.inl hApos.ne') (Or.inl hAtop), mul_comm]
  have hfloor' : ENNReal.ofReal c *
      ((ν (p.γ b)).prod volume) (p.A b ×ˢ p.block b) ≤
        ((ν (p.γ b)).prod volume) (H (p.γ b) ∩ p.F b) := by
    calc
      _ = (ENNReal.ofReal c * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹)) *
          ν (p.γ b) (p.A b) := by rw [Measure.prod_prod, p.volume_block]; ring
      _ = ENNReal.ofReal (c / (2 : ℝ) ^ p.T (p.lev b)) * ν (p.γ b) (p.A b) := by
        rw [← ENNReal.ofReal_mul hc.le, div_eq_mul_inv]
      _ ≤ _ := hfloor
  rw [href]
  have hinv := ENNReal.inv_le_inv.mpr hfloor'
  rw [ENNReal.mul_inv (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr hc))
    (Or.inl ENNReal.ofReal_ne_top)] at hinv
  have hrestrict : (((ν (p.γ b)).prod volume).restrict (H (p.γ b) ∩ p.F b)) ≤
      ((ν (p.γ b)).prod volume).restrict (p.A b ×ˢ p.block b) :=
    Measure.restrict_mono hsub le_rfl
  intro S
  have hmul := mul_le_mul hinv (hrestrict S) zero_le zero_le
  simpa only [residualPacketLaw, ProbabilityTheory.cond, Measure.smul_apply, smul_eq_mul,
    mul_assoc, ENNReal.ofReal_inv_of_pos hc] using hmul

/-- Every earlier level contains a residual packet with fixed full-assignment
reference probabilities and a conditional incidence density bounded by `4κ`. -/
theorem PathData.Valid.exists_conditional_packet {W : ℕ} {p : PathData W}
    {Nk L : ℝ} {ω : Fin W → ℝ} {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ} {f : ℝ → ℝ}
    {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hNk : 0 < Nk)
    (hν : ∀ w, IsProbabilityMeasure (ν w)) (hω : ∀ w, 0 ≤ ω w) (hsum : ∑ w, ω w = 1)
    (H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (hmass : ENNReal.ofReal (p.κ⁻¹ / 2) ≤
      ∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (H w)) (i : ℕ) (hi : i < m) :
    ∃ b, p.lev b = i ∧ 0 < ω (p.γ b) ∧
      IsProbabilityMeasure (p.referencePrior ν b) ∧
      IsProbabilityMeasure (p.referenceTime b) ∧
      IsProbabilityMeasure (p.residualPacketLaw ν H b) ∧
      p.residualPacketLaw ν H b ≤
        ENNReal.ofReal (4 * p.κ) • (p.referencePrior ν b).prod (p.referenceTime b) := by
  obtain ⟨b, hlev, hw, hb⟩ := h.exists_dense_packet hν hω hsum H hH hmass i hi
  have hκ : 0 < p.κ := lt_of_lt_of_le zero_lt_one h.1
  have hfloor : ENNReal.ofReal ((p.κ⁻¹ / 4) / (2 : ℝ) ^ p.T (p.lev b)) *
      ν (p.γ b) (p.A b) ≤ ((ν (p.γ b)).prod volume) (H (p.γ b) ∩ p.F b) := by
    simpa only [hlev] using hb.le
  have hpacket := h.conditional_packet_laws hNk hν H b (c := p.κ⁻¹ / 4) (by positivity) hfloor
  refine ⟨b, hlev, hw, hpacket.1, hpacket.2.1, hpacket.2.2.1, ?_⟩
  have hinv : (p.κ⁻¹ / 4)⁻¹ = 4 * p.κ := by field_simp
  simpa only [hinv] using hpacket.2.2.2

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
