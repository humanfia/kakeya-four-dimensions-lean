-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.PaletteCertificate, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/PaletteCertificate.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/PaletteCertificate.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/PaletteCertificate.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.SelectedPaletteFamily

/-! A finite family of actual original packet posteriors, with retained
mass and the joint bounds needed by both geometric alternatives. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}

structure PaletteFamily (Q : PreparedAngularPath d k p m H u τ) (i stop : ℕ)
    (a A : ℝ) (θ : ENNReal) where
  coding : PacketCoding p (d.ν k)
  active : Fin p.C → Prop
  code : Fin p.C → ℕ
  U : Fin p.C → Set (Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ))
  level : ∀ b, active b → p.lev b = i
  weight_positive : ∀ b, active b → 0 < d.ω k (p.γ b)
  current_positive : ∀ b, active b → Q.currentParentLaw b univ ≠ 0
  code_original : ∀ b, active b → code b = coding.code b
  packet : ∀ b, active b → ∀ z ∈ Q.coarseSupport (p.lev b) (code b),
    z.1 = p.γ b ∧ z.2 ∈ p.F b
  coarse_positive : ∀ b, active b → Q.law (Q.coarseSupport (p.lev b) (code b)) ≠ 0
  posterior : ∀ b, active b → (Q.coarseLaw (p.lev b) (code b)).map Prod.snd =
    ProbabilityTheory.cond (Q.currentParentLaw b) univ
  measurable_U : ∀ b, active b → MeasurableSet (U b)
  subset_coarse : ∀ b, active b → U b ⊆ Q.coarseSupport (p.lev b) (code b)
  reference_floor : ∀ b, active b →
    θ * d.pathAngularReference k p Q.base Q.mask b univ ≤ Q.currentParentLaw b univ
  joint_cap : ∀ b, active b → ∀ e q, (Q.coarseLaw (p.lev b) (code b)).real
    {z | z ∈ U b ∧ finitePacketHistory p.lev p.γ p.F stop z = e ∧
      p.labelledNormalizedPalette b a z = q} ≤
    A * (Q.coarseLaw (p.lev b) (code b)).real {z | finitePacketHistory p.lev p.γ p.F stop z = e} *
      (Q.coarseLaw (p.lev b) (code b)).real {z | p.labelledNormalizedPalette b a z = q}
  mass : ENNReal.ofReal (1 / 2 : ℝ) ≤ Q.law
    (labelledSupport (Q.packetFamilyResidual i (Q.selectedCoarseFamily active U)))

variable (Q : PreparedAngularPath d k p m H u τ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

theorem PreparedAngularPath.exists_paletteFamily (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (coding : PacketCoding p (d.ν k)) (i : ℕ) (hi : i < m) (stop : ℕ) (hst : i ≤ stop)
    {a₀ a₁ ε R α : ℝ} (ha₀ : 0 < a₀) (ha₁ : 0 < a₁) (hε : 0 < ε) (hR : 0 ≤ R)
    (hmesh : a₀ * d.N k ^ (2 * δ₀ * d.L) ≤ a₁) (K : ℕ) (hK : (4 * p.κ + 6) ^ 2 ≤ (K : ℝ))
    (θ : ENNReal)
    (hbad : Q.law (labelledSupport Q.residual \ likelihoodGood Q.law (labelledSupport Q.residual)
      (finitePacketHistory p.lev p.γ p.F) (labelledVelocityPalette a₀) i stop R) ≤ ENNReal.ofReal α)
    (hbudget : ENNReal.ofReal α + (θ * ENNReal.ofReal (8 * p.κ) + ENNReal.ofReal (ε * K)) ≤
      ENNReal.ofReal (1 / 2 : ℝ)) :
    Nonempty (PaletteFamily Q i stop a₁ (R / ε) θ) := by
  obtain ⟨code, hcode, hdata, hmass⟩ := Q.exists_selected_palette_family hd hp hHE hH coding i hi
    stop hst ha₀ ha₁ hε hR hmesh K hK θ hbad hbudget
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  exact ⟨{
    coding := coding
    active := Q.paletteActive i θ
    code := code
    U := fun b => Q.normalizedPaletteCut b (p.lev b) stop (code b) a₀ a₁ R ε
    level := fun _ hb => hb.1
    weight_positive := fun _ hb => hb.2.1
    current_positive := fun _ hb => hb.2.2.1
    code_original := fun b hb =>
      Q.coarse_code_eq_packetCoding coding hF b (code b) (hcode b hb).1 (hcode b hb).2.1
    packet := fun b hb => (hcode b hb).1
    coarse_positive := fun b hb => (hcode b hb).2.1
    posterior := fun b hb => (hcode b hb).2.2
    measurable_U := fun b hb => (hdata b hb).1
    subset_coarse := fun b hb => (hdata b hb).2.1
    reference_floor := fun b hb => (hdata b hb).2.2.1
    joint_cap := fun b hb => (hdata b hb).2.2.2
    mass := hmass
  }⟩

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
