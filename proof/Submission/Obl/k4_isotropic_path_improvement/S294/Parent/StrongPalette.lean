-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.StrongPalette, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/StrongPalette.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.SourceBridge

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.StrongPalette

open MeasureTheory Set
open ParentSource ParentSource.Native

noncomputable section

/-- Retain the explicit `15/16` palette mass from the original omission
budgets. Keeping this buffer makes the original narrow-capture threshold
compatible with the broad alternative. -/
theorem exists_strong_palette_family_with_original_likelihood {T : Type*} {d : ProblemData} {k : ℕ}
    {p : PathData (d.W k)} {m : ℕ} {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    (Q : PreparedAngularPath d k p m H u τ) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (coding : PacketCoding p (d.ν k)) (i : ℕ) (hi : i < m) (stop : ℕ) (hst : i ≤ stop)
    {a₀ a₁ ε R α : ℝ} (ha₀ : 0 < a₀) (ha₁ : 0 < a₁) (hε : 0 < ε) (hR : 0 ≤ R)
    (hmesh : a₀ * d.N k ^ (2 * δ₀ * d.L) ≤ a₁) (K : ℕ) (hK : (4 * p.κ + 6) ^ 2 ≤ (K : ℝ))
    (θ : ENNReal)
    (hbad : Q.law (labelledSupport Q.residual \ likelihoodGood Q.law (labelledSupport Q.residual)
      (finitePacketHistory p.lev p.γ p.F) (labelledVelocityPalette a₀) i stop R) ≤ ENNReal.ofReal α)
    (hbudget : ENNReal.ofReal α + (θ * ENNReal.ofReal (8 * p.κ) + ENNReal.ofReal (ε * K)) ≤
      ENNReal.ofReal (1 / 16 : ℝ)) :
    ∃ F : PaletteFamily Q i stop a₁ (R / ε) θ,
      ENNReal.ofReal (15 / 16 : ℝ) ≤ Q.law
        (labelledSupport (Q.packetFamilyResidual i (Q.selectedCoarseFamily F.active F.U))) ∧
      ∀ b, F.active b → F.U b ⊆
        likelihoodGood Q.law (labelledSupport Q.residual)
          (finitePacketHistory p.lev p.γ p.F) (labelledVelocityPalette a₀) i stop R := by
  obtain ⟨code,hcode,hdata,hmass⟩ := Q.exists_selected_palette_family_with_loss hd hp hHE hH
    coding i hi stop hst ha₀ ha₁ hε hR hmesh K hK θ hbad (ENNReal.ofReal (1 / 16 : ℝ)) hbudget
  have hmass' : ENNReal.ofReal (15 / 16 : ℝ) ≤ Q.law
      (labelledSupport (Q.packetFamilyResidual i
        (Q.selectedCoarseFamily (Q.paletteActive i θ)
          (fun b => Q.normalizedPaletteCut b (p.lev b) stop (code b) a₀ a₁ R ε)))) := by
    convert hmass using 1
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num : (0 : ℝ) ≤ 1 / 16)]
    norm_num
  let F : PaletteFamily Q i stop a₁ (R / ε) θ := {
    coding := coding
    active := Q.paletteActive i θ
    code := code
    U := fun b => Q.normalizedPaletteCut b (p.lev b) stop (code b) a₀ a₁ R ε
    level := fun _ hb => hb.1
    weight_positive := fun _ hb => hb.2.1
    current_positive := fun _ hb => hb.2.2.1
    code_original := fun b hb => Q.coarse_code_eq_packetCoding coding
      (fun b => (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1) b (code b)
      (hcode b hb).1 (hcode b hb).2.1
    packet := fun b hb => (hcode b hb).1
    coarse_positive := fun b hb => (hcode b hb).2.1
    posterior := fun b hb => (hcode b hb).2.2
    measurable_U := fun b hb => (hdata b hb).1
    subset_coarse := fun b hb => (hdata b hb).2.1
    reference_floor := fun b hb => (hdata b hb).2.2.1
    joint_cap := fun b hb => (hdata b hb).2.2.2
    mass := (ENNReal.ofReal_le_ofReal (by norm_num : (1 / 2 : ℝ) ≤ 15 / 16)).trans hmass'
  }
  refine ⟨F,hmass',?_⟩
  intro b hb z hz
  have hh : z ∈ likelihoodGood Q.law (labelledSupport Q.residual)
      (finitePacketHistory p.lev p.γ p.F) (labelledVelocityPalette a₀) (p.lev b) stop R := hz.1.1
  simpa only [F.level b hb] using hh

/-- The same strong family without its additional original-bin certificate. -/
theorem exists_strong_palette_family {T : Type*} {d : ProblemData} {k : ℕ}
    {p : PathData (d.W k)} {m : ℕ} {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    (Q : PreparedAngularPath d k p m H u τ) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (coding : PacketCoding p (d.ν k)) (i : ℕ) (hi : i < m) (stop : ℕ) (hst : i ≤ stop)
    {a₀ a₁ ε R α : ℝ} (ha₀ : 0 < a₀) (ha₁ : 0 < a₁) (hε : 0 < ε) (hR : 0 ≤ R)
    (hmesh : a₀ * d.N k ^ (2 * δ₀ * d.L) ≤ a₁) (K : ℕ) (hK : (4 * p.κ + 6) ^ 2 ≤ (K : ℝ))
    (θ : ENNReal)
    (hbad : Q.law (labelledSupport Q.residual \ likelihoodGood Q.law (labelledSupport Q.residual)
      (finitePacketHistory p.lev p.γ p.F) (labelledVelocityPalette a₀) i stop R) ≤ ENNReal.ofReal α)
    (hbudget : ENNReal.ofReal α + (θ * ENNReal.ofReal (8 * p.κ) + ENNReal.ofReal (ε * K)) ≤
      ENNReal.ofReal (1 / 16 : ℝ)) :
    ∃ F : PaletteFamily Q i stop a₁ (R / ε) θ,
      ENNReal.ofReal (15 / 16 : ℝ) ≤ Q.law
        (labelledSupport (Q.packetFamilyResidual i (Q.selectedCoarseFamily F.active F.U))) := by
  obtain ⟨F,hfull,_⟩ := exists_strong_palette_family_with_original_likelihood Q hd hp hHE hH
    coding i hi stop hst ha₀ ha₁ hε hR hmesh K hK θ hbad hbudget
  exact ⟨F,hfull⟩

/-- The actual native threshold choices give the strong palette buffer
as soon as the genuine velocity window omits at most `1/128`. -/
theorem exists_default_palette_family_with_original_likelihood {T : Type*} {d : ProblemData} {k : ℕ}
    {p : PathData (d.W k)} {m : ℕ} {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    (Q : PreparedAngularPath d k p m H u τ) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (coding : PacketCoding p (d.ν k)) (i : ℕ) (hi : i < m) (stop : ℕ) (hst : i ≤ stop)
    {a₀ a₁ R : ℝ} (ha₀ : 0 < a₀) (ha₁ : 0 < a₁) (hR : 0 ≤ R)
    (hmesh : a₀ * d.N k ^ (2 * δ₀ * d.L) ≤ a₁)
    (hbad : Q.law (labelledSupport Q.residual \ likelihoodGood Q.law (labelledSupport Q.residual)
      (finitePacketHistory p.lev p.γ p.F) (labelledVelocityPalette a₀) i stop R) ≤
        ENNReal.ofReal (1 / 128 : ℝ)) :
    let K := ⌈(4 * p.κ + 6) ^ 2⌉₊
    ∃ F : PaletteFamily Q i stop a₁ (R / palettePruningThreshold K) (lightParentThreshold p.κ),
      ENNReal.ofReal (15 / 16 : ℝ) ≤ Q.law
        (labelledSupport (Q.packetFamilyResidual i (Q.selectedCoarseFamily F.active F.U))) ∧
      ∀ b, F.active b → F.U b ⊆
        likelihoodGood Q.law (labelledSupport Q.residual)
          (finitePacketHistory p.lev p.γ p.F) (labelledVelocityPalette a₀) i stop R := by
  let K := ⌈(4 * p.κ + 6) ^ 2⌉₊
  obtain ⟨hK,hKbound⟩ := native_palette_integer_bounds hp.1
  exact exists_strong_palette_family_with_original_likelihood Q hd hp hHE hH coding i hi stop hst ha₀ ha₁
    (palettePruningThreshold_pos hK) hR hmesh K (Nat.le_ceil _) (lightParentThreshold p.κ)
    hbad (native_palette_budget_choices (zero_lt_one.trans_le hp.1) hK)

theorem exists_default_palette_family {T : Type*} {d : ProblemData} {k : ℕ}
    {p : PathData (d.W k)} {m : ℕ} {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    (Q : PreparedAngularPath d k p m H u τ) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (coding : PacketCoding p (d.ν k)) (i : ℕ) (hi : i < m) (stop : ℕ) (hst : i ≤ stop)
    {a₀ a₁ R : ℝ} (ha₀ : 0 < a₀) (ha₁ : 0 < a₁) (hR : 0 ≤ R)
    (hmesh : a₀ * d.N k ^ (2 * δ₀ * d.L) ≤ a₁)
    (hbad : Q.law (labelledSupport Q.residual \ likelihoodGood Q.law (labelledSupport Q.residual)
      (finitePacketHistory p.lev p.γ p.F) (labelledVelocityPalette a₀) i stop R) ≤
        ENNReal.ofReal (1 / 128 : ℝ)) :
    let K := ⌈(4 * p.κ + 6) ^ 2⌉₊
    ∃ F : PaletteFamily Q i stop a₁ (R / palettePruningThreshold K) (lightParentThreshold p.κ),
      ENNReal.ofReal (15 / 16 : ℝ) ≤ Q.law
        (labelledSupport (Q.packetFamilyResidual i (Q.selectedCoarseFamily F.active F.U))) := by
  let K := ⌈(4 * p.κ + 6) ^ 2⌉₊
  obtain ⟨hK,hKbound⟩ := native_palette_integer_bounds hp.1
  exact exists_strong_palette_family Q hd hp hHE hH coding i hi stop hst ha₀ ha₁
    (palettePruningThreshold_pos hK) hR hmesh K (Nat.le_ceil _) (lightParentThreshold p.κ)
    hbad (native_palette_budget_choices (zero_lt_one.trans_le hp.1) hK)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.StrongPalette
