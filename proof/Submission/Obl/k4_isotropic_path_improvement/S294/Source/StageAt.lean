-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.StageAt, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- The per-sample statement of `StagesProducer` (session x1088).

`StageAt … k σS` is the body of `Source.StagesProducer` after `∃ σS, 0 < σS ∧ ∀ᶠ k,`: everything
the outer assembly proves at one sample `k` for paths of factor exponent `σS`. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Stages

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open MeasureTheory Filter
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

noncomputable section

/-- **One sample of `StagesProducer`.** -/
def StageAt (tune : Tuning) (d₁ κ₁ : ℝ) (Ep : ℕ) (precision loss e0 : ℝ) (m : ℕ) (s : ℕ → ℝ)
    (δ₀ : ℝ) (C : ℕ) (indices : Finset ℕ) (d : ProblemData) (Mp Dp : ℕ) (budget : ℝ) (k : ℕ)
    (σS : ℝ) : Prop :=
  ∀ p : PathData (d.W k),
    p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σS →
    ∀ H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ), (∀ w, MeasurableSet (H w)) →
    (∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b}) →
    ENNReal.ofReal (p.κ⁻¹ / 2) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (H w) →
    ∀ (Qp : PreparedAngularPath d k p m H (fun _ : Fin 1 => d.η * d.L) (tauOf tune δ₀ d.L budget)),
    Qp.uniformPureBounds (tauOf tune δ₀ d.L budget) →
    ENNReal.ofReal (11 * p.κ⁻¹ / 32) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Qp.residual w) →
    ∀ i ∈ indices,
    ∀ Fp : PaletteFamily Qp i (i + C)
        (d.N k ^ (-paletteExpOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) d.L))
        (d.N k ^ entropyOf C m (ueOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) δ₀ d.L) /
          palettePruningThreshold ⌈(4 * p.κ + 6) ^ 2⌉₊)
        (lightParentThreshold p.κ),
    ∀ Rp : BroadResidual Fp
        (d.N k ^ (-(ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) * d.L)))
        (2 * ((d.N k ^ budget) ^ 1)⁻¹),
    ENNReal.ofReal (71 * p.κ⁻¹ / 512) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Rp.residual w) →
    (∀ b, Fp.active b → Fp.U b ⊆
      likelihoodGood Qp.law (labelledSupport Qp.residual)
        (finitePacketHistory p.lev p.γ p.F)
        (labelledVelocityPalette
          (d.N k ^ (-ueOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) δ₀ d.L)))
        i (i + C)
        (d.N k ^ entropyOf C m (ueOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) δ₀ d.L))) →
    -- the root surviving family, of some positive density (x1096 11:05Z)
    ∃ (density : ℝ) (E : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)), 0 < density ∧
      (∀ w, E w ⊆ Rp.residual w) ∧
      ENNReal.ofReal density + ENNReal.ofReal density ≤
        ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (E w) ∧
      -- the child stage
      ∀ b : Fin p.C,
        p.lev b = i + childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m →
        Fp.active (p.par^[childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m] b) →
        d.ν k (p.γ b) (p.A b) ≠ 0 →
        ENNReal.ofReal density *
            (d.ν k (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹)) ≤
          ((d.ν k (p.γ b)).prod volume) (E (p.γ b) ∩ p.F b) →
        let a := p.par^[childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m] b
        let gain := gainOf tune κ₁ d₁ Ep precision loss e0
        let K := KOf Ep loss gain (d.N k) d.L
        let θ := thetaOf Ep precision loss gain (d.N k) d.L (p.r i) (p.r (p.lev b)) (p.T i)
          (p.T (p.lev b))
        let ε := epsOf Ep precision loss gain (d.N k) d.L (p.r i) (p.r (p.lev b)) (p.T i)
          (p.T (p.lev b))
        let pv := pvOf Ep precision loss gain (d.N k) d.L (p.r i) (p.r (p.lev b)) (p.T i)
          (p.T (p.lev b))
        let aA := O204.Split.δ (d.N k) (p.r i)
        let q := ((2 : ℝ) ^ p.T i)⁻¹
        let zb := O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b)
        let Xnb := fun z => O204.Tangent.packetSignal (p.R a) z / O204.Split.δ (d.N k) (p.r (p.lev b))
        let ref := ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * d.ν k (p.γ b) (p.A b)
        ∃ (Se Er bad : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (st : ((ℕ × (Fin 6 → ℝ)) × ℝ) → ℕ)
          (G : ℕ → Fin 3 → ℝ) (pal : Measure (Fin 2 → ℤ)),
          Se ⊆ E (p.γ b) ∩ p.F b ∧ Se ⊆ Er ∧
          ref / ENNReal.ofReal K ≤ (((d.ν k (p.γ b)).prod volume).restrict Se) Set.univ ∧
          CapClauses K ε d₁ (hRelOf (p.T i) (p.T (p.lev b)))
            (aRelOf (d.N k) (p.r i) (p.r (p.lev b))) ref (d.ν k (p.γ b)) zb Xnb Se ∧
          StateClauses K ε pv (d.ν k (p.γ b)) zb Xnb Se st pal ∧
          RowClauses K θ aA q (p.R a) zb Se Er st G ∧
          QualClauses (qualDegree κ₁) K θ aA q (p.j b) ((2 : ℝ) ^ p.T (p.lev b))⁻¹
            (d.ν k (p.γ b)) Se Er bad st G

/-- `StagesProducer` from its samples. -/
theorem stagesProducer_of_stageAt (tune : Tuning)
    (h : O204.Split.mk →
      ∀ (d₁ κ₁ ρ : ℝ) (Ep : ℕ) (precision loss e0 : ℝ),
      0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 → 0 < ρ → d₁ + ρ < 1 → 1 ≤ precision → 0 < loss →
      loss ≤ 1 → 0 < e0 →
      ∀ (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ) (C target : ℕ) (indices : Finset ℕ),
      Parent.grid κ₁ ρ m s (gainOf tune κ₁ d₁ Ep precision loss e0) δ₀
          (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) / 8) →
      δ₀ ≤ tolOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) →
      4 * δ₀ * (m : ℝ) ≤ κ₁ → 8 ≤ m →
      8 ≤ gridFineOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) * m →
      target < m → s target = 1 / 2 → 2 * (target + 1) = m → 1 ≤ C →
      windowOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) * m ≤ C →
      (C : ℝ) ≤ windowOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) * m + 1 →
      C + 1 ≤ target → indices = Finset.range (target + 1 - C) →
      ∀ (d : ProblemData), d.Valid →
      (∀ r : ℝ, 0 ≤ r → r ≤ d.L → |d.f r - d.f 0 - d₁ * r| ≤ δ₀ * d.L) →
      ∀ (Mp Dp : ℕ) (budget : ℝ), 0 < budget → budget ≤ 1 →
      ∃ σS : ℝ, 0 < σS ∧ ∀ᶠ k in atTop,
        StageAt tune d₁ κ₁ Ep precision loss e0 m s δ₀ C indices d Mp Dp budget k σS) :
    StagesProducer tune := h

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
