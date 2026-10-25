-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.StageGlue, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.StageAt
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleFinal

/-!
# From the samples to `StageAt` (session x1082)

`StageAt … k σS` (x1088) states, at one sample `k`, the stages at the literal scalars with `let`
bindings at the child level `p.lev b`. `SampleKey … p i Rp` is the conclusion of
`Source.SampleFinal.sample_final` at the literal sample scalars (child offset
`c = childOffset κ₁ Ep precision gain m`, `K = KOf`, `θ = thetaOf`, `ε = epsOf`, `pv = pvOf` at the
levels `i` and `i + c`, `aA = δ(N, r i)`, `q = 2^-T i`, `M = qualDegree κ₁`):

* `stageAt_of_keys`: `SampleKey` at every sample of `StageAt` gives `StageAt`;
* `sampleKey_of_final`: `sample_final`'s conclusion at the literal scalars is `SampleKey`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open MeasureTheory Filter
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

noncomputable section

/-- The conclusion of one sample at the literal scalars. -/
def SampleKey (tune : Tuning) (d₁ κ₁ : ℝ) (Ep : ℕ) (precision loss e0 : ℝ) (m : ℕ)
    (d : ProblemData) (k : ℕ) (p : PathData (d.W k)) {H : Fin (d.W k) → Set ParentSource.Ev} {u : Fin 1 → ℝ}
    {τ : ℝ} {Qp : PreparedAngularPath d k p m H u τ} (i : ℕ) {stop : ℕ} {meshF envF : ℝ}
    {θF : ENNReal} {Fp : PaletteFamily Qp i stop meshF envF θF} {rF frF : ℝ}
    (Rp : BroadResidual Fp rF frF) : Prop :=
  ∃ (density : ℝ) (E : Fin (d.W k) → Set ParentSource.Ev), 0 < density ∧
    (∀ w, E w ⊆ Rp.residual w) ∧
    ENNReal.ofReal density + ENNReal.ofReal density ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (E w) ∧
    ∀ b : Fin p.C,
      p.lev b = i + childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m →
      Fp.active (p.par^[childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m] b) →
      d.ν k (p.γ b) (p.A b) ≠ 0 →
      ENNReal.ofReal density *
          (d.ν k (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹)) ≤
        ((d.ν k (p.γ b)).prod volume) (E (p.γ b) ∩ p.F b) →
      ∃ (Se Er bad : Set ParentSource.Ev) (st : ParentSource.Ev → ℕ) (G : ℕ → Fin 3 → ℝ) (pal : Measure (Fin 2 → ℤ)),
        Se ⊆ E (p.γ b) ∩ p.F b ∧ Se ⊆ Er ∧
        (ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * d.ν k (p.γ b) (p.A b)) /
            ENNReal.ofReal (KOf Ep loss (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L) ≤
          (((d.ν k (p.γ b)).prod volume).restrict Se) Set.univ ∧
        CapClauses (KOf Ep loss (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L)
          (epsOf Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L
            (p.r i) (p.r (i + childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m))
            (p.T i) (p.T (i + childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m)))
          d₁
          (hRelOf (p.T i)
            (p.T (i + childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m)))
          (aRelOf (d.N k) (p.r i)
            (p.r (i + childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m)))
          (ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * d.ν k (p.γ b) (p.A b)) (d.ν k (p.γ b))
          (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b))
          (fun z => O204.Tangent.packetSignal
              (p.R (p.par^[childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m] b))
              z / O204.Split.δ (d.N k) (p.r (p.lev b))) Se ∧
        StateClauses (KOf Ep loss (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L)
          (epsOf Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L
            (p.r i) (p.r (i + childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m))
            (p.T i) (p.T (i + childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m)))
          (pvOf Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L
            (p.r i) (p.r (i + childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m))
            (p.T i) (p.T (i + childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m)))
          (d.ν k (p.γ b))
          (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b))
          (fun z => O204.Tangent.packetSignal
              (p.R (p.par^[childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m] b))
              z / O204.Split.δ (d.N k) (p.r (p.lev b))) Se st pal ∧
        RowClauses (KOf Ep loss (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L)
          (thetaOf Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L
            (p.r i) (p.r (i + childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m))
            (p.T i) (p.T (i + childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m)))
          (O204.Split.δ (d.N k) (p.r i)) ((2 : ℝ) ^ p.T i)⁻¹
          (p.R (p.par^[childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m] b))
          (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b)) Se Er st G ∧
        QualClauses (qualDegree κ₁) (KOf Ep loss (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L)
          (thetaOf Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) (d.N k) d.L
            (p.r i) (p.r (i + childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m))
            (p.T i) (p.T (i + childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m)))
          (O204.Split.δ (d.N k) (p.r i)) ((2 : ℝ) ^ p.T i)⁻¹ (p.j b)
          ((2 : ℝ) ^ p.T (p.lev b))⁻¹ (d.ν k (p.γ b)) Se Er bad st G

/-- **`StageAt` from the keys of its samples.** -/
theorem stageAt_of_keys (tune : Tuning) {d₁ κ₁ : ℝ} {Ep : ℕ} {precision loss e0 : ℝ} {m : ℕ}
    {s : ℕ → ℝ} {δ₀ : ℝ} {C : ℕ} {indices : Finset ℕ} {d : ProblemData} {Mp Dp : ℕ}
    {budget : ℝ} {k : ℕ} {σS : ℝ}
    (h : ∀ p : PathData (d.W k),
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
          (d.N k ^ (-paletteExpOf tune κ₁ d₁ Ep precision loss
            (gainOf tune κ₁ d₁ Ep precision loss e0) d.L))
          (d.N k ^ entropyOf C m (ueOf tune κ₁ d₁ Ep precision loss
              (gainOf tune κ₁ d₁ Ep precision loss e0) δ₀ d.L) /
            palettePruningThreshold ⌈(4 * p.κ + 6) ^ 2⌉₊)
          (lightParentThreshold p.κ),
      ∀ Rp : BroadResidual Fp
          (d.N k ^ (-(ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) *
            d.L)))
          (2 * ((d.N k ^ budget) ^ 1)⁻¹),
      ENNReal.ofReal (71 * p.κ⁻¹ / 512) ≤
        ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Rp.residual w) →
      (∀ b, Fp.active b → Fp.U b ⊆
        likelihoodGood Qp.law (labelledSupport Qp.residual)
          (finitePacketHistory p.lev p.γ p.F)
          (labelledVelocityPalette
            (d.N k ^ (-ueOf tune κ₁ d₁ Ep precision loss
              (gainOf tune κ₁ d₁ Ep precision loss e0) δ₀ d.L)))
          i (i + C)
          (d.N k ^ entropyOf C m (ueOf tune κ₁ d₁ Ep precision loss
            (gainOf tune κ₁ d₁ Ep precision loss e0) δ₀ d.L))) →
      SampleKey tune d₁ κ₁ Ep precision loss e0 m d k p i Rp) :
    StageAt tune d₁ κ₁ Ep precision loss e0 m s δ₀ C indices d Mp Dp budget k σS := by
  intro p hp H hHmeas hH hmass Qp hpure hres i hi Fp Rp hRmass hgood
  obtain ⟨density, E, hdens, hEres, hEmass, hchild⟩ :=
    h p hp H hHmeas hH hmass Qp hpure hres i hi Fp Rp hRmass hgood
  refine ⟨density, E, hdens, hEres, hEmass, ?_⟩
  intro b hb hact hA hdense
  have := hchild b hb hact hA hdense
  simp only [hb] at this ⊢
  exact this

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
