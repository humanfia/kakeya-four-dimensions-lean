import Submission.Obl.k4_physical_parent_potential_candidates.PhysicalNumerics
import Submission.Obl.k4_physical_parent_potential_candidates.DirectExit

/-!
# The palette-free restoration, as an interface

The packet of o288 controls velocities only through per-state strip breadth: it admits
velocity laws on conics that vary with the base state, with no common palette. Then no seven
fixed directions have fine witnesses on a base set of positive volume, so the sampled exit
of `cd` is out of reach and the direct exit must be produced. `RestorationOutput` is exactly
what the direct exit consumes. `RestorationAssertion` states that every heavy one-branch
physical group (the output of `PhysicalSource.exists_physical_heavy_group`) carries such a
quadratic test, with a loss polynomial in the source constant `K` and LINEAR in the group
width `a * w`. `completion_of_restoration` (in `Main.lean`) proves the frozen statement from
`RestorationAssertion`.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates

open MeasureTheory Set MvPolynomial PhysicalPotentialData

noncomputable section

/-- A quadratic test of width `Cr * (a * w)` on retained lines of the group, with the old
hidden derivative scale, and a regular hidden derivative on retained events which keep a
`1/Cr` fraction of the group's original mass. -/
def RestorationOutput (μ : Measure Ev) (Mcoef Cr Bv a w : ℝ) (T j : ℕ)
    (Gl : Set Ln) (G : Set Ev) : Prop :=
  ∃ (R : Po) (A' : Set Ln) (G' : Set Ev),
    R.totalDegree ≤ 2 ∧ (∀ e, |R.coeff e| ≤ Mcoef) ∧
    MeasurableSet A' ∧ A' ⊆ Gl ∧ MeasurableSet G' ∧ G' ⊆ G ∧ (∀ p ∈ G', p.1 ∈ A') ∧
    (∀ l ∈ A', ∀ t ∈ Icc ((j : ℝ) / (2:ℝ) ^ T) (((j : ℝ) + 1) / (2:ℝ) ^ T),
      |eval (xp l t) R| ≤ Cr * (a * w) ∧
      |eval (xp l t) (pderiv 3 R)| ≤ Cr * Bv ∧
      |eval (xp l t) (pderiv 3 (pderiv 3 R))| ≤ Cr * Bv ^ 2 / (a * w)) ∧
    (∀ p ∈ G', Bv / Cr ≤ |eval (xp p.1 p.2) (pderiv 3 R)|) ∧
    μ G ≤ ENNReal.ofReal Cr * μ G'

/-- **The palette-free restoration (open).** For a fixed density constant `Cden` and potential
degree `q`, there are a constant `C0` and exponents `E`, `Ecoef` such that every heavy one-branch physical group of
an actual old packet carries a quadratic test as in `RestorationOutput`, allowing inverse target thickness
in the coefficient budget, with loss
`C0 * K^E`. The hypotheses are exactly what the frozen statement and
`PhysicalSource.exists_physical_heavy_group` supply. -/
def RestorationAssertion : Prop :=
  ∀ Cden : ℝ, 1 ≤ Cden → ∀ q : ℕ, 2 ≤ q → ∃ (P E Ecoef : ℕ) (C0 : ℝ), 1 ≤ C0 ∧
    ∀ (Nk : ℝ) (Mp Dp Mr : ℕ) (κ : ℝ) (T j : ℕ) (rr Bv ζ d : ℝ) (c u : P2)
      (Qm : Matrix (Fin 2) (Fin 2) ℝ) (Rb P0 : Po) (A : Set Ln) (F H : Set Ev) (ex : Prop)
      (ν : Measure Ln) [IsFiniteMeasure ν]
      (source : PhysicalSource q ν Bv (δ Nk rr) ζ d T j c u P0 A F H),
      2 ≤ Nk → 1 ≤ κ → κ ≤ source.K → 0 < Bv → Bv ≤ Nk ^ Mr → Bv⁻¹ ≤ Nk ^ Mr →
      (2:ℝ) ^ T ≤ Nk ^ Mr → P0.totalDegree ≤ 2 → (∀ e, |P0.coeff e| ≤ Nk ^ Mr) →
      ch Nk Mp Dp κ T (j : ℝ) rr Bv Set.univ c u Qm Rb A F ex → j < 2 ^ T → 0 ≤ rr →
      0 ≤ d → d < 1 →
      source.S ⊆ A ×ˢ Icc ((j : ℝ) * ((2:ℝ) ^ T)⁻¹) ((j : ℝ) * ((2:ℝ) ^ T)⁻¹ + ((2:ℝ) ^ T)⁻¹) →
    ∀ (w : ℝ) (g : ℤ) (β : Bool) (G : Set Ev),
      0 < w → 2 * w ≤ 1 →
      countingResolution source.K (physicalPotentialLip q source.K) * ζ ≤ w →
      source.K ^ P * ζ ≤ w →
      MeasurableSet G →
      G ⊆ source.positiveEvents ∩ (source.interceptBin w) ⁻¹' {g} ∩
        parentBranch P0 ⁻¹' {β} →
      (∀ e ∈ G, e.1 ∈ source.groupLines w g) →
      (∀ L : Set ((Fin 3 → ℤ) × ℤ), ∀ n : P2, ∀ t : ℝ, ‖n‖ = 1 →
        ((ν.prod volume).restrict G)
          {e | source.fineState e ∈ L ∧ |inner ℝ n (v e.1) - t| ≤ source.K ^ (-100:ℝ)} ≤
          ENNReal.ofReal ((1:ℝ) / 1000000) *
            ((ν.prod volume).restrict G) {e | source.fineState e ∈ L}) →
      (∀ U : Set P3, MeasurableSet U →
        ((ν.prod volume).restrict G) {e | packetBase T j c u e ∈ U} ≤
          ENNReal.ofReal (source.K * (2 * w) ^ d) *
            (ENNReal.ofReal (((2:ℝ) ^ T)⁻¹) * ν A) * volume U) →
      (∀ U : Set P3, MeasurableSet U →
        ((ν.prod volume).restrict G) {e | packetBase T j c u e ∈ U} ≤
          ENNReal.ofReal (Cden * source.K ^ 209) * ((ν.prod volume).restrict G) univ *
            volume U) →
      0 < (ν.prod volume) G →
      RestorationOutput (ν.prod volume)
        (C0 * (source.K * Nk ^ (Mp + Mr + 1) * (1 + (δ Nk rr * w)⁻¹)) ^ Ecoef) (C0 * source.K ^ E)
        Bv (δ Nk rr) w T j (source.groupLines w g) G

end

end Submission.Obl.k4_physical_parent_potential_candidates
