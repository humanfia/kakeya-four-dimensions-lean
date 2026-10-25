-- Adapted from this LOT tree, o232/x0812 f7bed5fb, Submission/Obl/k4_finite_positive_prepared_models/SourceGmVelCaps.lean; namespace renamed.
import Submission.Obl.k4_finite_affine_parent_sources.SourceBuildNumerators
import Submission.Obl.k4_finite_affine_parent_sources.SourceVelCaps

/-!
# Velocity caps of the models on the prepared set: the statement

`GmVelCaps`: a source model `D` over a subset of a retained set `S2 ⊆ S1` of the window parent
has its per-label velocity caps, from

* the window numerator `hwin` of `S1` per end history (level `e`) and original planar code
  (`SourceBuildWindow.window_parent_original`),
* the palette domination `hdom` of the parent's reference law (x0807's
  `PathData.Valid.source_parent_palette`, last conjunct),
* `end_bin_numerator` (model bins of `S2 ∩ {end = h}`), `history_eq_of_counted` (a counted
  terminal incidence of an end label `h` off block endpoints has end history `h`), and
  x0891's `SourceData.velCaps_of_end_numerator`.

Written by x0812 for o232 (statement; proof to be supplied).
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_finite_forest_width_selection

noncomputable section

/-- **Velocity caps of the models on the prepared set** (statement). -/
def GmVelCaps : Prop :=
  ∀ {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ},
    p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ →
    (∀ w, IsProbabilityMeasure (ν w)) → (∀ w, E w ⊆ univ ×ˢ Icc (0 : ℝ) 1) →
    (∀ w, MeasurableSet (E w)) → 1 < Nk →
    ∀ (D : SourceData p) (n : ℕ) (unit : ℝ) (e : ℕ) (δv Cw : ℝ)
      (S0w S1 S2 : Set Incidence) {blur : ℝ},
    D.D₀ = MajorFrame.frame (p.frame D.parent) →
    1 ≤ Nk ^ (unit * L) →
    e < m → (∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 → D.depth s ≤ e) → (∀ s, D.i₀ ≤ D.depth s) →
    MeasurableSet S0w → S0w ⊆ E D.w₀ →
    S1 ⊆ S0w ∩ {x | p.history m D.i₀ (D.w₀, x) = some D.parent} →
    0 ≤ Cw → 4 * Cw ≤ D.K →
    (∀ (h : Option (Fin p.C)) (z : Fin 2 → ℤ),
      ((ν D.w₀).prod volume).real (S1 ∩
        {x | p.history m e (D.w₀, x) = h ∧ worldBin δv (D.w₀, x) = z}) ≤
      Cw * ((ν D.w₀).prod volume).real (S0w ∩ {x | p.history m D.i₀ (D.w₀, x) = some D.parent} ∩
          {x | p.history m e (D.w₀, x) = h}) *
        (((ν D.w₀).prod volume).real (S0w ∩ {x | p.history m D.i₀ (D.w₀, x) = some D.parent} ∩
            {x | worldBin δv (D.w₀, x) = z}) /
          ((ν D.w₀).prod volume).real (S0w ∩
            {x | p.history m D.i₀ (D.w₀, x) = some D.parent}))) →
    ((ν D.w₀).prod volume) (S0w ∩ {x | p.history m D.i₀ (D.w₀, x) = some D.parent}) ≠ 0 →
    (∀ (ρ : Measure Incidence), ρ ≤ nuE (((ν D.w₀).prod volume).restrict (E D.w₀))
        (S0w ∩ {x | p.history m D.i₀ (D.w₀, x) = some D.parent}) →
      ∀ (P : Set Incidence) (C : ENNReal) (width : ℝ), 2 * blur ≤ width →
      (∀ z : Fin 2 → ℤ, ρ (P ∩ {x | worldBin δv (D.w₀, x) = z}) ≤
        C * nuE (((ν D.w₀).prod volume).restrict (E D.w₀))
          (S0w ∩ {x | p.history m D.i₀ (D.w₀, x) = some D.parent})
          {x | worldBin δv (D.w₀, x) = z}) →
      ∀ e' : ℤ, ρ (P ∩ {x | ⌊(labelFrame p D.parent (B D.w₀)
          (δ Nk (p.r D.i₀))).eb x.1 3 / width⌋ = e'}) ≤
        4 * C * D.π {w | ⌊w / width⌋ = e'}) →
    2 * blur ≤ (Nk ^ (unit * L)) ^ (-(n : ℝ)) →
    MeasurableSet S2 → S2 ⊆ S1 → D.S ⊆ S2 →
    D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀) →
    D.S ⊆ TerminalInc W p.C m p.lev p.world p.counted D.w₀ →
    (∀ z ∈ D.S, ∀ b : Fin p.C, z.2 ≠ (p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b) ∧
      z.2 ≠ ((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b)) →
    D.VelCaps n unit Nk L ν B

end

end Submission.Obl.k4_finite_affine_parent_sources
