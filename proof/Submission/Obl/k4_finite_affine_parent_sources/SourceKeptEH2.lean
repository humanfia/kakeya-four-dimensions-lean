-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceSelectionEH2
import Submission.Obl.k4_finite_affine_parent_sources.SourceSelectionSample

/-!
# `EH2` of a source stage on kept states: the statement

`KeptEH2` is the `EH2` assembly of a source stage `D` whose prepared set lies in the kept part
of a larger prepared set `S2`:

* palette bins: the hypothesis `hpal` (x0807's palette);
* pure cells, both alternatives: `source_pure_cell` on `D` (density mask of `S2` at a depth
  grid covering every composed depth `p.r i₀ + u L s`, `s ∈ [0, T]`);
* joint cells, true signal, at every `u ∈ [1/T, T]`, `t ∈ [0, T]`: `source_joint_cell` with the
  end-state numerator `hnum` and the original cell masses of `S2` from `cell_original_le` applied
  to `{D with S := S2}` and `source_pure_cell` for it (constant `81 Cn/δs Kpure ≤ K₀`);
* joint cells, raw hidden coordinate: `RawUpgrade n T N₀` with `N := N^(uL)`, `K := K₀`,
  `d := d₁`, `μ := D.stage.μ`, `x := exS b`, `C :=` the velocity bin, `β := π(bin)`; its a.e.
  bounds are `stage_good_bounds` (`7κ ≤ K₀`); cells convert by `candidate_base_mesh_eq`.

Written by x0812 for o232 (statement; proof to be supplied).
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_stable_native_signal_oscillation

noncomputable section

/-- The pure-cell constant of a source stage on a density mask (`source_pure_cell`). -/
def pureConst (κ Nk hd τd δ₀ L : ℝ) : ℝ :=
  κ * (4 * Nk ^ hd + 2) * Nk ^ (τd + 2 * (δ₀ * L)) * (16 * (1 + κ ^ 2))

/-- **`EH2` of a source stage on kept states** (statement). -/
def KeptEH2 : Prop :=
  ∀ {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ d₁ S : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ},
    p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ →
    (∀ w, IsProbabilityMeasure (ν w)) → (∀ w, E w ⊆ univ ×ˢ Icc (0 : ℝ) 1) →
    1 < Nk → 0 < L → 0 ≤ d₁ → d₁ ≤ 1 →
    ∀ (D : SourceData p) (n : ℕ) (unit T N₀ : ℝ), 1 ≤ n → 0 < unit → (n : ℝ) < T →
    RawUpgrade n T N₀ →
    0 < B D.w₀ → D.D₀ = MajorFrame.frame (p.frame D.parent) → MeasurableSet D.S →
    IsProbabilityMeasure D.π →
    -- the palette
    (∀ v : ℝ, (n : ℝ)⁻¹ ≤ v → v ≤ n → ∀ a : ℤ,
      D.π {w : ℝ | ⌊w / ((Nk ^ (unit * L)) ^ (-v))⌋ = a} ≤
        ENNReal.ofReal (D.K * (Nk ^ (unit * L)) ^ (-S * v))) →
    -- the larger prepared set and its density mask
    ∀ (S2 : Set Incidence), MeasurableSet S2 → S2 ⊆ p.counted D.parent →
    ∀ {G' : ℕ} (g : ℝ → Observation → ENNReal) (r : Fin G' → ℝ),
    (∀ j, Measurable (g (r j))) →
    (∀ j, (((ν D.w₀).prod volume).restrict (E D.w₀)).map (obs (B D.w₀) (δ Nk (r j))) =
      (volume.prod Measure.count).withDensity (g (r j))) →
    ∀ (τd hd : ℝ), 0 ≤ hd → S2 ⊆ E D.w₀ ∩ densMask g (B D.w₀) Nk τd f r →
    (∀ s : ℝ, 0 ≤ s → s ≤ T → ∃ j, p.r D.i₀ + unit * L * s ≤ r j ∧
      r j ≤ p.r D.i₀ + unit * L * s + hd ∧
      f (p.r D.i₀) + d₁ * (r j - p.r D.i₀) - 2 * (δ₀ * L) ≤ f (r j)) →
    -- the kept states
    ∀ {Hs : Type} [Fintype Hs] [MeasurableSpace Hs] [MeasurableSingletonClass Hs]
      (endL : Incidence → Hs), Measurable endL →
    ∀ (w : Hs → ENNReal) (δs : ENNReal), δs ≠ 0 → δs ≠ ⊤ →
    ∀ (mesh : ℝ), 0 < mesh → mesh ≤ (Nk ^ (unit * L)) ^ (-T) →
    D.S ⊆ S2 ∩ keptSet (((ν D.w₀).prod volume).restrict S2) endL
      (stateCode (frameBase (D.frame Nk B)) (frameSignal (D.frame Nk B)
        (D.stage Nk L unit ν B).P) mesh) w δs →
    -- the end-state numerator
    ∀ (Cn : ENNReal), (∀ v : ℝ, (n : ℝ)⁻¹ ≤ v → v ≤ n → ∀ (v₀ : ℤ) (h : Hs),
      ((ν D.w₀).prod volume) (S2 ∩ ({x | endL x = h} ∩
        {x | ⌊(D.frame Nk B).eb x.1 3 / ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀})) ≤
        Cn * w h * D.π {w : ℝ | ⌊w / ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀}) →
    -- the numerics
    ∀ (K₀ : ℝ), 1 ≤ K₀ → 7 * p.κ ≤ K₀ → K₀ ≤ Nk ^ (unit * L) → N₀ ≤ Nk ^ (unit * L) →
    pureConst p.κ Nk hd τd δ₀ L ≤ K₀ →
    81 * (Cn / δs) * ENNReal.ofReal (pureConst p.κ Nk hd τd δ₀ L) ≤ ENNReal.ofReal K₀ →
    400 * K₀ ^ 2 ≤ D.K →
    EH2 d₁ S (D.stage Nk L unit ν B) n

end

end Submission.Obl.k4_finite_affine_parent_sources
