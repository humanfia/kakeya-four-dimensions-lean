-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceBudgets

/-!
# The true inputs of a source stage

`SourceData.Inputs` lists the inputs of `SourceData.Facts` that are NOT numerical: the palette,
the prepared set and its floors, the determinant floors and tracking coefficients of the model
labels, the pure/joint/palette caps `EH2` and the per-label velocity caps. Everything else in
`Facts` is produced from the schedule by `SourceData.facts_of_inputs`.

Written by x0891 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set MvPolynomial

noncomputable section

namespace SourceData

variable {W : ℕ} {p : PathData W} (D : SourceData p)

/-- The non-numerical inputs of one source stage. -/
structure Inputs (n m : ℕ) (d₁ ℓ S unit Nk L τ : ℝ)
    (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ) (H : Fin W → Set Incidence) : Prop where
  π_prob : IsProbabilityMeasure D.π
  S_meas : MeasurableSet D.S
  S_res : D.S ⊆ H D.w₀
  S_open : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀)
  S_term : D.S ⊆ TerminalInc W p.C m p.lev p.world p.counted D.w₀
  S_end : ∀ z ∈ D.S, ∀ b : Fin p.C, z.2 ≠ (p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b) ∧
    z.2 ≠ ((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b)
  parent_floor : ENNReal.ofReal τ * ((ν D.w₀).prod volume) (p.packet D.parent) ≤
    ((ν D.w₀).prod volume) (D.S ∩ p.counted D.parent)
  label_floor : ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 → ∀ i : Fin (p.activeCount D.Hm (D.depth s)),
    ENNReal.ofReal τ * ((ν D.w₀).prod volume) (p.packet (D.old s i)) ≤
      ((ν D.w₀).prod volume) (D.S ∩ p.counted (D.old s i))
  det : ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 → ∀ i : Fin (p.activeCount D.Hm (D.depth s)),
    (Nk ^ (unit * L)) ^ (-ℓ * s) / D.K ≤
      |((D.q₀ / (((2 : ℝ) ^ p.T (p.lev (D.old s i)))⁻¹)) •
        (D.D₀⁻¹ * p.frame (D.old s i))).det|
  track : ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 → ∀ i : Fin (p.activeCount D.Hm (D.depth s)),
    (∀ e, |D.c s i e| ≤ D.K) ∧
    (∀ l ∈ p.assigned (D.old s i), ∀ t ∈ IS (D.relT s) (D.relBin s i),
      |(exS (D.stage Nk L unit ν B).b l t) 1 - D.c s i 0 - t * D.c s i 1| ≤
        D.K * (2 : ℝ) ^ (-(D.relT s : ℤ)) ∧
      |(exS (D.stage Nk L unit ν B).b l t) 2 - D.c s i 2 - t * D.c s i 3 -
          D.c s i 4 * (exS (D.stage Nk L unit ν B).b l t) 1| ≤
        D.K * (2 : ℝ) ^ (-(D.relT s : ℤ)) * (Nk ^ (unit * L)) ^ (-ℓ * s) ∧
      |(D.stage Nk L unit ν B).b l 4 - D.c s i 3 - D.c s i 4 * (D.stage Nk L unit ν B).b l 3| ≤
        D.K * (Nk ^ (unit * L)) ^ (-ℓ * s))
  vel : ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 → ∀ (i : Fin (p.activeCount D.Hm (D.depth s)))
      (v : ℝ) (v₀ : ℤ), (n : ℝ)⁻¹ ≤ v → v ≤ n →
    (D.stage Nk L unit ν B).μ {z | z.1 ∈ p.assigned (D.old s i) ∧
        z.2 ∈ IS (D.relT s) (D.relBin s i) ∧
        ⌊(D.stage Nk L unit ν B).b z.1 3 / ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀} ≤
      ENNReal.ofReal (D.K * (2 : ℝ) ^ (-(D.relT s : ℤ))) *
        (D.stage Nk L unit ν B).ν (p.assigned (D.old s i)) *
        D.π {w : ℝ | ⌊w / ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀}
  eh2 : EH2 d₁ S (D.stage Nk L unit ν B) n

end SourceData

section Path

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- Every label of a valid path has positive full prior. -/
theorem prior_pos_of_valid (hNk : 0 < Nk) (b : Fin p.C) :
    0 < ν (p.world b) (p.assigned b) := by
  have hsat := (hp.saturation b).1
  have hdet0 : (p.frame b).det ≠ 0 := (hp.chart b).1
  have hκ := hp.one_le_slack
  have hpos : 0 < ((ν (p.world b)).prod volume) (p.counted b) := by
    refine lt_of_lt_of_le ?_ hsat
    apply ENNReal.ofReal_pos.mpr
    apply div_pos (mul_pos (Real.rpow_pos_of_pos hNk _) (abs_pos.mpr hdet0))
    exact mul_pos (by positivity) (by linarith)
  have hsub : p.counted b ⊆ p.packet b := fun z hz =>
    ⟨(hp.counted_support b z hz).2.1, (hp.counted_support b z hz).2.2.1⟩
  have hpk := lt_of_lt_of_le hpos (measure_mono hsub)
  rw [PathData.packet, Measure.prod_prod] at hpk
  exact pos_of_ne_zero (fun h0 => by simp [h0] at hpk)

end Path

end

end Submission.Obl.k4_finite_affine_parent_sources
