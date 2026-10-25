-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativeDichotomy, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativeDichotomy.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativeDichotomy.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativeDichotomy.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PaletteCertificate

/-! Actual original-law residuals on both sides of the intrinsic narrowness
alternative. Every retained incidence has an old fine packet witness. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips
open scoped ENNReal BigOperators

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A : ℝ} {θ : ENNReal}

structure NarrowResidual (F : PaletteFamily Q i stop a A θ) (r fraction : ℝ) where
  prediction : NarrowPredictionFamily Q F.code stop F.U r fraction
  residual : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)
  measurable : ∀ w, MeasurableSet (residual w)
  subset_H : ∀ w, residual w ⊆ H w
  mass : ENNReal.ofReal ((p.κ⁻¹ / 8) * (fraction * (1 / 8))) ≤
    ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (residual w)
  witness : ∀ w x, x ∈ residual w → ∃ b, p.lev b = i ∧ p.γ b = w ∧ x ∈ p.F b ∧ ∃ f,
    p.lev f = stop ∧ p.γ f = w ∧ x ∈ p.packetWitness m stop w f ∧
    F.coding.code f ∈ Q.intrinsicNarrowStates F.code stop F.U r fraction b ∧ F.active b ∧
    p.normalizedVelocity b x ∈ affineStrip (prediction.normal b (F.coding.code f))
      (prediction.offset b (F.coding.code f)) r

structure BroadResidual (F : PaletteFamily Q i stop a A θ) (r fraction : ℝ) where
  residual : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)
  measurable : ∀ w, MeasurableSet (residual w)
  subset_H : ∀ w, residual w ⊆ H w
  mass : ENNReal.ofReal ((p.κ⁻¹ / 8) * ((1 / 2) / 2)) ≤
    ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (residual w)
  witness : ∀ w x, x ∈ residual w → ∃ b, p.lev b = i ∧ p.γ b = w ∧ x ∈ p.F b ∧
    F.active b ∧ (p.γ b, x) ∈ F.U b ∧ ∃ f,
      p.lev f = stop ∧ p.γ f = w ∧ x ∈ p.packetWitness m stop w f ∧
      F.coding.code f ∉ Q.intrinsicNarrowStates F.code stop F.U r fraction b ∧
      F.coding.code f ∉ fineRetentionFailures (Q.coarseLaw (p.lev b) (F.code b))
        (finitePacketHistory p.lev p.γ p.F stop) (F.U b) (ENNReal.ofReal (1 / 8 : ℝ))

variable (F : PaletteFamily Q i stop a A θ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

theorem PaletteFamily.broad_or_narrow (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (hi : i < m) (hstop : stop < m) (r fraction : ℝ) (hfraction : 0 ≤ fraction) :
    Nonempty (NarrowResidual F r fraction) ∨ Nonempty (BroadResidual F r fraction) := by
  classical
  let Bad := Q.intrinsicNarrowStates F.code stop F.U r fraction
  let D := labelledSupport (Q.packetFamilyResidual i (Q.badHistoryFamily F.active F.code stop Bad))
  have hcode (b : Fin p.C) (hb : F.active b) :=
    And.intro (F.packet b hb) (And.intro (F.coarse_positive b hb) (F.posterior b hb))
  by_cases hn : ENNReal.ofReal (1 / 8 : ℝ) ≤ Q.law D
  · obtain ⟨P⟩ := Q.exists_narrowPredictionFamily F.code stop F.U r fraction
    obtain ⟨hJ, hJH, hmass, _⟩ := P.residual_original_floor hd hp hHE i F.active
      (fun b hb => ⟨F.packet b hb, F.posterior b hb⟩) F.measurable_U F.subset_coarse hfraction hn
    have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
      (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
    refine Or.inl ⟨{
      prediction := P
      residual := F.coding.cleanResidual (P.residual F.active i)
      measurable := F.coding.cleanResidual_measurable hF _ hJ
      subset_H := fun w _ hx => hJH w hx.1.1
      mass := ?_
      witness := ?_
    }⟩
    · simpa only [F.coding.cleanResidual_original_mass hp] using hmass
    · exact P.cleaned_fine_packet_cover hp F.coding hstop F.active i
        (fun w x hx => by
          obtain ⟨t, ht, htw, hxt⟩ := hH w hx
          exact ⟨t, ⟨ht, htw⟩, hxt⟩) hJH
        (fun b hb z hz => (F.packet b hb z (F.subset_coarse b hb hz)).2)
  · have hbad : Q.law D ≤ ENNReal.ofReal ((1 / 2 : ℝ) / 4) := by
      convert (le_of_not_ge hn) using 1 <;> norm_num
    obtain ⟨J, hJ, hJH, hmass, hwitness⟩ := Q.broad_residual_of_small_narrow hd hp hHE hH
      F.coding stop hstop i hi F.active F.code hcode F.U F.measurable_U F.subset_coarse
      (mass := 1 / 2) (fraction := fraction) (r := r) (α := 1 / 8)
      (by norm_num) (by norm_num) (by norm_num) F.mass hbad
    exact Or.inr ⟨⟨J, hJ, hJH, hmass, hwitness⟩⟩

/-- The narrow predictors are heavy for the unchanged native velocity
posterior. This is the input used by an original-reference strip packing. -/
theorem NarrowResidual.heavy_strip {F : PaletteFamily Q i stop a A θ} {r fraction : ℝ}
    (R : NarrowResidual F r fraction) (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w) (ha : 0 < a) (hA : 0 < A)
    (b : Fin p.C) (hb : F.active b) (e : ℕ)
    (he : e ∈ Q.intrinsicNarrowStates F.code stop F.U r fraction b) :
    fraction / A ≤ (Q.velocityPosterior b).real
      (boundedStrip (R.prediction.normal b e) (R.prediction.offset b e) (r + 2 * a) (2 * p.κ)) :=
  R.prediction.heavy_strip_floor hd hp hHE b (F.packet b hb) (F.coarse_positive b hb)
    (F.posterior b hb) (F.subset_coarse b hb) ha hA (F.joint_cap b hb) e he

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
