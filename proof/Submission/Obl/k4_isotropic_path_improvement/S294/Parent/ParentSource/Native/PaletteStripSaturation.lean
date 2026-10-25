-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.PaletteStripSaturation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/PaletteStripSaturation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/PaletteStripSaturation.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/PaletteStripSaturation.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StateStripSaturation
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PaletteCertificate

/-! Bounded per-state strip predictions are heavy under the SAME original
native coarse posterior. Saturation leaves an absolute original-state cap;
no successful conditional law is substituted for the reference law. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A : ℝ} {θ : ENNReal}

structure PaletteStripSaturation (F : PaletteFamily Q i stop a A θ) (r fraction : ℝ) where
  predictions : Fin p.C → ℕ → Finset UnitStripParameter
  count : ∀ b, F.active b → ∀ e, ((predictions b e).card : ℝ) ≤ fraction⁻¹
  heavy : ∀ b, F.active b → ∀ e, ∀ q ∈ predictions b e,
    fraction / A ≤ (Q.velocityPosterior b).real
      (boundedStrip q.val.1 q.val.2 (r + 2 * a) (2 * p.κ))
  outside_cap : ∀ b, F.active b → ∀ e (n : StripSpace) (β : ℝ), ‖n‖ = 1 →
    (Q.coarseLaw (p.lev b) (F.code b)).real
      {z | finitePacketHistory p.lev p.γ p.F stop z = e ∧ z ∈ F.U b ∧
        p.normalizedVelocity b z.2 ∈ affineStrip n β r ∧
        ∀ q ∈ predictions b e, p.normalizedVelocity b z.2 ∉ affineStrip q.val.1 q.val.2 r} ≤
      fraction * (Q.coarseLaw (p.lev b) (F.code b)).real
        {z | finitePacketHistory p.lev p.γ p.F stop z = e}

variable (F : PaletteFamily Q i stop a A θ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

theorem PaletteFamily.exists_stripSaturation (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w) (r fraction : ℝ)
    (hfraction : 0 < fraction) (ha : 0 < a) (hA : 0 < A) :
    Nonempty (PaletteStripSaturation F r fraction) := by
  classical
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have hex (b : Fin p.C) : ∃ predictions : ℕ → Finset UnitStripParameter,
      F.active b →
      (∀ e, ((predictions e).card : ℝ) ≤ fraction⁻¹) ∧
      (∀ e, ∀ q ∈ predictions e, fraction * (Q.coarseLaw (p.lev b) (F.code b)).real
        {z | finitePacketHistory p.lev p.γ p.F stop z = e} <
        (Q.coarseLaw (p.lev b) (F.code b)).real
          {z | finitePacketHistory p.lev p.γ p.F stop z = e ∧ z ∈ F.U b ∧
            p.normalizedVelocity b z.2 ∈ affineStrip q.val.1 q.val.2 r}) ∧
      ∀ e (n : StripSpace) (β : ℝ), ‖n‖ = 1 →
        (Q.coarseLaw (p.lev b) (F.code b)).real
          {z | finitePacketHistory p.lev p.γ p.F stop z = e ∧ z ∈ F.U b ∧
            p.normalizedVelocity b z.2 ∈ affineStrip n β r ∧
            ∀ q ∈ predictions e, p.normalizedVelocity b z.2 ∉ affineStrip q.val.1 q.val.2 r} ≤
          fraction * (Q.coarseLaw (p.lev b) (F.code b)).real
            {z | finitePacketHistory p.lev p.γ p.F stop z = e} := by
    by_cases hb : F.active b
    · let : IsFiniteMeasure (Q.coarseLaw (p.lev b) (F.code b)) := by
        change IsFiniteMeasure (ProbabilityTheory.cond Q.law _)
        infer_instance
      obtain ⟨predictions, hpred⟩ := exists_state_strip_saturation
        (Q.coarseLaw (p.lev b) (F.code b)) (finitePacketHistory p.lev p.γ p.F stop)
        (fun e => measurableSet_eq_fun (measurable_finitePacketHistory p.lev p.γ p.F hF stop) measurable_const)
        (F.U b) (F.measurable_U b hb) (fun z => p.normalizedVelocity b z.2)
        ((p.measurable_normalizedVelocity b).comp measurable_snd) r fraction hfraction
      exact ⟨predictions, fun _ => hpred⟩
    · exact ⟨fun _ => ∅, fun h => False.elim (hb h)⟩
  choose predictions hpred using hex
  refine ⟨{
    predictions := predictions
    count := fun b hb => (hpred b hb).1
    outside_cap := fun b hb => (hpred b hb).2.2
    heavy := ?_
  }⟩
  intro b hb e q hq
  let : IsFiniteMeasure (Q.coarseLaw (p.lev b) (F.code b)) := by
    change IsFiniteMeasure (ProbabilityTheory.cond Q.law _)
    infer_instance
  have hheavy := (hpred b hb).2.1 e q hq
  have hpos : 0 < (Q.coarseLaw (p.lev b) (F.code b)).real
      {z | finitePacketHistory p.lev p.γ p.F stop z = e} :=
    (lt_of_le_of_lt (mul_nonneg hfraction.le ENNReal.toReal_nonneg) hheavy).trans_le
      (measureReal_mono (fun _ hz => hz.1))
  exact Q.coarse_strip_floor hd hp hHE b (F.code b) (F.packet b hb) (F.coarse_positive b hb)
    (F.posterior b hb) (F.U b) (F.subset_coarse b hb)
    (finitePacketHistory p.lev p.γ p.F stop) ha A fraction hA e hpos (F.joint_cap b hb e)
    q.val.1 q.val.2 r q.property (by simpa only [and_left_comm] using hheavy.le)

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
