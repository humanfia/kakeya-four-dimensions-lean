-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativeNarrowSelection, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativeNarrowSelection.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativeNarrowSelection.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativeNarrowSelection.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/NativeNarrowSelection.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeNarrowFamilies
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeNarrowTransfer

/-! Intrinsic narrow states and actual raw-strip witnesses. The threshold
uses the ORIGINAL fine marginal, including after the normalized-palette cut.
No measurable selection of continuous strip parameters is assumed. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips
open scoped ENNReal BigOperators

def narrowFineStates {Ω Z : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → Z) (U : Set Ω) (V : Ω → StripSpace) (r fraction : ℝ) : Set Z :=
  {e | 0 < μ.real {z | f z = e} ∧ ∃ n : StripSpace, ∃ β : ℝ, ‖n‖ = 1 ∧
    fraction * μ.real {z | f z = e} ≤
      μ.real {z | f z = e ∧ z ∈ U ∧ V z ∈ affineStrip n β r}}

theorem exists_narrowFineState_predictions {Ω Z : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → Z) (U : Set Ω) (V : Ω → StripSpace) (r fraction : ℝ) :
    ∃ (n : Z → StripSpace) (β : Z → ℝ), ∀ e ∈ narrowFineStates μ f U V r fraction,
      ‖n e‖ = 1 ∧ fraction * μ.real {z | f z = e} ≤
        μ.real {z | f z = e ∧ z ∈ U ∧ V z ∈ affineStrip (n e) (β e) r} := by
  classical
  have hex (e : Z) : ∃ n : StripSpace, ∃ β : ℝ, e ∈ narrowFineStates μ f U V r fraction →
      ‖n‖ = 1 ∧ fraction * μ.real {z | f z = e} ≤
        μ.real {z | f z = e ∧ z ∈ U ∧ V z ∈ affineStrip n β r} := by
    by_cases he : e ∈ narrowFineStates μ f U V r fraction
    · obtain ⟨n, β, hn, hstrip⟩ := he.2
      exact ⟨n, β, fun _ => ⟨hn, hstrip⟩⟩
    · exact ⟨0, 0, fun h => False.elim (he h)⟩
  choose n β h using hex
  exact ⟨n, β, h⟩

/-- Positive states outside the intrinsic narrow set have strict strip
avoidance with the same UNCHANGED fine marginal as denominator. -/
theorem broad_of_not_mem_narrowFineStates {Ω Z : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → Z) (U : Set Ω) (V : Ω → StripSpace) (r fraction : ℝ)
    {e : Z} (hpos : 0 < μ.real {z | f z = e})
    (he : e ∉ narrowFineStates μ f U V r fraction) (n : StripSpace) (β : ℝ) (hn : ‖n‖ = 1) :
    μ.real {z | f z = e ∧ z ∈ U ∧ V z ∈ affineStrip n β r} <
      fraction * μ.real {z | f z = e} := by
  apply lt_of_not_ge
  intro hstrip
  exact he ⟨hpos, n, β, hn, hstrip⟩

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  (Q : PreparedAngularPath d k p m H u τ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

def PreparedAngularPath.intrinsicNarrowStates (code : Fin p.C → ℕ) (stop : ℕ)
    (U : Fin p.C → Set (Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ)))
    (r fraction : ℝ) (b : Fin p.C) : Set ℕ :=
  narrowFineStates (Q.coarseLaw (p.lev b) (code b)) (finitePacketHistory p.lev p.γ p.F stop)
    (U b) (fun z => p.normalizedVelocity b z.2) r fraction

structure NarrowPredictionFamily
    (Q : PreparedAngularPath d k p m H u τ) (code : Fin p.C → ℕ) (stop : ℕ)
    (U : Fin p.C → Set (Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ))) (r fraction : ℝ) where
  normal : Fin p.C → ℕ → StripSpace
  offset : Fin p.C → ℕ → ℝ
  unit : ∀ b e, e ∈ Q.intrinsicNarrowStates code stop U r fraction b → ‖normal b e‖ = 1
  strip_floor : ∀ b e, e ∈ Q.intrinsicNarrowStates code stop U r fraction b →
    fraction * (Q.coarseLaw (p.lev b) (code b)).real {z | finitePacketHistory p.lev p.γ p.F stop z = e} ≤
      (Q.coarseLaw (p.lev b) (code b)).real {z | finitePacketHistory p.lev p.γ p.F stop z = e ∧
        z ∈ U b ∧ p.normalizedVelocity b z.2 ∈ affineStrip (normal b e) (offset b e) r}

theorem PreparedAngularPath.exists_narrowPredictionFamily (code : Fin p.C → ℕ) (stop : ℕ)
    (U : Fin p.C → Set (Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ))) (r fraction : ℝ) :
    Nonempty (NarrowPredictionFamily Q code stop U r fraction) := by
  classical
  have hex (b : Fin p.C) := exists_narrowFineState_predictions
    (Q.coarseLaw (p.lev b) (code b)) (finitePacketHistory p.lev p.γ p.F stop)
    (U b) (fun z => p.normalizedVelocity b z.2) r fraction
  choose n β h using hex
  exact ⟨⟨n, β, fun b e he => (h b e he).1, fun b e he => (h b e he).2⟩⟩

variable {Q} {code : Fin p.C → ℕ} {stop : ℕ}
  {U : Fin p.C → Set (Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ))} {r fraction : ℝ}
  (P : NarrowPredictionFamily Q code stop U r fraction)

theorem NarrowPredictionFamily.strip_floor_ennreal (hfraction : 0 ≤ fraction)
    (b : Fin p.C) (e : ℕ) (he : e ∈ Q.intrinsicNarrowStates code stop U r fraction b) :
    ENNReal.ofReal fraction * Q.coarseLaw (p.lev b) (code b) {z | finitePacketHistory p.lev p.γ p.F stop z = e} ≤
      Q.coarseLaw (p.lev b) (code b) {z | finitePacketHistory p.lev p.γ p.F stop z = e ∧
        z ∈ U b ∧ p.normalizedVelocity b z.2 ∈ affineStrip (P.normal b e) (P.offset b e) r} := by
  let : IsFiniteMeasure (Q.coarseLaw (p.lev b) (code b)) := by
    change IsFiniteMeasure (ProbabilityTheory.cond Q.law _)
    infer_instance
  apply (ENNReal.toReal_le_toReal (by finiteness) (measure_ne_top _ _)).mp
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hfraction, measureReal_def] using P.strip_floor b e he

theorem NarrowPredictionFamily.heavy_strip_floor (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w) (b : Fin p.C)
    (hPacket : ∀ z ∈ Q.coarseSupport (p.lev b) (code b), z.1 = p.γ b ∧ z.2 ∈ p.F b)
    (hCpos : Q.law (Q.coarseSupport (p.lev b) (code b)) ≠ 0)
    (hmap : (Q.coarseLaw (p.lev b) (code b)).map Prod.snd = ProbabilityTheory.cond (Q.currentParentLaw b) univ)
    (hUC : U b ⊆ Q.coarseSupport (p.lev b) (code b))
    {a A : ℝ} (ha : 0 < a) (hA : 0 < A)
    (hcap : ∀ e q, (Q.coarseLaw (p.lev b) (code b)).real
      {z | z ∈ U b ∧ finitePacketHistory p.lev p.γ p.F stop z = e ∧ p.labelledNormalizedPalette b a z = q} ≤
        A * (Q.coarseLaw (p.lev b) (code b)).real {z | finitePacketHistory p.lev p.γ p.F stop z = e} *
          (Q.coarseLaw (p.lev b) (code b)).real {z | p.labelledNormalizedPalette b a z = q})
    (e : ℕ) (he : e ∈ Q.intrinsicNarrowStates code stop U r fraction b) :
    fraction / A ≤ (Q.velocityPosterior b).real
      (boundedStrip (P.normal b e) (P.offset b e) (r + 2 * a) (2 * p.κ)) := by
  have hpos : 0 < (Q.coarseLaw (p.lev b) (code b)).real
      {z | finitePacketHistory p.lev p.γ p.F stop z = e} := he.1
  apply Q.coarse_strip_floor hd hp hHE b (code b) hPacket hCpos hmap (U b) hUC
    (finitePacketHistory p.lev p.γ p.F stop) ha A fraction hA e hpos (hcap e)
    (P.normal b e) (P.offset b e) r (P.unit b e he)
  simpa only [and_comm, and_left_comm, and_assoc] using P.strip_floor b e he

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
