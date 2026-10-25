-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Forward.FrontStates, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Forward.CoarseTransfer
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeDichotomy

/-!
# Breadth and palette of the virtual states, from the front

The broad branch of the ported front (`Parent/FrontAlternative.exists_narrow_or_broad`) returns a
palette family `F` at level `i` (palette of the velocity normalized to the active packet, joint
caps against the end histories at level `stop`) and a broad residual whose end histories are
neither intrinsically narrow nor retention failures. For such a GOOD end history `e` of an active
packet `a`, inside the likelihood cut `F.U a`:

* `coarse_breadth`: every strip of width `r` of the normalized velocity carries at most
  `8 * fraction` of the mass of `e ∩ F.U a`;
* `coarse_palette`: every normalized velocity bin carries at most `8 A` times the mass of
  `e ∩ F.U a` times the bin's mass in the coarse law of `a` (one palette for all `e`).

These are statements about the coarse law of `a`; `Forward/CoarseTransfer.lean` turns them into
the same ratios for the original world measure. With the plank frame of `a`
(`Forward/Plank.lean`) the normalized velocity is the virtual velocity, so these are the
per-state breadth and palette clauses of the virtual row packet with states = end histories.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294

namespace Forward

open MeasureTheory Set
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
open Submission.Lib.K4VelocityStrips
open scoped ENNReal

noncomputable section

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a₁ A : ℝ} {θ : ENNReal}

/-- Good end histories of an active packet: not intrinsically narrow and not a retention
failure (at the retention fraction `1/8` of the broad residual). -/
def goodEnd (F : PaletteFamily Q i stop a₁ A θ) (r fraction : ℝ) (a : Fin p.C) : Set ℕ :=
  {e | e ∉ Q.intrinsicNarrowStates F.code stop F.U r fraction a ∧
    e ∉ fineRetentionFailures (Q.coarseLaw (p.lev a) (F.code a))
      (finitePacketHistory p.lev p.γ p.F stop) (F.U a) (ENNReal.ofReal (1 / 8 : ℝ))}

theorem coarseLaw_isFinite (Q : PreparedAngularPath d k p m H u τ) (i c : ℕ) :
    IsFiniteMeasure (Q.coarseLaw i c) := by
  unfold PreparedAngularPath.coarseLaw
  infer_instance

/-- Retention floor of a good end history, in the coarse law of its active packet. -/
theorem coarse_retention (F : PaletteFamily Q i stop a₁ A θ) (hF : ∀ b, MeasurableSet (p.F b))
    {r fraction : ℝ} (a : Fin p.C) {e : ℕ} (he : e ∈ goodEnd F r fraction a) :
    (Q.coarseLaw (p.lev a) (F.code a)).real {z | finitePacketHistory p.lev p.γ p.F stop z = e} ≤
      8 * (Q.coarseLaw (p.lev a) (F.code a)).real
        {z | finitePacketHistory p.lev p.γ p.F stop z = e ∧ z ∈ F.U a} := by
  haveI := coarseLaw_isFinite Q (p.lev a) (F.code a)
  have hcell : MeasurableSet (finitePacketHistory p.lev p.γ p.F stop ⁻¹' {e}) :=
    (measurable_finitePacketHistory p.lev p.γ p.F hF stop) (measurableSet_singleton e)
  have h := fine_retention_floor_real (Q.coarseLaw (p.lev a) (F.code a))
    (finitePacketHistory p.lev p.γ p.F stop) (F.U a) e hcell (by norm_num : (0 : ℝ) ≤ 1 / 8)
    he.2
  linarith

/-- Breadth of a good end history inside the likelihood cut, in the coarse law. -/
theorem coarse_breadth (F : PaletteFamily Q i stop a₁ A θ) (hF : ∀ b, MeasurableSet (p.F b))
    {r fraction : ℝ} (hfr : 0 ≤ fraction) (a : Fin p.C) {e : ℕ}
    (he : e ∈ goodEnd F r fraction a) (n : StripSpace) (hn : ‖n‖ = 1) (β : ℝ) :
    (Q.coarseLaw (p.lev a) (F.code a)).real
        {z | finitePacketHistory p.lev p.γ p.F stop z = e ∧ z ∈ F.U a ∧
          p.normalizedVelocity a z.2 ∈ affineStrip n β r} ≤
      8 * fraction * (Q.coarseLaw (p.lev a) (F.code a)).real
        {z | finitePacketHistory p.lev p.γ p.F stop z = e ∧ z ∈ F.U a} := by
  haveI := coarseLaw_isFinite Q (p.lev a) (F.code a)
  set κ := Q.coarseLaw (p.lev a) (F.code a)
  set hist := finitePacketHistory p.lev p.γ p.F stop
  have hret := coarse_retention F hF a he
  have hnot := he.1
  simp only [PreparedAngularPath.intrinsicNarrowStates, narrowFineStates, mem_setOf_eq,
    not_and, not_exists, not_le] at hnot
  by_cases hpos : 0 < κ.real {z | hist z = e}
  · have hlt := hnot hpos n β hn
    have hle : κ.real {z | hist z = e ∧ z ∈ F.U a ∧ p.normalizedVelocity a z.2 ∈ affineStrip n β r}
        ≤ fraction * κ.real {z | hist z = e} := hlt.le
    calc _ ≤ fraction * κ.real {z | hist z = e} := hle
      _ ≤ fraction * (8 * κ.real {z | hist z = e ∧ z ∈ F.U a}) :=
          mul_le_mul_of_nonneg_left hret hfr
      _ = _ := by ring
  · have hzero : κ.real {z | hist z = e} = 0 :=
      le_antisymm (not_lt.mp hpos) measureReal_nonneg
    have hsub : κ.real {z | hist z = e ∧ z ∈ F.U a ∧ p.normalizedVelocity a z.2 ∈ affineStrip n β r}
        ≤ κ.real {z | hist z = e} :=
      measureReal_mono (fun z hz => hz.1) (measure_ne_top _ _)
    have hnn : 0 ≤ 8 * fraction * κ.real {z | hist z = e ∧ z ∈ F.U a} := by positivity
    linarith

/-- One palette for all good end histories: the velocity-bin marginal of the coarse law. -/
theorem coarse_palette (F : PaletteFamily Q i stop a₁ A θ) (hF : ∀ b, MeasurableSet (p.F b))
    (hA : 0 ≤ A) {r fraction : ℝ} (a : Fin p.C) (ha : F.active a) {e : ℕ}
    (he : e ∈ goodEnd F r fraction a) (q : ℤ × ℤ) :
    (Q.coarseLaw (p.lev a) (F.code a)).real
        {z | z ∈ F.U a ∧ finitePacketHistory p.lev p.γ p.F stop z = e ∧
          p.labelledNormalizedPalette a a₁ z = q} ≤
      8 * A * (Q.coarseLaw (p.lev a) (F.code a)).real
          {z | finitePacketHistory p.lev p.γ p.F stop z = e ∧ z ∈ F.U a} *
        (Q.coarseLaw (p.lev a) (F.code a)).real {z | p.labelledNormalizedPalette a a₁ z = q} := by
  haveI := coarseLaw_isFinite Q (p.lev a) (F.code a)
  have hcap := F.joint_cap a ha e q
  have hret := coarse_retention F hF a he
  have hp : 0 ≤ (Q.coarseLaw (p.lev a) (F.code a)).real
      {z | p.labelledNormalizedPalette a a₁ z = q} := measureReal_nonneg
  calc _ ≤ A * (Q.coarseLaw (p.lev a) (F.code a)).real
          {z | finitePacketHistory p.lev p.γ p.F stop z = e} *
        (Q.coarseLaw (p.lev a) (F.code a)).real {z | p.labelledNormalizedPalette a a₁ z = q} := hcap
    _ ≤ A * (8 * (Q.coarseLaw (p.lev a) (F.code a)).real
          {z | finitePacketHistory p.lev p.γ p.F stop z = e ∧ z ∈ F.U a}) *
        (Q.coarseLaw (p.lev a) (F.code a)).real {z | p.labelledNormalizedPalette a a₁ z = q} := by
          gcongr
    _ = _ := by ring

end

end Forward

end Submission.Obl.k4_isotropic_path_improvement.S294
