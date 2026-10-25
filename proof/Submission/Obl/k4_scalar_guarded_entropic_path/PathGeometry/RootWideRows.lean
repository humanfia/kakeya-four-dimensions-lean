/-
Adapted from this LOT tree, obligation o093, session x0535, commit 05931f40,
Submission/Obl/k4_scalar_critical_path_terminal/RootWideRows.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.UniformRootCharts
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PreparationCore

/-! Good original-root rows keep the exact width labels at every actual
local normalization. Their root widths are the corresponding products,
and the SAME common core is covered pointwise by these rows. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open PathMeasures

noncomputable section

namespace TrueNormalization.WidthChoice

variable {p q : Code} {r h : ℝ} {a : TrueNormalization p q r r h}

def allowance (choice : WidthChoice a) (k : ℕ) : ℝ :=
  4 * N q k ^ (a.ambientLoss k + choice.reading)

theorem allowance_pos (choice : WidthChoice a) (k : ℕ) : 0 < choice.allowance k := by
  have hN : 0 < N q k := by rw [(a.witness.charts k).1]; linarith [a.parent_exact.1.1 (a.witness.sample k)]
  exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hN _)

theorem local_width_lower (choice : WidthChoice a) (k : ℕ) (d : Fin (W q k))
    (hd : d ∉ NarrowWidths.narrowLabels (a.terminalAmbientChart choice.cap k)
      (N q k ^ (-choice.reading))) :
    (choice.allowance k * (2 : ℝ) ^ a.witness.T k)⁻¹ ≤ a.witness.width k d := by
  have hN : 0 < N p (a.witness.sample k) := by linarith [a.parent_exact.1.1 (a.witness.sample k)]
  have hd' := hd
  rw [(a.witness.charts k).1] at hd'
  have hbound := NarrowWidths.width_lower_of_not_mem
    (a.terminalAmbientChart choice.cap k) hN d hd'
  change ((4 * N p (a.witness.sample k) ^ (a.ambientLoss k + choice.reading)) *
    (2 : ℝ) ^ a.witness.T k)⁻¹ ≤ a.witness.width k d at hbound
  simpa only [allowance, (a.witness.charts k).1] using hbound

end TrueNormalization.WidthChoice

namespace PathNodes.TrueGridPath

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ}

def rootWidthAllowance {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : TrueGridPath ctx source start targets) (i : ℕ) :
    (certs : path.Certificates i) → path.WidthChoices i certs → (k : ℕ) → Fin targets.length → ℝ :=
  match path with
  | .nil _ _ => fun _ _ _ => Fin.elim0
  | .cons _ _ _ _ _ tail => fun certs choices k =>
      Fin.cases (choices.1.allowance ((tail.measuredChain i certs.2).sample k))
        (fun j => choices.1.allowance ((tail.measuredChain i certs.2).sample k) *
          tail.rootWidthAllowance i certs.2 choices.2 k j)

/-- Every local width label along this actual root row is good. -/
def RootWideRow {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : TrueGridPath ctx source start targets) (i : ℕ) :
    (certs : path.Certificates i) → path.WidthChoices i certs → (k : ℕ) →
      (j : Fin targets.length) → Fin (path.rootGeometry i certs k j).count → Prop :=
  match path with
  | .nil _ _ => fun _ _ _ j => Fin.elim0 j
  | .cons _ _ _ _ node tail => fun certs choices k =>
      let sample := (tail.measuredChain i certs.2).sample k
      let bad := NarrowWidths.narrowLabels (certs.1.terminalAmbientChart choices.1.cap sample)
        (N (node.remaining.problem i) sample ^ (-choices.1.reading))
      Fin.cases (fun d => d ∉ bad)
        (fun j d => (tail.rootGeometry i certs.2 k j).world d ∉ bad ∧
          tail.RootWideRow i certs.2 choices.2 k j d)

theorem rootWidthAllowance_pos (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs) (k : ℕ)
    (j : Fin targets.length) : 0 < path.rootWidthAllowance i certs choices k j := by
  induction path with
  | nil => exact Fin.elim0 j
  | cons r rs hstart hr node tail ih =>
    refine Fin.cases (choices.1.allowance_pos _) (fun j => ?_) j
    exact mul_pos (choices.1.allowance_pos _) (ih certs.2 choices.2 j)

/-- Every good original row has its actual full-block width lower bound.
The allowance multiplies exactly as the genuine original widths do. -/
theorem root_width_lower (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs) (k : ℕ) :
    ∀ (j : Fin targets.length) (d : Fin (path.rootGeometry i certs k j).count),
      path.RootWideRow i certs choices k j d →
      (path.rootWidthAllowance i certs choices k j *
        (2 : ℝ) ^ (path.rootGeometry i certs k j).generation)⁻¹ ≤
          (path.rootGeometry i certs k j).width d := by
  induction path with
  | nil => intro j; exact Fin.elim0 j
  | cons r rs hstart hr node tail ih =>
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro d hd
      exact choices.1.local_width_lower _ d hd
    · intro d hd
      have hhead := choices.1.local_width_lower _ ((tail.rootGeometry i certs.2 k j).world d) hd.1
      have htail := ih certs.2 choices.2 j d hd.2
      have hHhead := choices.1.allowance_pos ((tail.measuredChain i certs.2).sample k)
      have hHtail := tail.rootWidthAllowance_pos i certs.2 choices.2 k j
      have hprod := mul_le_mul hhead htail (by positivity)
        (certs.1.witness.width_pos _ ((tail.rootGeometry i certs.2 k j).world d)).le
      change ((choices.1.allowance ((tail.measuredChain i certs.2).sample k) *
        tail.rootWidthAllowance i certs.2 choices.2 k j) *
        (2 : ℝ) ^ (certs.1.witness.T ((tail.measuredChain i certs.2).sample k) +
          (tail.rootGeometry i certs.2 k j).generation))⁻¹ ≤ _
      calc
        _ = (choices.1.allowance ((tail.measuredChain i certs.2).sample k) *
            (2 : ℝ) ^ certs.1.witness.T ((tail.measuredChain i certs.2).sample k))⁻¹ *
            (tail.rootWidthAllowance i certs.2 choices.2 k j *
              (2 : ℝ) ^ (tail.rootGeometry i certs.2 k j).generation)⁻¹ := by
          simp only [pow_add, mul_inv]
          ring
        _ ≤ _ := hprod

/-- Every width-core point is covered by a good ORIGINAL row at every
prefix. The chosen row follows the actual current world through the same
pullbacks, so no uniqueness assertion at dyadic endpoints is needed. -/
theorem widthCore_covered_by_rootWideRows (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs) (k : ℕ) :
    ∀ z ∈ path.widthCore i certs choices k, ∀ j : Fin targets.length,
      ∃ d : Fin (path.rootGeometry i certs k j).count,
        path.RootWideRow i certs choices k j d ∧
        (path.rootGeometry i certs k j).world d = ((path.measuredChain i certs).pullback k z).1 ∧
        ((path.measuredChain i certs).pullback k z).2 ∈ (path.rootGeometry i certs k j).selected d := by
  induction path with
  | nil => intro z hz j; exact Fin.elim0 j
  | @cons source start r rs hstart hr node tail ih =>
    intro z hz j
    let inner := tail.measuredChain i certs.2
    let sample := inner.sample k
    let y := inner.pullback k z
    let x := (certs.1.witness.incidenceEquiv certs.1.parent_exact sample y.1).symm y.2
    have hsel := hz.1.2
    change x ∈ certs.1.witness.selected sample y.1 at hsel
    have hwide := (TrueGridPath.cons r rs hstart hr node tail).widthCore_subset_wide i certs choices k hz
    have htail : z ∈ tail.widthCore i certs.2 choices.2 k :=
      ⟨hz.1.1, fun hb => hz.2 (Or.inr hb)⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · exact ⟨y.1, hwide.2, rfl, certs.1.selected_subset_ambient sample y.1 hsel⟩
    · obtain ⟨d, hd, hw, hC⟩ := ih certs.2 choices.2 z htail j
      refine ⟨d, ⟨?_, hd⟩, ?_, ?_⟩
      · change (tail.rootGeometry i certs.2 k j).world d ∉ _
        rw [hw]
        exact hwide.2
      · change certs.1.witness.world sample ((tail.rootGeometry i certs.2 k j).world d) =
          certs.1.witness.world sample y.1
        rw [hw]
      · change x ∈ certs.1.witness.selected sample ((tail.rootGeometry i certs.2 k j).world d) ∩
          ((certs.1.witness.refBody.step sample).Φ ((tail.rootGeometry i certs.2 k j).world d)) ⁻¹'
            (tail.rootGeometry i certs.2 k j).selected d
        rw [hw]
        refine ⟨hsel, ?_⟩
        have hmap : (certs.1.witness.refBody.step sample).Φ y.1 =
            certs.1.witness.incidenceEquiv certs.1.parent_exact sample y.1 :=
          IntermediateLiftSupport.endpointStep_incidence_eq certs.1.witness certs.1.parent_exact 0 sample y.1
        change (certs.1.witness.refBody.step sample).Φ y.1 x ∈
          (tail.rootGeometry i certs.2 k j).selected d
        rw [hmap]
        simpa only [x, MeasurableEquiv.apply_symm_apply] using hC

end PathNodes.TrueGridPath

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
