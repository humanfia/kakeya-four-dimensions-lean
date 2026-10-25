import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootNesting
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathHistories

/-! The actual normalized end world reads one definite root row. Its
selection covers the same original path incidences, not a new decoder. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.TrueGridPath

open MeasureTheory Set PathMeasures
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

def rootRow {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : TrueGridPath ctx source start targets)
    (i : ℕ) : (certs : path.Certificates i) → (k : ℕ) → (j : Fin targets.length) →
      Fin (W (path.forget.finalFamily.problem i) k) → Fin (path.rootGeometry i certs k j).count :=
  match path with
  | .nil _ _ => fun _ _ j => Fin.elim0 j
  | .cons _ _ _ _ _ tail => fun certs k =>
      Fin.cases ((tail.measuredChain i certs.2).world k)
        (fun j => tail.rootRow i certs.2 k j)

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ}

theorem rootRow_world (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (k : ℕ) (j : Fin targets.length)
    (g : Fin (W (path.forget.finalFamily.problem i) k)) :
    (path.rootGeometry i certs k j).world (path.rootRow i certs k j g) =
      (path.measuredChain i certs).world k g := by
  induction path with
  | nil => exact Fin.elim0 j
  | cons r rs hstart hr node tail ih =>
    refine Fin.cases (by rfl) (fun j => ?_) j
    change certs.1.witness.world _
      ((tail.rootGeometry i certs.2 k j).world (tail.rootRow i certs.2 k j g)) = _
    rw [ih certs.2 j g]
    rfl

/-- A later original world label determines this row for ALL incidences. -/
theorem rootRow_history (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (k : ℕ) (j : Fin targets.length)
    (g : Fin (W (path.forget.finalFamily.problem i) k)) :
    (path.rootRow i certs k j g).val = (path.measuredChain i certs).history k (j.val + 1) g := by
  induction path with
  | nil => exact Fin.elim0 j
  | cons r rs hstart hr node tail ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · exact ((tail.measuredChain i certs.2).history_zero k g).symm
    · exact ih certs.2 j g

/-- The deterministic row contains the SAME actual original incidence
at every layer on the genuine path core. -/
theorem rootRow_selected (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (k : ℕ)
    (z : Fin (W (path.forget.finalFamily.problem i) k) × State)
    (hz : z ∈ (path.measuredChain i certs).pathSet k) (j : Fin targets.length) :
    ((path.measuredChain i certs).pullback k z).2 ∈
      (path.rootGeometry i certs k j).selected (path.rootRow i certs k j z.1) := by
  induction path with
  | nil => exact Fin.elim0 j
  | @cons source start r rs hstart hr node tail ih =>
    let inner := tail.measuredChain i certs.2
    let sample := inner.sample k
    let y := inner.pullback k z
    let x := (certs.1.witness.incidenceEquiv certs.1.parent_exact sample y.1).symm y.2
    have hsel := hz.2
    change x ∈ certs.1.witness.selected sample y.1 at hsel
    refine Fin.cases ?_ (fun j => ?_) j
    · change x ∈ certs.1.ambientSelected sample (inner.world k z.1)
      rw [← inner.pullback_world k z]
      exact certs.1.selected_subset_ambient sample y.1 hsel
    · have hC := ih certs.2 z hz.1 j
      have hworld := tail.rootRow_world i certs.2 k j z.1
      rw [← inner.pullback_world k z] at hworld
      change x ∈ certs.1.witness.selected sample
          ((tail.rootGeometry i certs.2 k j).world (tail.rootRow i certs.2 k j z.1)) ∩
        ((certs.1.witness.refBody.step sample).Φ
          ((tail.rootGeometry i certs.2 k j).world (tail.rootRow i certs.2 k j z.1))) ⁻¹'
          (tail.rootGeometry i certs.2 k j).selected (tail.rootRow i certs.2 k j z.1)
      rw [hworld]
      refine ⟨hsel, ?_⟩
      have hmap : (certs.1.witness.refBody.step sample).Φ y.1 =
          certs.1.witness.incidenceEquiv certs.1.parent_exact sample y.1 :=
        IntermediateLiftSupport.endpointStep_incidence_eq certs.1.witness certs.1.parent_exact 0 sample y.1
      change (certs.1.witness.refBody.step sample).Φ y.1 x ∈
        (tail.rootGeometry i certs.2 k j).selected (tail.rootRow i certs.2 k j z.1)
      rw [hmap]
      simpa only [x, MeasurableEquiv.apply_symm_apply] using hC

/-- Every later dominated residual inherits this fixed-row readout. -/
theorem rootRow_selected_ae (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (k : ℕ)
    (ρ : Measure (Fin (W (path.forget.finalFamily.problem i) k) × State))
    (hρ : ρ ≤ normalizedWorldMixture (path.forget.finalFamily.problem i) k)
    (j : Fin targets.length) :
    ∀ᵐ z ∂ρ, ((path.measuredChain i certs).pullback k z).2 ∈
      (path.rootGeometry i certs k j).selected (path.rootRow i certs k j z.1) :=
  Filter.Eventually.mono
    (Filter.Eventually.filter_mono (Measure.absolutelyContinuous_of_le hρ).ae_le
      ((path.measuredChain i certs).pathSet_ae_normalized k))
    (fun z hz => path.rootRow_selected i certs k z hz j)

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.TrueGridPath
