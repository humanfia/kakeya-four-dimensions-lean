import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootReadouts

/-! Connect the incidence readout with the actual world decoder, and
retain every local width exclusion on the same common core. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.TrueGridPath

open MeasureTheory Set PathMeasures
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ}

theorem rowAt_eq_rootRow (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (k : ℕ) (j : Fin targets.length)
    (z : Fin (W (path.forget.finalFamily.problem i) k) × State) :
    path.rowAt i certs k j z = path.rootRow i certs k j z.1 := by
  induction path with
  | nil => exact Fin.elim0 j
  | cons r rs hstart hr node tail ih =>
    refine Fin.cases ?_ (fun j => ih certs.2 j z) j
    exact (tail.measuredChain i certs.2).pullback_world k z

/-- The literal row decoder retains all local width exclusions from the
common width core. -/
theorem rowAt_wide_of_widthCore (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs) (k : ℕ)
    (z : Fin (W (path.forget.finalFamily.problem i) k) × State)
    (hz : z ∈ path.widthCore i certs choices k) (j : Fin targets.length) :
    path.RootWideRow i certs choices k j (path.rowAt i certs k j z) := by
  induction path with
  | nil => exact Fin.elim0 j
  | cons r rs hstart hr node tail ih =>
    have hwide := (TrueGridPath.cons r rs hstart hr node tail).widthCore_subset_wide
      i certs choices k hz
    have htail : z ∈ tail.widthCore i certs.2 choices.2 k :=
      ⟨hz.1.1, fun hb => hz.2 (Or.inr hb)⟩
    refine Fin.cases hwide.2 (fun j => ?_) j
    change (tail.rootGeometry i certs.2 k j).world (tail.rowAt i certs.2 k j z) ∉ _ ∧ _
    rw [tail.rowAt_world i certs.2 k j z]
    exact ⟨hwide.2, ih certs.2 choices.2 z htail j⟩

theorem rootRow_wide_of_widthCore (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs) (k : ℕ)
    (z : Fin (W (path.forget.finalFamily.problem i) k) × State)
    (hz : z ∈ path.widthCore i certs choices k) (j : Fin targets.length) :
    path.RootWideRow i certs choices k j (path.rootRow i certs k j z.1) := by
  rw [← path.rowAt_eq_rootRow i certs k j z]
  exact path.rowAt_wide_of_widthCore i certs choices k z hz j

/-- Conditioning on the later original world fixes the literal fine row. -/
theorem rootRow_eq_of_history_eq (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (k : ℕ) (j : Fin targets.length)
    (g g' : Fin (W (path.forget.finalFamily.problem i) k))
    (hg : (path.measuredChain i certs).history k (j.val + 1) g =
      (path.measuredChain i certs).history k (j.val + 1) g') :
    path.rootRow i certs k j g = path.rootRow i certs k j g' := by
  apply Fin.ext
  simpa only [path.rootRow_history i certs k j] using hg

/-- The same earlier row is read from every later row. -/
theorem root_rowProjection_with_rootRow (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (k : ℕ) (c f : Fin targets.length) (hcf : c ≤ f) :
    ∃ π : ChartGeometry.RowProjection (path.rootGeometry i certs k c)
      (path.rootGeometry i certs k f),
      (∀ g, π.row (path.rootRow i certs k f g) = path.rootRow i certs k c g) ∧
        ∀ choices : path.WidthChoices i certs, ∀ d,
          path.RootWideRow i certs choices k f d →
            path.RootWideRow i certs choices k c (π.row d) := by
  obtain ⟨π, hπ, hw⟩ := path.root_rowProjection_with_readout i certs k c f hcf
  refine ⟨π, ?_, hw⟩
  intro g
  simpa only [path.rowAt_eq_rootRow i certs k] using hπ (g, (0 : State))

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.TrueGridPath
