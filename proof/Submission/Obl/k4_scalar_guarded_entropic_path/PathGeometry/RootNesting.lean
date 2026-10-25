/-
Adapted from this LOT tree, obligation o093, session x0535, commit b0d1e0aa,
Submission/Obl/k4_scalar_critical_path_terminal/RootNesting.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootWideRows

/-! A finer actual root row determines ONE earlier row, including its
original world and selected incidence set. This is a deterministic map
of rows, rather than a new row choice for each incidence. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open Set
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

namespace ChartGeometry

structure RowProjection {p : Code} {k : ℕ} (coarse fine : Geometry p k) where
  row : Fin fine.count → Fin coarse.count
  world_eq : ∀ d, coarse.world (row d) = fine.world d
  selected_subset : ∀ d, fine.selected d ⊆ coarse.selected (row d)

def RowProjection.refl {p : Code} {k : ℕ} (g : Geometry p k) : RowProjection g g :=
  ⟨id, fun _ => rfl, fun _ => Subset.rfl⟩

def RowProjection.lift {p q : Code} {r b h : ℝ} (w : RefinementWitness p q r b h)
    (k : ℕ) {coarse fine : Geometry q k} (π : RowProjection coarse fine) :
    RowProjection (ChartGeometry.lift w k coarse) (ChartGeometry.lift w k fine) where
  row := π.row
  world_eq d := congrArg (w.world k) (π.world_eq d)
  selected_subset d := by
    intro z hz
    change z ∈ w.selected k (coarse.world (π.row d)) ∩
      (w.refBody.step k).Φ (coarse.world (π.row d)) ⁻¹' coarse.selected (π.row d)
    rw [π.world_eq d]
    exact ⟨hz.1, π.selected_subset d hz.2⟩

def ambientProjection {p q : Code} {r h : ℝ} (a : TrueNormalization p q r r h)
    (k : ℕ) (fine : Geometry q k) :
    RowProjection (ofChart (RootTrueCharts.ambientChart a k))
      (ChartGeometry.lift a.witness k fine) where
  row := fine.world
  world_eq _ := rfl
  selected_subset d := by
    intro z hz
    exact a.selected_subset_ambient k (fine.world d) hz.1

end ChartGeometry

namespace PathNodes.TrueGridPath

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ}

/-- The literal normalized-world label at a prefix, read on the common
final space. No incidence-dependent covering choice is made. -/
def rowAt {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : TrueGridPath ctx source start targets) (i : ℕ) :
    (certs : path.Certificates i) → (k : ℕ) → (j : Fin targets.length) →
      (Fin (W (path.forget.finalFamily.problem i) k) × PathMeasures.State) →
        Fin (path.rootGeometry i certs k j).count :=
  match path with
  | .nil _ _ => fun _ _ j => Fin.elim0 j
  | .cons _ _ _ _ _ tail => fun certs k j =>
      Fin.cases
        (fun z => ((tail.measuredChain i certs.2).pullback k z).1)
        (fun j => tail.rowAt i certs.2 k j) j

theorem measurable_rowAt (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (k : ℕ) (j : Fin targets.length) :
    Measurable (path.rowAt i certs k j) := by
  induction path with
  | nil => exact Fin.elim0 j
  | cons r rs hstart hr node tail ih =>
    refine Fin.cases ?_ (fun j => ih certs.2 j) j
    exact measurable_fst.comp ((tail.measuredChain i certs.2).measurable_pullback k)

theorem rowAt_world (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (k : ℕ) (j : Fin targets.length)
    (z : Fin (W (path.forget.finalFamily.problem i) k) × PathMeasures.State) :
    (path.rootGeometry i certs k j).world (path.rowAt i certs k j z) =
      ((path.measuredChain i certs).pullback k z).1 := by
  induction path with
  | nil => exact Fin.elim0 j
  | cons r rs hstart hr node tail ih =>
    refine Fin.cases (by rfl) (fun j => ?_) j
    change certs.1.witness.world ((tail.measuredChain i certs.2).sample k)
      ((tail.rootGeometry i certs.2 k j).world (tail.rowAt i certs.2 k j z)) = _
    rw [ih certs.2 j z]
    rfl

/-- Every fine row determines the same coarser row for ALL its incidences.
This is the finite-history readout used before appending point states. -/
theorem root_rowProjection_with_readout (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (k : ℕ) (c f : Fin targets.length) (hcf : c ≤ f) :
    ∃ π : ChartGeometry.RowProjection (path.rootGeometry i certs k c)
      (path.rootGeometry i certs k f),
      (∀ z, π.row (path.rowAt i certs k f z) = path.rowAt i certs k c z) ∧
        ∀ choices : path.WidthChoices i certs, ∀ d,
          path.RootWideRow i certs choices k f d →
            path.RootWideRow i certs choices k c (π.row d) := by
  induction path with
  | nil => exact Fin.elim0 c
  | cons r rs hstart hr node tail ih =>
    revert f hcf
    refine Fin.cases ?_ (fun c => ?_) c
    · intro f _
      refine Fin.cases ?_ (fun f => ?_) f
      · exact ⟨ChartGeometry.RowProjection.refl _, fun _ => rfl, fun _ _ hd => hd⟩
      · refine ⟨ChartGeometry.ambientProjection certs.1
          ((tail.measuredChain i certs.2).sample k) (tail.rootGeometry i certs.2 k f), ?_,
          fun _ _ hd => hd.1⟩
        exact fun z => tail.rowAt_world i certs.2 k f z
    · intro f
      refine Fin.cases (fun hcf => ?_) (fun f hcf => ?_) f
      · exact (Nat.not_succ_le_zero c.val hcf).elim
      · obtain ⟨π, hreadout, hwide⟩ := ih certs.2 c f (Nat.le_of_succ_le_succ hcf)
        refine ⟨π.lift certs.1.witness ((tail.measuredChain i certs.2).sample k), hreadout, ?_⟩
        intro choices d hd
        change (tail.rootGeometry i certs.2 k c).world (π.row d) ∉ _ ∧ _
        rw [π.world_eq d]
        exact ⟨hd.1, hwide choices.2 d hd.2⟩

theorem root_rowProjection_with_width (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (k : ℕ) (c f : Fin targets.length) (hcf : c ≤ f) :
    ∃ π : ChartGeometry.RowProjection (path.rootGeometry i certs k c)
      (path.rootGeometry i certs k f),
      ∀ choices : path.WidthChoices i certs, ∀ d,
        path.RootWideRow i certs choices k f d →
          path.RootWideRow i certs choices k c (π.row d) := by
  obtain ⟨π, _, hwide⟩ := path.root_rowProjection_with_readout i certs k c f hcf
  exact ⟨π, hwide⟩

theorem root_rowProjection (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (k : ℕ) (c f : Fin targets.length) (hcf : c ≤ f) :
    Nonempty (ChartGeometry.RowProjection (path.rootGeometry i certs k c)
      (path.rootGeometry i certs k f)) := by
  obtain ⟨π, _⟩ := path.root_rowProjection_with_width i certs k c f hcf
  exact ⟨π⟩

end PathNodes.TrueGridPath

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
