/-
Adapted from this LOT tree, obligation o093, session x0535, commit 21cac614,
Submission/Obl/k4_scalar_critical_path_terminal/PathWidthMasks.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrueWidthTails
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TruePathSupport
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.SampledPathMasks
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.LiteralLayer
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.DensityMasks

/-! All local chosen true-chart width exceptions are removed on one
common final probability space, before any later packet pruning. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_native_grid_profile_extension.Profiles
open PathMeasures

noncomputable section

namespace TrueNormalization

/-- Any positive angular reading of the literal outer may be chosen.
It is fixed before the inner exact sample. -/
structure WidthChoice {p q : Code} {r h : ℝ} (a : TrueNormalization p q r r h) where
  cap : ℝ
  outer_exact : Exact (PathNodes.literalCoarsen p r cap)
  reading : ℝ
  reading_pos : 0 < reading
  reading_le : reading ≤ U (PathNodes.literalCoarsen p r cap)

namespace WidthChoice

variable {p q : Code} {r h : ℝ} {a : TrueNormalization p q r r h}

theorem nonempty (a : TrueNormalization p q r r h) (cap : ℝ)
    (houter : Exact (PathNodes.literalCoarsen p r cap)) : Nonempty (WidthChoice a) := by
  have hU := (exact_angular_pos houter).2
  exact ⟨⟨cap, houter, U (PathNodes.literalCoarsen p r cap) / 2, by positivity,
    by linarith⟩⟩

def event (choice : WidthChoice a) (k : ℕ) :
    Set (Fin (W p (a.witness.sample k)) × State) :=
  taggedEvent (fun g => NarrowWidths.narrowUnion (a.terminalAmbientChart choice.cap k)
    (N q k ^ (-choice.reading)) g)

theorem event_measurable (choice : WidthChoice a) (k : ℕ) : MeasurableSet (choice.event k) :=
  measurableSet_taggedEvent _ (fun g => NarrowWidths.measurableSet_narrowUnion
    (a.terminalAmbientChart choice.cap k) (N q k ^ (-choice.reading)) g)

theorem event_powerSmall (choice : WidthChoice a) :
    IsPowerSmall (N q) (fun k => worldMixture p (a.witness.sample k) (choice.event k)) := by
  obtain ⟨c, hc, hbound⟩ := a.narrow_masks_powerSmall choice.outer_exact
    choice.reading_pos choice.reading_le
  refine ⟨c, hc, hbound.mono ?_⟩
  intro k hk
  change worldMixture (PathNodes.literalCoarsen p r choice.cap) (a.witness.sample k)
    (taggedEvent (fun g => NarrowWidths.narrowUnion (a.terminalAmbientChart choice.cap k)
      (N q k ^ (-choice.reading)) g)) ≤ _
  rw [worldMixture_taggedEvent _ _ _ (fun g => NarrowWidths.measurableSet_narrowUnion
    (a.terminalAmbientChart choice.cap k) (N q k ^ (-choice.reading)) g)]
  exact hk

end WidthChoice

end TrueNormalization

namespace PathNodes.TrueGridPath

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ}

def WidthChoices {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : TrueGridPath ctx source start targets) (i : ℕ) :
    path.Certificates i → Type :=
  match path with
  | .nil _ _ => fun _ => PUnit
  | .cons _ _ _ _ _ tail => fun certs =>
      TrueNormalization.WidthChoice certs.1 × tail.WidthChoices i certs.2

/-- Actual valid layers supply a positive angular reading without any
identification of their abstract outer codes with literal coarsenings. -/
theorem nonempty_widthChoices (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (hi : path.forget.AllLayers i) :
    Nonempty (path.WidthChoices i certs) := by
  induction path with
  | nil => exact ⟨PUnit.unit⟩
  | @cons source start r rs hstart hr node tail ih =>
    obtain ⟨choice⟩ := TrueNormalization.WidthChoice.nonempty certs.1
      (ctx.dstar + (ctx.D i - ctx.dstar) / 2)
      (hi.1.literal_outer_exact (source.angular i).1)
    obtain ⟨rest⟩ := ih certs.2 hi.2
    exact ⟨choice, rest⟩

def widthEvents {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : TrueGridPath ctx source start targets)
    (i : ℕ) : (certs : path.Certificates i) →
    path.WidthChoices i certs → (path.measuredChain i certs).SampledEvents :=
  match path with
  | .nil _ _ => fun _ _ => PUnit.unit
  | .cons _ _ _ _ _ tail => fun certs choices =>
      (choices.1.event, tail.widthEvents i certs.2 choices.2)

theorem widthEvents_measurable (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs) :
    (path.measuredChain i certs).SampledEventsMeasurable (path.widthEvents i certs choices) := by
  induction path with
  | nil => trivial
  | cons r rs hstart hr node tail ih =>
    exact ⟨choices.1.event_measurable, ih certs.2 choices.2⟩

theorem widthEvents_small (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs) :
    (path.measuredChain i certs).SampledEventsSmall (path.widthEvents i certs choices) := by
  induction path with
  | nil => trivial
  | cons r rs hstart hr node tail ih =>
    exact ⟨choices.1.event_powerSmall, ih certs.2 choices.2⟩

/-- One common measurable mask removes every local narrow-width event. -/
def widthCore (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs) (k : ℕ) :
    Set (Fin (W (path.forget.finalFamily.problem i) k) × State) :=
  (path.measuredChain i certs).sampledCore (path.widthEvents i certs choices) k

theorem measurableSet_widthCore (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs) (k : ℕ) :
    MeasurableSet (path.widthCore i certs choices k) :=
  (path.measuredChain i certs).measurableSet_sampledCore _ (path.widthEvents_measurable i certs choices) k

/-- The unchanged path probability retains at least half its mass after
all local width deletions simultaneously. -/
theorem eventually_widthCore_mass_half (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs) :
    ∀ᶠ k in atTop, ENNReal.ofReal (1 / 2 : ℝ) ≤
      normalizedWorldMixture (path.forget.finalFamily.problem i) k (path.widthCore i certs choices k) :=
  (path.measuredChain i certs).eventually_sampledCore_mass_half
    (path.forget.finalFamily.angular i).1 _
    (path.widthEvents_measurable i certs choices) (path.widthEvents_small i certs choices)

theorem widthCore_subset_ambient (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs) (k : ℕ) :
    path.widthCore i certs choices k ⊆ path.ambientPathSet i certs k :=
  fun _ hz => path.pathSet_subset_ambient i certs k hz.1

/-- The actual normalized world at every local layer has a surviving
width label, all tested on the same final coordinates. -/
def widePathSet {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : TrueGridPath ctx source start targets)
    (i : ℕ) : (certs : path.Certificates i) → path.WidthChoices i certs → (k : ℕ) →
      Set (Fin (W (path.forget.finalFamily.problem i) k) × State) :=
  match path with
  | .nil _ _ => fun _ _ _ => univ
  | .cons _ _ _ _ node tail => fun certs choices k =>
      tail.widePathSet i certs.2 choices.2 k ∩
        {z | ((tail.measuredChain i certs.2).pullback k z).1 ∉
          NarrowWidths.narrowLabels
            (certs.1.terminalAmbientChart choices.1.cap ((tail.measuredChain i certs.2).sample k))
            (N (node.remaining.problem i) ((tail.measuredChain i certs.2).sample k) ^ (-choices.1.reading))}

/-- Every point of the common width core has a good actual width label
at EVERY local true normalization, before any later dominated pruning. -/
theorem widthCore_subset_wide (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs) (k : ℕ) :
    path.widthCore i certs choices k ⊆ path.widePathSet i certs choices k := by
  classical
  induction path with
  | nil => exact Set.subset_univ _
  | @cons source start r rs hstart hr node tail ih =>
    intro z hz
    have htail : z ∈ tail.widthCore i certs.2 choices.2 k :=
      ⟨hz.1.1, fun hb => hz.2 (Or.inr hb)⟩
    refine ⟨ih certs.2 choices.2 htail, ?_⟩
    let inner := tail.measuredChain i certs.2
    let j := inner.sample k
    let y := inner.pullback k z
    have hsel := hz.1.2
    change (certs.1.witness.incidenceEquiv certs.1.parent_exact j y.1).symm y.2 ∈
      certs.1.witness.selected j y.1 at hsel
    have hC := certs.1.selected_subset_ambient j y.1 hsel
    intro hbad
    apply hz.2
    left
    change (certs.1.witness.incidenceEquiv certs.1.parent_exact j y.1).symm y.2 ∈
      NarrowWidths.narrowUnion (certs.1.terminalAmbientChart choices.1.cap j)
        (N (node.remaining.problem i) j ^ (-choices.1.reading)) (certs.1.witness.world j y.1)
    exact NarrowWidths.mem_narrowUnion
      (certs.1.terminalAmbientChart choices.1.cap j)
      (N (node.remaining.problem i) j ^ (-choices.1.reading))
      (certs.1.witness.world j y.1) y.1 hbad rfl
      ((certs.1.witness.incidenceEquiv certs.1.parent_exact j y.1).symm y.2)
      ((certs.1.ambient_charts j).2.2.2.2.1 y.1 hC).2

end PathNodes.TrueGridPath

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
