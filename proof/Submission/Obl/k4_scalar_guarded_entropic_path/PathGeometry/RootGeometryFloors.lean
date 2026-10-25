/-
Adapted from this LOT tree, obligation o093, session x0544, commit 74042dea,
Submission/Obl/k4_scalar_critical_path_terminal/RootGeometryFloors.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootFloorCore
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.GeometryCharts

/-! Current packet floors belong to the immutable original geometry.
They therefore transfer to every later injectively selected good-width
chart with the same fields, independently of its list or tolerance choice. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootPacketFamilies

open MeasureTheory Set Filter PathMeasures PathNodes
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_true_terminal_lifting (ChartW)

noncomputable section

def geometryPriorCell {p : Code} {K : ℕ} (g : ChartGeometry.Geometry p K)
    (d : Fin g.count) : Set State := g.assignment d ×ˢ I g.generation (g.block d)

def geometryCell {p z : Code} (view : RefinementChain p z) (k : ℕ)
    (g : ChartGeometry.Geometry p (view.sample k)) (d : Fin g.count) :
    Set (Fin (W z k) × State) :=
  view.pullback k ⁻¹' ({g.world d} ×ˢ geometryPriorCell g d)

def CurrentGeometryFloors {p z : Code} (view : RefinementChain p z) (k : ℕ)
    (g : ChartGeometry.Geometry p (view.sample k)) (H : ℝ)
    (E : Set (Fin (W z k) × State))
    (σ : Fin (W p (view.sample k)) → Measure State) : Prop :=
  ∀ d : Fin g.count, 0 < ω p (view.sample k) (g.world d) →
    E ∩ geometryCell view k g d = ∅ ∨
      (ENNReal.ofReal H)⁻¹ * ENNReal.ofReal (((2 : ℝ) ^ g.generation)⁻¹) *
        ν p (view.sample k) (g.world d) (g.assignment d) ≤
          σ (g.world d) (geometryPriorCell g d)

def GeometryFloors {p z : Code} (view : RefinementChain p z) (k : ℕ)
    (g : ChartGeometry.Geometry p (view.sample k)) (H : ℝ)
    (E : Set (Fin (W z k) × State)) : Prop :=
  CurrentGeometryFloors view k g H E (view.selectedWorldLaw k E)

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ}

/-- The floor mask is fixed from the common law, while the original
geometry is fixed independently of losses and observation lists. -/
theorem eventually_root_geometry_floors (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs)
    (hl : path.forget.AllLayers i) (grid : DensityGrid) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ j : Fin targets.length,
      GeometryFloors (path.measuredChain i certs) k (path.rootGeometry i certs k j)
        (N (path.forget.finalFamily.problem i) k ^ ε)
        (floorCore path i certs choices grid ε k) := by
  filter_upwards [eventually_floorCore_properties path i certs choices grid ε hε,
    eventually_rootChoices path i certs hl ε hε] with k hcore hchoices
  intro j
  obtain ⟨P, hchoice, hgeometry, _⟩ := hchoices j
  have hf := hcore.2.2.2 j
  have hfP : GeometryFloors (path.measuredChain i certs) k (ChartGeometry.ofChart P)
      (N (path.forget.finalFamily.problem i) k ^ ε)
      (floorCore path i certs choices grid ε k) := by
    change ∀ d : Fin (sampleOfChoice (source.angular i).1 (rootChoices path i certs ε j k)).count,
      0 < ω (source.problem i) ((path.measuredChain i certs).sample k)
        ((sampleOfChoice (source.angular i).1 (rootChoices path i certs ε j k)).world d) →
      floorCore path i certs choices grid ε k ∩
        ((path.measuredChain i certs).pullback k ⁻¹'
          ({(sampleOfChoice (source.angular i).1 (rootChoices path i certs ε j k)).world d} ×ˢ
            ((sampleOfChoice (source.angular i).1 (rootChoices path i certs ε j k)).assignment d ×ˢ
              I (sampleOfChoice (source.angular i).1 (rootChoices path i certs ε j k)).generation
                ((sampleOfChoice (source.angular i).1 (rootChoices path i certs ε j k)).block d)))) = ∅ ∨
        (ENNReal.ofReal (N (path.forget.finalFamily.problem i) k ^ ε))⁻¹ *
          ENNReal.ofReal (((2 : ℝ) ^
            (sampleOfChoice (source.angular i).1 (rootChoices path i certs ε j k)).generation)⁻¹) *
          ν (source.problem i) ((path.measuredChain i certs).sample k)
            ((sampleOfChoice (source.angular i).1 (rootChoices path i certs ε j k)).world d)
            ((sampleOfChoice (source.angular i).1 (rootChoices path i certs ε j k)).assignment d) ≤
        (path.measuredChain i certs).selectedWorldLaw k (floorCore path i certs choices grid ε k)
          ((sampleOfChoice (source.angular i).1 (rootChoices path i certs ε j k)).world d)
          ((sampleOfChoice (source.angular i).1 (rootChoices path i certs ε j k)).assignment d ×ˢ
            I (sampleOfChoice (source.angular i).1 (rootChoices path i certs ε j k)).generation
              ((sampleOfChoice (source.angular i).1 (rootChoices path i certs ε j k)).block d)) at hf
    rw [hchoice] at hf
    exact hf
  rw [hgeometry] at hfP
  exact hfP

/-- Row selection inherits the exact original full-prior floor. -/
theorem subChart_current_floor_of_currentGeometry {p z : Code} (view : RefinementChain p z) (k : ℕ)
    {g : ChartGeometry.Geometry p (view.sample k)} {B : ℕ} {r b h ε : ℝ} {flag : Bool}
    (s : ChartGeometry.SubChart g B r b h ε flag) (H : ℝ)
    (E : Set (Fin (W z k) × State)) (σ : Fin (W p (view.sample k)) → Measure State)
    (hfloor : CurrentGeometryFloors view k g H E σ)
    (d : Fin s.chart.n) (hω : 0 < ω p (view.sample k) (s.chart.γ d))
    (hactive : E ∩ (view.pullback k ⁻¹'
      ({s.chart.γ d} ×ˢ (s.chart.A d ×ˢ I s.chart.T (s.chart.j d)))) ≠ ∅) :
    (ENNReal.ofReal H)⁻¹ * ENNReal.ofReal (((2 : ℝ) ^ s.chart.T)⁻¹) *
      ν p (view.sample k) (s.chart.γ d) (s.chart.A d) ≤
        σ (s.chart.γ d) (s.chart.A d ×ˢ I s.chart.T (s.chart.j d)) := by
  rcases hfloor (s.embedding d) hω with hempty | hmass
  · exact (hactive hempty).elim
  · exact hmass

/-- Row selection inherits the exact original full-prior floor. -/
theorem subChart_current_floor {p z : Code} (view : RefinementChain p z) (k : ℕ)
    {g : ChartGeometry.Geometry p (view.sample k)} {B : ℕ} {r b h ε : ℝ} {flag : Bool}
    (s : ChartGeometry.SubChart g B r b h ε flag) (H : ℝ)
    (E : Set (Fin (W z k) × State)) (hfloor : GeometryFloors view k g H E)
    (d : Fin s.chart.n) (hω : 0 < ω p (view.sample k) (s.chart.γ d))
    (hactive : E ∩ (view.pullback k ⁻¹'
      ({s.chart.γ d} ×ˢ (s.chart.A d ×ˢ I s.chart.T (s.chart.j d)))) ≠ ∅) :
    (ENNReal.ofReal H)⁻¹ * ENNReal.ofReal (((2 : ℝ) ^ s.chart.T)⁻¹) *
      ν p (view.sample k) (s.chart.γ d) (s.chart.A d) ≤
        view.selectedWorldLaw k E (s.chart.γ d) (s.chart.A d ×ˢ I s.chart.T (s.chart.j d)) := by
  exact subChart_current_floor_of_currentGeometry view k s H E
    (view.selectedWorldLaw k E) hfloor d hω hactive

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootPacketFamilies
