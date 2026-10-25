/-
Adapted from this LOT tree, obligation o093, session x0535, commit 05931f40,
Submission/Obl/k4_scalar_critical_path_terminal/GeometryCharts.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ChartGeometry
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.DensityMasks
import Submission.Obl.k4_scalar_normalized_exact_refinement.AtlasPruning

/-! Transfer true chart data to its fixed geometry, and select a finite
family of rows while retaining all full original assignments and fields.
All chart restriction estimates are the accepted Bool-generic o166 API. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ChartGeometry

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_true_terminal_lifting
open Submission.Obl.k4_scalar_normalized_exact_refinement
open PathMeasures

noncomputable section

variable {p : Code} {k : ℕ}

def worldRegion (g : Geometry p k) (good : Fin g.count → Prop) (a : Fin (W p k)) : Set PathMeasures.State :=
  {z | ∃ d, good d ∧ g.world d = a ∧ z ∈ g.selected d}

def region (g : Geometry p k) (good : Fin g.count → Prop) : Set (Fin (W p k) × PathMeasures.State) :=
  taggedEvent (worldRegion g good)

theorem measurableSet_worldRegion (g : Geometry p k) (good : Fin g.count → Prop)
    (hC : ∀ d, MeasurableSet (g.selected d)) (a : Fin (W p k)) :
    MeasurableSet (worldRegion g good a) := by
  have heq : worldRegion g good a = ⋃ d, ⋃ (_ : good d ∧ g.world d = a), g.selected d := by
    ext z
    simp only [worldRegion, mem_ofPred_eq, mem_iUnion, exists_prop, and_assoc]
  rw [heq]
  exact MeasurableSet.iUnion fun d => MeasurableSet.iUnion fun _ => hC d

theorem measurableSet_region (g : Geometry p k) (good : Fin g.count → Prop)
    (hC : ∀ d, MeasurableSet (g.selected d)) : MeasurableSet (region g good) :=
  measurableSet_taggedEvent _ (measurableSet_worldRegion g good hC)

theorem worldMixture_region (g : Geometry p k) (good : Fin g.count → Prop)
    (hC : ∀ d, MeasurableSet (g.selected d)) :
    worldMixture p k (region g good) =
      ∑ a, ENNReal.ofReal (ω p k a) * mu p k a (worldRegion g good a) :=
  worldMixture_taggedEvent p k _ (measurableSet_worldRegion g good hC)

/-- Equality of geometry transports every field of the actual chart,
without carrying its original list or tolerance proof into later choices. -/
theorem exists_chartData {B : ℕ} {r b h ε : ℝ} {flag : Bool}
    (Q : ChartW p B r b h ε flag k) (g : Geometry p k) (heq : ofChart Q = g) :
    ∃ Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin g.count),
      ChartData p B r b h ε flag k g.generation g.count g.world g.block g.assignment g.selected
        g.center g.speed g.width g.polynomial Λ := by
  subst g
  exact ⟨Q.Λ, Q.hcd⟩

/-- The subfamily changes only the finite row index and the lists. All
original priors, assigned trajectory sets and geometric fields are kept. -/
structure SubChart (g : Geometry p k) (B : ℕ) (r b h ε : ℝ) (flag : Bool) where
  count : ℕ
  embedding : Fin count ↪ Fin g.count
  lists : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin count)
  data : ChartData p B r b h ε flag k g.generation count (g.world ∘ embedding)
    (g.block ∘ embedding) (g.assignment ∘ embedding) (g.selected ∘ embedding)
    (g.center ∘ embedding) (g.speed ∘ embedding) (g.width ∘ embedding)
    (g.polynomial ∘ embedding) lists

def SubChart.chart {g : Geometry p k} {B : ℕ} {r b h ε : ℝ} {flag : Bool}
    (s : SubChart g B r b h ε flag) : ChartW p B r b h ε flag k :=
  ⟨g.generation, s.count, g.world ∘ s.embedding, g.block ∘ s.embedding,
    g.assignment ∘ s.embedding, g.selected ∘ s.embedding, g.center ∘ s.embedding,
    g.speed ∘ s.embedding, g.width ∘ s.embedding, g.polynomial ∘ s.embedding, s.lists, s.data⟩

/-- Retain exactly the declared good rows. The supplied original-law mass
floor is the only new condition; accepted chart restriction does the rest. -/
theorem select_charts (g : Geometry p k) {B : ℕ} {r b h ε : ℝ} {flag : Bool}
    (Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin g.count))
    (hc : ChartData p B r b h ε flag k g.generation g.count g.world g.block g.assignment g.selected
      g.center g.speed g.width g.polynomial Λ)
    (good : Fin g.count → Prop)
    (hmass : ENNReal.ofReal (N p k ^ (-ε)) ≤
      ∑ a, ENNReal.ofReal (ω p k a) * mu p k a (worldRegion g good a)) :
    ∃ s : SubChart g B r b h ε flag,
      (∀ d, good (s.embedding d)) ∧ (∀ d, good d → ∃ i, s.embedding i = d) := by
  classical
  let keep := Finset.univ.filter good
  let e : Fin keep.card ↪ Fin g.count := (keep.orderEmbOfFin rfl).toEmbedding
  have he (i : Fin keep.card) : good (e i) :=
    (Finset.mem_filter.mp (keep.orderEmbOfFin_mem rfl i)).2
  have hsurj (d : Fin g.count) (hd : good d) : ∃ i, e i = d := by
    have hmem : d ∈ keep := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩
    refine ⟨(keep.orderIsoOfFin rfl).symm ⟨d, hmem⟩, ?_⟩
    exact congrArg Subtype.val ((keep.orderIsoOfFin rfl).apply_symm_apply ⟨d, hmem⟩)
  have hm : ENNReal.ofReal (N p k ^ (-ε)) ≤
      ∑ a, ENNReal.ofReal (ω p k a) * mu p k a
        {z | ∃ i : Fin keep.card, g.world (e i) = a ∧ z ∈ g.selected (e i)} := by
    apply hmass.trans
    apply Finset.sum_le_sum
    intro a _
    apply mul_le_mul' le_rfl
    apply measure_mono
    rintro z ⟨d, hd, hworld, hz⟩
    obtain ⟨i, rfl⟩ := hsurj d hd
    exact ⟨i, hworld, hz⟩
  exact ⟨⟨keep.card, e, restrictedChartList e Λ, chartData_restrict hc e hm⟩, he, hsurj⟩

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ChartGeometry
