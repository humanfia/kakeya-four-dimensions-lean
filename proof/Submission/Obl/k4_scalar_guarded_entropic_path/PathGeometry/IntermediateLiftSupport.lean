/-
Adapted from this LOT tree, obligation o093, session x0535, commit 5d4e5637,
Submission/Obl/k4_scalar_critical_path_terminal/IntermediateLiftSupport.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.IntermediateTrueLift
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathSupport

/-! The finite intermediate TRUE lift covers the same original pulled-back
law. This remains valid for arbitrary later dominated or absolutely
continuous selections, including fractional residuals. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.IntermediateLiftSupport

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_true_terminal_lifting
open PathMeasures IntermediateTrueLift

noncomputable section

/-- World-tagged coverage by the selected events of the actual chart. -/
def chartRegion {p : Code} {B k : ℕ} {r b h ε : ℝ} {flag : Bool}
    (Q : ChartW p B r b h ε flag k) : Set (Fin (W p k) × PathMeasures.State) :=
  {z | ∃ d, Q.γ d = z.1 ∧ z.2 ∈ Q.C d}

theorem measurableSet_chartRegion {p : Code} {B k : ℕ} {r b h ε : ℝ} {flag : Bool}
    (Q : ChartW p B r b h ε flag k) : MeasurableSet (chartRegion Q) := by
  have heq : chartRegion Q = ⋃ d, ({Q.γ d} ×ˢ Q.C d) := by
    ext z
    simp only [chartRegion, mem_ofPred_eq, mem_iUnion, mem_prod, mem_singleton_iff]
    exact exists_congr fun d => and_congr_left fun _ => eq_comm
  rw [heq]
  exact MeasurableSet.iUnion fun d =>
    (measurableSet_singleton _).prod ((Q.hcd.2.2.1 d).2)

variable {p q : Code} {r b h : ℝ} (w : RefinementWitness p q r b h)

theorem endpointStep_incidence_eq (hp : Exact p) (s : ℝ) (k : ℕ) (i : Fin (W q k)) :
    (endpointStep w s k).Φ i = w.incidenceEquiv hp k i := by
  funext z
  apply Prod.ext
  · exact congr_fun (w.trajectory_eq hp k i) z.1
  · rfl

/-- Full assignments stay separate from the selected incidence masks in
the actual original region of a lifted child chart. -/
def originalRegion (hp : Exact p) {B k : ℕ} {s c h₂ ε : ℝ} {flag : Bool}
    (Q : ChartW q B s c h₂ ε flag k) : Set (Fin (W p (w.sample k)) × PathMeasures.State) :=
  {z | ∃ d, w.world k (Q.γ d) = z.1 ∧
    z.2 ∈ w.selected k (Q.γ d) ∩ (w.incidenceEquiv hp k (Q.γ d)) ⁻¹' Q.C d}

theorem measurableSet_originalRegion (hp : Exact p) {B k : ℕ} {s c h₂ ε : ℝ} {flag : Bool}
    (Q : ChartW q B s c h₂ ε flag k) : MeasurableSet (originalRegion w hp Q) := by
  have heq : originalRegion w hp Q = ⋃ d,
      ({w.world k (Q.γ d)} ×ˢ
        (w.selected k (Q.γ d) ∩ (w.incidenceEquiv hp k (Q.γ d)) ⁻¹' Q.C d)) := by
    ext z
    simp only [originalRegion, mem_ofPred_eq, mem_iUnion, mem_prod, mem_singleton_iff]
    exact exists_congr fun d => and_congr_left fun _ => eq_comm
  rw [heq]
  exact MeasurableSet.iUnion fun d => (measurableSet_singleton _).prod
    ((((w.charts k).2.2.2.1 (Q.γ d)).2).inter
      ((Q.hcd.2.2.1 d).2.preimage (w.incidenceEquiv hp k (Q.γ d)).measurable))

theorem pullback_mem_originalRegion (hp : Exact p) {B k : ℕ} {s c h₂ ε : ℝ} {flag : Bool}
    (Q : ChartW q B s c h₂ ε flag k) (z : Fin (W q k) × PathMeasures.State)
    (hz : z ∈ selectedPreimage w hp k) (hQ : z ∈ chartRegion Q) :
    pullbackMap w hp k z ∈ originalRegion w hp Q := by
  rcases z with ⟨i, z⟩
  obtain ⟨d, rfl, hd⟩ := hQ
  refine ⟨d, rfl, hz, ?_⟩
  change (w.incidenceEquiv hp k (Q.γ d))
    ((w.incidenceEquiv hp k (Q.γ d)).symm z) ∈ Q.C d
  simpa using hd

/-- The SAME pulled-back original law is covered; it may already have
been restricted or normalized by any later selection. -/
theorem originalRegion_ae_map (hp : Exact p) {B k : ℕ} {s c h₂ ε : ℝ} {flag : Bool}
    (Q : ChartW q B s c h₂ ε flag k) (ρ : Measure (Fin (W q k) × PathMeasures.State))
    (hρ : ρ ≪ worldMixture q k) (hQ : ∀ᵐ z ∂ρ, z ∈ chartRegion Q) :
    ∀ᵐ z ∂ρ.map (pullbackMap w hp k), z ∈ originalRegion w hp Q := by
  apply (ae_map_iff (measurable_pullbackMap w hp k).aemeasurable
    (measurableSet_originalRegion w hp Q)).mpr
  filter_upwards [hρ.ae_le (selectedPreimage_ae w hp k), hQ] with z hz hQz
  exact pullback_mem_originalRegion w hp Q z hz hQz

variable (hp : Exact p) (hq : Exact q) {B₂ k : ℕ} {s h₂ ε₂ : ℝ}
    (Q : ChartW q B₂ s s h₂ ε₂ true k)
    (σ : ℕ → ℝ) (hsat : w.toRefinementData.Saturated r σ)
    (hrelative : f q s - f q 0 = f p (r + s) - f p r)
    (hr : 0 ≤ r) (hbs : b ≤ r + s) (hloss₁ : w.loss k ≤ 1)
    (hε₂ : 0 ≤ ε₂) {δ ε₃ : ℝ} (hσ : σ k ≤ δ)
    (hδ : 0 ≤ δ) (hε₃ : w.loss k + ε₂ + δ ≤ ε₃)
    (hε₃' : 4 * N p (w.sample k) ^ (w.loss k + ε₂) ≤ N p (w.sample k) ^ ε₃)

/-- The accepted finite lifting data is exactly the original selected
intersection, with the canonical SAME inverse coordinate map. -/
theorem chartRegion_liftChartW :
    chartRegion (liftChartW w hp hq Q σ hsat hrelative hr hbs hloss₁ hε₂ hσ hδ hε₃ hε₃') =
      originalRegion w hp Q := by
  ext z
  change (∃ d, w.world k (Q.γ d) = z.1 ∧
    z.2 ∈ w.selected k (Q.γ d) ∩ (endpointStep w s k).Φ (Q.γ d) ⁻¹' Q.C d) ↔ _
  simp only [endpointStep_incidence_eq w hp, originalRegion, mem_ofPred_eq]

/-- Actual TRUE lifted charts cover every absolutely continuous child
residual on the identical original pulled-back law. -/
theorem liftChartW_covers (ρ : Measure (Fin (W q k) × PathMeasures.State))
    (hρ : ρ ≪ worldMixture q k) (hQ : ∀ᵐ z ∂ρ, z ∈ chartRegion Q) :
    ∀ᵐ z ∂ρ.map (pullbackMap w hp k),
      z ∈ chartRegion (liftChartW w hp hq Q σ hsat hrelative hr hbs hloss₁ hε₂ hσ hδ hε₃ hε₃') := by
  rw [chartRegion_liftChartW w hp hq Q σ hsat hrelative hr hbs hloss₁ hε₂ hσ hδ hε₃ hε₃']
  exact originalRegion_ae_map w hp Q ρ hρ hQ

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.IntermediateLiftSupport
