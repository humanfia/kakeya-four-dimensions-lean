-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Graph.PositivePhysicalRowRegularity, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph.PhysicalRowLists
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.CountablePositiveStateCut

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph

open Set MeasureTheory
open Qualification
open Submission.Lib.K4ThreeBaseRows
open Submission.Lib.K4ThreeBaseRows.RowBinLists (rowEval vbin rowBin)
open Submission.Lib.K4CommonLocalChoice (cell)
open scoped ENNReal BigOperators

noncomputable section

/-- Physical row regularity removes null graph cells internally. Its
final source is still a union of whole original fine states, with the
same mass factor and no positive-fiber hypothesis. -/
theorem physical_row_regularity_with_null_cells (pm : PhysicalModel) (hκ : 1 ≤ pm.slack)
    (μ : Measure Ev) [IsFiniteMeasure μ] (E : Set Ev) (hE : MeasurableSet E) (hEp : E ⊆ pm.event)
    (hfull : ∀ᵐ z ∂μ, z ∈ E)
    {b ρ : ℝ} (hb : 0 < b) (hbρ : b ≤ ρ) (G : (Fin 4 → ℤ) → Fin 3 → ℝ)
    (L : ℕ) (hL : 1 ≤ L) (s : ℕ → ℝ) (hs0 : s 0 = 1) (hspos : ∀ i, 0 < s i)
    (hbgrid : ∀ i < L, b ≤ s i) {Ar : ℝ} (hAr : 1 ≤ Ar)
    (hratio : ∀ i, i + 1 < L → s i ≤ Ar * s (i + 1)) (hfloor : s (L - 1) ≤ ρ)
    (hnest : ∀ i < L, ∀ x ∈ E, ∀ z ∈ E, pm.physicalState b x = pm.physicalState b z →
      cell (s i) (physX pm x) = cell (s i) (physX pm z))
    (π : ℕ → (Fin 2 → ℤ) → ℝ) (Bv : ℕ → Finset (Fin 2 → ℤ))
    (Lst : ℕ → (Fin 4 → ℤ) → (Fin 2 → ℤ) → Finset ℤ)
    {K ε ρb c₀ D KL A P : ℝ} (hρb : 0 < ρb) (hK : 0 ≤ K) (hε : 0 ≤ ε) (hc₀ : 0 < c₀) (hD : 0 < D)
    (hA : 1 ≤ A) (hKA : K ≤ A) (hKLA : KL ≤ A) (hDA : D ≤ A) (hcA : c₀⁻¹ ≤ A)
    (hρA : ρb⁻¹ ≤ A) (hεA : ∀ i < L, ε / s i ≤ A) (hπ0 : ∀ i β, 0 ≤ π i β)
    (hP : ∀ i < L, ∑ β ∈ Bv i, π i β ≤ P)
    (hG : ∀ z ∈ E, ∀ k, |G (pm.physicalState b z) k| ≤ K)
    (hvel : ∀ z ∈ E, ∀ k, |planarVel pm z.1 k| ≤ K)
    (hgraph : ∀ z ∈ E, |physRate pm z - rowEval (G (pm.physicalState b z)) (planarVel pm z.1)| ≤ ε)
    (hderiv : ∀ i < L, ∀ z ∈ E,
      ⌊physRate pm z / s i⌋ ∈ Lst i (cell (s i) (physX pm z)) (vbin (s i) (planarVel pm z.1)))
    (hLcard : ∀ i < L, ∀ n β, ((Lst i n β).card : ℝ) ≤ KL)
    (hBv : ∀ i < L, ∀ z ∈ E, vbin (s i) (planarVel pm z.1) ∈ Bv i)
    (hdom : ∀ i < L, ∀ z ∈ E, ∀ β, μ.real (E ∩ pm.physicalState b ⁻¹' {pm.physicalState b z} ∩
        {x | vbin (s i) (planarVel pm x.1) = β}) ≤
      D * μ.real (E ∩ pm.physicalState b ⁻¹' {pm.physicalState b z}) * π i β)
    (hbroad : ∀ z ∈ E, Broad (μ.restrict (E ∩ pm.physicalState b ⁻¹' {pm.physicalState b z}))
      (fun x => SupportedTriples.liftE (planarVel pm x.1)) ρb c₀) :
    ∃ U : Set (Fin 4 → ℤ), MeasurableSet U ∧
      μ univ ≤ (∏ i ∈ Finset.range L, ((4 : ENNReal) ^ 4 *
        ((7 : ℕ) ^ 4 * ⌊10 ^ 10 * A ^ 27 * (P ^ 3 + 1)⌋₊))) *
        μ ((pm.physicalState b) ⁻¹' U) ∧
      ∀ z ∈ E, pm.physicalState b z ∈ U → ∀ z' ∈ E, pm.physicalState b z' ∈ U →
        ‖G (pm.physicalState b z) - G (pm.physicalState b z')‖ ≤
          6 * (Ar + 3 * K) * (‖physX pm z - physX pm z'‖ + ρ) := by
  let state := pm.physicalState b
  obtain ⟨U0,hU0,hkeep,hrestrict,hpos⟩ :=
    exists_positive_whole_state_source μ E hE hfull state (pm.measurable_physicalState b)
  let keep := E∩state ⁻¹' U0
  have hkeepE : keep⊆E := inter_subset_left
  have hkeepFull : ∀ᵐ z ∂μ, z∈keep := by
    rw [←hrestrict]
    exact ae_restrict_mem hkeep
  have hErestrict : μ.restrict E=μ := Measure.restrict_eq_self_of_ae_mem hfull
  have hrealEq (B : Set Ev) : μ.real (keep∩B)=μ.real (E∩B) := by
    change (μ (keep∩B)).toReal=(μ (E∩B)).toReal
    congr 1
    rw [inter_comm keep B,←Measure.restrict_apply' hkeep,hrestrict,
      inter_comm E B,←Measure.restrict_apply' hE,hErestrict]
  have hcellEq (q : Fin 4 → ℤ) : μ.restrict (keep∩state ⁻¹' {q})=
      μ.restrict (E∩state ⁻¹' {q}) := by
    have hm : MeasurableSet (state ⁻¹' {q}) :=
      (pm.measurable_physicalState b) (measurableSet_singleton q)
    rw [inter_comm keep _,←Measure.restrict_restrict hm,hrestrict,
      inter_comm E _,←Measure.restrict_restrict hm,hErestrict]
  obtain ⟨U1,hU1,hmass,hrow⟩ := physical_row_regularity pm hκ μ keep hkeep
    (hkeepE.trans hEp) hkeepFull hb hbρ G hpos L hL s hs0 hspos hbgrid hAr hratio hfloor
    (fun i hi x hx z hz hxz => hnest i hi x (hkeepE hx) z (hkeepE hz) hxz)
    π Bv Lst hρb hK hε hc₀ hD hA hKA hKLA hDA hcA hρA hεA hπ0 hP
    (fun z hz => hG z (hkeepE hz)) (fun z hz => hvel z (hkeepE hz))
    (fun z hz => hgraph z (hkeepE hz))
    (fun i hi z hz => hderiv i hi z (hkeepE hz)) hLcard
    (fun i hi z hz => hBv i hi z (hkeepE hz)) (by
      intro i hi z hz β
      rw [inter_assoc,hrealEq,hrealEq]
      simpa only [inter_assoc] using hdom i hi z (hkeepE hz) β)
    (by
      intro z hz
      rw [hcellEq]
      exact hbroad z (hkeepE hz))
  refine ⟨U0∩U1,hU0.inter hU1,?_,?_⟩
  · have hU0full : ∀ᵐ z ∂μ, z∈state ⁻¹' U0 := hkeepFull.mono (fun _ hz => hz.2)
    have hμU0 : μ.restrict (state ⁻¹' U0)=μ := Measure.restrict_eq_self_of_ae_mem hU0full
    have hmeasure : μ (state ⁻¹' U1)=μ (state ⁻¹' (U0∩U1)) := by
      calc
        _ = (μ.restrict (state ⁻¹' U0)) (state ⁻¹' U1) := by rw [hμU0]
        _ = _ := by
          rw [Measure.restrict_apply ((pm.measurable_physicalState b) hU1)]
          congr 1
          ext z
          change (state z∈U1 ∧ state z∈U0) ↔ (state z∈U0 ∧ state z∈U1)
          tauto
    dsimp only [state] at hmeasure
    simpa only [hmeasure] using hmass
  · intro z hz hzU z' hz' hzU'
    exact hrow z ⟨hz,hzU.1⟩ hzU.2 z' ⟨hz',hzU'.1⟩ hzU'.2

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph
