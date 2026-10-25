import Submission.Obl.k4_physical_parent_potential_candidates.PhysicalCatalogue
import Submission.Obl.k4_physical_parent_potential_candidates.HeavyBranch

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory MvPolynomial PhysicalPotentialData
open Submission.Lib.K4ContinuousKakeya
open scoped ENNReal

noncomputable section

/-- Explicit original-reference mass provided by the physical MK3 count. -/
def physicalHeavyFloor (h prior C K w d : ℝ) : ℝ :=
  h*prior*((K^(-100:ℝ))^2/(1+K)^3/8)*w^d /
    (31850496*(1000*C)^2*K^5)

namespace PhysicalSource

variable {q T j : ℕ} {ν : Measure Ln} [IsFiniteMeasure ν]
  {B a ζ d : ℝ} {c u : P2} {P0 : Po} {A : Set Ln} {F H : Set Ev}
  (source : PhysicalSource q ν B a ζ d T j c u P0 A F H)

def fineState : Ev → (Fin 3 → ℤ) × ℤ :=
  physicalCode (packetBase T j c u) (fun e => packetSignal P0 e/a) source.ε

theorem measurable_fineState : Measurable source.fineState := by
  change Measurable (fun e : Ev =>
    ((fun i : Fin 3 => ⌊packetBase T j c u e i/source.ε⌋),
      ⌊(packetSignal P0 e/a)/source.ε⌋))
  have hz := measurable_packetBase T j c u
  have hX := (measurable_packetSignal P0).div_const a
  fun_prop

/-- Maximize the original intercept bin before choosing a sign and retaining
original-state fractions. The floor keeps the original old-packet reference. -/
theorem exists_physical_heavy_branch
    (hSA : source.S ⊆ A ×ˢ Icc ((j:ℝ)*((2:ℝ)^T)⁻¹)
      ((j:ℝ)*((2:ℝ)^T)⁻¹+((2:ℝ)^T)⁻¹))
    {C w : ℝ} (hC : 0 < C) (hMK : FiniteMK 3 C)
    (hw : 0 < w) (hw1 : w ≤ 1)
    (hresolve : countingResolution source.K (physicalPotentialLip q source.K)*ζ ≤ w) :
    ∃ (g : ℤ) (β : Bool) (G : Set Ev), MeasurableSet G ∧
      G ⊆ source.positiveEvents ∩ (source.interceptBin w) ⁻¹' {g} ∩
        parentBranch P0 ⁻¹' {β} ∧
      physicalHeavyFloor ((2:ℝ)^T)⁻¹ (ν.real A) C source.K w d ≤
        (ν.prod volume).real G ∧
      (∀ Q : Set Ev, MeasurableSet Q →
        (∀ k, ((ν.prod volume).restrict source.S) (source.fineState ⁻¹' {k} ∩ Q) ≤
          ENNReal.ofReal ((1:ℝ)/1000000000000) *
            ((ν.prod volume).restrict source.S) (source.fineState ⁻¹' {k})) →
        ∀ L : Set ((Fin 3 → ℤ) × ℤ),
          ((ν.prod volume).restrict G) (source.fineState ⁻¹' L ∩ Q) ≤
            ENNReal.ofReal ((1:ℝ)/1000000) *
              ((ν.prod volume).restrict G) (source.fineState ⁻¹' L)) := by
  classical
  let μ := (ν.prod volume).restrict source.S
  have hμfin : μ univ < ⊤ :=
    lt_of_le_of_lt (original_block_mass_le ν A _ _ source.S hSA)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ν A))
  letI : IsFiniteMeasure μ := ⟨hμfin⟩
  have hE : ∀ᵐ e ∂μ, e ∈ source.positiveEvents := by
    dsimp only [μ]
    rw [← source.positive_events_law]
    exact ae_restrict_mem source.measurable_positiveEvents
  have hEne : source.positiveEvents.Nonempty := by
    by_contra he
    have heq := Set.not_nonempty_iff_eq_empty.mp he
    have hmass := source.positive_events_mass_floor hSA
    rw [heq, measureReal_empty] at hmass
    have hpos : 0 < ((2:ℝ)^T)⁻¹*ν.real A/source.K :=
      div_pos (mul_pos (by positivity) source.reference_prior_pos)
        (by linarith [source.K_two])
    linarith
  obtain ⟨catalogue, hcat⟩ := source.finite_intercept_catalogue hSA hw hw1 hresolve
  have hheavy := physical_source_heavy_bin source hSA hC hMK hw hw1 hresolve
  obtain ⟨g, β, G, hGm, hGsub, hGmass, hratios⟩ :=
    exists_retained_heavy_branch μ source.positiveEvents source.measurable_positiveEvents
      hE hEne (source.interceptBin w) (source.measurable_interceptBin w)
      source.fineState source.measurable_fineState (parentBranch P0)
      (measurable_parentBranch P0) catalogue
      (fun e he => hcat e he.1)
      (fun e he f hf hs => source.intercept_bins_close hSA hw hresolve he.1 hf.1 hs)
      hheavy
  have hGS : G ⊆ source.S := fun e he => (hGsub he).1.1.1
  have hraw : μ.restrict G = (ν.prod volume).restrict G :=
    Measure.restrict_restrict_of_subset hGS
  refine ⟨g, β, G, hGm, hGsub, ?_, ?_⟩
  · have hreal : μ.real G = (ν.prod volume).real G := by
      dsimp only [μ, measureReal_def]
      rw [Measure.restrict_apply hGm, inter_eq_left.mpr hGS]
    rw [hreal] at hGmass
    convert hGmass using 1
    unfold physicalHeavyFloor
    ring
  · intro Q hQ hQcap L
    have hr := hratios Q hQ hQcap L
    have hleft : μ (G ∩ source.fineState ⁻¹' L ∩ Q) =
        (μ.restrict G) (source.fineState ⁻¹' L ∩ Q) := by
      rw [Measure.restrict_apply' hGm]
      congr 1
      ext e
      simp only [mem_inter_iff]
      tauto
    have hright : μ (G ∩ source.fineState ⁻¹' L) =
        (μ.restrict G) (source.fineState ⁻¹' L) := by
      rw [Measure.restrict_apply' hGm, inter_comm]
    rw [hleft, hright, hraw] at hr
    exact hr

end PhysicalSource

end

end Submission.Obl.k4_physical_parent_potential_candidates
