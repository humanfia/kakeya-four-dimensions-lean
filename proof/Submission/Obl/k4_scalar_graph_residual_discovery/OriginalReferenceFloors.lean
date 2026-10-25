/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file OriginalReferenceFloors.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.AllPieceFloors
import Submission.Obl.k4_scalar_graph_residual_discovery.EntryReferences

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice
open Submission.Obl.k4_crop_angular_finite_tail
open Submission.Obl.k4_scalar_grid_parameter_preparation

namespace Zoom

noncomputable section

/-- Prepare original-state, global-strip, posterior and coefficient-entry
floors in ONE law. Their budgets are derived from the original measures
and the bounded posterior incidence lists, before any world is chosen. -/
theorem prepare_original_reference_floors {σ W Q A V : Type*}
    [Fintype σ]
    [MeasurableSpace W] [MeasurableSingletonClass W] [Countable W]
    [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A] [DecidableEq A]
    [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    (μ oldGraph oldStrip : Measure ScalarIncidence) (θ : Measure ScalarLine) (π : Measure V)
    {ρ H : ℝ} (hρ : 0 < ρ) (hH : 0 ≤ H) (β h Ac : σ → ℝ)
    (hβ : ∀ s, 0 < β s) (hscale : ∀ s, β s ≤ ρ * h s)
    (hh : ∀ s, 0 < h s) (hh₁ : ∀ s, h s ≤ 1) (hAc : ∀ s, 0 < Ac s)
    (state : ScalarIncidence → W) (hstate : Measurable state)
    (strip : σ → ScalarIncidence → Q) (hstrip : ∀ s, Measurable (strip s))
    (post : σ → ScalarIncidence → A × (W × V)) (hpost : ∀ s, Measurable (post s))
    (lists : σ → W × V → Finset A) (D ηstrip ηpost : σ → ℝ≥0∞) (ηstate : ℝ≥0∞)
    (hD : ∀ s wv, ((lists s wv).card : ℝ≥0∞) ≤ D s)
    {E : Set ScalarIncidence} (hE : MeasurableSet E)
    (htime : ∀ p ∈ E, p.2 ∈ Icc (0 : ℝ) 1)
    (hcoeff : ∀ p ∈ E, ∀ e, |p.1.2 e| ≤ H)
    (hfstate : (state '' E).Finite)
    (hfstrip : ∀ s, (strip s '' E).Finite) (hfpost : ∀ s, (post s '' E).Finite)
    (hlisted : ∀ s p, p ∈ E → (post s p).1 ∈ lists s (post s p).2) :
    ∃ R : Set ScalarIncidence, MeasurableSet R ∧ R ⊆ E ∧
      μ (E \ R) ≤
        (ηstate * oldGraph univ +
          ((∑ s, ηstrip s * oldStrip univ) +
            ∑ s, ηpost s * (D s * (oldGraph univ * π univ)))) +
          (∑ s, ENNReal.ofReal ((5000 * 111 ^ 3) / Ac s)) * θ univ ∧
      (∀ w, R ∩ state ⁻¹' {w} = ∅ ∨ ηstate * oldGraph (state ⁻¹' {w}) < μ (R ∩ state ⁻¹' {w})) ∧
      (∀ s q, R ∩ strip s ⁻¹' {q} = ∅ ∨
        ηstrip s * oldStrip (strip s ⁻¹' {q}) < μ (R ∩ strip s ⁻¹' {q})) ∧
      (∀ s e, R ∩ post s ⁻¹' {e} = ∅ ∨
        ηpost s * oldGraph (state ⁻¹' {e.2.1}) * π {e.2.2} < μ (R ∩ post s ⁻¹' {e})) ∧
      ∀ s q b z,
        R ∩ coefficientPhysicalEntry (normalizedCoeff ρ) (parameterPiece ρ (β s) q b) (h s) z = ∅ ∨
        ENNReal.ofReal (h s / Ac s) * θ (parameterPiece ρ (β s) q b) <
          μ (R ∩ coefficientPhysicalEntry (normalizedCoeff ρ) (parameterPiece ρ (β s) q b) (h s) z) := by
  classical
  let P := A × (W × V)
  let I := Unit ⊕ (σ ⊕ σ)
  let T := W ⊕ (Q ⊕ P)
  letI : MeasurableSpace T := ⊤
  letI : MeasurableSingletonClass T := ⟨fun _ => trivial⟩
  let record : I → ScalarIncidence → T
    | .inl _, p => .inl (state p)
    | .inr (.inl s), p => .inr (.inl (strip s p))
    | .inr (.inr s), p => .inr (.inr (post s p))
  let oldW (w : W) := oldGraph (state ⁻¹' {w})
  let old : I → T → ℝ≥0∞
    | .inl _, .inl w => oldW w
    | .inr (.inl s), .inr (.inl q) => oldStrip (strip s ⁻¹' {q})
    | .inr (.inr s), .inr (.inr e) => productEntryReference oldW π (lists s) e
    | _, _ => 0
  let η : I → ℝ≥0∞
    | .inl _ => ηstate
    | .inr (.inl s) => ηstrip s
    | .inr (.inr s) => ηpost s
  let B : I → ℝ≥0∞
    | .inl _ => oldGraph univ
    | .inr (.inl _) => oldStrip univ
    | .inr (.inr s) => D s * (oldGraph univ * π univ)
  have hrecord (i : I) : Measurable (record i) := by
    rcases i with _ | (s | s)
    · exact (measurable_of_countable (Sum.inl : W → T)).comp hstate
    · exact (measurable_of_countable (fun q : Q => (Sum.inr (.inl q) : T))).comp (hstrip s)
    · exact (measurable_of_countable (fun e : P => (Sum.inr (.inr e) : T))).comp (hpost s)
  have hfinite (i : I) : (record i '' E).Finite := by
    rcases i with _ | (s | s)
    · simpa only [image_image, Function.comp_def] using hfstate.image (Sum.inl : W → T)
    · simpa only [image_image, Function.comp_def] using
        (hfstrip s).image (fun q : Q => (Sum.inr (.inl q) : T))
    · simpa only [image_image, Function.comp_def] using
        (hfpost s).image (fun e : P => (Sum.inr (.inr e) : T))
  have hsumW : (∑' w, oldW w) = oldGraph univ := by
    simpa only [oldW, univ_inter] using (measure_eq_tsum_label oldGraph hstate MeasurableSet.univ).symm
  have hsplit (f : T → ℝ≥0∞) : (∑' t, f t) =
      (∑' w : W, f (.inl w)) +
        ((∑' q : Q, f (.inr (.inl q))) + ∑' e : P, f (.inr (.inr e))) := by
    rw [Summable.tsum_sum ENNReal.summable ENNReal.summable]
    congr 1
    exact Summable.tsum_sum ENNReal.summable ENNReal.summable
  have hbudget (i : I) : (∑' t, old i t) ≤ B i := by
    rw [hsplit]
    rcases i with _ | (s | s)
    · simpa only [old, B, tsum_zero, zero_add, add_zero] using hsumW.le
    · have hh := (measure_eq_tsum_label oldStrip (hstrip s) MeasurableSet.univ).symm.le
      simpa only [old, B, tsum_zero, zero_add, add_zero, univ_inter] using hh
    · have hh := sum_productEntryReference_le oldW π (lists s) (D s) (hD s)
      rw [hsumW] at hh
      simpa only [old, B, tsum_zero, zero_add] using hh
  obtain ⟨R, hR, hRE, hmass, hfloors, hentries⟩ := global_entry_and_reference_floors μ θ
    hρ hH β h Ac hβ hscale hh hh₁ hAc record hrecord old η B hbudget hE htime hcoeff hfinite
  have htotal : (∑ i : I, η i * B i) = ηstate * oldGraph univ +
      ((∑ s, ηstrip s * oldStrip univ) + ∑ s, ηpost s * (D s * (oldGraph univ * π univ))) := by
    dsimp only [I]
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [η, B, Fintype.sum_unique]
  have hcellState (w : W) : record (.inl ()) ⁻¹' {(.inl w : T)} = state ⁻¹' {w} := by
    ext p
    change (Sum.inl (state p) : T) = Sum.inl w ↔ state p = w
    exact ⟨Sum.inl.inj, fun h => congrArg Sum.inl h⟩
  have hcellStrip (s : σ) (q : Q) :
      record (.inr (.inl s)) ⁻¹' {(.inr (.inl q) : T)} = strip s ⁻¹' {q} := by
    ext p
    change (Sum.inr (.inl (strip s p)) : T) = Sum.inr (.inl q) ↔ strip s p = q
    exact ⟨fun h => Sum.inl.inj (Sum.inr.inj h),
      fun h => congrArg (fun q : Q => (Sum.inr (.inl q) : T)) h⟩
  have hcellPost (s : σ) (e : P) :
      record (.inr (.inr s)) ⁻¹' {(.inr (.inr e) : T)} = post s ⁻¹' {e} := by
    ext p
    change (Sum.inr (.inr (post s p)) : T) = Sum.inr (.inr e) ↔ post s p = e
    exact ⟨fun h => Sum.inr.inj (Sum.inr.inj h),
      fun h => congrArg (fun e : P => (Sum.inr (.inr e) : T)) h⟩
  rw [htotal] at hmass
  refine ⟨R, hR, hRE, hmass, ?_, ?_, ?_, hentries⟩
  · intro w
    have hh := hfloors (.inl ()) (.inl w)
    rw [hcellState] at hh
    simpa only [old, η, oldW] using hh
  · intro s q
    have hh := hfloors (.inr (.inl s)) (.inr (.inl q))
    rw [hcellStrip] at hh
    simpa only [old, η] using hh
  · intro s e
    have hh := hfloors (.inr (.inr s)) (.inr (.inr e))
    rw [hcellPost] at hh
    simp only [old, η] at hh
    rcases hh with hempty | hfloor
    · exact Or.inl hempty
    · right
      have hpos := ne_of_gt (lt_of_le_of_lt zero_le hfloor)
      obtain ⟨p, hpR, hpe⟩ := nonempty_of_measure_ne_zero hpos
      have hpe' : post s p = e := by simpa only [mem_preimage, mem_singleton_iff] using hpe
      have hlisted' : e.1 ∈ lists s e.2 := by
        simpa only [hpe'] using hlisted s p (hRE hpR)
      simpa only [productEntryReference, ite_eq_left hlisted', oldW, mul_assoc] using hfloor

end

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
