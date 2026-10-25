/-
Adapted from: here:o227 (session x0786), OutputReferences.lean and
PaletteCount.lean, commit26350c83. Original-reference palette transfer
through finite observation menus and subsequent light-state pruning.
-/
import Mathlib
import Submission.Lib.K4ReferencePruning
import Submission.Lib.K4OutputReferenceMenus.WindowCaps

namespace Submission.Lib.K4OutputReferenceMenus

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Each output state is charged the full earlier weight of every history
whose finite observation menu contains it. -/
def outputReferenceWeight {J I : Type*} [Fintype J]
    (menus : J → Finset I) (w : J → ℝ≥0∞) (i : I) : ℝ≥0∞ := by
  classical
  exact ∑ j, if i ∈ menus j then w j else 0

/-- A bounded number of observations per history bounds the total original
reference budget of every finite output table. -/
theorem output_reference_budget {J I : Type*} [Fintype J]
    (menus : J → Finset I) (w : J → ℝ≥0∞) (D : ℕ)
    (hcard : ∀ j, (menus j).card ≤ D) (F : Finset I) :
    ∑ i ∈ F, outputReferenceWeight menus w i ≤ (D : ℝ≥0∞) * ∑ j, w j := by
  classical
  have hper (j : J) :
      (∑ i ∈ F, if i ∈ menus j then w j else 0) ≤ (D : ℝ≥0∞) * w j := by
    have hsub : F.filter (fun i => i ∈ menus j) ⊆ menus j := by
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    have hc : ((F.filter (fun i => i ∈ menus j)).card : ℝ≥0∞) ≤ D := by
      exact_mod_cast (Finset.card_le_card hsub).trans (hcard j)
    calc
      _ = ((F.filter (fun i => i ∈ menus j)).card : ℝ≥0∞) * w j := by
        rw [← Finset.sum_filter]
        simp
      _ ≤ _ := mul_le_mul' hc le_rfl
  calc
    _ = ∑ j, ∑ i ∈ F, if i ∈ menus j then w j else 0 := by
      simp only [outputReferenceWeight]
      rw [Finset.sum_comm]
    _ ≤ ∑ j, (D : ℝ≥0∞) * w j := Finset.sum_le_sum (fun j _ => hper j)
    _ = _ := (Finset.mul_sum ..).symm

theorem output_reference_total_budget {J I : Type*} [Fintype J]
    (menus : J → Finset I) (w : J → ℝ≥0∞) (D : ℕ)
    (hcard : ∀ j, (menus j).card ≤ D) :
    ∑' i, outputReferenceWeight menus w i ≤ (D : ℝ≥0∞) * ∑ j, w j := by
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le (fun F => output_reference_budget menus w D hcard F)

/-- Earlier palette numerators survive any later restriction. Charging each
new output state to its compatible earlier histories restores the bound
with the new reference weight, before deleting light output states. -/
theorem output_reference_palette_cap {Ω J I V : Type*}
    [MeasurableSpace Ω] [MeasurableSpace V] [Fintype J]
    (μ θ : Measure Ω) (hθ : θ ≤ μ) (E : J → Set Ω)
    (state : Ω → I) (control : Ω → V) (π : Measure V)
    (menus : J → Finset I) (w : J → ℝ≥0∞) (C : ℝ≥0∞)
    (hcover : ∀ᵐ p ∂θ, ∃ j, p ∈ E j)
    (hmenu : ∀ᵐ p ∂θ, ∀ j, p ∈ E j → state p ∈ menus j)
    (hcap : ∀ j (A : Set V), MeasurableSet A →
      μ {p | p ∈ E j ∧ control p ∈ A} ≤ C * w j * π A)
    (i : I) (A : Set V) (hA : MeasurableSet A) :
    θ {p | state p = i ∧ control p ∈ A} ≤
      C * outputReferenceWeight menus w i * π A := by
  classical
  let Q : Finset J := Finset.univ.filter (fun j => i ∈ menus j)
  have hsub : {p | state p = i ∧ control p ∈ A} ≤ᵐ[θ]
      ⋃ j ∈ Q, {p | p ∈ E j ∧ control p ∈ A} := by
    filter_upwards [hcover, hmenu] with p hp hm hi
    obtain ⟨j, hj⟩ := hp
    have hmem : j ∈ Q := by
      simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa only [hi.1] using hm j hj
    exact mem_biUnion hmem ⟨hj, hi.2⟩
  calc
    _ ≤ θ (⋃ j ∈ Q, {p | p ∈ E j ∧ control p ∈ A}) := measure_mono_ae hsub
    _ ≤ ∑ j ∈ Q, θ {p | p ∈ E j ∧ control p ∈ A} :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Q, C * w j * π A :=
      Finset.sum_le_sum (fun j _ => (hθ _).trans (hcap j A hA))
    _ = C * (∑ j ∈ Q, w j) * π A := by
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ = _ := by simp only [Q, Finset.sum_filter, outputReferenceWeight]

/-- The renewed output-state palette ceiling, together with its original
reference deletion budget. This performs pruning only after changing the
observations. -/
theorem exists_pruned_output_palette {Ω J I V : Type*}
    [MeasurableSpace Ω] [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I]
    [MeasurableSpace V] [Fintype J]
    (μ θ : Measure Ω) (hθ : θ ≤ μ) (E : J → Set Ω)
    (state : Ω → I) (hstate : Measurable state) (control : Ω → V) (π : Measure V)
    (menus : J → Finset I) (w : J → ℝ≥0∞) (C δ : ℝ≥0∞)
    (hδ0 : δ ≠ 0) (hδtop : δ ≠ ⊤) (D : ℕ)
    (hcard : ∀ j, (menus j).card ≤ D)
    (hcover : ∀ᵐ p ∂θ, ∃ j, p ∈ E j)
    (hmenu : ∀ᵐ p ∂θ, ∀ j, p ∈ E j → state p ∈ menus j)
    (hcap : ∀ j (A : Set V), MeasurableSet A →
      μ {p | p ∈ E j ∧ control p ∈ A} ≤ C * w j * π A) :
    ∃ θ' : Measure Ω, θ' ≤ θ ∧
      θ Set.univ ≤ θ' Set.univ + δ * ((D : ℝ≥0∞) * ∑ j, w j) ∧
      ∀ i (A : Set V), MeasurableSet A →
        θ' {p | state p = i ∧ control p ∈ A} ≤
          (C / δ) * θ' (state ⁻¹' {i}) * π A := by
  let wout := outputReferenceWeight menus w
  let θ' := θ.restrict (Submission.Lib.K4ReferencePruning.referenceKeep θ state wout δ)
  have hnew := output_reference_palette_cap μ θ hθ E state control π menus w C hcover hmenu hcap
  refine ⟨θ', Measure.restrict_le_self, ?_, ?_⟩
  · have h := Submission.Lib.K4ReferencePruning.reference_pruning_mass_budget
      θ state hstate wout δ
    exact h.trans (add_le_add le_rfl (mul_le_mul' le_rfl
      (output_reference_total_budget menus w D hcard)))
  · exact Submission.Lib.K4ReferencePruning.reference_pruned_palette_cap
      θ state hstate control π wout C δ hδ0 hδtop hnew

end

end Submission.Lib.K4OutputReferenceMenus

namespace Submission.Lib.K4OutputReferenceMenus

open Set MeasureTheory
open scoped ENNReal

noncomputable def paletteStates {V I : Type*} (S : Finset I) (C : I → Set V)
    (v : V) : Finset I := by
  classical
  exact S.filter (fun i => v ∈ C i)

/-- Count output states by integrating their compatible-velocity lists
against the original probability palette. -/
theorem palette_support_count {V I : Type*} [MeasurableSpace V]
    (π : Measure V) [IsProbabilityMeasure π] (S : Finset I)
    (C : I → Set V) (hC : ∀ i ∈ S, MeasurableSet (C i))
    (K L : ℝ≥0∞) (hfloor : ∀ i ∈ S, 1 ≤ K * π (C i))
    (hlist : ∀ v, ((paletteStates S C v).card : ℝ≥0∞) ≤ L) :
    (S.card : ℝ≥0∞) ≤ K * L := by
  classical
  have hsum : ∑ i ∈ S, π (C i) ≤ L := by
    calc
      _ = ∫⁻ v, ∑ i ∈ S, (C i).indicator (fun _ => (1 : ℝ≥0∞)) v ∂π := by
        rw [lintegral_finsetSum]
        · apply Finset.sum_congr rfl
          intro i hi
          rw [lintegral_indicator (hC i hi)]
          simp
        · intro i hi
          exact measurable_const.indicator (hC i hi)
      _ ≤ ∫⁻ _v, L ∂π := by
        apply lintegral_mono
        intro v
        have hid : (∑ i ∈ S, (C i).indicator (fun _ => (1 : ℝ≥0∞)) v) =
            ((S.filter (fun i => v ∈ C i)).card : ℝ≥0∞) := by
          simpa only [Set.indicator_apply] using
            (Finset.sum_boole (R := ℝ≥0∞) (fun i => v ∈ C i) S)
        change (∑ i ∈ S, (C i).indicator (fun _ => (1 : ℝ≥0∞)) v) ≤ L
        rw [hid]
        exact hlist v
      _ = L := by simp
  calc
    (S.card : ℝ≥0∞) = ∑ _i ∈ S, (1 : ℝ≥0∞) := by simp
    _ ≤ ∑ i ∈ S, K * π (C i) := Finset.sum_le_sum hfloor
    _ = K * ∑ i ∈ S, π (C i) := (Finset.mul_sum ..).symm
    _ ≤ K * L := mul_le_mul' le_rfl hsum

/-- Positive original state mass and a relative palette ceiling supply the
compatibility floor. No individual surviving mass is normalized or selected. -/
theorem palette_support_count_of_caps {Ω V I : Type*}
    [MeasurableSpace Ω] [MeasurableSpace V]
    (μ : Measure Ω) [IsFiniteMeasure μ] (π : Measure V) [IsProbabilityMeasure π]
    (state : Ω → I) (control : Ω → V)
    (S : Finset I) (C : I → Set V) (hC : ∀ i ∈ S, MeasurableSet (C i))
    (K L : ℝ≥0∞)
    (hcap : ∀ i ∈ S,
      μ {p | state p = i ∧ control p ∈ C i} ≤ K * μ {p | state p = i} * π (C i))
    (hcompat : ∀ᵐ p ∂μ, control p ∈ C (state p))
    (hpositive : ∀ i ∈ S, μ {p | state p = i} ≠ 0)
    (hlist : ∀ v, ((paletteStates S C v).card : ℝ≥0∞) ≤ L) :
    (S.card : ℝ≥0∞) ≤ K * L := by
  apply palette_support_count π S C hC K L ?_ hlist
  intro i hi
  have heq : μ {p | state p = i ∧ control p ∈ C i} = μ {p | state p = i} := by
    apply measure_congr
    filter_upwards [hcompat] with p hp
    apply propext
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h, by simpa only [h] using hp⟩
  have hmass := hcap i hi
  rw [heq] at hmass
  calc
    1 = (μ {p | state p = i})⁻¹ * μ {p | state p = i} :=
      (ENNReal.inv_mul_cancel (hpositive i hi) (measure_ne_top _ _)).symm
    _ ≤ (μ {p | state p = i})⁻¹ *
        (K * μ {p | state p = i} * π (C i)) := mul_le_mul' le_rfl hmass
    _ = K * π (C i) := by
      rw [show K * μ {p | state p = i} * π (C i) =
        μ {p | state p = i} * (K * π (C i)) by ac_rfl,
        ← mul_assoc, ENNReal.inv_mul_cancel (hpositive i hi) (measure_ne_top _ _), one_mul]

end Submission.Lib.K4OutputReferenceMenus
