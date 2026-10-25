-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.RelativeIncidence.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.BrushAverage
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.Incidence

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity

open MeasureTheory Set
open WangZahlLot.Obl.wz_extremal_lipschitz_grains
open scoped Classical

/-- Delete points where a selected shading has too little of the original
incidence. The lost mass is at most `theta` times the original mass. -/
theorem relative_incidence_refinement {n : ℕ} {Y Z : Fin n → Set Space}
    (hY : ∀ i, MeasurableSet (Y i)) (hZ : ∀ i, MeasurableSet (Z i))
    (hfin : ∀ i, volume (Y i) ≠ ⊤) (hZY : ∀ i, Z i ⊆ Y i)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    ∃ W : Fin n → Set Space, (∀ i, MeasurableSet (W i) ∧ W i ⊆ Z i) ∧
      shadingMass Z - θ * shadingMass Y ≤ shadingMass W ∧
      ∀ p ∈ ⋃ i, W i, θ * incidence Y p ≤ incidence W p := by
  let G := {p | θ * incidence Y p < incidence Z p}
  have hG : MeasurableSet G := measurableSet_lt
    (measurable_const.mul (measurable_incidence hY)) (measurable_incidence hZ)
  let W := fun i => Z i ∩ G
  let L := fun i => Z i ∩ Gᶜ
  have hZfin : ∀ i, volume (Z i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (hfin i) (measure_mono (hZY i))
  have hLm : ∀ i, MeasurableSet (L i) := fun i => (hZ i).inter hG.compl
  have hLfin : ∀ i, volume (L i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (hZfin i) (measure_mono inter_subset_left)
  have hlow : shadingMass L ≤ θ * shadingMass Y := by
    rw [← integral_incidence hLm hLfin, ← integral_incidence hY hfin, ← integral_const_mul]
    apply integral_mono (integrable_incidence hLm hLfin) ((integrable_incidence hY hfin).const_mul θ)
    intro p
    rw [show incidence L p = Gᶜ.indicator (incidence Z) p from incidence_restrict Z Gᶜ p]
    by_cases hp : p ∈ Gᶜ
    · rw [indicator_of_mem hp]
      exact le_of_not_gt hp
    · rw [indicator_of_notMem hp]
      exact mul_nonneg hθ (incidence_nonneg Y p)
  have heq := shadingMass_restrict_add_compl hZfin hG
  refine ⟨W, fun i => ⟨(hZ i).inter hG, inter_subset_left⟩, ?_, ?_⟩
  · change shadingMass W + shadingMass L = shadingMass Z at heq
    linarith
  · intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    change p ∈ Z i ∩ G at hi
    rw [show incidence W p = G.indicator (incidence Z) p from incidence_restrict Z G p,
      indicator_of_mem hi.2]
    exact le_of_lt hi.2

/-- A cap bound for the original family passes to a refinement retaining a
fixed pointwise fraction of its incidence. -/
theorem broadness_of_relative_incidence {n : ℕ} {Y Z : Fin n → Set Space}
    (v : Fin n → Space) {b θ q : ℝ} (hZY : ∀ i, Z i ⊆ Y i)
    (hrelative : ∀ p ∈ ⋃ i, Z i, θ * incidence Y p ≤ incidence Z p)
    (hq : q ≤ θ / 2)
    (hcap : ∀ p u, ‖u‖ = 1 →
      ({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b}.ncard : ℝ) ≤ q * incidence Y p) :
    ∀ p u, ‖u‖ = 1 →
      ({i | p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b}.ncard : ℝ) ≤
        (1 / 2 : ℝ) * ({i | p ∈ Z i}.ncard : ℝ) := by
  intro p u hu
  rw [← incidence_eq_ncard]
  by_cases hp : p ∈ ⋃ i, Z i
  · have hsub : {i | p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b} ⊆
        {i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b} :=
      fun i hi => ⟨hZY i hi.1, hi.2⟩
    have hmono : ({i | p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b}.ncard : ℝ) ≤
        ({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b}.ncard : ℝ) := by
      exact_mod_cast Set.ncard_mono hsub
    have hq' := mul_le_mul_of_nonneg_right hq (incidence_nonneg Y p)
    have hrel := hrelative p hp
    linarith [hmono.trans (hcap p u hu)]
  · have hzero : {i | p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hp (mem_iUnion.mpr ⟨i, hi.1⟩)
    rw [hzero, Set.ncard_empty, Nat.cast_zero, incidence_eq_zero_of_notMem Z hp]
    norm_num

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity
