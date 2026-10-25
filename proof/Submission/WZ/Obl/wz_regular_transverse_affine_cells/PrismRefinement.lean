-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.PrismRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.CombinedRefinement
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.DyadicPrisms
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Indexing

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open Module MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_balanced_cluster_cover

lemma regularity_cost_bound (K : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    ENNReal.ofReal (512 * h) * (1 + 1000 * (K + 1 : ℕ) : ℝ≥0∞) +
      2304 * ENNReal.ofReal h ≤ ENNReal.ofReal (1000000 * (K + 1 : ℕ) * h) := by
  have he : (1 + 1000 * (K + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (1 + 1000 * (K + 1 : ℕ) : ℝ) := by
    rw [ENNReal.ofReal_add (by norm_num) (by positivity),
      ENNReal.ofReal_mul (by norm_num)]
    push_cast
    rw [ENNReal.ofReal_add (by positivity) (by norm_num)]
    norm_num
  rw [he, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_ofNat 2304,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  push_cast
  nlinarith

/-- The data retained by one simultaneous regularity and angular refinement. -/
structure PrismRefinement {ι : Type*} (I : Finset ι) (a b θ h : ℝ) (K : ℕ)
    (c : ι → E) (u : ι → OrthonormalBasis (Fin 3) ℝ E) (Y : ι → Set E) where
  core : ι → Set E
  narrow : ι → Set E
  labels : Finset Angular.Label
  region : Angular.Label → Set E
  core_measurable : ∀ i ∈ I, MeasurableSet (core i)
  narrow_measurable : ∀ i ∈ I, MeasurableSet (narrow i)
  core_subset : ∀ i ∈ I, core i ⊆ Y i
  narrow_subset : ∀ i ∈ I, narrow i ⊆ Y i
  disjoint_parts : Disjoint (⋃ i ∈ I, core i) (⋃ i ∈ I, narrow i)
  transverse : ∀ p, (∃ i ∈ I, p ∈ core i) → ∃ i ∈ I, ∃ j ∈ I,
    p ∈ core i ∧ p ∈ core j ∧ θ ≤ a / b + min ‖u i 0 - u j 0‖ ‖u i 0 + u j 0‖
  core_density : ∀ i ∈ I, (core i).Nonempty →
    ENNReal.ofReal h * volume (prism a b (c i) (u i)) ≤ volume (core i)
  core_regular : ∀ i ∈ I, ∀ p ∈ core i, ∀ r : ℝ, a ≤ r → r ≤ 1 →
    ENNReal.ofReal h * volume (prism a b (c i) (u i) ∩ ball p r) ≤ volume (core i ∩ ball p r)
  region_measurable : ∀ ℓ, MeasurableSet (region ℓ)
  region_disjoint : Pairwise (fun ℓ ℓ' => Disjoint (region ℓ) (region ℓ'))
  narrow_cover : ∀ i ∈ I, narrow i ⊆ ⋃ ℓ ∈ labels, region ℓ
  narrow_density : ∀ i ∈ I, ∀ ℓ ∈ labels, (narrow i ∩ region ℓ).Nonempty →
    ENNReal.ofReal h * volume (prism a b (c i) (u i)) ≤ volume (narrow i ∩ region ℓ)
  narrow_whole : ∀ i ∈ I, ∀ ℓ, (narrow i ∩ region ℓ).Nonempty →
    ‖W θ ℓ.1‖ = 1 ∧ prism a b (c i) (u i) ⊆ slab (innerSL ℝ (W θ ℓ.1)) (θ * ℓ.2) (9 * θ)
  mass : (∑ i ∈ I, volume (Y i)) ≤ (∑ i ∈ I, volume (core i)) +
    (∑ i ∈ I, volume (narrow i)) +
      ENNReal.ofReal (1000000 * (K + 1 : ℕ) * h) * ∑ i ∈ I, volume (prism a b (c i) (u i))

lemma exists_prism_refinement_univ {n : ℕ} (hn : 0 < n) (c : Fin n → E)
    (u : Fin n → OrthonormalBasis (Fin 3) ℝ E) (Y : Fin n → Set E)
    {a b θ h : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) (hθ : 0 < θ) (hh : 0 ≤ h)
    (hPball : ∀ i, prism a b (c i) (u i) ⊆ closedBall (0 : E) 1)
    (hYm : ∀ i, MeasurableSet (Y i)) (hYP : ∀ i, Y i ⊆ prism a b (c i) (u i))
    {K : ℕ} (hK : (1 / 2 : ℝ) ^ K < 2 * a) :
    Nonempty (PrismRefinement Finset.univ a b θ h K c u Y) := by
  let P := fun i => prism a b (c i) (u i)
  have hPm : ∀ i, MeasurableSet (P i) := fun i => prism_measurable _ _ _ _
  have hPc : ∀ i, Convex ℝ (P i) := fun i => prism_convex _ _ _ _
  have hPne : ∀ i, (P i).Nonempty := fun i => ⟨c i, center_mem_prism ha.le (ha.le.trans hab) _ _⟩
  have habpos : 0 ≤ a / b := div_nonneg ha.le (ha.le.trans hab)
  by_cases haθ : a ≤ θ
  · obtain ⟨H, Q, F, V, hHm, hQm, hHY, hQY, hHQ, htr, hHd, hHr, hVm, hVd, hQc, hQd, hQw, hmass⟩ :=
      regular_transverse_or_slabs hn P Y (fun i => u i 0) c hPm hPc hPne
        (fun i => (u i).norm_eq_one _) hYm hYP hPball ha haθ hh
        (fun _ _ hp => hp.1) hK
    refine ⟨{
      core := H, narrow := Q, labels := F, region := V,
      core_measurable := fun i _ => hHm i, narrow_measurable := fun i _ => hQm i,
      core_subset := fun i _ => hHY i, narrow_subset := fun i _ => hQY i,
      disjoint_parts := ?_, transverse := ?_, core_density := fun i _ => hHd i,
      core_regular := fun i _ => hHr i, region_measurable := hVm, region_disjoint := hVd,
      narrow_cover := fun i _ => hQc i, narrow_density := fun i _ => hQd i,
      narrow_whole := fun i _ => hQw i, mass := ?_ }⟩
    · simpa using hHQ
    · intro p hp
      obtain ⟨i, hi, hp⟩ := hp
      obtain ⟨i, j, hpi, hpj, hij⟩ := htr p ⟨i, hp⟩
      exact ⟨i, Finset.mem_univ _, j, Finset.mem_univ _, hpi, hpj, by linarith⟩
    · simpa only [P] using hmass.trans (add_le_add le_rfl
        (mul_le_mul_left (regularity_cost_bound K hh) _))
  · obtain ⟨H, B, hHm, hBm, hHY, hBY, hHB, hHbr, hBnar, hmass, hd, hreg⟩ :=
      regular_broad_core (fun _ _ => True) P Y hPm hPc hYm hYP hPball ha hh hK
    have hBempty : ∀ i, B i = ∅ := by
      intro i
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hBnar p i i hp hp trivial
    have hθab : θ ≤ a / b := by
      rw [le_div_iff₀ (ha.trans_le hab)]
      have hθb : θ * b ≤ θ := by nlinarith
      linarith
    refine ⟨{
      core := H, narrow := fun _ => ∅, labels := ∅, region := fun _ => ∅,
      core_measurable := fun i _ => hHm i, narrow_measurable := fun _ _ => MeasurableSet.empty,
      core_subset := fun i _ => hHY i, narrow_subset := fun _ _ => empty_subset _,
      disjoint_parts := ?_, transverse := ?_, core_density := fun i _ => hd i,
      core_regular := fun i _ => hreg i, region_measurable := fun _ => MeasurableSet.empty,
      region_disjoint := ?_, narrow_cover := fun _ _ => empty_subset _,
      narrow_density := ?_, narrow_whole := ?_, mass := ?_ }⟩
    · simp
    · intro p hp
      obtain ⟨i, hi, hpi⟩ := hp
      exact ⟨i, hi, i, hi, hpi, hpi, hθab.trans
        (le_add_of_nonneg_right (le_min (norm_nonneg _) (norm_nonneg _)))⟩
    · intro i j _
      simp
    · intro i hi ℓ hℓ
      exact False.elim (Finset.notMem_empty _ hℓ)
    · intro i hi ℓ hne
      simp at hne
    · have hcost : ENNReal.ofReal (512 * h) * (1 + 1000 * (K + 1 : ℕ) : ℝ≥0∞) ≤
          ENNReal.ofReal (1000000 * (K + 1 : ℕ) * h) :=
        le_self_add.trans (regularity_cost_bound K hh)
      simpa only [P, hBempty, measure_empty, Finset.sum_const_zero, add_zero] using
        hmass.trans (add_le_add le_rfl (mul_le_mul_left hcost _))

lemma exists_prism_refinement {ι : Type*} (I : Finset ι) (hI : I.Nonempty) (c : ι → E)
    (u : ι → OrthonormalBasis (Fin 3) ℝ E) (Y : ι → Set E)
    {a b θ h : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) (hθ : 0 < θ) (hh : 0 ≤ h)
    (hPball : ∀ i ∈ I, prism a b (c i) (u i) ⊆ closedBall (0 : E) 1)
    (hYm : ∀ i ∈ I, MeasurableSet (Y i)) (hYP : ∀ i ∈ I, Y i ⊆ prism a b (c i) (u i))
    {K : ℕ} (hK : (1 / 2 : ℝ) ^ K < 2 * a) :
    Nonempty (PrismRefinement I a b θ h K c u Y) := by
  obtain ⟨R⟩ := exists_prism_refinement_univ hI.card_pos (fun j => c (enumerate I j))
    (fun j => u (enumerate I j)) (fun j => Y (enumerate I j)) ha hab hb hθ hh
    (fun j => hPball _ (enumerate_mem I j)) (fun j => hYm _ (enumerate_mem I j))
    (fun j => hYP _ (enumerate_mem I j)) hK
  refine ⟨{
    core := extendSets I R.core, narrow := extendSets I R.narrow,
    labels := R.labels, region := R.region,
    core_measurable := ?_, narrow_measurable := ?_, core_subset := ?_, narrow_subset := ?_,
    disjoint_parts := ?_, transverse := ?_, core_density := ?_, core_regular := ?_,
    region_measurable := R.region_measurable, region_disjoint := R.region_disjoint,
    narrow_cover := ?_, narrow_density := ?_, narrow_whole := ?_, mass := ?_ }⟩
  · intro i hi
    obtain ⟨j, rfl⟩ := enumerate_surj I hi
    rw [extendSets_enumerate]
    exact R.core_measurable j (Finset.mem_univ _)
  · intro i hi
    obtain ⟨j, rfl⟩ := enumerate_surj I hi
    rw [extendSets_enumerate]
    exact R.narrow_measurable j (Finset.mem_univ _)
  · intro i hi
    obtain ⟨j, rfl⟩ := enumerate_surj I hi
    rw [extendSets_enumerate]
    exact R.core_subset j (Finset.mem_univ _)
  · intro i hi
    obtain ⟨j, rfl⟩ := enumerate_surj I hi
    rw [extendSets_enumerate]
    exact R.narrow_subset j (Finset.mem_univ _)
  · rw [iUnion_extendSets, iUnion_extendSets]
    simpa using R.disjoint_parts
  · intro p hp
    obtain ⟨i, hi, hpi⟩ := hp
    obtain ⟨j, rfl⟩ := enumerate_surj I hi
    rw [extendSets_enumerate] at hpi
    obtain ⟨k, _, l, _, hpk, hpl, hangle⟩ := R.transverse p ⟨j, Finset.mem_univ _, hpi⟩
    exact ⟨enumerate I k, enumerate_mem I k, enumerate I l, enumerate_mem I l,
      by simpa only [extendSets_enumerate] using hpk,
      by simpa only [extendSets_enumerate] using hpl, hangle⟩
  · intro i hi
    obtain ⟨j, rfl⟩ := enumerate_surj I hi
    rw [extendSets_enumerate]
    exact R.core_density j (Finset.mem_univ _)
  · intro i hi
    obtain ⟨j, rfl⟩ := enumerate_surj I hi
    rw [extendSets_enumerate]
    exact R.core_regular j (Finset.mem_univ _)
  · intro i hi
    obtain ⟨j, rfl⟩ := enumerate_surj I hi
    rw [extendSets_enumerate]
    exact R.narrow_cover j (Finset.mem_univ _)
  · intro i hi
    obtain ⟨j, rfl⟩ := enumerate_surj I hi
    rw [extendSets_enumerate]
    exact R.narrow_density j (Finset.mem_univ _)
  · intro i hi
    obtain ⟨j, rfl⟩ := enumerate_surj I hi
    rw [extendSets_enumerate]
    exact R.narrow_whole j (Finset.mem_univ _)
  · rw [sum_extendSets, sum_extendSets, ← sum_enumerate I (fun i => volume (Y i)),
      ← sum_enumerate I (fun i => volume (prism a b (c i) (u i)))]
    exact R.mass

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
