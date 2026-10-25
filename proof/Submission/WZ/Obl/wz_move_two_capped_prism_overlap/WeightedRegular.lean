-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.WeightedRegular.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.RegularCells
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Definitions
import Submission.WZ.Obl.wz_terminal_grains_restoration.Basic

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, WeightedRegular.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V O)

/-- Regularity relative to convex-body volume can be enforced using any finite
measure of the shading. In particular the retained mass may count fine-tube
incidences rather than just the volume of their union. -/
theorem convex_weighted_regular_at_radius (ν : Measure V)
    {U H : Set V} (hU : Convex ℝ U) (hUm : MeasurableSet U)
    (hUt : TotallyBounded U) (hHm : MeasurableSet H) (hHU : H ⊆ U)
    (hfin : ν H ≠ ⊤) {D r : ℝ} (hD : 0 ≤ D) (hr : 0 < r)
    (hdensity : O D * volume U ≤ ν H) :
    ∃ C : Set V, MeasurableSet C ∧ C ⊆ H ∧
      (1 / 2 : ENNReal) * ν H ≤ ν C ∧
      ∀ p ∈ C, O (D / 16000) * volume (U ∩ ball p r) ≤ ν (C ∩ ball p r) := by
  classical
  obtain ⟨F, hFU, hsum, hcover⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.convex_regular_cells
      hU hUm hUt (r := r / 4) (by positivity)
  let B : V → Set V := fun q => U ∩ closedBall q (2 * (r / 4))
  let t : V → ENNReal := fun q => O (D / 250) * volume (B q)
  have hbudget : ∑ q ∈ F, t q ≤ (1 / 2 : ENNReal) * ν H := by
    change (∑ q ∈ F, O (D / 250) * volume (B q)) ≤ _
    rw [← Finset.mul_sum]
    calc
      _ ≤ O (D / 250) * (125 * volume U) := mul_le_mul' le_rfl hsum
      _ = (1 / 2 : ENNReal) * (O D * volume U) := by
        rw [← mul_assoc, ← mul_assoc]
        congr 1
        change ENNReal.ofReal (D / 250) * 125 = (1 / 2 : ENNReal) * ENNReal.ofReal D
        rw [show (125 : ENNReal) = ENNReal.ofReal (125 : ℝ) by norm_num,
          show (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) by
            norm_num [ENNReal.ofReal_div_of_pos],
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
      _ ≤ _ := mul_le_mul' le_rfl hdensity
  obtain ⟨C, hCm, hCH, hmass, hreg⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.regular_subshading_half ν F B t
      (fun q _ => hUm.inter measurableSet_closedBall) H hHm hfin hbudget
  refine ⟨C, hCm, hCH, hmass, ?_⟩
  intro p hp
  obtain ⟨q, hq, hpB, hBr, hvol⟩ := hcover p (hHU (hCH hp))
  have hnon : (C ∩ B q).Nonempty := ⟨p, hp, hpB⟩
  have hlocal : t q ≤ ν (C ∩ B q) :=
    ((hreg q hq).resolve_left hnon.ne_empty).le
  calc
    O (D / 16000) * volume (U ∩ ball p r) =
        O (D / 250) * (O (1 / 64 : ℝ) * volume (U ∩ ball p (4 * (r / 4)))) := by
      rw [show 4 * (r / 4) = r by ring, ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ D / 250)]
      congr 2
      ring
    _ ≤ O (D / 250) * volume (B q) := mul_le_mul' le_rfl hvol
    _ ≤ ν (C ∩ B q) := hlocal
    _ ≤ ν (C ∩ ball p r) := measure_mono (by
      intro x hx
      refine ⟨hx.1, ?_⟩
      simpa only [show 4 * (r / 4) = r by ring] using (hBr hx.2).2)

/-- A common spatial cut retains half of a packet's incidence mass and makes
that mass regular in the containing convex body. No comparability of the
pointwise multiplicities is assumed. -/
theorem incidence_regular_at_radius {n : ℕ} (W : Fin n → Set V)
    (hW : ∀ i, MeasurableSet (W i)) (hWfin : ∀ i, volume (W i) ≠ ⊤)
    {U : Set V} (hU : Convex ℝ U) (hUm : MeasurableSet U)
    (hUt : TotallyBounded U) (hWU : ∀ i, W i ⊆ U)
    {D r : ℝ} (hD : 0 ≤ D) (hr : 0 < r)
    (hdensity : O D * volume U ≤ ∑ i, volume (W i)) :
    ∃ C : Set V, MeasurableSet C ∧ C ⊆ ⋃ i, W i ∧
      (1 / 2 : ENNReal) * (∑ i, volume (W i)) ≤ ∑ i, volume (W i ∩ C) ∧
      ∀ p ∈ C, O (D / 16000) * volume (U ∩ ball p r) ≤
        ∑ i, volume ((W i ∩ C) ∩ ball p r) := by
  let ν : Measure V := ∑ i, volume.restrict (W i)
  let H : Set V := ⋃ i, W i
  have hH : MeasurableSet H := MeasurableSet.iUnion hW
  have hν (S : Set V) (hS : MeasurableSet S) : ν S = ∑ i, volume (W i ∩ S) := by
    simp only [ν, Measure.finsetSum_apply, Measure.restrict_apply hS]
    simp only [inter_comm]
  have htotal : ν H = ∑ i, volume (W i) := by
    rw [hν H hH]
    apply Finset.sum_congr rfl
    intro i _
    rw [inter_eq_left.mpr (subset_iUnion W i)]
  have hfin : ν H ≠ ⊤ := by
    rw [htotal]
    exact ENNReal.sum_ne_top.mpr fun i _ => hWfin i
  obtain ⟨C, hC, hCH, hkeep, hreg⟩ := convex_weighted_regular_at_radius ν
    hU hUm hUt hH (iUnion_subset hWU) hfin hD hr (htotal.symm ▸ hdensity)
  refine ⟨C, hC, hCH, ?_, ?_⟩
  · rwa [htotal, hν C hC] at hkeep
  · intro p hp
    have hh := hreg p hp
    rw [hν _ (hC.inter measurableSet_ball)] at hh
    simpa only [inter_assoc] using hh

/-- An upper bound for fine multiplicity converts weighted regularity to
physical volume regularity. The required density is stated relative to that
upper bound, so no transfer of unweighted density is implicit. -/
theorem incidence_regular_volume_at_radius {n : ℕ} (W : Fin n → Set V)
    (hW : ∀ i, MeasurableSet (W i)) (hWfin : ∀ i, volume (W i) ≠ ⊤)
    {U : Set V} (hU : Convex ℝ U) (hUm : MeasurableSet U)
    (hUt : TotallyBounded U) (hWU : ∀ i, W i ⊆ U)
    {D m r : ℝ} (hD : 0 ≤ D) (hm : 0 < m) (hr : 0 < r)
    (hcount : ∀ p, ({i | p ∈ W i}.ncard : ℝ) ≤ m)
    (hdensity : O (D * m) * volume U ≤ ∑ i, volume (W i)) :
    ∃ C : Set V, MeasurableSet C ∧ C ⊆ ⋃ i, W i ∧
      (1 / 2 : ENNReal) * (∑ i, volume (W i)) ≤ ∑ i, volume (W i ∩ C) ∧
      ∀ p ∈ C, O (D / 16000) * volume (U ∩ ball p r) ≤ volume (C ∩ ball p r) := by
  classical
  obtain ⟨C, hC, hCW, hkeep, hreg⟩ := incidence_regular_at_radius W hW hWfin
    hU hUm hUt hWU (mul_nonneg hD hm.le) hr hdensity
  refine ⟨C, hC, hCW, hkeep, ?_⟩
  intro p hp
  have hmass_upper : (∑ i, volume ((W i ∩ C) ∩ ball p r)) ≤
      O m * volume (C ∩ ball p r) := by
    have hh := WangZahlLot.Obl.wz_terminal_grains_restoration.sum_measure_le_of_mult_le
      volume Finset.univ (fun i => (W i ∩ C) ∩ ball p r)
      (fun i _ => ((hW i).inter hC).inter measurableSet_ball) m (fun x _ => ?_)
    · have he : (⋃ i ∈ (Finset.univ : Finset (Fin n)), (W i ∩ C) ∩ ball p r) =
          C ∩ ball p r := by
        ext x
        simp only [Finset.mem_univ, iUnion_true, mem_iUnion, mem_inter_iff]
        constructor
        · rintro ⟨i, ⟨_, hxC⟩, hxB⟩
          exact ⟨hxC, hxB⟩
        · rintro ⟨hxC, hxB⟩
          obtain ⟨i, hi⟩ := mem_iUnion.mp (hCW hxC)
          exact ⟨i, ⟨hi, hxC⟩, hxB⟩
      simpa only [he] using hh
    · apply le_trans _ (hcount x)
      apply Nat.cast_le.mpr
      simp only [WangZahlLot.Obl.wz_terminal_grains_restoration.mult,
        Set.ncard_eq_toFinset_card']
      apply Finset.card_le_card
      intro i hi
      have hiW := ((Finset.mem_filter.mp hi).2).1.1
      simpa using hiW
  have hh := (hreg p hp).trans hmass_upper
  have he : O (D * m / 16000) = O m * O (D / 16000) := by
    rw [← ENNReal.ofReal_mul hm.le]
    congr 1
    ring
  rw [he, mul_assoc] at hh
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hm).ne'
    ENNReal.ofReal_ne_top).mp hh

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
