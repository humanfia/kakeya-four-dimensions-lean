-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.WeightedCut.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BadIncidences

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, WeightedCut.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory

/-- The loss is measured separately for each object. This permits the measure
of prism `j` to count precisely the fine incidences assigned to that prism. -/
theorem heterogeneous_remove_bad_incidences {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (ν : Fin n → Measure Ω) (H : Fin n → Set Ω)
    (R : Fin n → Fin n → Prop) (t : Fin n → ENNReal)
    (hHm : ∀ i, MeasurableSet (H i)) (hfin : ∀ i, ν i (H i) ≠ ⊤)
    (ht : ∀ i, t i ≤ (1 / 2 : ENNReal) * ν i (H i)) :
    (∃ (i : Fin n) (A : Set Ω), MeasurableSet A ∧ A ⊆ H i ∧ t i ≤ ν i A ∧
      ∀ p ∈ A, ∃ j, R i j ∧ p ∈ H j) ∨
    (∃ G : Fin n → Set Ω,
      (∀ i, MeasurableSet (G i) ∧ G i ⊆ H i ∧
        (1 / 2 : ENNReal) * ν i (H i) ≤ ν i (G i)) ∧
      ∀ i j p, p ∈ G i → p ∈ G j → ¬ R i j) := by
  classical
  let B (i : Fin n) : Set Ω := {p | ∃ j, R i j ∧ p ∈ H j}
  have hBm (i : Fin n) : MeasurableSet (B i) := by
    have he : B i = ⋃ j, ⋃ (_ : R i j), H j := by ext p; simp [B]
    rw [he]
    exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => hHm j
  by_cases hb : ∃ i, t i ≤ ν i (H i ∩ B i)
  · obtain ⟨i, hi⟩ := hb
    exact Or.inl ⟨i, H i ∩ B i, (hHm i).inter (hBm i), inter_subset_left,
      hi, fun _ hp => hp.2⟩
  · refine Or.inr ⟨fun i => H i \ B i, ?_, ?_⟩
    · intro i
      refine ⟨(hHm i).diff (hBm i), sdiff_subset, ?_⟩
      have hsmall : ν i (H i ∩ B i) ≤ (1 / 2 : ENNReal) * ν i (H i) :=
        (not_le.mp (fun hi => hb ⟨i, hi⟩)).le.trans (ht i)
      exact WangZahlLot.Obl.wz_clustered_cover_volume_gain.half_mass_after_loss
        (hfin i) (measure_sdiff_add_inter (H i) (hBm i)).ge hsmall
    · intro i j p hi hj hij
      exact hi.2 ⟨j, hij, hj.1⟩

/-- A weighted bad set has ordinary density once the object's measure is
bounded by a multiple of volume. No lower pointwise multiplicity is needed. -/
theorem dominated_remove_bad_incidences {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (ν : Fin n → Measure Ω)
    (H U : Fin n → Set Ω) (R : Fin n → Fin n → Prop)
    (m : Fin n → ℝ) {D : ℝ} (hD : 0 ≤ D) (hm : ∀ i, 0 < m i)
    (hHm : ∀ i, MeasurableSet (H i)) (hfin : ∀ i, ν i (H i) ≠ ⊤)
    (hdom : ∀ i A, MeasurableSet A → ν i A ≤ ENNReal.ofReal (m i) * μ A)
    (hdense : ∀ i, ENNReal.ofReal (D * m i) * μ (U i) ≤ ν i (H i)) :
    (∃ (i : Fin n) (A : Set Ω), MeasurableSet A ∧ A ⊆ H i ∧
      ENNReal.ofReal (D / 2) * μ (U i) ≤ μ A ∧
      ∀ p ∈ A, ∃ j, R i j ∧ p ∈ H j) ∨
    (∃ G : Fin n → Set Ω,
      (∀ i, MeasurableSet (G i) ∧ G i ⊆ H i ∧
        (1 / 2 : ENNReal) * ν i (H i) ≤ ν i (G i)) ∧
      ∀ i j p, p ∈ G i → p ∈ G j → ¬ R i j) := by
  let t (i : Fin n) := ENNReal.ofReal (D * m i / 2) * μ (U i)
  have ht (i : Fin n) : t i ≤ (1 / 2 : ENNReal) * ν i (H i) := by
    calc
      _ = (1 / 2 : ENNReal) * (ENNReal.ofReal (D * m i) * μ (U i)) := by
        dsimp [t]
        rw [← mul_assoc]
        congr 1
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num [div_eq_mul_inv, mul_comm]
      _ ≤ _ := mul_le_mul' le_rfl (hdense i)
  rcases heterogeneous_remove_bad_incidences ν H R t hHm hfin ht with hbad | hgood
  · obtain ⟨i, A, hA, hAH, hmass, hrel⟩ := hbad
    refine Or.inl ⟨i, A, hA, hAH, ?_, hrel⟩
    have hh := hmass.trans (hdom i A hA)
    have he : ENNReal.ofReal (D * m i / 2) =
        ENNReal.ofReal (m i) * ENNReal.ofReal (D / 2) := by
      rw [← ENNReal.ofReal_mul (hm i).le]
      congr 1
      ring
    change ENNReal.ofReal (D * m i / 2) * μ (U i) ≤ _ at hh
    rw [he, mul_assoc] at hh
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr (hm i)).ne'
      ENNReal.ofReal_ne_top).mp hh
  · exact Or.inr hgood

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
