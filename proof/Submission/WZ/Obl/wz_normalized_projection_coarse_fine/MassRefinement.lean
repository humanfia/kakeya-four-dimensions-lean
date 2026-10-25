-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.MassRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.MassSelection
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.LightRefinement

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

noncomputable section

/-- Restrict a shading to a finite collection of indices. -/
def restrictShading {n : ℕ} (S : Finset (Fin n)) (Y : Fin n → Set Space) :
    Fin n → Set Space := fun i => if i ∈ S then Y i else ∅

lemma restrictShading_subset {n : ℕ} (S : Finset (Fin n)) (Y : Fin n → Set Space) (i : Fin n) :
    restrictShading S Y i ⊆ Y i := by
  classical
  simp only [restrictShading]
  split_ifs <;> simp

lemma sum_restrictShading {n : ℕ} (S : Finset (Fin n)) (Y : Fin n → Set Space) :
    (∑ i, volume (restrictShading S Y i)) = ∑ i ∈ S, volume (Y i) := by
  classical
  simp only [restrictShading, apply_ite volume, measure_empty]
  simpa only [Finset.univ_inter] using Finset.sum_ite_mem Finset.univ S (fun i => volume (Y i))

lemma sum_restrictShading_inter {n : ℕ} (S : Finset (Fin n)) (Y : Fin n → Set Space)
    (A : Set Space) :
    (∑ i, volume (restrictShading S Y i ∩ A)) = ∑ i ∈ S, volume (Y i ∩ A) := by
  classical
  have he : (fun i => restrictShading S Y i ∩ A) = restrictShading S (fun i => Y i ∩ A) := by
    funext i
    simp only [restrictShading]
    split_ifs <;> simp
  simp_rw [show ∀ i, restrictShading S Y i ∩ A = restrictShading S (fun i => Y i ∩ A) i from fun i => congrFun he i]
  exact sum_restrictShading S (fun i => Y i ∩ A)

lemma summed_class_bound {n : ℕ} (G : Finset (Finset (Fin n)))
    (hG : (G : Set (Finset (Fin n))).PairwiseDisjoint id)
    (w : Fin n → ℝ≥0∞) {B : ℝ} (hB : 0 ≤ B)
    (hclass : ∀ Q ∈ G, (∑ i ∈ Q, w i) ≤ ENNReal.ofReal (B * Q.card)) :
    (∑ i ∈ G.biUnion id, w i) ≤ ENNReal.ofReal (B * n) := by
  classical
  calc
    _ = ∑ Q ∈ G, ∑ i ∈ Q, w i := (disjoint_class_sum G hG w).symm
    _ ≤ ∑ Q ∈ G, ENNReal.ofReal (B * Q.card) := Finset.sum_le_sum hclass
    _ = ENNReal.ofReal (B * ∑ Q ∈ G, (Q.card : ℝ)) := by
      rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun Q _ => by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (disjoint_class_card G hG) hB)

lemma selected_mass_budget {M W B : ℝ≥0∞} {L : ℕ}
    (hM : M ≤ (2 * (L + 1 : ℝ≥0∞)) * W)
    (hB : (4 * (L + 1 : ℝ≥0∞)) * B ≤ M) : B ≤ W / 2 := by
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
    (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))).mpr
  apply (ENNReal.mul_le_mul_iff_right
    (by positivity : (2 * (L + 1 : ℝ≥0∞)) ≠ 0)
    (by finiteness : (2 * (L + 1 : ℝ≥0∞)) ≠ ⊤)).mp
  calc
    (2 * (L + 1 : ℝ≥0∞)) * (B * 2) = (4 * (L + 1 : ℝ≥0∞)) * B := by ring
    _ ≤ M := hB
    _ ≤ _ := hM

/-- Summable light-mass bounds on disjoint classes give the measurable refinement,
including both the preliminary level-selection loss and the final removal loss. -/
theorem disjoint_light_refinement {n L : ℕ} {f : ℝ → ℝ} (hf : Continuous f)
    (Y : Fin n → Set Space) (hY : ∀ i, MeasurableSet (Y i))
    (hfinite : ∀ i, volume (Y i) ≠ ⊤)
    (G : Finset (Finset (Fin n))) (hG : (G : Set (Finset (Fin n))).PairwiseDisjoint id)
    {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 ≤ B) (α M K : ℝ≥0∞)
    (hmass : M ≤ (2 * (L + 1 : ℝ≥0∞)) * ∑ Q ∈ G, ∑ i ∈ Q, volume (Y i))
    (hremove : (4 * (L + 1 : ℝ≥0∞)) * ENNReal.ofReal (B * n) ≤ M)
    (hretain : (4 * (L + 1 : ℝ≥0∞)) * K ≤ M)
    (hlight : ∀ A : Set (ℝ × ℝ), MeasurableSet A →
      (∀ S : Set (ℝ × ℝ),
        volume ((projection f '' (⋃ i, restrictShading (G.biUnion id) Y i)) ∩ A ∩ S) ≤
          (9 * α) * volume (thickening ρ S)) →
      ∀ Q ∈ G, (∑ i ∈ Q, volume (Y i ∩ projection f ⁻¹' A)) ≤
        ENNReal.ofReal (B * Q.card)) :
    ∃ Z : Fin n → Set Space, (∀ i, MeasurableSet (Z i)) ∧ (∀ i, Z i ⊆ Y i) ∧
      K ≤ ∑ i, volume (Z i) ∧
      α * volume (thickening ρ (projection f '' (⋃ i, Z i))) ≤
        volume (projection f '' (⋃ i, Z i)) := by
  classical
  let S := G.biUnion id
  let Y' := restrictShading S Y
  have hm' : M ≤ (2 * (L + 1 : ℝ≥0∞)) * ∑ i, volume (Y' i) := by
    simpa only [Y', sum_restrictShading, disjoint_class_sum G hG] using hmass
  have hY' (i : Fin n) : MeasurableSet (Y' i) := by
    dsimp [Y', restrictShading]
    split_ifs <;> simp [hY i]
  have hfin' : (∑ i, volume (Y' i)) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro i _
    exact ne_top_of_le_ne_top (hfinite i) (measure_mono (restrictShading_subset S Y i))
  obtain ⟨Z, hZ, hZY, hmassZ, harea⟩ := exists_refinement_of_grid_light_mass hf Y' hY' hfin' hρ α
    (by
      intro A hA hlightA
      change (∑ i, volume (restrictShading S Y i ∩ projection f ⁻¹' A)) ≤ _
      rw [sum_restrictShading_inter]
      exact (summed_class_bound G hG (fun i => volume (Y i ∩ projection f ⁻¹' A)) hB
        (hlight A hA hlightA)).trans (selected_mass_budget hm' hremove))
  exact ⟨Z, hZ, fun i => (hZY i).trans (restrictShading_subset S Y i),
    (selected_mass_budget hm' hretain).trans hmassZ, harea⟩

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
