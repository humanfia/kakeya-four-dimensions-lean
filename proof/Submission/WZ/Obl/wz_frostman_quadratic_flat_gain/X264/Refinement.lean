-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.Refinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.Structure
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file Refinement.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set

/-- Balance on a nonempty packet forces the multiplicative error to be at least one. -/
lemma Factored.one_le_error {D b : ℝ} {n p : ℕ} {T : Fin n → Set Space}
    {P : Fin p → Set Space} (hf : Factored D b T P) (hn : 0 < n) : 1 ≤ D := by
  obtain ⟨j, hj⟩ := hf.1 ⟨0, hn⟩
  have hpos : (0 : ℝ) < Set.ncard {i | T i ⊆ P j} := Nat.cast_pos.mpr (hf.count_pos hn j)
  nlinarith [hf.2.1 j j]

lemma ncard_reindex_le {n k : ℕ} (g : Fin k → Fin n) (hg : Function.Injective g)
    (S : Set (Fin n)) : (g ⁻¹' S).ncard ≤ S.ncard := by
  rw [← Set.ncard_image_of_injective (g ⁻¹' S) hg]
  exact Set.ncard_le_ncard (Set.image_preimage_subset g S)

/-- A refinement retaining a controlled fraction of every surviving packet and
of the prism indices preserves all four counting bounds with the same loss. -/
lemma Factored.restrict {D κ b : ℝ} (hD : 0 ≤ D) (hκ : 1 ≤ κ)
    {n p k q : ℕ} {T : Fin n → Set Space} {P : Fin p → Set Space}
    (hf : Factored D b T P) (g : Fin k → Fin n) (h : Fin q → Fin p)
    (hg : Function.Injective g) (hh : Function.Injective h)
    (hcover : ∀ i, ∃ j, T (g i) ⊆ P (h j))
    (hpacket : ∀ j, (Set.ncard {i | T i ⊆ P (h j)} : ℝ) ≤
      κ * Set.ncard {i | T (g i) ⊆ P (h j)})
    (hprisms : (p : ℝ) ≤ κ * q) :
    Factored (D * κ) b (T ∘ g) (P ∘ h) := by
  have hcounts (j : Fin q) :
      (Set.ncard {i | T (g i) ⊆ P (h j)} : ℝ) ≤
        Set.ncard {i | T i ⊆ P (h j)} :=
    Nat.cast_le.mpr (ncard_reindex_le g hg {i | T i ⊆ P (h j)})
  have hDD : D ≤ D * κ := by nlinarith
  refine ⟨hcover, ?_, ?_, ?_, ?_⟩
  · intro j j'
    change (Set.ncard {i | T (g i) ⊆ P (h j)} : ℝ) ≤
      D * κ * Set.ncard {i | T (g i) ⊆ P (h j')}
    calc
      _ ≤ (Set.ncard {i | T i ⊆ P (h j)} : ℝ) := hcounts j
      _ ≤ D * Set.ncard {i | T i ⊆ P (h j')} := hf.2.1 (h j) (h j')
      _ ≤ D * (κ * Set.ncard {i | T (g i) ⊆ P (h j')}) :=
        mul_le_mul_of_nonneg_left (hpacket j') hD
      _ = _ := by ring
  · intro U hU
    change ENNReal.ofReal (Set.ncard {j | P (h j) ⊆ U} : ℝ) ≤
      ENNReal.ofReal (D * κ * q) * volume U
    have hc : (Set.ncard {j | P (h j) ⊆ U} : ℝ) ≤ Set.ncard {j | P j ⊆ U} :=
      Nat.cast_le.mpr (ncard_reindex_le h hh {j | P j ⊆ U})
    calc
      _ ≤ ENNReal.ofReal (Set.ncard {j | P j ⊆ U} : ℝ) := ENNReal.ofReal_le_ofReal hc
      _ ≤ ENNReal.ofReal (D * p) * volume U := hf.2.2.1 U hU
      _ ≤ _ := by
        apply mul_le_mul' _ le_rfl
        apply ENNReal.ofReal_le_ofReal
        nlinarith [mul_le_mul_of_nonneg_left hprisms hD]
  · intro j U hU
    change ENNReal.ofReal (Set.ncard {i | T (g i) ⊆ P (h j) ∧ T (g i) ⊆ U} : ℝ) *
      volume (P (h j)) ≤
      ENNReal.ofReal (D * κ * Set.ncard {i | T (g i) ⊆ P (h j)}) * volume U
    have hc : (Set.ncard {i | T (g i) ⊆ P (h j) ∧ T (g i) ⊆ U} : ℝ) ≤
        Set.ncard {i | T i ⊆ P (h j) ∧ T i ⊆ U} :=
      Nat.cast_le.mpr (ncard_reindex_le g hg {i | T i ⊆ P (h j) ∧ T i ⊆ U})
    calc
      _ ≤ ENNReal.ofReal (Set.ncard {i | T i ⊆ P (h j) ∧ T i ⊆ U} : ℝ) *
          volume (P (h j)) := mul_le_mul' (ENNReal.ofReal_le_ofReal hc) le_rfl
      _ ≤ ENNReal.ofReal (D * Set.ncard {i | T i ⊆ P (h j)}) * volume U :=
        hf.2.2.2.1 (h j) U hU
      _ ≤ _ := by
        apply mul_le_mul' _ le_rfl
        apply ENNReal.ofReal_le_ofReal
        nlinarith [mul_le_mul_of_nonneg_left (hpacket j) hD]
  · intro j U hU
    change ENNReal.ofReal (Set.ncard {j' | P (h j') ⊆ Metric.thickening b (P (h j)) ∧
      P (h j') ⊆ U} : ℝ) * volume (P (h j)) ≤ ENNReal.ofReal (D * κ) * volume U
    have hc : (Set.ncard {j' | P (h j') ⊆ Metric.thickening b (P (h j)) ∧
        P (h j') ⊆ U} : ℝ) ≤
        Set.ncard {j' | P j' ⊆ Metric.thickening b (P (h j)) ∧ P j' ⊆ U} :=
      Nat.cast_le.mpr (ncard_reindex_le h hh
        {j' | P j' ⊆ Metric.thickening b (P (h j)) ∧ P j' ⊆ U})
    calc
      _ ≤ ENNReal.ofReal (Set.ncard {j' | P j' ⊆ Metric.thickening b (P (h j)) ∧
          P j' ⊆ U} : ℝ) * volume (P (h j)) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hc) le_rfl
      _ ≤ ENNReal.ofReal D * volume U := hf.2.2.2.2 (h j) U hU
      _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hDD) le_rfl

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
