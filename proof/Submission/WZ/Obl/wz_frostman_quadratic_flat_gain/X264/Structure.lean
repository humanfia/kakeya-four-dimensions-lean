-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.Structure.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.Basic
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file Structure.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set

/-- A nonempty tube family requires a nonempty covering family. -/
lemma Factored.index_pos {D b : ℝ} {n p : ℕ} {T : Fin n → Set Space}
    {P : Fin p → Set Space} (h : Factored D b T P) (hn : 0 < n) : 0 < p := by
  obtain ⟨j, hj⟩ := h.1 ⟨0, hn⟩
  exact Nat.zero_lt_of_lt j.isLt

/-- Balance rules out unused prisms; this is needed when passing to each packet. -/
lemma Factored.count_pos {D b : ℝ} {n p : ℕ} {T : Fin n → Set Space}
    {P : Fin p → Set Space} (h : Factored D b T P) (hn : 0 < n) (j : Fin p) :
    0 < Set.ncard {i | T i ⊆ P j} := by
  obtain ⟨k, hk⟩ := h.1 ⟨0, hn⟩
  have hkpos : 0 < Set.ncard {i | T i ⊆ P k} := (Set.ncard_pos (Set.toFinite _)).mpr ⟨⟨0, hn⟩, hk⟩
  by_contra hpos
  have hz : Set.ncard {i | T i ⊆ P j} = 0 := Nat.eq_zero_of_not_pos hpos
  have hc := h.2.1 k j
  rw [hz, Nat.cast_zero, mul_zero] at hc
  have hp : (0 : ℝ) < Set.ncard {i | T i ⊆ P k} := Nat.cast_pos.mpr hkpos
  linarith

lemma Factored.occupied {D b : ℝ} {n p : ℕ} {T : Fin n → Set Space}
    {P : Fin p → Set Space} (h : Factored D b T P) (hn : 0 < n) (j : Fin p) :
    ∃ i, T i ⊆ P j := (Set.ncard_pos (Set.toFinite _)).mp (h.count_pos hn j)

/-- The normalization used by the counting constants is monotone in the error. -/
lemma Factored.mono_error {D D' b : ℝ} {n p : ℕ} {T : Fin n → Set Space}
    {P : Fin p → Set Space} (h : Factored D b T P) (hDD' : D ≤ D') :
    Factored D' b T P := by
  refine ⟨h.1, ?_, ?_, ?_, ?_⟩
  · intro j k
    exact (h.2.1 j k).trans (mul_le_mul_of_nonneg_right hDD' (Nat.cast_nonneg _))
  · intro U hU
    exact (h.2.2.1 U hU).trans (mul_le_mul_left
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hDD' (Nat.cast_nonneg _))) _)
  · intro j U hU
    exact (h.2.2.2.1 j U hU).trans (mul_le_mul_left
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hDD' (Nat.cast_nonneg _))) _)
  · intro j U hU
    exact (h.2.2.2.2 j U hU).trans
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal hDD') _)

lemma PrismStructure.mono_error {ζ₂ ζ₃ ζ₃' δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hζ : ζ₃ ≤ ζ₃') {n : ℕ} {T : Fin n → Set Space}
    (h : PrismStructure ζ₂ ζ₃ δ T) : PrismStructure ζ₂ ζ₃' δ T := by
  obtain ⟨a, b, hδa, hab, hb1, p, c, e₁, e₂, e₃, he, hf⟩ := h
  exact ⟨a, b, hδa, hab, hb1, p, c, e₁, e₂, e₃, he,
    hf.mono_error (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hζ))⟩

/-- Every occupied prism must retain most of its volume after restriction to a convex
container holding all its tubes. This statement requires no regularity of the container. -/
lemma Factored.volume_le_container {D b : ℝ} {n p : ℕ} {T : Fin n → Set Space}
    {P : Fin p → Set Space} (h : Factored D b T P) (hn : 0 < n)
    (j : Fin p) {U : Set Space} (hU : Convex ℝ U)
    (hTU : ∀ i, T i ⊆ P j → T i ⊆ U) :
    volume (P j) ≤ ENNReal.ofReal D * volume U := by
  let N : ℕ := Set.ncard {i | T i ⊆ P j}
  have hN : 0 < N := h.count_pos hn j
  have hN0 : 0 < ENNReal.ofReal (N : ℝ) := ENNReal.ofReal_pos.mpr (Nat.cast_pos.mpr hN)
  have hc := h.2.2.2.1 j U hU
  have he : {i | T i ⊆ P j ∧ T i ⊆ U} = {i | T i ⊆ P j} := by
    ext i
    exact ⟨And.left, fun hi => ⟨hi, hTU i hi⟩⟩
  rw [he, ENNReal.ofReal_mul' (Nat.cast_nonneg _)] at hc
  apply (ENNReal.mul_le_mul_iff_right hN0.ne' ENNReal.ofReal_ne_top).mp
  simpa only [N, mul_assoc, mul_left_comm] using hc

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
