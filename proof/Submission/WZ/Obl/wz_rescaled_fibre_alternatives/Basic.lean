-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal

abbrev Space := EuclideanSpace ℝ (Fin 3)

abbrev tube (d : ℝ) (x v : Space) : Set Space :=
  thickening d (segment ℝ x (x + v))

abbrev slab (u : Space) (t r : ℝ) : Set Space :=
  {p | |inner ℝ u p - t| ≤ r}

abbrev doubled (r : ℝ) (y w : Space) : Set Space :=
  tube (2 * r) (y - (1 / 2 : ℝ) • w) (2 • w)

abbrev ConvexCount (s L : ℝ) {n : ℕ} (P : Fin n → Prop)
    (U : Fin n → Set Space) : Prop :=
  ∀ W, Convex ℝ W →
    ENNReal.ofReal (({i | P i ∧ U i ⊆ W}.ncard : ℝ) * s ^ 2) ≤
      ENNReal.ofReal L * volume W

abbrev SlabBound (D : Set Space) (L : ℝ) {n : ℕ} (P : Fin n → Prop)
    (U : Fin n → Set Space) : Prop :=
  ∀ u t r, ‖u‖ = 1 → 0 < r →
    ENNReal.ofReal ({i | P i ∧ U i ⊆ D ∩ slab u t r}.ncard : ℝ) * volume D ≤
      ENNReal.ofReal (L * ({i | P i}.ncard : ℝ)) * volume (D ∩ slab u t r)

lemma tube_convex (d : ℝ) (x v : Space) : Convex ℝ (tube d x v) :=
  (convex_segment x (x + v)).thickening d

lemma tube_measurable (d : ℝ) (x v : Space) : MeasurableSet (tube d x v) :=
  isOpen_thickening.measurableSet

lemma segment_subset_doubled (y w : Space) :
    segment ℝ y (y + w) ⊆ segment ℝ (y - (1 / 2 : ℝ) • w)
      (y - (1 / 2 : ℝ) • w + 2 • w) := by
  intro p hp
  rw [segment_eq_image'] at hp ⊢
  obtain ⟨t, ht, rfl⟩ := hp
  refine ⟨(t + 1 / 2) / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
  module

lemma tube_subset_doubled {r : ℝ} (hr : 0 ≤ r) (y w : Space) :
    tube r y w ⊆ doubled r y w := by
  exact (thickening_mono (by linarith : r ≤ 2 * r) _).trans
    (thickening_subset_of_subset _ (segment_subset_doubled y w))

lemma convexCount_mono {s L L' : ℝ} {n : ℕ} {P : Fin n → Prop}
    {U : Fin n → Set Space} (hLL' : L ≤ L') (h : ConvexCount s L P U) :
    ConvexCount s L' P U := by
  intro W hW
  exact (h W hW).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hLL') _)

lemma slabBound_mono {D : Set Space} {L L' : ℝ} {n : ℕ}
    {P : Fin n → Prop} {U : Fin n → Set Space} (hLL' : L ≤ L')
    (h : SlabBound D L P U) : SlabBound D L' P U := by
  intro u t r hu hr
  exact (h u t r hu hr).trans (mul_le_mul_left
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hLL' (Nat.cast_nonneg _))) _)

lemma count_subfamily {n m : ℕ} (j : Fin m → Fin n) (hj : Function.Injective j)
    (P : Fin n → Prop) : {i | P (j i)}.ncard ≤ {i | P i}.ncard := by
  exact Set.ncard_le_ncard_of_injOn j (fun _ h => h) hj.injOn

lemma convexCount_subfamily {s L : ℝ} {n m : ℕ} (j : Fin m → Fin n)
    (hj : Function.Injective j) {U : Fin n → Set Space}
    (h : ConvexCount s L (fun _ => True) U) :
    ConvexCount s L (fun _ => True) (U ∘ j) := by
  intro W hW
  have hc := count_subfamily j hj (fun i => U i ⊆ W)
  simp only [ConvexCount, true_and] at h ⊢
  exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr hc) (sq_nonneg s))).trans (h W hW)

abbrev Admissible (d η M L : ℝ) {n : ℕ} (x v : Fin n → Space)
    (Y : Fin n → Set Space) : Prop :=
  0 < n ∧
  (∀ i, ‖v i‖ = 1 ∧ tube d (x i) (v i) ⊆ ball 0 1 ∧ MeasurableSet (Y i) ∧ Y i ⊆ tube d (x i) (v i)) ∧
  (∀ i j, i ≠ j → volume (tube d (x i) (v i) ∩ tube d (x j) (v j)) ≤
    (1 / 2 : ENNReal) * volume (tube d (x i) (v i))) ∧
  ENNReal.ofReal (d ^ η * n * d ^ 2) ≤ ∑ i, volume (Y i) ∧
  ConvexCount d M (fun _ => True) (fun i => tube d (x i) (v i)) ∧
  ∀ u t r, ‖u‖ = 1 → 0 < r →
    ENNReal.ofReal ({i | tube d (x i) (v i) ⊆ ball 0 1 ∩ slab u t r}.ncard : ℝ) ≤
      ENNReal.ofReal (L * n) * volume (ball (0 : Space) 1 ∩ slab u t r)

abbrev Fibre (r s η : ℝ) (y w : Space) {n : ℕ} (x v : Fin n → Space)
    (Y : Fin n → Set Space) : Prop :=
  0 < n ∧
  (∀ i, ‖v i‖ = 1 ∧ tube s (x i) (v i) ⊆ tube r y w ∧
    MeasurableSet (Y i) ∧ Y i ⊆ tube s (x i) (v i)) ∧
  ENNReal.ofReal ((s / r) ^ η * n * s ^ 2) ≤ ∑ i, volume (Y i) ∧
  ConvexCount s ((s / r) ^ (-η)) (fun _ => True) (fun i => tube s (x i) (v i)) ∧
  SlabBound (doubled r y w) ((s / r) ^ (-η)) (fun _ => True) (fun i => tube s (x i) (v i))

lemma admissible_mono {d θ η M M' L L' : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space} (hd : 0 < d) (hd1 : d ≤ 1)
    (hθη : θ ≤ η) (hMM' : M ≤ M') (hLL' : L ≤ L') (h : Admissible d θ M L x v Y) :
    Admissible d η M' L' x v Y := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_, convexCount_mono hMM' h.2.2.2.2.1, ?_⟩
  · exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hd hd1 hθη)
        (Nat.cast_nonneg n)) (sq_nonneg d))).trans h.2.2.2.1
  · intro u t r hu hr
    exact (h.2.2.2.2.2 u t r hu hr).trans (mul_le_mul_left
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hLL' (Nat.cast_nonneg n))) _)

end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
