-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.Counts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Basic

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory

/-- Passing to an injectively indexed subfamily cannot increase any containment count. -/
theorem subfamily_count {n k : ℕ} (g : Fin k → Fin n) (hg : Function.Injective g)
    (P : Fin n → Prop) :
    Set.ncard {i | P (g i)} ≤ Set.ncard {i | P i} := by
  rw [← Set.ncard_image_of_injective {i | P (g i)} hg]
  exact Set.ncard_le_ncard (by rintro _ ⟨i, hi, rfl⟩; exact hi)

theorem convexCount_subfamily {δ m : ℝ} {n k : ℕ} {x v : Fin n → Space}
    (g : Fin k → Fin n) (hg : Function.Injective g) (h : ConvexCount δ m x v) :
    ConvexCount δ m (fun i => x (g i)) (fun i => v (g i)) := by
  intro U hU
  apply le_trans (ENNReal.ofReal_le_ofReal _) (h U hU)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg δ)
  exact_mod_cast subfamily_count g hg (fun i => tube δ (x i) (v i) ⊆ U)

theorem convexCount_mono {δ m M : ℝ} {n : ℕ} {x v : Fin n → Space}
    (hm : m ≤ M) (h : ConvexCount δ m x v) : ConvexCount δ M x v := by
  intro U hU
  apply (h U hU).trans
  gcongr

/-- The Frostman slab constant increases by the reciprocal fraction retained. -/
theorem slabCount_subfamily {δ l L : ℝ} {n k : ℕ} {x v : Fin n → Space}
    (g : Fin k → Fin n) (hg : Function.Injective g)
    (hsize : l * n ≤ L * k) (h : SlabCount δ l x v) :
    SlabCount δ L (fun i => x (g i)) (fun i => v (g i)) := by
  intro u t r hu hr
  calc
    _ ≤ ENNReal.ofReal (Set.ncard {i | tube δ (x i) (v i) ⊆
        (unitBall ∩ {p | |inner ℝ u p - t| ≤ r})} : ℝ) :=
      ENNReal.ofReal_le_ofReal (by
        exact_mod_cast subfamily_count g hg
          (fun i => tube δ (x i) (v i) ⊆ (unitBall ∩ {p | |inner ℝ u p - t| ≤ r})))
    _ ≤ ENNReal.ofReal (l * n) * volume (unitBall ∩ {p | |inner ℝ u p - t| ≤ r}) :=
      h u t r hu hr
    _ ≤ _ := by gcongr

theorem slabCount_mono {δ l L : ℝ} {n : ℕ} {x v : Fin n → Space}
    (hl : l ≤ L) (h : SlabCount δ l x v) : SlabCount δ L x v := by
  intro u t r hu hr
  apply (h u t r hu hr).trans
  gcongr

/-- Keeping a `δ^ν` fraction of the indices costs one additional `δ^(-ν)` in slab count. -/
theorem slabCount_subfamily_power {δ ν : ℝ} (hδ : 0 < δ)
    {n k : ℕ} {x v : Fin n → Space} (g : Fin k → Fin n) (hg : Function.Injective g)
    (hsize : δ ^ ν * n ≤ k) (h : SlabCount δ (δ ^ (-ν)) x v) :
    SlabCount δ (δ ^ (-2 * ν)) (fun i => x (g i)) (fun i => v (g i)) := by
  apply slabCount_subfamily g hg _ h
  calc
    δ ^ (-ν) * n = δ ^ (-2 * ν) * (δ ^ ν * n) := by
      rw [← mul_assoc, ← Real.rpow_add hδ]
      congr 2
      ring
    _ ≤ δ ^ (-2 * ν) * k :=
      mul_le_mul_of_nonneg_left hsize (Real.rpow_nonneg hδ.le _)

/-- Individual lower density automatically persists under arbitrary reindexing. -/
theorem subfamily_density {δ ν : ℝ} (hδ : 0 ≤ δ) {n k : ℕ}
    {Y : Fin n → Set Space} (g : Fin k → Fin n)
    (h : ∀ i, ENNReal.ofReal (δ ^ ν * δ ^ 2) ≤ volume (Y i)) :
    ENNReal.ofReal (δ ^ ν * k * δ ^ 2) ≤ ∑ i, volume (Y (g i)) := by
  calc
    ENNReal.ofReal (δ ^ ν * k * δ ^ 2) =
        ∑ _ : Fin k, ENNReal.ofReal (δ ^ ν * δ ^ 2) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
      congr 1
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => h (g i)

/-- No volume is lost when comparing a subfamily union to the original union. -/
theorem subfamily_union_volume {n k : ℕ} (Y : Fin n → Set Space) (g : Fin k → Fin n) :
    volume (⋃ i, Y (g i)) ≤ volume (⋃ i, Y i) := by
  apply measure_mono
  exact Set.iUnion_subset fun i => Set.subset_iUnion Y (g i)

end WangZahlLot.Obl.wz_nonflat_factored_improvement
