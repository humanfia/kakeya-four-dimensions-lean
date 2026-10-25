-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.Transport.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.Types

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open scoped ENNReal

theorem density_sum {ν δ : ℝ} {n : ℕ} {Y : Fin n → Set Space}
    (hY : IndividuallyDense ν δ Y) :
    ENNReal.ofReal (δ ^ ν * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y i) := by
  calc
    ENNReal.ofReal (δ ^ ν * (n : ℝ) * δ ^ 2) =
        ∑ _i : Fin n, ENNReal.ofReal (δ ^ ν * δ ^ 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        show δ ^ ν * (n : ℝ) * δ ^ 2 = (n : ℝ) * (δ ^ ν * δ ^ 2) by ring,
        ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
    _ ≤ ∑ i, volume (Y i) := Finset.sum_le_sum fun i _ => hY i

/-- Restriction only changes the factor multiplying volume in the slab count. -/
theorem slabCount_restrict {δ L L' : ℝ} {n k : ℕ} {x v : Fin n → Space}
    (g : Fin k → Fin n) (hg : Function.Injective g)
    (hL : L * n ≤ L' * k) (h : SlabCount δ L n x v) :
    SlabCount δ L' k (x ∘ g) (v ∘ g) := by
  intro u t r hu hr
  calc
    ENNReal.ofReal (Set.ncard {i | Tube δ ((x ∘ g) i) ((v ∘ g) i) ⊆
        ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ r}} : ℝ) ≤
      ENNReal.ofReal (Set.ncard {i | Tube δ (x i) (v i) ⊆
        ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ r}} : ℝ) := by
      apply ENNReal.ofReal_le_ofReal
      exact_mod_cast WangZahlLot.Obl.wz_tower_balanced_refinement.count_restrict g hg
        (fun i => Tube δ (x i) (v i) ⊆ ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ r})
    _ ≤ ENNReal.ofReal (L * n) * volume (ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ r}) :=
      h u t r hu hr
    _ ≤ ENNReal.ofReal (L' * k) * volume (ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ r}) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hL) le_rfl

/-- The slab coefficient doubles its tolerance exponent after retention. -/
theorem slab_retention_budget {δ ν : ℝ} {n k : ℕ} (hδ : 0 < δ)
    (hk : δ ^ ν * (n : ℝ) ≤ k) :
    δ ^ (-ν) * (n : ℝ) ≤ δ ^ (-2 * ν) * (k : ℝ) := by
  calc
    δ ^ (-ν) * (n : ℝ) = δ ^ (-2 * ν) * (δ ^ ν * (n : ℝ)) := by
      rw [← mul_assoc, ← Real.rpow_add hδ]
      congr 2
      ring
    _ ≤ δ ^ (-2 * ν) * (k : ℝ) :=
      mul_le_mul_of_nonneg_left hk (Real.rpow_nonneg hδ.le _)

/-- Individual density is what makes admissibility survive an arbitrary retained subfamily. -/
theorem admissible_restrict {δ ν m c : ℝ} {n k : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hδ : 0 < δ) (g : Fin k → Fin n) (hg : Function.Injective g) (hk : 0 < k)
    (hret : δ ^ ν * (n : ℝ) ≤ k)
    (hA : Admissible δ ν m (δ ^ (-ν)) n x v Y)
    (hY : IndividuallyDense ν δ Y)
    (hC : ConvexCount δ c k (x ∘ g) (v ∘ g)) :
    Admissible δ ν c (δ ^ (-2 * ν)) k (x ∘ g) (v ∘ g) (Y ∘ g) := by
  obtain ⟨hn, hfamily, hsep, hsum, hconv, hslab⟩ := hA
  refine ⟨hk, fun i => hfamily (g i), ?_, density_sum (fun i => hY (g i)), hC, ?_⟩
  · exact fun i j hij => hsep _ _ (hg.ne hij)
  · exact slabCount_restrict g hg (slab_retention_budget hδ hret) hslab

/-- The union of retained shadings is a subset of the original union. -/
theorem volume_restrict {n k : ℕ} (g : Fin k → Fin n) (Y : Fin n → Set Space) :
    volume (⋃ i, (Y ∘ g) i) ≤ volume (⋃ i, Y i) := by
  apply measure_mono
  exact iUnion_subset fun i => subset_iUnion Y (g i)

end WangZahlLot.Obl.wz_flat_factored_improvement
