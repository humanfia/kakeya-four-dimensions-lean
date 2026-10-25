-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.DenseLabels.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/DenseLabels.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641, commit 707550d, DenseLabels.lean
   (x0670 first-filling chain, building on x0551 geometry). -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core

noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open scoped ENNReal Classical

/-- Discarding low-density labels preserves half the total mass when the
sum of label cardinalities pays the density threshold. Labels with no indices
are discarded too. The upper row-mass bound converts retained mass to retained
index cardinality. -/
theorem dense_labels_retain_count {ι : Type*} (Λ : Finset ι)
    (s : ι → ℕ) (mass : ι → ℝ) {τ K D L N : ℝ}
    (hτ : 0 ≤ τ) (hK : 0 < K) (hN : 0 ≤ N)
    (_hmass : ∀ ℓ ∈ Λ, 0 ≤ mass ℓ)
    (hupper : ∀ ℓ ∈ Λ, mass ℓ ≤ K * s ℓ)
    (hlower : D * N ≤ ∑ ℓ ∈ Λ, mass ℓ)
    (hcount : (∑ ℓ ∈ Λ, (s ℓ : ℝ)) ≤ L * N)
    (hbudget : 2 * τ * L ≤ D) :
    ∃ good : Finset ι, good ⊆ Λ ∧
      (∀ ℓ ∈ good, 0 < s ℓ ∧ τ * s ℓ ≤ mass ℓ) ∧
      (1 / 2 : ℝ) * (∑ ℓ ∈ Λ, mass ℓ) ≤ ∑ ℓ ∈ good, mass ℓ ∧
      (D / (2 * K)) * N ≤ ∑ ℓ ∈ good, (s ℓ : ℝ) := by
  classical
  let good := Λ.filter fun ℓ => 0 < s ℓ ∧ τ * s ℓ ≤ mass ℓ
  have hg : good ⊆ Λ := Finset.filter_subset _ _
  have hgood ℓ (hℓ : ℓ ∈ good) : 0 < s ℓ ∧ τ * s ℓ ≤ mass ℓ :=
    (Finset.mem_filter.mp hℓ).2
  have hbad ℓ (hℓ : ℓ ∈ Λ) (hnot : ℓ ∉ good) : mass ℓ ≤ τ * s ℓ := by
    by_cases hs : 0 < s ℓ
    · have hh : ¬ τ * s ℓ ≤ mass ℓ := by
        intro hh
        exact hnot (Finset.mem_filter.mpr ⟨hℓ, hs, hh⟩)
      exact (lt_of_not_ge hh).le
    · have hs0 : s ℓ = 0 := Nat.eq_zero_of_not_pos hs
      simpa only [hs0, Nat.cast_zero, mul_zero] using hupper ℓ hℓ
  have hloss : (∑ ℓ ∈ Λ, mass ℓ) ≤ (∑ ℓ ∈ good, mass ℓ) + τ * L * N := by
    calc
      _ = (∑ ℓ ∈ good, mass ℓ) + ∑ ℓ ∈ Λ.filter (fun ℓ => ℓ ∉ good), mass ℓ := by
        rw [← Finset.sum_filter_add_sum_filter_not Λ (fun ℓ => ℓ ∈ good)]
        congr 2
        ext ℓ
        simp only [Finset.mem_filter, and_iff_right_iff_imp]
        exact fun h => hg h
      _ ≤ (∑ ℓ ∈ good, mass ℓ) + ∑ ℓ ∈ Λ.filter (fun ℓ => ℓ ∉ good), τ * s ℓ := by
        gcongr with ℓ hℓ
        exact hbad ℓ (Finset.mem_filter.mp hℓ).1 (Finset.mem_filter.mp hℓ).2
      _ ≤ (∑ ℓ ∈ good, mass ℓ) + ∑ ℓ ∈ Λ, τ * s ℓ := by
        exact add_le_add le_rfl (Finset.sum_le_sum_of_subset_of_nonneg
          (f := fun ℓ => τ * (s ℓ : ℝ))
          (Finset.filter_subset (fun ℓ => ℓ ∉ good) Λ)
          (fun _ _ _ => mul_nonneg hτ (Nat.cast_nonneg _)))
      _ = (∑ ℓ ∈ good, mass ℓ) + τ * (∑ ℓ ∈ Λ, (s ℓ : ℝ)) := by
        rw [Finset.mul_sum]
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hcount hτ
        nlinarith only [hh]
  have hcost : τ * L * N ≤ (1 / 2 : ℝ) * (∑ ℓ ∈ Λ, mass ℓ) := by
    have hh := mul_le_mul_of_nonneg_right hbudget hN
    linarith
  have hretain : (1 / 2 : ℝ) * (∑ ℓ ∈ Λ, mass ℓ) ≤ ∑ ℓ ∈ good, mass ℓ := by
    linarith
  have hup : (∑ ℓ ∈ good, mass ℓ) ≤ K * (∑ ℓ ∈ good, (s ℓ : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun ℓ hℓ => hupper ℓ (hg hℓ)
  refine ⟨good, hg, hgood, hretain, ?_⟩
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < 2 * K)).mpr
  nlinarith only [hlower, hretain, hup]

/-- The mass-pruning estimate in the extended nonnegative reals, with a
common body volume. It keeps whole labels, so every pointwise property of a
label's shading is unchanged. -/
theorem dense_label_measures_retain_count {ι : Type*} (Λ : Finset ι)
    (s : ι → ℕ) (mass : ι → ℝ≥0∞) {τ w D L N : ℝ}
    (hτ : 0 ≤ τ) (hw : 0 < w) (hN : 0 ≤ N)
    (hupper : ∀ ℓ ∈ Λ, mass ℓ ≤ O (w * s ℓ))
    (hlower : O (D * w * N) ≤ ∑ ℓ ∈ Λ, mass ℓ)
    (hcount : (∑ ℓ ∈ Λ, (s ℓ : ℝ)) ≤ L * N)
    (hbudget : 2 * τ * L ≤ D) :
    ∃ good : Finset ι, good ⊆ Λ ∧
      (∀ ℓ ∈ good, 0 < s ℓ ∧ O (τ * w * s ℓ) ≤ mass ℓ) ∧
      (1 / 2 : ℝ≥0∞) * (∑ ℓ ∈ Λ, mass ℓ) ≤ ∑ ℓ ∈ good, mass ℓ ∧
      (D / 2) * N ≤ ∑ ℓ ∈ good, (s ℓ : ℝ) := by
  classical
  have hfin ℓ (hℓ : ℓ ∈ Λ) : mass ℓ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hupper ℓ hℓ)
  have hsumfin : (∑ ℓ ∈ Λ, mass ℓ) ≠ ⊤ := ENNReal.sum_ne_top.mpr hfin
  have hlowreal : D * w * N ≤ ∑ ℓ ∈ Λ, (mass ℓ).toReal := by
    have hh := (ENNReal.ofReal_le_iff_le_toReal hsumfin).mp hlower
    rwa [ENNReal.toReal_sum hfin] at hh
  have hu ℓ (hℓ : ℓ ∈ Λ) : (mass ℓ).toReal ≤ w * s ℓ :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) (hupper ℓ hℓ)
  have hb : 2 * (τ * w) * L ≤ D * w := by
    nlinarith only [mul_le_mul_of_nonneg_right hbudget hw.le]
  obtain ⟨good, hg, hden, hret, hcard⟩ := dense_labels_retain_count Λ s
    (fun ℓ => (mass ℓ).toReal) (mul_nonneg hτ hw.le) hw hN
    (fun _ _ => ENNReal.toReal_nonneg) hu hlowreal hcount hb
  have hsum (Q : Finset ι) (hQ : Q ⊆ Λ) :
      ENNReal.ofReal (∑ ℓ ∈ Q, (mass ℓ).toReal) = ∑ ℓ ∈ Q, mass ℓ := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
    exact Finset.sum_congr rfl fun ℓ hℓ => ENNReal.ofReal_toReal (hfin ℓ (hQ hℓ))
  refine ⟨good, hg, ?_, ?_, ?_⟩
  · intro ℓ hℓ
    exact ⟨(hden ℓ hℓ).1, (ENNReal.ofReal_le_iff_le_toReal (hfin ℓ (hg hℓ))).mpr
      (hden ℓ hℓ).2⟩
  · have hh := ENNReal.ofReal_le_ofReal hret
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      hsum Λ Subset.rfl, hsum good hg] at hh
    norm_num [ENNReal.ofReal_div_of_pos] at hh ⊢
    exact hh
  · have he : D * w / (2 * w) = D / 2 := by field_simp
    simpa only [he] using hcard

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
