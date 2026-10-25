-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_all_scales_volume.Reduction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
/-!
# Elementary reductions for `WangZahlLot.wz_frostman_all_scales_volume`

This file isolates the parts of the frozen statement of o015 that do not need the
sticky-Kakeya machinery:

* `AtScale ε a η δ` is the frozen statement for one scale `δ` and fixed constants;
  the frozen statement is `∀ ε > 0, ∃ a > 0, ∃ η > 0, ∀ δ ∈ (0, 1/100], AtScale ε a η δ`
  (definitionally, see `Statement`).
* `ofReal_le_volume_iUnion_of_le_sum`: average density bounds the union from below by the
  average shading volume.
* `statement_of_small_scales`: it suffices to prove `AtScale` for `δ ≤ δ₀`, where `δ₀ > 0`
  may depend on `ε`; the remaining compact range of scales is handled by density alone.
-/

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

namespace WangZahlLot.Obl.wz_frostman_all_scales_volume

/-- The frozen statement of o015 for one scale `δ`, with the constants `ε, a, η` fixed. -/
def AtScale (ε a η δ : ℝ) : Prop :=
  ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), 0 < n → (∀ i : Fin n, ‖v i‖ = 1) → (∀ i : Fin n, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ i j : Fin n, i ≠ j → MeasureTheory.volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)) ∩ Metric.thickening δ (segment ℝ (x j) (x j + v j))) ≤ (1 / 2 : ENNReal) * MeasureTheory.volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)))) → (∀ i : Fin n, MeasurableSet (Y i)) → (∀ i : Fin n, Y i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i))) → ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i : Fin n => MeasureTheory.volume (Y i)) → (∀ ρ₀ : ℝ, δ ≤ ρ₀ → ρ₀ ≤ 1 → ∃ ρ : ℝ, ρ₀ ≤ ρ ∧ ρ ≤ 1 ∧ ρ ≤ (δ ^ (-η)) * ρ₀ ∧ ∃ k : ℕ, 0 < k ∧ ∃ (z w : Fin k → LeanEval.Analysis.WangZahlKakeya.Space), (∀ j : Fin k, ‖w j‖ = 1) ∧ (∀ j j' : Fin k, j ≠ j' → MeasureTheory.volume (Metric.thickening ρ (segment ℝ (z j) (z j + w j)) ∩ Metric.thickening ρ (segment ℝ (z j') (z j' + w j'))) ≤ (1 / 2 : ENNReal) * MeasureTheory.volume (Metric.thickening ρ (segment ℝ (z j) (z j + w j)))) ∧ (∀ i : Fin n, ∃! j : Fin k, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.thickening ρ (segment ℝ (z j) (z j + w j))) ∧ (∀ j : Fin k, ∃ i : Fin n, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.thickening ρ (segment ℝ (z j) (z j + w j))) ∧ (∀ j j' : Fin k, (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.thickening ρ (segment ℝ (z j) (z j + w j))} : ℕ) : ℝ)) ≤ (δ ^ (-η)) * (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.thickening ρ (segment ℝ (z j') (z j' + w j'))} : ℕ) : ℝ))) ∧ (∀ j : Fin k, ∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal ((((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.thickening ρ (segment ℝ (z j) (z j + w j)) ∧ Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W} : ℕ) : ℝ)) * ρ ^ 2) ≤ ENNReal.ofReal ((δ ^ (-η)) * (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.thickening ρ (segment ℝ (z j) (z j + w j))} : ℕ) : ℝ))) * MeasureTheory.volume W)) → ENNReal.ofReal (a * δ ^ ε) ≤ MeasureTheory.volume (⋃ i : Fin n, Y i)

/-- The frozen statement of o015, written with `AtScale`. -/
def Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → AtScale ε a η δ

/-- Average density bounds the union from below: if `∑ |Y i| ≥ b n d` then `|⋃ Y i| ≥ b d`. -/
theorem ofReal_le_volume_iUnion_of_le_sum {n : ℕ} (hn : 0 < n) (Y : Fin n → Set Space)
    {b d : ℝ}
    (h : ENNReal.ofReal (b * (n : ℝ) * d) ≤ Finset.sum Finset.univ (fun i : Fin n => volume (Y i))) :
    ENNReal.ofReal (b * d) ≤ volume (⋃ i : Fin n, Y i) := by
  have hsum : Finset.sum Finset.univ (fun i : Fin n => volume (Y i)) ≤
      (n : ENNReal) * volume (⋃ i : Fin n, Y i) := by
    calc Finset.sum Finset.univ (fun i : Fin n => volume (Y i))
        ≤ Finset.sum Finset.univ (fun _i : Fin n => volume (⋃ i : Fin n, Y i)) :=
          Finset.sum_le_sum fun i _ => measure_mono (Set.subset_iUnion Y i)
      _ = (n : ENNReal) * volume (⋃ i : Fin n, Y i) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have key : ENNReal.ofReal (b * (n : ℝ) * d) = (n : ENNReal) * ENNReal.ofReal (b * d) := by
    rw [show b * (n : ℝ) * d = (n : ℝ) * (b * d) by ring, ENNReal.ofReal_mul hn'.le,
      ENNReal.ofReal_natCast]
  have h2 : (n : ENNReal) * ENNReal.ofReal (b * d) ≤ (n : ENNReal) * volume (⋃ i : Fin n, Y i) :=
    key ▸ h.trans hsum
  have hn0 : (n : ENNReal) ≠ 0 := by exact_mod_cast hn.ne'
  exact (ENNReal.mul_le_mul_iff_right hn0 (ENNReal.natCast_ne_top n)).1 h2

/-- At every scale, the union is at least `δ ^ η * δ ^ 2`, by average density alone. -/
theorem atScale_of_le {ε a η δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε)
    (ha : a ≤ δ ^ η * δ ^ 2) : AtScale ε a η δ := by
  intro n x v Y hn _ _ _ _ _ hdens _
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (ofReal_le_volume_iUnion_of_le_sum hn Y hdens)
  have h1 : δ ^ ε ≤ 1 := Real.rpow_le_one hδ.le hδ1 hε.le
  have h0 : 0 ≤ δ ^ η * δ ^ 2 := by positivity
  rcases le_or_gt 0 a with ha0 | ha0
  · calc a * δ ^ ε ≤ a * 1 := mul_le_mul_of_nonneg_left h1 ha0
      _ = a := mul_one a
      _ ≤ δ ^ η * δ ^ 2 := ha
  · have : 0 ≤ δ ^ ε := Real.rpow_nonneg hδ.le ε
    nlinarith

/-- Shrinking `a` keeps `AtScale` true. -/
theorem AtScale.mono {ε a a' η δ : ℝ} (h : AtScale ε a η δ) (ha : a' ≤ a) (hδ : 0 < δ) :
    AtScale ε a' η δ := by
  intro n x v Y h1 h2 h3 h4 h5 h6 h7 h8
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (h n x v Y h1 h2 h3 h4 h5 h6 h7 h8)
  exact mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hδ.le ε)

/-- **Small-scale reduction.** It suffices to prove the frozen statement for `δ ≤ δ₀`,
where `δ₀ > 0` may depend on `ε`: on the compact range `[δ₀, 1/100]`, average density
alone gives the union volume `δ ^ η * δ ^ 2 ≥ δ₀ ^ η * δ₀ ^ 2`. -/
theorem statement_of_small_scales
    (H : ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → δ ≤ (1 / 100 : ℝ) → AtScale ε a η δ) :
    Statement := by
  intro ε hε
  obtain ⟨a, ha, η, hη, δ₀, hδ₀, hsmall⟩ := H ε hε
  refine ⟨min a (δ₀ ^ η * δ₀ ^ 2), lt_min ha (by positivity), η, hη, fun δ hδ hδ1 => ?_⟩
  rcases le_or_gt δ δ₀ with hle | hlt
  · exact (hsmall δ hδ hle hδ1).mono (min_le_left _ _) hδ
  · refine atScale_of_le hδ (hδ1.trans (by norm_num)) hε ((min_le_right _ _).trans ?_)
    have h1 : δ₀ ^ η ≤ δ ^ η := Real.rpow_le_rpow hδ₀.le hlt.le hη.le
    have h2 : δ₀ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hδ₀.le hlt.le 2
    exact mul_le_mul h1 h2 (by positivity) (by positivity)

end WangZahlLot.Obl.wz_frostman_all_scales_volume

namespace WangZahlLot.Obl.wz_frostman_all_scales_volume

/-- The all-scales hypothesis of the frozen statement, for fixed `η δ n x v`. -/
def AllScales (η δ : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ ρ₀ : ℝ, δ ≤ ρ₀ → ρ₀ ≤ 1 → ∃ ρ : ℝ, ρ₀ ≤ ρ ∧ ρ ≤ 1 ∧ ρ ≤ (δ ^ (-η)) * ρ₀ ∧ ∃ k : ℕ, 0 < k ∧ ∃ (z w : Fin k → LeanEval.Analysis.WangZahlKakeya.Space), (∀ j : Fin k, ‖w j‖ = 1) ∧ (∀ j j' : Fin k, j ≠ j' → MeasureTheory.volume (Metric.thickening ρ (segment ℝ (z j) (z j + w j)) ∩ Metric.thickening ρ (segment ℝ (z j') (z j' + w j'))) ≤ (1 / 2 : ENNReal) * MeasureTheory.volume (Metric.thickening ρ (segment ℝ (z j) (z j + w j)))) ∧ (∀ i : Fin n, ∃! j : Fin k, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.thickening ρ (segment ℝ (z j) (z j + w j))) ∧ (∀ j : Fin k, ∃ i : Fin n, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.thickening ρ (segment ℝ (z j) (z j + w j))) ∧ (∀ j j' : Fin k, (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.thickening ρ (segment ℝ (z j) (z j + w j))} : ℕ) : ℝ)) ≤ (δ ^ (-η)) * (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.thickening ρ (segment ℝ (z j') (z j' + w j'))} : ℕ) : ℝ))) ∧ (∀ j : Fin k, ∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal ((((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.thickening ρ (segment ℝ (z j) (z j + w j)) ∧ Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W} : ℕ) : ℝ)) * ρ ^ 2) ≤ ENNReal.ofReal ((δ ^ (-η)) * (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.thickening ρ (segment ℝ (z j) (z j + w j))} : ℕ) : ℝ))) * MeasureTheory.volume W)

/-- Counting along a partition: if every `i` lies in exactly one class `A j`, the number of
`i` with `P i` is the sum over the classes. -/
theorem ncard_eq_sum_of_existsUnique {n k : ℕ} (A : Fin k → Fin n → Prop)
    (hA : ∀ i, ∃! j, A j i) (P : Fin n → Prop) :
    Set.ncard {i | P i} = ∑ j, Set.ncard {i | A j i ∧ P i} := by
  classical
  choose f hf using fun i => (hA i).exists
  have hAeq : ∀ j i, A j i ↔ f i = j :=
    fun j i => ⟨fun h => (hA i).unique (hf i) h ▸ rfl, fun h => h ▸ hf i⟩
  simp only [hAeq]
  have hcard : ∀ Q : Fin n → Prop, Set.ncard {i | Q i} = (Finset.univ.filter Q).card := by
    intro Q
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp
  rw [hcard, Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ)
    (fun i _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hcard, Finset.filter_filter]
  congr 1
  ext i
  simp [and_comm]

/-- A partitioning cover whose fibers satisfy the Frostman count of the frozen statement
yields the global count `#{i | T i ⊆ W} ρ² ≤ δ^{-η} n |W|` for every convex `W`. -/
theorem frostman_of_cover {n k : ℕ} {δ η ρ : ℝ} (hδ : 0 ≤ δ) (T : Fin n → Set Space)
    (U : Fin k → Set Space) (hpart : ∀ i, ∃! j, T i ⊆ U j)
    (hfro : ∀ j, ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal ((((Set.ncard {i | T i ⊆ U j ∧ T i ⊆ W} : ℕ) : ℝ)) * ρ ^ 2) ≤
        ENNReal.ofReal (δ ^ (-η) * (((Set.ncard {i | T i ⊆ U j} : ℕ) : ℝ))) * volume W)
    (W : Set Space) (hW : Convex ℝ W) :
    ENNReal.ofReal ((((Set.ncard {i | T i ⊆ W} : ℕ) : ℝ)) * ρ ^ 2) ≤
      ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume W := by
  have h1 := ncard_eq_sum_of_existsUnique (fun j i => T i ⊆ U j) hpart (fun i => T i ⊆ W)
  have h2 := ncard_eq_sum_of_existsUnique (fun j i => T i ⊆ U j) hpart (fun _ => True)
  simp only [and_true, Set.ofPred_true, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin] at h2
  have hδη : 0 ≤ δ ^ (-η) := Real.rpow_nonneg hδ _
  calc ENNReal.ofReal ((((Set.ncard {i | T i ⊆ W} : ℕ) : ℝ)) * ρ ^ 2)
      = ∑ j, ENNReal.ofReal ((((Set.ncard {i | T i ⊆ U j ∧ T i ⊆ W} : ℕ) : ℝ)) * ρ ^ 2) := by
        rw [h1, Nat.cast_sum, Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg]
        intro j _
        positivity
    _ ≤ ∑ j, ENNReal.ofReal (δ ^ (-η) * (((Set.ncard {i | T i ⊆ U j} : ℕ) : ℝ))) * volume W :=
        Finset.sum_le_sum fun j _ => hfro j W hW
    _ = ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume W := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity),
          ← Finset.mul_sum, ← Nat.cast_sum, ← h2]

/-- **Global Frostman bound.** The all-scales hypothesis at `ρ₀ = 1` forces `ρ = 1`, and the
cover yields `#{i | T i ⊆ W} ≤ δ^{-η} n |W|` for every convex `W`. -/
theorem global_frostman {η δ : ℝ} {n : ℕ} {x v : Fin n → Space} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hall : AllScales η δ n x v) (W : Set Space) (hW : Convex ℝ W) :
    ENNReal.ofReal (((Set.ncard {i : Fin n |
        Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W} : ℕ) : ℝ)) ≤
      ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume W := by
  obtain ⟨ρ, hρ1, hρ2, -, k, -, z, w, -, -, hpart, -, -, hfro⟩ := hall 1 hδ1 le_rfl
  have hρ : ρ = 1 := le_antisymm hρ2 hρ1
  subst hρ
  have := frostman_of_cover (δ := δ) (η := η) (ρ := 1) hδ.le
    (fun i => Metric.thickening δ (segment ℝ (x i) (x i + v i)))
    (fun j => Metric.thickening 1 (segment ℝ (z j) (z j + w j))) hpart hfro W hW
  simpa using this

end WangZahlLot.Obl.wz_frostman_all_scales_volume
