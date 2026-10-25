-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.PairArea.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.BipartiteMoment

noncomputable section

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open MeasureTheory Set
open scoped ENNReal
open WangZahlLot.Obl.wz_jet_close_pair_moment (strip measurableSet_strip JetControlled)

/-- The product counts all ordered cross incidences, with no slope restriction. -/
theorem finiteMultiplicity_mul_eq {ι : Type*} (A B : Finset ι) (δ : ℝ)
    (g : ι → ℝ → ℝ) (p : ℝ × ℝ) :
    finiteMultiplicity A δ g p * finiteMultiplicity B δ g p =
      ∑ i ∈ A, ∑ j ∈ B,
        (strip δ (g i) ∩ strip δ (g j)).indicator (fun _ => (1 : ℝ≥0∞)) p := by
  classical
  unfold finiteMultiplicity
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hi : p ∈ strip δ (g i) <;>
    by_cases hj : p ∈ strip δ (g j) <;> simp [hi, hj]

/-- The precise product threshold at which the unrestricted pair moment
implies the desired linear curve-mass expression. -/
theorem pair_expression_le_linear_mass {C δ D μ F X Y : ℝ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hμ : 0 < μ)
    (hproduct : Real.sqrt (δ / D) * X * Y ≤ F * (X + Y) * Real.sqrt μ) :
    C * δ * Real.sqrt (δ / D) * X * Y / μ ^ 2 ≤
      C * F * δ * (X + Y) * μ ^ (-(3 / 2 : ℝ)) := by
  have hpow : Real.sqrt μ / μ ^ 2 = μ ^ (-(3 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_two, ← Real.rpow_sub hμ]
    norm_num
  calc
    _ = C * δ / μ ^ 2 * (Real.sqrt (δ / D) * X * Y) := by ring
    _ ≤ C * δ / μ ^ 2 * (F * (X + Y) * Real.sqrt μ) :=
      mul_le_mul_of_nonneg_left hproduct (by positivity)
    _ = C * F * δ * (X + Y) * (Real.sqrt μ / μ ^ 2) := by ring
    _ = _ := by rw [hpow]

/-- Both elementary moment estimates apply to arbitrary subsets of the
simultaneously rich set; no measurability of that subset is needed. -/
theorem exists_area_constant_of_first_or_pair : ∃ C : ℝ, 0 < C ∧
    ∀ {n : ℕ} {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ},
      JetControlled q g → (∀ i, ContDiff ℝ 2 (g i)) →
    ∀ (A B : Finset (Fin n)) (δ D μ F : ℝ), 0 < δ → 0 < D → 0 < μ → 0 ≤ F →
      (∀ i ∈ A, ∀ j ∈ B, D ≤ dist (q i) (q j)) →
      (Real.sqrt μ ≤ F ∨ Real.sqrt (δ / D) * (A.card : ℝ) * (B.card : ℝ) ≤
        F * ((A.card : ℝ) + (B.card : ℝ)) * Real.sqrt μ) →
    ∀ E : Set (ℝ × ℝ),
      E ⊆ {p | ENNReal.ofReal μ ≤ finiteMultiplicity A δ g p ∧
        ENNReal.ofReal μ ≤ finiteMultiplicity B δ g p} →
      volume E ≤ ENNReal.ofReal (C * F * δ *
        ((A.card : ℝ) + (B.card : ℝ)) * μ ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨C, hC, hpair⟩ := exists_bipartite_pair_area_constant
  refine ⟨max 4 C, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro n q g hjet hg A B δ D μ F hδ hD hμ hF hfar hcase E hE
  rcases hcase with hfirst | hproduct
  · have hroot : μ ^ (1 / 2 : ℝ) ≤ F := by rwa [← Real.sqrt_eq_rpow]
    apply (volume_subset_rich_le A B (fun i _ => (hg i).continuous) hδ.le hμ hroot
      (fun p hp => (hE hp).1)).trans
    apply ENNReal.ofReal_le_ofReal
    gcongr
    exact le_max_left _ _
  · apply (measure_mono hE).trans
    apply (hpair hjet hg A B δ D μ hδ hD hμ hfar).trans
    apply ENNReal.ofReal_le_ofReal
    apply (pair_expression_le_linear_mass hC.le hδ.le hμ hproduct).trans
    gcongr
    exact le_max_right _ _

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
