-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_off_stem_brush_overlap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_off_stem_brush_overlap.Counts
import Submission.WZ.Obl.wz_off_stem_brush_overlap.Summation
set_option linter.unusedVariables false

/-!
# Off-stem brush overlap

Angular caps lie in convex boxes of volume `O(θδ/r)`. Convex counting bounds
the cap cardinality, and the transverse intersection estimate supplies reciprocal
angular weights. Dyadic summation loses only `δ^(-ε)`.
-/

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_off_stem_brush_overlap

theorem WangZahlLot.wz_off_stem_brush_overlap : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ δ r m : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → δ ≤ r → r ≤ 1 → 1 ≤ m → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Z : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), (∀ i : Fin n, ‖v i‖ = 1) → (∀ i : Fin n, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W} : ℕ) : ℝ) * δ ^ 2) ≤ ENNReal.ofReal m * MeasureTheory.volume W) → ∀ (i₀ : Fin n) (F : Finset (Fin n)), (∀ i : Fin n, i ∈ F → MeasurableSet (Z i)) → (∀ i : Fin n, i ∈ F → Z i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i)) \ Metric.thickening r (Set.range (fun t : ℝ => x i₀ + t • v i₀))) → (∀ i : Fin n, i ∈ F → (Metric.thickening δ (segment ℝ (x i) (x i + v i)) ∩ Metric.thickening δ (segment ℝ (x i₀) (x i₀ + v i₀))).Nonempty) → ∀ i : Fin n, i ∈ F → Finset.sum F (fun j : Fin n => (MeasureTheory.volume (Z i ∩ Z j)).toReal) ≤ C * m * δ ^ ((2 : ℝ) - ε) * r⁻¹ := by
  classical
  intro ε hε
  obtain ⟨C, hC, hsum⟩ := power_weighted_sum ε hε
  refine ⟨16777216 * C, by positivity, ?_⟩
  intro δ r m hδ hδ100 hδr hr1 hm n x v Z hv hball hcount i₀ F hZm hZ hstem i hi
  have hr : 0 < r := hδ.trans_le hδr
  have hδ1 : δ ≤ 1 := by linarith
  have hm0 : 0 ≤ m := by linarith
  let G : Finset (Fin n) := F.filter (fun j => (Z i ∩ Z j).Nonempty)
  let a : Fin n → ℝ := fun j => (volume (Z i ∩ Z j)).toReal
  let d : Fin n → ℝ := fun j => max δ (angle (v i) (v j))
  have hGF : ∀ j ∈ G, j ∈ F := fun j hj => (Finset.mem_filter.mp hj).1
  have hoff : ∀ j ∈ G,
      ((Tube δ (x i) (v i) \ thickening r (Stem (x i₀) (v i₀))) ∩
        Tube δ (x j) (v j)).Nonempty := by
    intro j hj
    obtain ⟨p, hpi, hpj⟩ := (Finset.mem_filter.mp hj).2
    exact ⟨p, hZ i hi hpi, (hZ j (hGF j hj) hpj).1⟩
  have ha : ∀ j ∈ G, 0 ≤ a j := fun _ _ => ENNReal.toReal_nonneg
  have hd : ∀ j ∈ G, δ ≤ d j ∧ d j ≤ 2 := by
    intro j hj
    exact ⟨le_max_left _ _, max_le (by linarith) (angle_le_two (hv i) (hv j))⟩
  have hab : ∀ j ∈ G, a j ≤ (8192 * δ ^ 3) / d j := by
    intro j hj
    have hsub : Z i ∩ Z j ⊆ Tube δ (x i) (v i) ∩ Tube δ (x j) (v j) := by
      intro p hp
      exact ⟨(hZ i hi hp.1).1, (hZ j (hGF j hj) hp.2).1⟩
    have hh := (measure_mono hsub).trans (regularized_intersection hδ hδ1 (hv i) (hv j))
    have hh' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
    rw [ENNReal.toReal_ofReal (by positivity)] at hh'
    exact hh'
  have hc : ∀ θ : ℝ, δ ≤ θ → ((G.filter (fun j => d j ≤ θ)).card : ℝ) ≤
      (1024 * m / (r * δ)) * θ := by
    intro θ hδθ
    apply cap_count hδ hδr hr1 hδθ hm0 hv hball hcount i i₀
      (G.filter (fun j => d j ≤ θ)) (hstem i hi)
    · intro j hj
      exact hstem j (hGF j (Finset.mem_filter.mp hj).1)
    · intro j hj
      exact hoff j (Finset.mem_filter.mp hj).1
    · intro j hj
      exact (le_max_right δ (angle (v i) (v j))).trans (Finset.mem_filter.mp hj).2
  have hbound := hsum G a d δ (1024 * m / (r * δ)) (8192 * δ ^ 3)
    hδ hδ1 (by positivity) (by positivity) ha hd hab hc
  have hsum_eq : ∑ j ∈ F, (volume (Z i ∩ Z j)).toReal = ∑ j ∈ G, a j := by
    simp only [G, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : (Z i ∩ Z j).Nonempty
    · simp [h, a]
    · have he : Z i ∩ Z j = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      simp [he, a]
  have hpow : δ ^ (-ε) * δ ^ 2 = δ ^ ((2 : ℝ) - ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hδ]
    congr 1
    norm_num
    ring
  rw [hsum_eq]
  refine hbound.trans_eq ?_
  rw [← hpow]
  field_simp
  ring
