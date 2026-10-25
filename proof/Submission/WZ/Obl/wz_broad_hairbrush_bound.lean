-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_hairbrush_bound.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_transverse_brush_selection
import Submission.WZ.Obl.wz_dense_transverse_brush_bound

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_broad_hairbrush_bound

/-- Combine incidence selection and the linear-cardinality brush bound. -/
private theorem combine_bounds {a b d δ lam m N k q α : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hδ : 0 < δ)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hm : 1 ≤ m)
    (hN : 0 ≤ N) (hq : 0 ≤ q)
    (hsel : a * b * lam ^ 2 * N * δ ≤ k * q)
    (hbrush : d * δ ^ ((2 : ℝ) + 2 * α) * (a * lam) ^ 3 * m⁻¹ * k ≤ q) :
    Real.sqrt (d * a ^ 4 * b) * δ ^ ((3 / 2 : ℝ) + α) *
      lam ^ (3 : ℝ) * m ^ (-3 : ℝ) * N ^ (1 / 2 : ℝ) ≤ q := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  let A := d * δ ^ ((2 : ℝ) + 2 * α) * (a * lam) ^ 3 * m⁻¹
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hprod : A * (a * b * lam ^ 2 * N * δ) ≤ q ^ 2 := by
    calc
      A * (a * b * lam ^ 2 * N * δ) ≤ A * (k * q) :=
        mul_le_mul_of_nonneg_left hsel hA
      _ = (A * k) * q := by ring
      _ ≤ q * q := mul_le_mul_of_nonneg_right hbrush hq
      _ = q ^ 2 := by ring
  have hdsq : (δ ^ ((3 / 2 : ℝ) + α)) ^ 2 =
      δ ^ ((2 : ℝ) + 2 * α) * δ := by
    calc
      (δ ^ ((3 / 2 : ℝ) + α)) ^ 2 = δ ^ (((3 / 2 : ℝ) + α) * 2) := by
        rw [Real.rpow_mul hδ.le, Real.rpow_two]
      _ = δ ^ (((2 : ℝ) + 2 * α) + 1) := by congr 1; ring
      _ = δ ^ ((2 : ℝ) + 2 * α) * δ := by
        rw [Real.rpow_add hδ, Real.rpow_one]
  have hlsq : (lam ^ (3 : ℝ)) ^ 2 = lam ^ 6 := by
    rw [show lam ^ (3 : ℝ) = lam ^ (3 : ℕ) from Real.rpow_natCast lam 3]
    ring
  have hmsq : (m ^ (-3 : ℝ)) ^ 2 = m ^ (-6 : ℝ) := by
    calc
      (m ^ (-3 : ℝ)) ^ 2 = m ^ ((-3 : ℝ) * 2) := by
        rw [Real.rpow_mul hmpos.le, Real.rpow_two]
      _ = m ^ (-6 : ℝ) := by norm_num
  have hnsq : (N ^ (1 / 2 : ℝ)) ^ 2 = N := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hN]
  have hcsq : (Real.sqrt (d * a ^ 4 * b)) ^ 2 = d * a ^ 4 * b :=
    Real.sq_sqrt (by positivity)
  have hlam65 : lam ^ 6 ≤ lam ^ 5 := by
    calc
      lam ^ 6 = lam ^ 5 * lam := by ring
      _ ≤ lam ^ 5 * 1 := mul_le_mul_of_nonneg_left hlam1 (by positivity)
      _ = lam ^ 5 := mul_one _
  have hm61 : m ^ (-6 : ℝ) ≤ m⁻¹ := by
    simpa only [Real.rpow_neg_one] using
      (Real.rpow_le_rpow_of_exponent_le hm (by norm_num : (-6 : ℝ) ≤ -1))
  apply (sq_le_sq₀ (by positivity) hq).mp
  calc
    (Real.sqrt (d * a ^ 4 * b) * δ ^ ((3 / 2 : ℝ) + α) *
        lam ^ (3 : ℝ) * m ^ (-3 : ℝ) * N ^ (1 / 2 : ℝ)) ^ 2 =
        (d * a ^ 4 * b) * (δ ^ ((2 : ℝ) + 2 * α) * δ) *
          lam ^ 6 * m ^ (-6 : ℝ) * N := by
      simp only [mul_pow, hcsq, hdsq, hlsq, hmsq, hnsq]
    _ ≤ (d * a ^ 4 * b) * (δ ^ ((2 : ℝ) + 2 * α) * δ) *
        lam ^ 5 * m⁻¹ * N := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_left hlam65 (by positivity)) hm61
          (by positivity) (by positivity)) hN
    _ = A * (a * b * lam ^ 2 * N * δ) := by dsimp [A]; ring
    _ ≤ q ^ 2 := hprod

end WangZahlLot.Obl.wz_broad_hairbrush_bound

theorem WangZahlLot.wz_broad_hairbrush_bound : ∃ K : ℝ, 1 ≤ K ∧ ∀ α b : ℝ, 0 < α → 0 < b → b ≤ 1 → ∃ c : ℝ, 0 < c ∧ ∀ δ lam m : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → 0 < lam → lam ≤ 1 → 1 ≤ m → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), 0 < n → (∀ i : Fin n, ‖v i‖ = 1) → (∀ i : Fin n, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ i : Fin n, MeasurableSet (Y i)) → (∀ i : Fin n, Y i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i))) → ENNReal.ofReal (lam * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i : Fin n => MeasureTheory.volume (Y i)) → (∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W} : ℕ) : ℝ) * δ ^ 2) ≤ ENNReal.ofReal m * MeasureTheory.volume W) → (∀ (p w : LeanEval.Analysis.WangZahlKakeya.Space), ‖w‖ = 1 → (((Set.ncard {i : Fin n | p ∈ Y i ∧ min ‖v i - w‖ ‖v i + w‖ ≤ b} : ℕ) : ℝ)) ≤ (1 / 2 : ℝ) * (((Set.ncard {i : Fin n | p ∈ Y i} : ℕ) : ℝ))) → ENNReal.ofReal (c * δ ^ ((3 / 2 : ℝ) + α) * lam ^ K * m ^ (-K) * (n : ℝ) ^ (1 / 2 : ℝ)) ≤ MeasureTheory.volume (⋃ i : Fin n, Y i) := by
  obtain ⟨a, ha, ha1, hselect⟩ := WangZahlLot.wz_transverse_brush_selection
  refine ⟨3, by norm_num, ?_⟩
  intro α b hα hb hb1
  obtain ⟨d, hd, hbrush⟩ :=
    WangZahlLot.wz_dense_transverse_brush_bound (2 * α) b (by positivity) hb hb1
  refine ⟨Real.sqrt (d * a ^ 4 * b), by positivity, ?_⟩
  intro δ lam m hδ hδ1 hlam hlam1 hm n x v Y hn hv hT hYm hYT hmass hcount hbroad
  obtain ⟨i₀, F, hmeet, hsep, hdensity, hsel⟩ :=
    hselect b δ lam hb hb1 hδ hδ1 hlam hlam1 n x v Y hn hv hT hYm hYT hmass hbroad
  have harho : a * lam ≤ 1 := by
    calc
      a * lam ≤ 1 * 1 := mul_le_mul ha1 hlam1 hlam.le (by norm_num)
      _ = 1 := by norm_num
  have hbr := hbrush δ (a * lam) m hδ hδ1 (by positivity) harho hm
    n x v Y hv hT hYm hYT hcount i₀ F hmeet hsep hdensity
  have hreal := Obl.wz_broad_hairbrush_bound.combine_bounds ha hb hd hδ hlam hlam1 hm
    (Nat.cast_nonneg n) ENNReal.toReal_nonneg hsel hbr
  exact (ENNReal.ofReal_le_ofReal hreal).trans ENNReal.ofReal_toReal_le
