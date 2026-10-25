-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.SharpBrush.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.Basic
import Submission.WZ.Obl.wz_transverse_brush_selection
import Submission.WZ.Obl.wz_dense_transverse_brush_bound

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal

/-- The square-root dependence on the convex counting constant in the brush argument. -/
lemma sharp_brush_algebra {a b d δ lam m N k q α : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hδ : 0 < δ)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hm : 0 < m)
    (hN : 0 ≤ N) (hq : 0 ≤ q)
    (hsel : a * b * lam ^ 2 * N * δ ≤ k * q)
    (hbrush : d * δ ^ ((2 : ℝ) + 2 * α) * (a * lam) ^ 3 * m⁻¹ * k ≤ q) :
    Real.sqrt (d * a ^ 4 * b) * δ ^ ((3 / 2 : ℝ) + α) *
      lam ^ 3 * m ^ (-(1 / 2 : ℝ)) * N ^ (1 / 2 : ℝ) ≤ q := by
  let A := d * δ ^ ((2 : ℝ) + 2 * α) * (a * lam) ^ 3 * m⁻¹
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hprod : A * (a * b * lam ^ 2 * N * δ) ≤ q ^ 2 := by
    calc
      A * (a * b * lam ^ 2 * N * δ) ≤ A * (k * q) :=
        mul_le_mul_of_nonneg_left hsel hA
      _ = (A * k) * q := by ring
      _ ≤ q * q := mul_le_mul_of_nonneg_right hbrush hq
      _ = q ^ 2 := by ring
  have hdsq : (δ ^ ((3 / 2 : ℝ) + α)) ^ 2 = δ ^ ((2 : ℝ) + 2 * α) * δ := by
    rw [← Real.rpow_two (δ ^ _), ← Real.rpow_mul hδ.le]
    rw [show ((3 / 2 : ℝ) + α) * 2 = ((2 : ℝ) + 2 * α) + 1 by ring,
      Real.rpow_add hδ, Real.rpow_one]
  have hmsq : (m ^ (-(1 / 2 : ℝ))) ^ 2 = m⁻¹ := by
    rw [← Real.rpow_two (m ^ _), ← Real.rpow_mul hm.le]
    norm_num [Real.rpow_neg_one]
  have hnsq : (N ^ (1 / 2 : ℝ)) ^ 2 = N := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hN]
  have hcsq : (Real.sqrt (d * a ^ 4 * b)) ^ 2 = d * a ^ 4 * b :=
    Real.sq_sqrt (by positivity)
  have hlam65 : lam ^ 6 ≤ lam ^ 5 := by
    calc
      lam ^ 6 = lam ^ 5 * lam := by ring
      _ ≤ lam ^ 5 * 1 := mul_le_mul_of_nonneg_left hlam1 (by positivity)
      _ = lam ^ 5 := mul_one _
  apply (sq_le_sq₀ (by positivity) hq).mp
  calc
    (Real.sqrt (d * a ^ 4 * b) * δ ^ ((3 / 2 : ℝ) + α) *
      lam ^ 3 * m ^ (-(1 / 2 : ℝ)) * N ^ (1 / 2 : ℝ)) ^ 2 =
        (d * a ^ 4 * b) * (δ ^ ((2 : ℝ) + 2 * α) * δ) * lam ^ 6 * m⁻¹ * N := by
      simp only [mul_pow, hcsq, hdsq, hmsq, hnsq]
      ring
    _ ≤ (d * a ^ 4 * b) * (δ ^ ((2 : ℝ) + 2 * α) * δ) * lam ^ 5 * m⁻¹ * N := by
      gcongr
    _ = A * (a * b * lam ^ 2 * N * δ) := by dsimp [A]; ring
    _ ≤ q ^ 2 := hprod

def SharpBroad : Prop :=
  ∀ α b : ℝ, 0 < α → 0 < b → b ≤ 1 → ∃ c : ℝ, 0 < c ∧
    ∀ δ lam m : ℝ, 0 < δ → δ ≤ 1 / 100 → 0 < lam → lam ≤ 1 → 1 ≤ m →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space), 0 < n →
    (∀ i, ‖v i‖ = 1) → (∀ i, tube δ (x i) (v i) ⊆ ball 0 1) →
    (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
    ENNReal.ofReal (lam * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y i) →
    (∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (({i | tube δ (x i) (v i) ⊆ W}.ncard : ℝ) * δ ^ 2) ≤
        ENNReal.ofReal m * volume W) →
    (∀ p w : Space, ‖w‖ = 1 →
      ({i | p ∈ Y i ∧ min ‖v i - w‖ ‖v i + w‖ ≤ b}.ncard : ℝ) ≤
        (1 / 2 : ℝ) * ({i | p ∈ Y i}.ncard : ℝ)) →
    ENNReal.ofReal (c * δ ^ ((3 / 2 : ℝ) + α) * lam ^ 3 *
      m ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (1 / 2 : ℝ)) ≤ volume (⋃ i, Y i)

theorem sharp_broad : SharpBroad := by
  obtain ⟨a, ha, ha1, hselect⟩ := WangZahlLot.wz_transverse_brush_selection
  intro α b hα hb hb1
  obtain ⟨d, hd, hbrush⟩ :=
    WangZahlLot.wz_dense_transverse_brush_bound (2 * α) b (by positivity) hb hb1
  refine ⟨Real.sqrt (d * a ^ 4 * b), by positivity, ?_⟩
  intro δ lam m hδ hδ1 hlam hlam1 hm n x v Y hn hv hT hYm hYT hmass hcount hbroad
  obtain ⟨i₀, F, hmeet, hsep, hdensity, hsel⟩ :=
    hselect b δ lam hb hb1 hδ hδ1 hlam hlam1 n x v Y hn hv hT hYm hYT hmass hbroad
  have harho : a * lam ≤ 1 := by nlinarith
  have hbr := hbrush δ (a * lam) m hδ hδ1 (by positivity) harho hm
    n x v Y hv hT hYm hYT hcount i₀ F hmeet hsep hdensity
  have hreal := sharp_brush_algebra ha hb hd hδ hlam hlam1 (by linarith : 0 < m)
    (Nat.cast_nonneg n) ENNReal.toReal_nonneg hsel hbr
  exact (ENNReal.ofReal_le_ofReal hreal).trans ENNReal.ofReal_toReal_le

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
