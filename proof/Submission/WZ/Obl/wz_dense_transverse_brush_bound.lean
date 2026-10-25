-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_dense_transverse_brush_bound.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_transverse_stem_deletion
import Submission.WZ.Obl.wz_off_stem_brush_overlap
import Submission.WZ.Obl.wz_finite_shading_second_moment

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_dense_transverse_brush_bound

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya

/-- Scalar cancellation after the second-moment estimate. -/
theorem small_scale_algebra {a C δ rho m N q ε : ℝ}
    (ha : 0 < a) (hC : 0 < C) (hδ : 0 < δ) (hrho : 0 < rho) (hm : 0 < m)
    (h : ((rho / 2) * δ ^ 2) ^ 2 * N ≤
      (C * m * δ ^ ((2 : ℝ) - ε) * (a * rho)⁻¹) * q) :
    (a / (4 * C)) * δ ^ ((2 : ℝ) + ε) * rho ^ 3 * m⁻¹ * N ≤ q := by
  have hA : 0 < C * m * δ ^ ((2 : ℝ) - ε) * (a * rho)⁻¹ := by positivity
  have hp : δ ^ ((2 : ℝ) + ε) * δ ^ ((2 : ℝ) - ε) = δ ^ 4 := by
    rw [← Real.rpow_add hδ]
    norm_num [show (2 : ℝ) + ε + (2 - ε) = 4 by ring]
  apply (mul_le_mul_iff_right₀ hA).mp
  calc
    (C * m * δ ^ ((2 : ℝ) - ε) * (a * rho)⁻¹) *
        (a / (4 * C) * δ ^ ((2 : ℝ) + ε) * rho ^ 3 * m⁻¹ * N) =
        (δ ^ ((2 : ℝ) + ε) * δ ^ ((2 : ℝ) - ε)) * (rho / 2) ^ 2 * N := by
      field_simp
      ring
    _ = ((rho / 2) * δ ^ 2) ^ 2 * N := by rw [hp]; ring
    _ ≤ _ := h

/-- The unit-ball count controls the complementary range of scales. -/
theorem large_scale_algebra {a δ rho m N q ε : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hrho : 0 < rho)
    (hm : 0 < m) (hN : 0 ≤ N) (hε : 0 < ε) (hscale : a * rho ≤ δ)
    (hcount : N * δ ^ 2 ≤ 16 * m) (hdense : rho * δ ^ 2 ≤ q) :
    (a ^ 2 / 16) * δ ^ ((2 : ℝ) + ε) * rho ^ 3 * m⁻¹ * N ≤ q := by
  have hp : δ ^ ((2 : ℝ) + ε) ≤ δ ^ 2 := by
    rw [Real.rpow_add hδ, Real.rpow_two]
    exact mul_le_of_le_one_right (sq_nonneg δ) (Real.rpow_le_one hδ.le hδ1 hε.le)
  calc
    (a ^ 2 / 16) * δ ^ ((2 : ℝ) + ε) * rho ^ 3 * m⁻¹ * N ≤
        (a ^ 2 / 16) * δ ^ 2 * rho ^ 3 * m⁻¹ * N := by gcongr
    _ = (a ^ 2 * rho ^ 3) * ((N * δ ^ 2) / (16 * m)) := by ring
    _ ≤ a ^ 2 * rho ^ 3 := by
      apply mul_le_of_le_one_right (by positivity)
      exact (div_le_one (by positivity : 0 < 16 * m)).2 hcount
    _ ≤ rho * δ ^ 2 := by
      have hs := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity : 0 ≤ a * rho) hscale 2) hrho.le
      nlinarith
    _ ≤ q := hdense

end WangZahlLot.Obl.wz_dense_transverse_brush_bound

theorem WangZahlLot.wz_dense_transverse_brush_bound : ∀ ε b : ℝ, 0 < ε → 0 < b → b ≤ 1 → ∃ d : ℝ, 0 < d ∧ ∀ δ rho m : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → 0 < rho → rho ≤ 1 → 1 ≤ m → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), (∀ i : Fin n, ‖v i‖ = 1) → (∀ i : Fin n, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ i : Fin n, MeasurableSet (Y i)) → (∀ i : Fin n, Y i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i))) → (∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W} : ℕ) : ℝ) * δ ^ 2) ≤ ENNReal.ofReal m * MeasureTheory.volume W) → ∀ (i₀ : Fin n) (F : Finset (Fin n)), (∀ i : Fin n, i ∈ F → (Metric.thickening δ (segment ℝ (x i) (x i + v i)) ∩ Metric.thickening δ (segment ℝ (x i₀) (x i₀ + v i₀))).Nonempty) → (∀ i : Fin n, i ∈ F → b ≤ min ‖v i - v i₀‖ ‖v i + v i₀‖) → (∀ i : Fin n, i ∈ F → ENNReal.ofReal (rho * δ ^ 2) ≤ MeasureTheory.volume (Y i)) → d * δ ^ ((2 : ℝ) + ε) * rho ^ 3 * m⁻¹ * (F.card : ℝ) ≤ (MeasureTheory.volume (⋃ i : Fin n, Y i)).toReal := by
  classical
  intro ε b hε hb hb1
  obtain ⟨a, ha, ha1, hdelete⟩ := WangZahlLot.wz_transverse_stem_deletion b hb hb1
  obtain ⟨C, hC, hoverlap⟩ := WangZahlLot.wz_off_stem_brush_overlap ε hε
  refine ⟨min (a / (4 * C)) (a ^ 2 / 16), lt_min (by positivity) (by positivity), ?_⟩
  intro δ rho m hδ hδ100 hrho hrho1 hm n x v Y hv hball hY hsub hcount
    i₀ F hmeet hangle hdense
  let E := ⋃ i : Fin n, Y i
  have hEball : E ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 :=
    Set.iUnion_subset (fun i => (hsub i).trans (hball i))
  have hEfin : MeasureTheory.volume E ≠ ⊤ :=
    ne_top_of_le_ne_top MeasureTheory.measure_ball_lt_top.ne (MeasureTheory.measure_mono hEball)
  have hEmeas : MeasurableSet E := MeasurableSet.iUnion hY
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have hN : 0 ≤ (F.card : ℝ) := Nat.cast_nonneg _
  have hq : 0 ≤ (MeasureTheory.volume E).toReal := ENNReal.toReal_nonneg
  change min (a / (4 * C)) (a ^ 2 / 16) * δ ^ ((2 : ℝ) + ε) * rho ^ 3 *
    m⁻¹ * (F.card : ℝ) ≤ (MeasureTheory.volume E).toReal
  by_cases hscale : δ ≤ a * rho
  · let Z : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space := fun i =>
      Y i \ Metric.thickening (a * rho) (Set.range (fun t : ℝ => x i₀ + t • v i₀))
    have hZmeas : ∀ i : Fin n, i ∈ F → MeasurableSet (Z i) :=
      fun i _ => (hY i).diff Metric.isOpen_thickening.measurableSet
    have hZE : ∀ i : Fin n, i ∈ F → Z i ⊆ E :=
      fun i _ => Set.Subset.trans Set.sdiff_subset (Set.subset_iUnion Y i)
    have hZtube : ∀ i : Fin n, i ∈ F → Z i ⊆
        Metric.thickening δ (segment ℝ (x i) (x i + v i)) \ Metric.thickening (a * rho) (Set.range (fun t : ℝ => x i₀ + t • v i₀)) :=
      fun i _ p hp => ⟨hsub i hp.1, hp.2⟩
    have hZdense : ∀ i : Fin n, i ∈ F →
        (rho / 2) * δ ^ 2 ≤ (MeasureTheory.volume (Z i)).toReal := by
      intro i hi
      apply (ENNReal.ofReal_le_iff_le_toReal
        (ne_top_of_le_ne_top hEfin (MeasureTheory.measure_mono (hZE i hi)))).mp
      exact hdelete δ rho hδ hrho hrho1 hscale (x i) (v i) (x i₀) (v i₀) (Y i)
        (hv i) (hv i₀) (hangle i hi) (hY i) (hsub i) (hdense i hi)
    have hr1 : a * rho ≤ 1 := by nlinarith
    have hrow := hoverlap δ (a * rho) m hδ hδ100 hscale hr1 hm
      n x v Z hv hball hcount i₀ F hZmeas hZtube hmeet
    have hmoment := WangZahlLot.wz_finite_shading_second_moment n F Z E
      ((rho / 2) * δ ^ 2) (C * m * δ ^ ((2 : ℝ) - ε) * (a * rho)⁻¹)
      hEmeas hEfin hZmeas hZE (by positivity) (by positivity) hZdense hrow
    calc
      min (a / (4 * C)) (a ^ 2 / 16) * δ ^ ((2 : ℝ) + ε) * rho ^ 3 *
          m⁻¹ * (F.card : ℝ) ≤
          (a / (4 * C)) * δ ^ ((2 : ℝ) + ε) * rho ^ 3 * m⁻¹ * (F.card : ℝ) := by
        gcongr
        exact min_le_left _ _
      _ ≤ _ := WangZahlLot.Obl.wz_dense_transverse_brush_bound.small_scale_algebra
        ha hC hδ hrho hmpos hmoment
  · rcases F.eq_empty_or_nonempty with hF | hF
    · simp only [hF, Finset.card_empty, Nat.cast_zero, mul_zero]
      exact hq
    obtain ⟨i, hi⟩ := hF
    have hsingle : rho * δ ^ 2 ≤ (MeasureTheory.volume E).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hEfin).mp
        ((hdense i hi).trans (MeasureTheory.measure_mono (Set.subset_iUnion Y i)))
    have hcountBall := hcount (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1)
      (convex_ball _ _)
    have hall : {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
        Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1} = Set.univ :=
      Set.eq_univ_of_forall hball
    rw [hall] at hcountBall
    simp only [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hcountBall
    rw [EuclideanSpace.volume_ball_fin_three] at hcountBall
    norm_num only [ENNReal.ofReal_one, one_pow, one_mul] at hcountBall
    rw [← ENNReal.ofReal_mul hmpos.le] at hcountBall
    have hn : (n : ℝ) * δ ^ 2 ≤ m * (Real.pi * 4 / 3) :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hcountBall
    have hFle : (F.card : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (show F.card ≤ n by simpa using F.card_le_univ)
    have hcard : (F.card : ℝ) * δ ^ 2 ≤ 16 * m := by
      have h₁ := mul_le_mul_of_nonneg_right hFle (sq_nonneg δ)
      have h₂ : Real.pi * 4 / 3 ≤ (16 : ℝ) := by linarith [Real.pi_lt_four]
      have h₃ := mul_le_mul_of_nonneg_left h₂ hmpos.le
      nlinarith
    calc
      min (a / (4 * C)) (a ^ 2 / 16) * δ ^ ((2 : ℝ) + ε) * rho ^ 3 *
          m⁻¹ * (F.card : ℝ) ≤
          (a ^ 2 / 16) * δ ^ ((2 : ℝ) + ε) * rho ^ 3 * m⁻¹ * (F.card : ℝ) := by
        gcongr
        exact min_le_right _ _
      _ ≤ _ := WangZahlLot.Obl.wz_dense_transverse_brush_bound.large_scale_algebra
        ha hδ (hδ100.trans (by norm_num)) hrho hmpos hN hε
        (le_of_not_ge hscale) hcard hsingle
