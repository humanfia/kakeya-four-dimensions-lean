/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeMenuBounds.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeObservedPredictors
import Submission.Obl.k4_horizontal_strict_parameter_step.PredictorBounds

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Obl.k4_critical_derivative_evaluation_lists

noncomputable section

namespace NativeModel

variable {α : Type} [MeasurableSpace α] (cfg : NativeModel α)

/-- Every sheet tested against an actual colour has uniform derivatives there.
An old source need not own the tested trajectory: its whole-square norm applies
because both sources have the same unchanged static grid cell. -/
theorem observed_menu_derivatives {k : ℕ} {s ε D a χ M : ℝ} {m : ℕ}
    {AH : Fin m → Set α} {group : Fin m → Fin 3 → ℤ} {hH : Fin m → Fin 6 → ℝ}
    {σ : Measure (α × ℝ)}
    (H : LayerAt cfg.N cfg.d cfg.e₀ cfg.π cfg.b k ε σ D a m AH group hH)
    {G : Set (α × ℝ)}
    (T : ObservedPairs G (fun i => AH i ×ˢ (univ : Set ℝ))
      (fun i => cfg.B k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i)))
    (frame : (Fin 3 → ℤ) × Fin (2 ^ cfg.T k s) → ComparisonFrame)
    (hframe : ∀ g j, (frame (g, j)).velocity = χ * (g 0 : ℝ))
    (L : Fin (cfg.n k s) → Fin 4 → ℝ) (hL : ∀ i (e : Fin 3), |L i e.succ| ≤ M)
    (hN : 0 < cfg.N k) (hK : 1 ≤ cfg.K k) (hM : 0 ≤ M)
    (hD : 0 < D) (hD1 : D ≤ 1) (hχ : 0 < χ) (hχ1 : χ ≤ 1)
    (hχeq : χ = cfg.N k ^ (-cfg.e₀))
    (hcoeff : ∀ p ∈ G, ∀ e, |cfg.b k p.1 e| ≤ 2 * cfg.K k)
    (p : α × ℝ) (hp : p ∈ G) (i : T.Index group (cfg.j k s))
    (hcolour : T.colour group (cfg.j k s) i =
      T.colour group (cfg.j k s) (T.source group (cfg.j k s) (T.mark p)))
    {τ : ℝ} (hτ : τ ∈ Icc (-1 : ℝ) 2) :
    let f := T.physicalPredictors group (cfg.j k s) frame hH L i
    let B := cfg.N k ^ ε + M * (1 + 6 * cfg.K k)
    |predictorTimeSlope f (cfg.b k p.1 0) (cfg.b k p.1 1)| ≤ 2 * B ∧
      |f 2 + f 3 * τ| ≤ 8 * B / D ∧ |f 4 + f 5 * τ| ≤ 8 * B / D := by
  have hpow : 0 ≤ cfg.N k ^ ε := Real.rpow_nonneg hN.le _
  let B := cfg.N k ^ ε + M * (1 + 6 * cfg.K k)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hNB : cfg.N k ^ ε ≤ B := by dsimp [B]; nlinarith
  have hMB : M ≤ B := by dsimp [B]; nlinarith
  have href := cfg.observed_reference_bounds H T hK hD hD1 hχ hχ1 hχeq hcoeff
  have hgrid := (H.2.2.1 (T.old (T.mark p))).1 p.1 (T.decode_old p hp).1
  cases i with
  | inl i =>
    have hg : group i.val.1 = group (T.old (T.mark p)) := congrArg Prod.fst hcolour
    rw [← hg] at hgrid
    let p₀ := (group i.val.1 1 : ℝ) * D
    let q₀ := (group i.val.1 2 : ℝ) * D
    have hb0 : cfg.b k p.1 0 ∈ Icc p₀ (p₀ + D) := by
      have hh := Int.floor_eq_iff.mp hgrid.2.1
      rw [le_div_iff₀ hD, div_lt_iff₀ hD] at hh
      exact ⟨hh.1, by dsimp [p₀]; nlinarith [hh.2]⟩
    have hb1 : cfg.b k p.1 1 ∈ Icc q₀ (q₀ + D) := by
      have hh := Int.floor_eq_iff.mp hgrid.2.2
      rw [le_div_iff₀ hD, div_lt_iff₀ hD] at hh
      exact ⟨hh.1, by dsimp [q₀]; nlinarith [hh.2]⟩
    have hbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc p₀ (p₀ + D),
        ∀ v ∈ Icc q₀ (q₀ + D), |predictor (hH i.val.1) t u v| ≤ cfg.N k ^ ε := by
      intro t ht u hu v hv
      apply (H.2.2.1 i.val.1).2.1 t ht u _ v _
      · convert hu using 1 <;> dsimp [p₀] <;> congr 1 <;> ring
      · convert hv using 1 <;> dsimp [q₀] <;> congr 1 <;> ring
    have hslope := predictor_timeSlope_bound
      (fun t ht => hbound t ht _ hb0 _ hb1)
    have hgrad := predictor_gradients_extended hD hτ hbound
    refine ⟨hslope.trans ?_, hgrad.1.trans ?_, hgrad.2.trans ?_⟩ <;> change _ ≤ _
    · exact mul_le_mul_of_nonneg_left hNB (by norm_num)
    · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hNB (by norm_num)) hD.le
    · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hNB (by norm_num)) hD.le
  | inr i =>
    let v := (frame (i.val.2, cfg.j k s i.val.1)).velocity
    have hv : |v| ≤ 3 * cfg.K k := by
      dsimp [v]
      rw [hframe]
      exact (href (Sum.inr i)).1
    have hb0 : |cfg.b k p.1 0| ≤ 3 * cfg.K k := (hcoeff p hp 0).trans (by linarith)
    have hslope := affinePredictor_time_slope (L i.val.1) (q := cfg.b k p.1 1)
      (hL _ (0 : Fin 3)) (hL _ (1 : Fin 3)) (hL _ (2 : Fin 3)) hv hb0
    have hτ2 : |τ| ≤ 2 := abs_le.mpr ⟨by linarith [hτ.1], hτ.2⟩
    have hgrad := affinePredictor_gradients (L i.val.1) v hτ2
      (hL _ (1 : Fin 3)) (hL _ (2 : Fin 3))
    have hg : 3 * M ≤ 8 * B / D := by
      apply (le_div_iff₀ hD).mpr
      nlinarith [mul_le_mul_of_nonneg_left hD1 (by linarith : 0 ≤ 3 * M)]
    refine ⟨hslope.trans ?_, hgrad.1.trans hg, hgrad.2.trans ?_⟩
    · change M * (1 + 2 * (3 * cfg.K k)) ≤
        2 * (cfg.N k ^ ε + M * (1 + 6 * cfg.K k))
      nlinarith
    · exact (by linarith : M ≤ 3 * M).trans hg

end NativeModel

end

end Submission.Obl.k4_horizontal_strict_parameter_step
