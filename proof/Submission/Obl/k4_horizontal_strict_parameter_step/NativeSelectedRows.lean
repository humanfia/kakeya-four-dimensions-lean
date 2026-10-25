/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 89648dfeac59b903d3d93ae0dca8d07a6202ebdf, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeSelectedRows.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.SelectedRowDefinitions
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeGoodSelection
import Submission.Obl.k4_horizontal_strict_parameter_step.PredictorBounds

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps
open Submission.Obl.k4_critical_derivative_evaluation_lists

noncomputable section

namespace NativeComparisonData

variable {α : Type} [MeasurableSpace α] {cfg : NativeModel α}
  {k : ℕ} {s : ℝ} {σ : Measure (α × ℝ)} (c : NativeComparisonData cfg k s σ)

/-- The successful observed mark certifies the same whole product for its
selected old/native pair, independent of later current incidence restrictions. -/
theorem paired_product_comparison {M δ : ℝ} (hprod : NativeProductComparison c M)
    {h : Fin c.m} {i : Fin (cfg.n k s)} (hp : c.paired M δ h i) :
    ∀ t ∈ Data.I (cfg.T k s) (cfg.j k s i),
    ∀ p ∈ Icc ((c.group h 1 : ℝ) * c.D) (((c.group h 1 : ℝ) + 1) * c.D),
    ∀ q ∈ Icc ((c.group h 2 : ℝ) * c.D) (((c.group h 2 : ℝ) + 1) * c.D),
      |predictor (c.nativePhysical h i) t p q - predictor (c.hH h) t p q| ≤ M := by
  obtain ⟨r, hold, hnative, hgood, -, -⟩ := hp
  have hh := hprod r hgood
  change (∀ t ∈ Data.I (cfg.T k s) (cfg.j k s (c.support.table.native r)),
    ∀ p ∈ Icc ((c.group (c.support.table.old r) 1 : ℝ) * c.D)
      (((c.group (c.support.table.old r) 1 : ℝ) + 1) * c.D),
    ∀ q ∈ Icc ((c.group (c.support.table.old r) 2 : ℝ) * c.D)
      (((c.group (c.support.table.old r) 2 : ℝ) + 1) * c.D),
      |predictor (c.nativePhysical (c.support.table.old r) (c.support.table.native r)) t p q -
        predictor (c.hH (c.support.table.old r)) t p q| ≤ M) at hh
  rwa [hold, hnative] at hh

/-- Native block selection gives a uniformly bounded row on ALL real times.
Closed endpoints cost a factor two; the number of blocks never enters. -/
theorem selectedF_bound {M δ : ℝ} (ha : 0 < c.a) (hM : 0 ≤ M)
    (hprod : NativeProductComparison c M)
    (choice : Fin c.m → Fin (2 ^ cfg.T k s) → Option (Fin (cfg.n k s)))
    (hchoice : ∀ h j i, choice h j = some i → c.paired M δ h i ∧ cfg.j k s i = j)
    (h : Fin c.m) (t : ℝ) (e : Fin 2) :
    |c.selectedF choice h t e| ≤ 4 * (M / c.a) := by
  have hrow (j : Fin (2 ^ cfg.T k s)) (t : ℝ)
      (ht : t ∈ Icc ((j : ℝ) / (2 ^ cfg.T k s : ℕ)) (((j : ℝ) + 1) / (2 ^ cfg.T k s : ℕ))) :
      ∀ e, |c.selectedRow choice h j t e| ≤ 2 * (M / c.a) := by
    cases hj : choice h j with
    | none => simp only [selectedRow, hj, Pi.zero_apply, abs_zero]; intro e; positivity
    | some i =>
      have hc := hchoice h j i hj
      have hti : t ∈ Data.I (cfg.T k s) (cfg.j k s i) := by
        rw [hc.2]
        simpa only [Data.I, Nat.cast_pow, Nat.cast_ofNat] using ht
      have hp := c.paired_product_comparison hprod hc.1 t hti
      simp only [selectedRow, hj]
      apply normalizedRow_bound (p₀ := (c.group h 1 : ℝ) * c.D)
        (q₀ := (c.group h 2 : ℝ) * c.D) c.D_pos ha
      intro p hp' q hq'
      have hp'' : p ∈ Icc ((c.group h 1 : ℝ) * c.D) (((c.group h 1 : ℝ) + 1) * c.D) := by
        constructor <;> nlinarith [hp'.1, hp'.2]
      have hq'' : q ∈ Icc ((c.group h 2 : ℝ) * c.D) (((c.group h 2 : ℝ) + 1) * c.D) := by
        constructor <;> nlinarith [hq'.1, hq'.2]
      exact (hp p hp'' q hq'').trans_eq (by field_simp)
  exact (closedBlockRow_bound (by positivity : 0 < 2 ^ cfg.T k s)
    (c.selectedRow choice h) (by positivity : 0 ≤ 2 * (M / c.a)) hrow t e).trans_eq (by ring)

end NativeComparisonData

end

end Submission.Obl.k4_horizontal_strict_parameter_step
