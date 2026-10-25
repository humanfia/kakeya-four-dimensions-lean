import Submission.Obl.k4_scalar_pure_multiworld_homogenization.RawSource
import Submission.Obl.k4_scalar_pure_multiworld_homogenization.Exception
import Submission.Obl.k4_scalar_pure_multiworld_homogenization.Numerics
import Submission.Obl.k4_scalar_pure_multiworld_homogenization.SelectionInterface

noncomputable section

namespace Submission.Obl.k4_scalar_pure_multiworld_homogenization

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Lib.K4ModelReduction

theorem chartLabel_inv_chartPoint (N : ℝ) (H : ℕ) (z : Incidence) :
    chartLabel (N ^ H)⁻¹ (chartPoint z) = scalarLabel N H z := by
  ext i
  fin_cases i <;>
    simp [chartLabel, chartPoint, chartEquiv, scalarLabel, y, x, div_inv_eq_mul, mul_comm]

/-- Finite-resolution scalar base flattening, uniformly in worlds and real depths. -/
theorem scalar_flattening : ScalarFlatteningStatement := by
  classical
  intro p hp
  let M := sizeBudget p
  let D := degreeBudget p
  let d : ℕ := ⌈length p⌉₊
  let C := approximationBudget M d
  have hN (k : ℕ) : 2 ≤ resolution p k := hp.1.1 k
  obtain ⟨H, hCH, hH⟩ := uniform_scalar_flattening_above M D 10 C
  choose f hfmt hf hfb hsf hsource using fun k a => raw_scalar_source hp k a
  choose h hh hb hcell hsh herr using fun k a =>
    hH (resolution p k) (hN k) (f k a) (hfmt k a)
  let g (k : ℕ) (a : Fin (p.1 k)) (r : ℝ) (l : Fin 3 → ℤ) : ℝ :=
    chartTable ((resolution p k ^ H)⁻¹) (resolution p k ^ (-r)) (h k a) l
  refine ⟨C, H, g, Eventually.of_forall ?_⟩
  intro k a r hr hrL
  have hN₀ : 0 < resolution p k := by linarith [hN k]
  have hR : 0 ≤ resolution p k ^ (M + 3) := by positivity
  have hM : 0 ≤ resolution p k ^ (2 * M) := by positivity
  have hσ : 0 < (resolution p k ^ H)⁻¹ := by positivity
  have ha : 0 < resolution p k ^ (-r) := by positivity
  have hrd : r ≤ (d : ℝ) := hrL.trans (Nat.le_ceil _)
  have hf₀ : ∀ z, 0 ≤ f k a z := fun z => (hfb k a z).1
  have hh₀ : ∀ z, 0 ≤ h k a z := fun z => (hb k a z).1
  have hbf : ∀ z, f k a z ≤ resolution p k ^ (2 * M) := fun z => (hfb k a z).2
  have hbh : ∀ z, h k a z ≤ resolution p k ^ (2 * M) := fun z => (hb k a z).2
  have hsf' : supportedInCube (f k a) (resolution p k ^ (M + 3)) := by
    have hthree : (3 : ℝ) ≤ resolution p k ^ 3 := by
      calc
        (3 : ℝ) ≤ 2 ^ 3 := by norm_num
        _ ≤ resolution p k ^ 3 := pow_le_pow_left₀ (by norm_num) (hN k) _
    have hrad : 3 * resolution p k ^ M ≤ resolution p k ^ (M + 3) := by
      rw [pow_add]
      nlinarith [mul_le_mul_of_nonneg_left hthree (by positivity : 0 ≤ resolution p k ^ M)]
    intro z i hi
    exact hsf k a z i (lt_of_le_of_lt hrad hi)
  have hcell' : ∀ z z', (∀ i ∉ ([0, 1] : List (Fin 6)), z i = z' i) →
      (∀ i ∈ ([0, 1] : List (Fin 6)),
        ⌊z i / (resolution p k ^ H)⁻¹⌋ = ⌊z' i / (resolution p k ^ H)⁻¹⌋) →
      h k a z = h k a z' := by
    intro z z' ho hc
    apply hcell k a z z' ho
    intro i hi
    simpa only [div_inv_eq_mul, mul_comm] using hc i hi
  refine ⟨?_, ?_⟩
  · intro l
    have hbnd := chartTable_bounds ((resolution p k ^ H)⁻¹)
      (resolution p k ^ (-r)) (hh k a) hh₀ hR hM (hsh k a) hbh l
    refine ⟨hbnd.1, hbnd.2.trans ?_⟩
    simpa only [Real.rpow_natCast] using table_height_power_bound (hN k) M d
  · intro G hG hlaw
    have hex := single_sample_table_exception (law p k a) (f k a) (h k a)
      (hf k a) (hh k a) hf₀ hh₀ hR hM hσ ha hsf' (hsh k a) hbf hbh
      (hsource k a) hcell' G hG hlaw
      (ENNReal.ofReal (resolution p k ^ (-(C : ℝ))))
    have hstr : ENNReal.ofReal (resolution p k ^ (2 * M)) *
        ENNReal.ofReal ((2 * resolution p k ^ (M + 3) / resolution p k ^ (-r) + 5) *
          (2 * (resolution p k ^ H)⁻¹ * (2 * resolution p k ^ (M + 3)) ^ 5)) ≤
        ENNReal.ofReal ((resolution p k ^ (10 : ℕ))⁻¹) := by
      rw [← ENNReal.ofReal_mul hM]
      exact ENNReal.ofReal_le_ofReal (straddling_power_bound (hN k) hr M d H hrd hCH)
    have hcut : ENNReal.ofReal (resolution p k ^ (-(C : ℝ))) *
        ENNReal.ofReal ((2 * resolution p k ^ (M + 3)) ^ 2 *
          (2 * resolution p k ^ (M + 3) / resolution p k ^ (-r) + 5)) ≤
        ENNReal.ofReal ((resolution p k ^ (10 : ℕ))⁻¹) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (cutoff_power_bound (hN k) hr M d hrd)
    have hbound : ENNReal.ofReal (resolution p k ^ (2 * M)) *
        ENNReal.ofReal ((2 * resolution p k ^ (M + 3) / resolution p k ^ (-r) + 5) *
          (2 * (resolution p k ^ H)⁻¹ * (2 * resolution p k ^ (M + 3)) ^ 5)) +
        2 * densityL1Distance volume (h k a) (f k a) +
        ENNReal.ofReal (resolution p k ^ (-(C : ℝ))) *
          ENNReal.ofReal ((2 * resolution p k ^ (M + 3)) ^ 2 *
            (2 * resolution p k ^ (M + 3) / resolution p k ^ (-r) + 5)) ≤
        ENNReal.ofReal (resolution p k ^ (-1 : ℝ)) := by
      calc
        _ ≤ ENNReal.ofReal ((resolution p k ^ (10 : ℕ))⁻¹) +
            2 * ENNReal.ofReal ((resolution p k ^ (10 : ℕ))⁻¹) +
            ENNReal.ofReal ((resolution p k ^ (10 : ℕ))⁻¹) :=
          add_le_add (add_le_add hstr (mul_le_mul' le_rfl (herr k a))) hcut
        _ = ENNReal.ofReal (4 * (resolution p k ^ (10 : ℕ))⁻¹) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
          norm_num
          ring
        _ ≤ _ := ENNReal.ofReal_le_ofReal (four_error_power_bound (hN k))
    have hfinal := hex.trans hbound
    simp only [chartLabel_inv_chartPoint] at hfinal
    exact hfinal

end Submission.Obl.k4_scalar_pure_multiworld_homogenization
