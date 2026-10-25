import Submission.Obl.k4_raw_critical_segment_forests.Layers
import Submission.Obl.k4_raw_critical_segment_forests.Widths

namespace Submission.Obl.k4_raw_localized_native_systems

open MeasureTheory
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_raw_critical_segment_forests

noncomputable section

/-- Original coverage forces every genuine level to contain an original label. -/
theorem source_level_nonempty {p : Data} {k M D m : ℕ} {r : ℕ → ℝ}
    {F : Forest p k} (hcore : F.Core M D m r) {i : ℕ} (hi : i < m) :
    ∃ b : Fin F.C, F.lev b = i := by
  classical
  by_contra h
  have hnone : ∀ b : Fin F.C, F.lev b ≠ i := by simpa only [not_exists] using h
  have hcov := hcore.2.2.2.1 i hi
  simp only [if_neg (hnone _), Finset.sum_const_zero] at hcov
  have hκ : 0 < F.κ := lt_of_lt_of_le zero_lt_one hcore.1
  have hpos : 0 < ENNReal.ofReal F.κ⁻¹ := ENNReal.ofReal_pos.mpr (inv_pos.mpr hκ)
  exact (not_le_of_gt hpos) hcov

/-- The lower edge of a homogeneous logarithmic width band is an exact
narrowness exponent for every original chart of that level. -/
theorem homogeneous_level_narrow {p : Data} {k : ℕ} (hp : Valid p)
    {F : Forest p k} {width : Fin F.C → ℝ} {nw : ℕ → ℝ} {band : ℝ}
    (hexact : ∀ b, p.N k ^ (-width b) =
      |(F.Q b).det| * (4 : ℝ) ^ F.T (F.lev b))
    (hband : ∀ b, |width b - nw (F.lev b)| ≤ band)
    {i : ℕ} (b : Fin F.C) (hb : F.lev b = i) :
    |(F.Q b).det| * (4 : ℝ) ^ F.T i ≤ p.N k ^ (-(nw i - band)) := by
  have he := hexact b
  have hw := (abs_le.mp (hband b)).1
  rw [hb] at he hw
  rw [← he]
  exact Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one k) (by linarith only [hw])

/-- The original inverse-frame format gives a fixed upper bound for the
actual, sample-dependent lower edge of every nonempty homogeneous width band. -/
theorem homogeneous_level_width_upper {p : Data} {k M D m : ℕ} {r : ℕ → ℝ}
    (hp : Valid p) {F : Forest p k} (hcore : F.Core M D m r)
    {width : Fin F.C → ℝ} {nw : ℕ → ℝ} {band : ℝ}
    (hexact : ∀ b, p.N k ^ (-width b) =
      |(F.Q b).det| * (4 : ℝ) ^ F.T (F.lev b))
    (hband : ∀ b, |width b - nw (F.lev b)| ≤ band)
    {i : ℕ} (hi : i < m) : nw i - band ≤ 2 * (M : ℝ) := by
  obtain ⟨b, hb⟩ := source_level_nonempty hcore hi
  have hc := (hcore.2.2.2.2.2 b).2.2.1
  have hlo := chart_width_lower (hp.scale_pos k) hc
  rw [hb] at hlo
  have hhi := homogeneous_level_narrow hp hexact hband b hb
  have hN : 1 < p.N k := lt_of_lt_of_le (by norm_num) (hp.scale_ge_two k)
  have he := (Real.rpow_le_rpow_left_iff hN).mp (hlo.trans hhi)
  linarith only [he]

end
end Submission.Obl.k4_raw_localized_native_systems
