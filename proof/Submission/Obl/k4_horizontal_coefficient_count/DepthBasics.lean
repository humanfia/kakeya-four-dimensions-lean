import Submission.Obl.k4_horizontal_coefficient_count.LMSetup
import Submission.Obl.k4_horizontal_coefficient_count.Bounded

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

namespace DepthData

variable {α : Type} [MeasurableSpace α] {D : DepthData α} (h : D.Hyp)

include h

theorem Hyp.q_pos : 0 < D.q := by
  have hp : (0 : ℝ) < 2 ^ D.T := by positivity
  nlinarith [h.hqT]

theorem Hyp.q_le_one : D.q ≤ 1 := by
  have hp : (1 : ℝ) ≤ 2 ^ D.T := one_le_pow₀ (by norm_num)
  nlinarith [h.hqT, mul_le_mul_of_nonneg_left hp h.q_pos.le]

theorem Hyp.a_le_q : D.a ≤ D.q :=
  h.haq.trans (by nlinarith [h.q_pos, h.q_le_one])

theorem Hyp.a_le_one : D.a ≤ 1 := h.a_le_q.trans h.q_le_one

theorem Hyp.mu_mass_le : D.μ univ ≤ ENNReal.ofReal D.K := by
  letI := h.hν
  exact current_total_mass_le D.ν D.μ h.hμν h.hμsupp

theorem Hyp.block_subset_unit (j : Fin (2 ^ D.T)) : tblock D.q j ⊆ Icc (0 : ℝ) 1 := by
  intro t ht
  have hj : (j : ℝ) + 1 ≤ (2 : ℝ) ^ D.T := by exact_mod_cast Nat.succ_le_of_lt j.isLt
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have hprod : ((2 : ℝ) ^ D.T) * D.q = 1 := by simpa only [mul_comm] using h.hqT
  exact ⟨(mul_nonneg hj0 h.q_pos.le).trans ht.1,
    ht.2.trans ((mul_le_mul_of_nonneg_right hj h.q_pos.le).trans_eq hprod)⟩

omit h in
def midpoint (D : DepthData α) (j : Fin (2 ^ D.T)) : ℝ :=
  ((j : ℝ) + 1 / 2) * D.q

theorem Hyp.block_time_gap (j : Fin (2 ^ D.T)) {t : ℝ} (ht : t ∈ tblock D.q j) :
    |t - D.midpoint j| ≤ D.q / 2 := by
  change (j : ℝ) * D.q ≤ t ∧ t ≤ ((j : ℝ) + 1) * D.q at ht
  rw [abs_le]
  dsimp [midpoint]
  constructor <;> nlinarith only [ht.1, ht.2]

theorem Hyp.midpoint_abs_le_one (j : Fin (2 ^ D.T)) : |D.midpoint j| ≤ 1 := by
  have ht : D.midpoint j ∈ tblock D.q j := by
    dsimp [midpoint, tblock]
    constructor <;> nlinarith [h.q_pos]
  have hh := h.block_subset_unit j ht
  simpa only [abs_of_nonneg hh.1] using hh.2

theorem Hyp.incidence_witness_floor (i : Fin D.n) :
    ENNReal.ofReal (D.a ^ D.d / D.K ^ 3 * D.q ^ 4) ≤
      D.μ (D.B i ×ˢ tblock D.q (D.j i)) := by
  have hK : 0 < D.K := by linarith [h.hK]
  have hq := h.q_pos
  have haD : 0 < D.a ^ D.d := Real.rpow_pos_of_pos h.ha0 _
  have hnum : D.a ^ D.d / D.K ^ 3 * D.q ^ 4 ≤
      (D.q / D.K) * (D.a ^ D.d * D.q ^ 2 * D.g / D.K) := by
    have hh := mul_le_mul_of_nonneg_left h.hqg
      (by positivity : 0 ≤ D.a ^ D.d * D.q ^ 3 / D.K ^ 3)
    convert hh using 1 <;> field_simp <;> ring
  calc
    _ ≤ ENNReal.ofReal ((D.q / D.K) * (D.a ^ D.d * D.q ^ 2 * D.g / D.K)) :=
      ENNReal.ofReal_le_ofReal hnum
    _ = ENNReal.ofReal (D.q / D.K) * ENNReal.ofReal (D.a ^ D.d * D.q ^ 2 * D.g / D.K) :=
      ENNReal.ofReal_mul (by positivity)
    _ ≤ ENNReal.ofReal (D.q / D.K) * D.ν (D.A i) := mul_le_mul' le_rfl (h.hνA i)
    _ ≤ _ := h.hμB i

theorem Hyp.witness_disjoint {i i' : Fin D.n} (hne : i ≠ i') (hj : D.j i = D.j i') :
    Disjoint (D.B i ×ˢ tblock D.q (D.j i)) (D.B i' ×ˢ tblock D.q (D.j i')) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨hp, ht⟩ ⟨hp', ht'⟩
  exact Set.disjoint_left.mp (h.hdisj i i' hne hj) (h.hBA i hp) (h.hBA i' hp')

omit h in
def groupReference (D : DepthData α) (g : ℤ × ℤ × ℤ) : Fin 3 → ℝ :=
  ![D.a * (g.2.1 : ℝ), D.a * (g.2.2 : ℝ), D.χ * (g.1 : ℝ)]

theorem Hyp.group_coordinate_gaps (g : ℤ × ℤ × ℤ) {l : α}
    (hl : l ∈ groupSet D.b D.χ D.a g) :
    |D.b l 0 - D.groupReference g 0| ≤ D.a ∧
      |D.b l 1 - D.groupReference g 1| ≤ D.a ∧
      |D.b l 3 - D.groupReference g 2| ≤ D.χ := by
  have hgap (x r : ℝ) (hr : 0 < r) (z : ℤ) (hz : ⌊x / r⌋ = z) :
      |x - r * (z : ℝ)| ≤ r := by
    have hh := Int.floor_eq_iff.mp hz
    have hlo := (le_div_iff₀ hr).mp hh.1
    have hhi := (div_lt_iff₀ hr).mp hh.2
    rw [abs_of_nonneg (by nlinarith)]
    nlinarith
  exact ⟨hgap _ _ h.ha0 _ hl.2.1, hgap _ _ h.ha0 _ hl.2.2,
    hgap _ _ h.hχ0 _ hl.1⟩

theorem Hyp.good_position_bounds {l : α} (hl : l ∈ goodSet D.b D.K D.χ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : |X1 (D.b l) t| ≤ D.K ∧ |X2 (D.b l) t| ≤ D.K := by
  have ht' : |t| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  constructor
  · calc
      _ ≤ |D.b l 0| + |t| * |D.b l 3| := by simpa only [X1, abs_mul] using abs_add_le (D.b l 0) (t * D.b l 3)
      _ ≤ |D.b l 0| + 1 * |D.b l 3| := by gcongr
      _ ≤ D.K := by linarith [hl.1, abs_nonneg (D.b l 1), abs_nonneg (D.b l 4)]
  · calc
      _ ≤ |D.b l 1| + |t| * |D.b l 4| := by simpa only [X2, abs_mul] using abs_add_le (D.b l 1) (t * D.b l 4)
      _ ≤ |D.b l 1| + 1 * |D.b l 4| := by gcongr
      _ ≤ D.K := by linarith [hl.1, abs_nonneg (D.b l 0), abs_nonneg (D.b l 3)]

theorem Hyp.reference_coefficient_bounds (g : ℤ × ℤ × ℤ) {l : α}
    (hg : l ∈ groupSet D.b D.χ D.a g) (hl : l ∈ goodSet D.b D.K D.χ) :
    |D.groupReference g 0| ≤ 2 * D.K ∧ |D.groupReference g 2| ≤ 2 * D.K := by
  have hgap := h.group_coordinate_gaps g hg
  have h0 : |D.b l 0| ≤ D.K := by
    linarith [hl.1, abs_nonneg (D.b l 1), abs_nonneg (D.b l 3), abs_nonneg (D.b l 4)]
  have h3 : |D.b l 3| ≤ D.K := by
    linarith [hl.1, abs_nonneg (D.b l 0), abs_nonneg (D.b l 1), abs_nonneg (D.b l 4)]
  constructor
  · have hh := abs_sub_le (D.groupReference g 0) (D.b l 0) 0
    rw [sub_zero, sub_zero, abs_sub_comm (D.groupReference g 0)] at hh
    linarith [h.a_le_one, h.hK]
  · have hh := abs_sub_le (D.groupReference g 2) (D.b l 3) 0
    rw [sub_zero, sub_zero, abs_sub_comm (D.groupReference g 2)] at hh
    linarith [h.a_le_one, h.hχa, h.hK]

theorem Hyp.group_reference_errors (g : ℤ × ℤ × ℤ) {l : α}
    (hg : l ∈ groupSet D.b D.χ D.a g) (hl : l ∈ goodSet D.b D.K D.χ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |X1 (D.b l) t - (D.groupReference g 0 + t * D.groupReference g 2)| ≤ 2 * D.a ∧
      |X2 (D.b l) t - (D.groupReference g 1 - t * D.groupReference g 0)| ≤ 3 * D.a := by
  obtain ⟨hgap0, hgap1, hgap3⟩ := h.group_coordinate_gaps g hg
  have ht' : |t| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  constructor
  · calc
      _ = |(D.b l 0 - D.groupReference g 0) + t * (D.b l 3 - D.groupReference g 2)| := by
        dsimp [X1]; congr 1; ring
      _ ≤ |D.b l 0 - D.groupReference g 0| + |t| * |D.b l 3 - D.groupReference g 2| := by
        simpa only [abs_mul] using abs_add_le (D.b l 0 - D.groupReference g 0) (t * (D.b l 3 - D.groupReference g 2))
      _ ≤ D.a + 1 * D.χ := by gcongr
      _ ≤ 2 * D.a := by linarith [h.hχa]
  · calc
      _ = |(D.b l 1 - D.groupReference g 1) + t * (D.b l 4 + D.b l 0) -
          t * (D.b l 0 - D.groupReference g 0)| := by dsimp [X2]; congr 1; ring
      _ ≤ |D.b l 1 - D.groupReference g 1| + |t| * |D.b l 4 + D.b l 0| +
          |t| * |D.b l 0 - D.groupReference g 0| := by
        simpa only [sub_eq_add_neg, abs_neg, abs_mul] using abs_add_three
          (D.b l 1 - D.groupReference g 1) (t * (D.b l 4 + D.b l 0))
          (-(t * (D.b l 0 - D.groupReference g 0)))
      _ ≤ D.a + 1 * D.χ + 1 * D.a := by gcongr; exact hl.2.1
      _ ≤ 3 * D.a := by linarith [h.hχa]

end DepthData
end
end Submission.Obl.k4_horizontal_coefficient_count
