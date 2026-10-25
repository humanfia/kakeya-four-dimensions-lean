import Submission.Obl.k4_quadratic_mesh_coefficient_calibration.DiscreteCoefficientCalibration
import Submission.Lib.K4CommonLocalChoice

/-! Finite occupied cells of the original measure, with actual good witnesses.
The cells are rescaled into the unit cube only for coefficient calibration;
the source events retain the original floor labels and original mass.

Adapted from: here:o200 (session x0829, commit 40d3c941; as at commit 6f32949a),
file `Submission/Obl/k4_finite_projected_horizontal_candidates/OccupiedGridCalibration.lean`,
moved into this obligation's namespace. -/

namespace Submission.Obl.k4_quadratic_mesh_coefficient_calibration

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4CommonLocalChoice (cell)

noncomputable section

def calibrationBase (H : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun j => (x j + 2 * H) / (8 * H)

def calibrationCell (H h : ℝ) (q : Fin 3 → ℤ) : Set (Fin 3 → ℝ) :=
  univ.pi fun j => Ico ((h * (q j : ℝ) + 2 * H) / (8 * H))
    ((h * ((q j : ℝ) + 1) + 2 * H) / (8 * H))

theorem measurableSet_calibrationCell (H h : ℝ) (q : Fin 3 → ℤ) :
    MeasurableSet (calibrationCell H h q) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem calibrationCell_floor {H h : ℝ} (hH : 0 < H) (hh : 0 < h)
    {q : Fin 3 → ℤ} {x : Fin 3 → ℝ} (hx : x ∈ calibrationCell H h q) :
    cell h (fun j => 8 * H * x j - 2 * H) = q := by
  funext j
  have hj := mem_univ_pi.mp hx j
  change (h * (q j : ℝ) + 2 * H) / (8 * H) ≤ x j ∧
    x j < (h * ((q j : ℝ) + 1) + 2 * H) / (8 * H) at hj
  have hlo := (div_le_iff₀ (by positivity : 0 < 8 * H)).mp hj.1
  have hup := (lt_div_iff₀ (by positivity : 0 < 8 * H)).mp hj.2
  apply Int.floor_eq_iff.mpr
  constructor
  · apply (le_div_iff₀ hh).mpr
    nlinarith
  · apply (div_lt_iff₀ hh).mpr
    nlinarith

theorem calibrationCell_disjoint {H h : ℝ} (hH : 0 < H) (hh : 0 < h) :
    Pairwise (fun q r : Fin 3 → ℤ => Disjoint (calibrationCell H h q)
      (calibrationCell H h r)) := by
  intro q r hqr
  apply disjoint_left.mpr
  intro x hx hy
  exact hqr ((calibrationCell_floor hH hh hx).symm.trans (calibrationCell_floor hH hh hy))

theorem volume_calibrationCell {H h : ℝ} (hH : 0 < H) (hh : 0 ≤ h)
    (q : Fin 3 → ℤ) :
    volume (calibrationCell H h q) = ENNReal.ofReal ((h / (8 * H)) ^ 3) := by
  rw [calibrationCell, volume_pi_pi]
  simp only [Real.volume_Ico]
  have hd (j : Fin 3) : (h * ((q j : ℝ) + 1) + 2 * H) / (8 * H) -
      (h * (q j : ℝ) + 2 * H) / (8 * H) = h / (8 * H) := by ring
  simp_rw [hd]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by positivity)]

theorem calibrationBase_mem_cell {H h : ℝ} (hH : 0 < H) (hh : 0 < h)
    (x : Fin 3 → ℝ) : calibrationBase H x ∈ calibrationCell H h (cell h x) := by
  apply mem_univ_pi.mpr
  intro j
  constructor
  · apply (div_le_div_iff_of_pos_right (by positivity : 0 < 8 * H)).mpr
    have hl := (le_div_iff₀ hh).mp (Int.floor_le (x j / h))
    dsimp only [cell]
    nlinarith
  · apply (div_lt_div_iff_of_pos_right (by positivity : 0 < 8 * H)).mpr
    have hu := (div_lt_iff₀ hh).mp (Int.lt_floor_add_one (x j / h))
    dsimp only [cell]
    nlinarith

theorem calibrationCell_near_witness {H h : ℝ} (hH : 0 < H) (hh : 0 < h)
    {q : Fin 3 → ℤ} {y : Fin 3 → ℝ} (hy : cell h y = q)
    {x : Fin 3 → ℝ} (hx : x ∈ calibrationCell H h q) (j : Fin 3) :
    |x j - calibrationBase H y j| ≤ h / (8 * H) := by
  have hym := calibrationBase_mem_cell hH hh y
  rw [hy] at hym
  have hxj := mem_univ_pi.mp hx j
  have hyj := mem_univ_pi.mp hym j
  have hd : (h * ((q j : ℝ) + 1) + 2 * H) / (8 * H) -
      (h * (q j : ℝ) + 2 * H) / (8 * H) = h / (8 * H) := by ring
  exact (abs_lt.mpr ⟨by linarith [hxj.1, hyj.2], by linarith [hxj.2, hyj.1]⟩).le

theorem calibrationBase_bounds {H : ℝ} (hH : 0 < H) {y : Fin 3 → ℝ}
    (hy : ∀ j, |y j| ≤ H) (j : Fin 3) :
    1 / 8 ≤ calibrationBase H y j ∧ calibrationBase H y j ≤ 3 / 8 := by
  obtain ⟨hl, hu⟩ := abs_le.mp (hy j)
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 8 * H)).mpr
    linarith
  · apply (div_le_iff₀ (by positivity : 0 < 8 * H)).mpr
    linarith

theorem euclidean_norm_le_one_of_half_cube {x : Fin 3 → ℝ}
    (hx : x ∈ Icc (0 : Fin 3 → ℝ) (fun _ => 1 / 2)) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3))‖ ≤ 1 := by
  have hs : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3))‖ ^ 2 ≤ 3 * (1 / 2 : ℝ) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _j : Fin 3, (1 / 2 : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        have hl := hx.1 j
        have hu := hx.2 j
        change 0 ≤ x j at hl
        change x j ≤ 1 / 2 at hu
        simpa only [Real.norm_eq_abs, sq_abs] using
          pow_le_pow_left₀ hl hu 2
      _ = _ := by simp
  nlinarith [norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3))]

theorem calibrationBase_norm {H : ℝ} (hH : 0 < H) {y : Fin 3 → ℝ}
    (hy : ∀ j, |y j| ≤ H) :
    ‖(WithLp.toLp 2 (calibrationBase H y) : EuclideanSpace ℝ (Fin 3))‖ ≤ 1 := by
  apply euclidean_norm_le_one_of_half_cube
  constructor <;> intro j
  · change 0 ≤ calibrationBase H y j
    linarith [(calibrationBase_bounds hH hy j).1]
  · change calibrationBase H y j ≤ 1 / 2
    linarith [(calibrationBase_bounds hH hy j).2]

theorem calibrationCell_half_cube {H h : ℝ} (hH : 0 < H) (hh : 0 < h)
    (hhH : h ≤ H) {q : Fin 3 → ℤ} {y : Fin 3 → ℝ}
    (hy : ∀ j, |y j| ≤ H) (hyq : cell h y = q) :
    calibrationCell H h q ⊆ Icc (0 : Fin 3 → ℝ) (fun _ => 1 / 2) := by
  have hmesh : h / (8 * H) ≤ 1 / 8 := by
    apply (div_le_iff₀ (by positivity : 0 < 8 * H)).mpr
    linarith
  intro x hx
  have hd (j) := abs_le.mp (calibrationCell_near_witness hH hh hyq hx j)
  have hb (j) := calibrationBase_bounds hH hy j
  constructor <;> intro j
  · change 0 ≤ x j
    linarith [(hd j).1, (hb j).1]
  · change x j ≤ 1 / 2
    linarith [(hd j).2, (hb j).2]

def calibrationLabels (H h : ℝ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc ⌊-H / h⌋ ⌊H / h⌋

theorem cell_mem_calibrationLabels {H h : ℝ} (hh : 0 < h) {y : Fin 3 → ℝ}
    (hy : ∀ j, |y j| ≤ H) : cell h y ∈ calibrationLabels H h := by
  simp only [calibrationLabels, Fintype.mem_piFinset, Finset.mem_Icc, cell]
  intro j
  obtain ⟨hl, hu⟩ := abs_le.mp (hy j)
  exact ⟨Int.floor_mono (div_le_div_of_nonneg_right hl hh.le),
    Int.floor_mono (div_le_div_of_nonneg_right hu hh.le)⟩

/-- Keep precisely positive-mass cells; a null exception is never chosen as
the representative of an occupied cell. -/
def occupiedCalibrationLabels {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) (H h : ℝ) : Finset (Fin 3 → ℤ) := by
  classical
  exact (calibrationLabels H h).filter fun q => μ {p | cell h (Z p) = q} ≠ 0

theorem occupiedCalibration_cover {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) {H h : ℝ} (hh : 0 < h)
    (hbound : ∀ᵐ p ∂μ, ∀ j, |Z p j| ≤ H) :
    ∀ᵐ p ∂μ, cell h (Z p) ∈ occupiedCalibrationLabels μ Z H h := by
  classical
  have hpos : ∀ᵐ p ∂μ, ∀ q : Fin 3 → ℤ,
      cell h (Z p) = q → μ {p | cell h (Z p) = q} ≠ 0 := by
    apply ae_all_iff.mpr
    intro q
    by_cases hq : μ {p | cell h (Z p) = q} = 0
    · have hn : ∀ᵐ p ∂μ, cell h (Z p) ≠ q := by
        simpa only [ae_iff, not_not] using hq
      filter_upwards [hn] with p hp he
      exact (hp he).elim
    · exact ae_of_all _ fun _ _ => hq
  filter_upwards [hbound, hpos] with p hp hpp
  simp only [occupiedCalibrationLabels, Finset.mem_filter]
  exact ⟨cell_mem_calibrationLabels hh hp, hpp _ rfl⟩

theorem occupiedCalibration_witness {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) {H h : ℝ} {G : Ω → Prop}
    (hgood : ∀ᵐ p ∂μ, G p) {q : Fin 3 → ℤ}
    (hq : q ∈ occupiedCalibrationLabels μ Z H h) :
    ∃ p : Ω, cell h (Z p) = q ∧ G p := by
  classical
  have hp := (Finset.mem_filter.mp hq).2
  exact Measure.exists_mem_of_measure_ne_zero_of_ae hp (ae_restrict_of_ae hgood)

/-- Primitive ORIGINAL grid caps suffice for coefficient calibration. Both
the finite spatial cells and actual good representatives are constructed
here. In particular this does not assume domination of the base law on
arbitrary Borel sets. `P` is expressed in the displayed bounded coordinates. -/
theorem exists_coefficient_bound_from_original_grid (D : ℕ) :
    ∃ C L : ℝ, 0 < C ∧ 0 < L ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ)
        (P : MvPolynomial (Fin 3) ℝ), P.totalDegree ≤ D →
      ∀ H h m beta E : ℝ, 0 < H → 0 < h → h ≤ H →
        0 < m → 0 < beta → m ≤ beta * (8 * H) ^ 3 → 0 ≤ E →
        ENNReal.ofReal m ≤ μ univ →
        (∀ q : Fin 3 → ℤ,
          μ {p | cell h (Z p) = q} ≤ ENNReal.ofReal (beta * h ^ 3)) →
        (∀ᵐ p ∂μ, (∀ j, |Z p j| ≤ H) ∧ |eval (calibrationBase H (Z p)) P| ≤ E) →
        2 * L * ((D + 1) ^ 3 : ℕ) * C *
          (32 * ((D : ℝ) + 1) / (m / (beta * (8 * H) ^ 3))) ^ (3 * D) *
            (h / (8 * H)) ≤ 1 / 2 →
        ∀ e, |P.coeff e| ≤ 2 * ((D + 1) ^ 3 : ℕ) * C *
          (32 * ((D : ℝ) + 1) / (m / (beta * (8 * H) ^ 3))) ^ (3 * D) * E := by
  classical
  obtain ⟨C, L, hC, hL, hcal⟩ := exists_coefficient_bound_from_original_cells D
  refine ⟨C, L, hC, hL, ?_⟩
  intro Ω _ μ Z P hP H h m beta E hH hh hhH hm hbeta hmb hE hmass hcap hgood hsmall
  let Q := occupiedCalibrationLabels μ Z H h
  let events : Q → Set Ω := fun q => {p | cell h (Z p) = q.1}
  let cells : Q → Set (Fin 3 → ℝ) := fun q => calibrationCell H h q.1
  have hbound : ∀ᵐ p ∂μ, ∀ j, |Z p j| ≤ H := hgood.mono fun _ hp => hp.1
  have hwitness (q : Q) : ∃ p : Ω, cell h (Z p) = q.1 ∧
      (∀ j, |Z p j| ≤ H) ∧ |eval (calibrationBase H (Z p)) P| ≤ E :=
    occupiedCalibration_witness μ Z hgood q.2
  apply hcal Ω Q μ events cells ?_ (fun q => measurableSet_calibrationCell H h q.1)
    P hP m (beta * (8 * H) ^ 3) E (h / (8 * H)) hm (by positivity) hmb hE
      (by positivity) hmass ?_ ?_ ?_ ?_ ?_ hsmall
  · intro q r hqr
    exact calibrationCell_disjoint hH hh (fun he => hqr (Subtype.ext he))
  · filter_upwards [occupiedCalibration_cover μ Z hh hbound] with p hp
    exact ⟨⟨cell h (Z p), hp⟩, rfl⟩
  · intro q
    change μ {p | cell h (Z p) = q.1} ≤
      ENNReal.ofReal (beta * (8 * H) ^ 3) * volume (calibrationCell H h q.1)
    rw [volume_calibrationCell hH hh.le, ← ENNReal.ofReal_mul (by positivity)]
    have he : beta * (8 * H) ^ 3 * (h / (8 * H)) ^ 3 = beta * h ^ 3 := by
      rw [div_pow]
      field_simp
    rw [he]
    exact hcap q.1
  · intro q x hx
    obtain ⟨p, hpq, hp, _⟩ := hwitness q
    have hb := calibrationCell_half_cube hH hh hhH hp hpq hx
    exact ⟨hb.1, fun j => (hb.2 j).trans (by norm_num)⟩
  · intro q x hx
    obtain ⟨p, hpq, hp, _⟩ := hwitness q
    exact euclidean_norm_le_one_of_half_cube (calibrationCell_half_cube hH hh hhH hp hpq hx)
  · intro q
    obtain ⟨p, hpq, hp, hval⟩ := hwitness q
    exact ⟨calibrationBase H (Z p), calibrationBase_norm hH hp,
      fun x hx j => calibrationCell_near_witness hH hh hpq hx j, hval⟩

end
end Submission.Obl.k4_quadratic_mesh_coefficient_calibration
