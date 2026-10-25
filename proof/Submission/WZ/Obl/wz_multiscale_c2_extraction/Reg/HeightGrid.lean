-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.HeightGrid.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.HeightPruning

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set MeasureTheory
open scoped ENNReal

noncomputable def heightGrid (h : ℝ) : Finset ℤ :=
  Finset.Icc (-⌈4 / h⌉) ⌈4 / h⌉

theorem heightGrid_card_bound {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    ((heightGrid h).card : ℝ) ≤ 11 / h := by
  have hc : (0 : ℤ) ≤ ⌈4 / h⌉ := by
    exact_mod_cast (show (0 : ℝ) ≤ (⌈4 / h⌉ : ℝ) from
      (by positivity : (0 : ℝ) ≤ 4 / h).trans (Int.le_ceil _))
  have hcard : ((heightGrid h).card : ℤ) = 2 * ⌈4 / h⌉ + 1 := by
    rw [heightGrid, Int.card_Icc, Int.toNat_of_nonneg (by omega)]
    ring
  have hcardR : ((heightGrid h).card : ℝ) = 2 * (⌈4 / h⌉ : ℝ) + 1 := by
    exact_mod_cast hcard
  have hceil : (⌈4 / h⌉ : ℝ) * h ≤ 4 + h := by
    have hh' := (mul_lt_mul_of_pos_right (Int.ceil_lt_add_one (4 / h)) hh).le
    simpa only [add_mul, div_mul_cancel₀ _ hh.ne', one_mul] using hh'
  apply (le_div_iff₀ hh).mpr
  rw [hcardR]
  nlinarith

theorem mem_heightGrid {h : ℝ} (hh : 0 < h) {j : ℤ}
    (hj : |(j : ℝ) * h| ≤ 4) : j ∈ heightGrid h := by
  have hc := Int.le_ceil (4 / h)
  have hch : (4 : ℝ) ≤ (⌈4 / h⌉ : ℝ) * h := (div_le_iff₀ hh).mp hc
  have hj' := abs_le.mp hj
  apply Finset.mem_Icc.mpr
  constructor
  · have hs : -(⌈4 / h⌉ : ℝ) ≤ (j : ℝ) := by nlinarith
    exact_mod_cast hs
  · have hs : (j : ℝ) ≤ (⌈4 / h⌉ : ℝ) := by nlinarith
    exact_mod_cast hs

theorem height_floor_bounds {h z : ℝ} (hh : 0 < h) :
    (⌊z / h⌋ : ℝ) * h ≤ z ∧ z < ((⌊z / h⌋ : ℝ) + 1) * h := by
  exact ⟨(le_div_iff₀ hh).mp (Int.floor_le _),
    (div_lt_iff₀ hh).mp (Int.lt_floor_add_one _)⟩

theorem height_floor_mem {h z : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hz : z ∈ Icc (-1 : ℝ) 1) :
    ⌊z / h⌋ ∈ heightGrid h ∧ ⌊z / h⌋ + 1 ∈ heightGrid h := by
  have hb := height_floor_bounds (z := z) hh
  constructor
  · apply mem_heightGrid hh
    rw [abs_le]
    constructor <;> nlinarith [hz.1, hz.2]
  · apply mem_heightGrid hh
    simp only [Int.cast_add, Int.cast_one]
    rw [abs_le]
    constructor <;> nlinarith [hz.1, hz.2]

noncomputable def heightGridBand (h r : ℝ) : Set ℝ :=
  ⋃ j : ↥(heightGrid h), Icc ((j.1 : ℝ) * h - r) ((j.1 : ℝ) * h + r)

theorem heightGridBand_mass {μ : Measure ℝ} {L : ℝ≥0∞}
    (hμ : ∀ l u : ℝ, μ (Icc l u) ≤ L * ENNReal.ofReal (u - l)) (h r : ℝ) :
    μ (heightGridBand h r) ≤
      ((heightGrid h).card : ℝ≥0∞) * L * ENNReal.ofReal (2 * r) := by
  classical
  calc
    μ (heightGridBand h r) ≤
        ∑ j : ↥(heightGrid h), μ (Icc ((j.1 : ℝ) * h - r) ((j.1 : ℝ) * h + r)) :=
      measure_iUnion_fintype_le μ _
    _ ≤ ∑ _j : ↥(heightGrid h), L * ENNReal.ofReal (2 * r) := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [show (j.1 : ℝ) * h + r - ((j.1 : ℝ) * h - r) = 2 * r by ring]
        using hμ ((j.1 : ℝ) * h - r) ((j.1 : ℝ) * h + r)
    _ = ((heightGrid h).card : ℝ≥0∞) * L * ENNReal.ofReal (2 * r) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      ring

def safeGridHeights (h r : ℝ) : Set ℝ := {z | ∀ j : ℤ, r ≤ |z - (j : ℝ) * h|}

theorem isClosed_safeGridHeights (h r : ℝ) : IsClosed (safeGridHeights h r) := by
  have he : safeGridHeights h r = ⋂ j : ℤ, {z : ℝ | r ≤ |z - (j : ℝ) * h|} := by
    ext z
    simp [safeGridHeights]
  rw [he]
  exact isClosed_iInter (fun j => isClosed_le continuous_const
    ((continuous_id.sub continuous_const).abs))

theorem outside_height_mem_band {h r z : ℝ} (hh : 0 < h) (hr3 : r ≤ 3)
    (hz : z ∈ Icc (-1 : ℝ) 1) (houtside : z ∉ safeGridHeights h r) :
    z ∈ heightGridBand h r := by
  simp only [safeGridHeights, mem_setOf_eq, not_forall, not_le] at houtside
  obtain ⟨j, hj⟩ := houtside
  have hji : j ∈ heightGrid h := by
    apply mem_heightGrid hh
    calc |(j : ℝ) * h| = |z - (z - (j : ℝ) * h)| := by congr 1; ring
      _ ≤ |z| + |z - (j : ℝ) * h| := abs_sub _ _
      _ ≤ 1 + r := add_le_add (abs_le.mpr hz) hj.le
      _ ≤ 4 := by linarith
  apply mem_iUnion.mpr
  refine ⟨⟨j, hji⟩, ?_⟩
  have hj' := abs_le.mp hj.le
  constructor <;> linarith

/-- A grid interval with a sample separated from the coarser grid boundary lies
entirely in a single coarser cell. The two grids need not be nested. -/
theorem grid_cell_contained_of_safe {h H z : ℝ} {j : ℤ}
    (hh : 0 < h) (hH : 0 < H)
    (hz : z ∈ Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h))
    (hsafe : z ∈ safeGridHeights H (2 * h)) :
    ∃ m : ℤ, Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h) ⊆
      Icc ((m : ℝ) * H) (((m : ℝ) + 1) * H) := by
  let m := ⌊z / H⌋
  have hm := height_floor_bounds (z := z) hH
  have hlo := hsafe m
  have hup := hsafe (m + 1)
  have hmlo : 0 ≤ z - (m : ℝ) * H := sub_nonneg.mpr hm.1
  have hmup : z - (((m : ℝ) + 1) * H) ≤ 0 := sub_nonpos.mpr hm.2.le
  rw [abs_of_nonneg hmlo] at hlo
  simp only [Int.cast_add, Int.cast_one] at hup
  rw [abs_of_nonpos hmup] at hup
  refine ⟨m, ?_⟩
  intro t ht
  constructor <;> nlinarith [hz.1, hz.2, ht.1, ht.2]

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
