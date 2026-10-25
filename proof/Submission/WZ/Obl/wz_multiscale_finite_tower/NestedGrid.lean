-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.NestedGrid.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.GridCapacity

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal
open WangZahlLot.Obl.wz_nonflat_factored_improvement
  (gridCell gridKey gridUnion mem_gridCell_iff gridUnion_product gridUnion_measurable)
open WangZahlLot.Obl.wz_flat_factored_improvement
  (gridHull gridHull_measurable gridHull_volume_ne_top)

lemma gridKey_nat_mul (a : ℝ) (k : ℕ) (p : Space) :
    gridKey ((k : ℝ) * a) p = fun i => gridKey a p i / (k : ℤ) := by
  funext i
  dsimp [gridKey]
  rw [mul_comm (k : ℝ) a, div_mul_eq_div_div, Int.floor_div_natCast]

/-- A fine grid cell lies in one coarse cell whenever the widths have an integer ratio. -/
lemma gridCell_subset_nat_mul {a : ℝ} (ha : 0 < a) {k : ℕ} (hk : 0 < k)
    (z : Fin 3 → ℤ) :
    gridCell a z ⊆ gridCell ((k : ℝ) * a) (fun i => z i / (k : ℤ)) := by
  intro p hp
  apply (mem_gridCell_iff (mul_pos (Nat.cast_pos.mpr hk) ha) _ p).mpr
  rw [gridKey_nat_mul, (mem_gridCell_iff ha z p).mp hp]

/-- Cutting by coarse cells is compatible with taking a fine-grid shadow. -/
lemma gridHull_subset_coarse_grid {a : ℝ} (ha : 0 < a) {k : ℕ} (hk : 0 < k)
    (S T : Finset (Fin 3 → ℤ)) {Y : Set Space}
    (hY : Y ⊆ gridUnion ((k : ℝ) * a) T) :
    gridHull a S Y ⊆ gridUnion ((k : ℝ) * a) T := by
  classical
  have hb := mul_pos (Nat.cast_pos.mpr hk) ha
  intro p hp
  obtain ⟨z, hz, hpz⟩ := mem_iUnion₂.mp hp
  obtain ⟨q, hq, hqz⟩ := (Finset.mem_filter.mp hz).2
  obtain ⟨u, hu, hqu⟩ := mem_iUnion₂.mp (hY hq)
  have hqp := (gridCell_subset_nat_mul ha hk z) hqz
  have hp' := (gridCell_subset_nat_mul ha hk z) hpz
  have he := ((mem_gridCell_iff hb _ q).mp hqp).symm.trans
    ((mem_gridCell_iff hb u q).mp hqu)
  exact mem_iUnion₂.mpr ⟨u, hu, by simpa only [he] using hp'⟩

lemma gridHull_iUnion {ι : Type*} (a : ℝ) (S : Finset (Fin 3 → ℤ))
    (U : ι → Set Space) : gridHull a S (⋃ i, U i) = ⋃ i, gridHull a S (U i) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨z, hz, hpz⟩ := mem_iUnion₂.mp hp
    obtain ⟨q, hq, hqz⟩ := (Finset.mem_filter.mp hz).2
    obtain ⟨i, hqi⟩ := mem_iUnion.mp hq
    exact mem_iUnion.mpr ⟨i, mem_iUnion₂.mpr
      ⟨z, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1, q, hqi, hqz⟩, hpz⟩⟩
  · intro hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    obtain ⟨z, hz, hpz⟩ := mem_iUnion₂.mp hi
    obtain ⟨q, hq, hqz⟩ := (Finset.mem_filter.mp hz).2
    exact mem_iUnion₂.mpr ⟨z, Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hz).1, q, mem_iUnion.mpr ⟨i, hq⟩, hqz⟩, hpz⟩

/-- The lower cell density also holds locally inside every union of whole selected cells. -/
lemma gridHull_local_density {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t)
    (S : Finset (Fin 3 → ℤ)) {E : Set Space} (hE : MeasurableSet E)
    (hclass : ∀ z ∈ S, t * a ^ 3 ≤ volume.real (E ∩ gridCell a z)) (U : Set Space) :
    ENNReal.ofReal t * volume (gridHull a S U) ≤ volume (E ∩ gridHull a S U) := by
  classical
  let S' := S.filter (fun z => (U ∩ gridCell a z).Nonempty)
  apply gridUnion_product ha S' (E ∩ gridHull a S U)
    (hE.inter (gridHull_measurable _ _ _)) (ENNReal.ofReal t)
  intro z hz
  have hcell : gridCell a z ⊆ gridHull a S U := fun p hp => mem_iUnion₂.mpr ⟨z, hz, hp⟩
  have he : (E ∩ gridHull a S U) ∩ gridCell a z = E ∩ gridCell a z := by
    ext p
    constructor
    · exact fun hp => ⟨hp.1.1, hp.2⟩
    · exact fun hp => ⟨⟨hp.1, hcell hp.2⟩, hp.2⟩
  rw [he, WangZahlLot.Obl.wz_nonflat_factored_improvement.gridCell_volume ha.le,
    ← ENNReal.ofReal_mul ht]
  exact (ENNReal.ofReal_le_iff_le_toReal
    (ne_top_of_le_ne_top (WangZahlLot.Obl.wz_nonflat_factored_improvement.gridCell_volume_ne_top ha z)
      (measure_mono inter_subset_right))).mpr (hclass z (Finset.mem_filter.mp hz).1)

/-- Fine and coarse density classes give a ratio estimate. This avoids changing
the reference union while passing through many scales. -/
lemma nested_grid_density_ratio {a ρ t u A V : ℝ}
    (ha : 0 < a) {k : ℕ} (hk : 0 < k)
    (hρ : 0 ≤ ρ) (ht : 0 ≤ t) (hu : 0 ≤ u) (hV : 0 < V)
    (S T : Finset (Fin 3 → ℤ)) {E U W : Set Space} (hE : MeasurableSet E)
    (hU : U ⊆ gridUnion ((k : ℝ) * a) T)
    (hUW : gridHull a S U ⊆ W)
    (hsmall : ∀ z ∈ S, u * a ^ 3 ≤ volume.real (E ∩ gridCell a z))
    (hbig : ∀ z ∈ T, ρ * volume.real (E ∩ gridCell ((k : ℝ) * a) z) ≤
      t * ((k : ℝ) * a) ^ 3)
    (hlower : ENNReal.ofReal (A * V) ≤ volume (gridHull a S U))
    (hcap : volume (gridHull ((k : ℝ) * a) T W) ≤ ENNReal.ofReal V) :
    ρ * u * A ≤ t := by
  have hb := mul_pos (Nat.cast_pos.mpr hk) ha
  have hl := gridHull_local_density ha hu S hE hsmall U
  have hh := grid_class_upper hb hρ T hE inter_subset_left
    (inter_subset_right.trans hUW)
    (inter_subset_right.trans (gridHull_subset_coarse_grid ha hk S T hU)) hbig
  have hineq : ENNReal.ofReal (ρ * (u * (A * V))) ≤ ENNReal.ofReal (t * V) := by
    rw [ENNReal.ofReal_mul hρ, ENNReal.ofReal_mul hu, ENNReal.ofReal_mul ht]
    exact ((mul_le_mul' le_rfl ((mul_le_mul' le_rfl hlower).trans hl)).trans hh).trans
      (mul_le_mul' le_rfl hcap)
  have hreal := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg ht hV.le)).mp hineq
  exact (mul_le_mul_iff_left₀ hV).mp (by nlinarith)

end WangZahlLot.Obl.wz_multiscale_finite_tower
