-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.GridTransfer.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Basic
import Submission.WZ.Obl.wz_flat_factored_improvement.GridHull
import Submission.WZ.Obl.wz_flat_factored_improvement.FlatRegularization
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.Basic

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_nonflat_factored_improvement
  (gridCell gridUnion gridCell_dist_lt gridCell_volume gridUnion_volume
    gridCell_volume_ne_top gridUnion_product tube_gridUnion_volumeReal)
open WangZahlLot.Obl.wz_flat_factored_improvement
  (gridHull gridHull_measurable gridHull_volume_ne_top subset_gridHull gridHull_subset)

/-- The coarse shadow of an averaged dense fibre is dense, even when its individual
shadings do not have uniform mass. -/
theorem fibre_gridHull_density {a d lam : ℝ} (ha : 0 < a) (hd : 0 < d)
    {n : ℕ} (hn : 0 < n) (x v : Fin n → Space) (Y : Fin n → Set Space)
    (hv : ∀ i, ‖v i‖ = 1) (hYT : ∀ i, Y i ⊆ Tube d (x i) (v i))
    (s : Finset (Fin 3 → ℤ)) (hgrid : ∀ i, Y i ⊆ gridUnion a s)
    (hmass : ENNReal.ofReal (lam * n * d ^ 2) ≤ ∑ i, volume (Y i)) :
    ENNReal.ofReal (lam * a ^ 2 / 16) ≤ volume (gridHull a s (⋃ i, Y i)) := by
  let Z := gridHull a s (⋃ i, Y i)
  have hZfin : volume Z ≠ ⊤ := gridHull_volume_ne_top ha s _
  have hYZ : ∀ i, Y i ⊆ Z := fun i =>
    (subset_iUnion Y i).trans (subset_gridHull (iUnion_subset hgrid))
  have hYfin : ∀ i, volume (Y i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top hZfin (measure_mono (hYZ i))
  have hupper (i : Fin n) : volume.real (Y i) ≤
      16 * d ^ 2 / a ^ 2 * volume.real Z := by
    exact (measureReal_mono (subset_inter (hYT i) (hYZ i))
      (ne_top_of_le_ne_top hZfin (measure_mono inter_subset_right))).trans
        (tube_gridUnion_volumeReal ha d (x i) (v i) (hv i) _)
  have hsumfin : (∑ i, volume (Y i)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun i _ => hYfin i)
  have hlower : lam * n * d ^ 2 ≤ ∑ i, volume.real (Y i) := by
    have hh := (ENNReal.ofReal_le_iff_le_toReal hsumfin).mp hmass
    simpa only [ENNReal.toReal_sum (fun i _ => hYfin i), measureReal_def] using hh
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hupper i)
  have hbound : lam * n * d ^ 2 ≤ (n : ℝ) * (16 * d ^ 2 / a ^ 2 * volume.real Z) :=
    hlower.trans (by simpa using hsum)
  apply (ENNReal.ofReal_le_iff_le_toReal hZfin).mpr
  have hp : 0 < (n : ℝ) * (16 * d ^ 2 / a ^ 2) := by
    have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    positivity
  apply (mul_le_mul_iff_right₀ hp).mp
  have he : ((n : ℝ) * (16 * d ^ 2 / a ^ 2)) * (lam * a ^ 2 / 16) =
      lam * n * d ^ 2 := by field_simp
  rw [he]
  simpa only [mul_assoc, measureReal_def] using hbound

/-- A parent-scale grid shadow stays inside the doubled parent when the cell width
is at most half the parent radius. -/
theorem gridHull_subset_doubled_parent {a r : ℝ} (ha : 0 < a) (har : 2 * a ≤ r)
    (s : Finset (Fin 3 → ℤ)) {y w : Space} {Y : Set Space}
    (hY : Y ⊆ Tube r y w) :
    gridHull a s Y ⊆ Tube (2 * r) (y - (1 / 2 : ℝ) • w) (2 • w) := by
  classical
  intro p hp
  obtain ⟨z, hz, hpz⟩ := mem_iUnion₂.mp hp
  obtain ⟨q, hq, hqz⟩ := (Finset.mem_filter.mp hz).2
  obtain ⟨u, hu, hqu⟩ := mem_thickening_iff.mp (hY hq)
  refine mem_thickening_iff.mpr ⟨u,
    WangZahlLot.Obl.wz_rescaled_fibre_alternatives.segment_subset_doubled y w hu, ?_⟩
  have hpq := gridCell_dist_lt ha hpz hqz
  have hpu := dist_triangle p q u
  linarith

/-- A common density class on one global grid controls the union of all fibre shadows.
The fibres may overlap, and the shadings used for the shadows may be further restricted. -/
theorem fibre_gridHull_union_transfer {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t)
    (s : Finset (Fin 3 → ℤ)) {E : Set Space} (hE : MeasurableSet E)
    (hclass : ∀ z ∈ s, t * a ^ 3 ≤ volume.real (E ∩ gridCell a z))
    {N : ℕ} (U : Fin N → Set Space) :
    ENNReal.ofReal t * volume (⋃ k, gridHull a s (U k)) ≤ volume E := by
  have hloc : ∀ z ∈ s,
      ENNReal.ofReal t * volume (gridCell a z) ≤ volume (E ∩ gridCell a z) := by
    intro z hz
    rw [gridCell_volume ha.le, ← ENNReal.ofReal_mul ht]
    exact (ENNReal.ofReal_le_iff_le_toReal
      (ne_top_of_le_ne_top (gridCell_volume_ne_top ha z) (measure_mono inter_subset_right))).mpr
        (hclass z hz)
  exact (mul_le_mul' le_rfl (measure_mono
    (iUnion_subset fun k => gridHull_subset a s (U k)))).trans
      (gridUnion_product ha s E hE (ENNReal.ofReal t) hloc)

/-- The accepted grid selection also supplies the volume transfer needed by a tower
edge, for every later choice of fibre shadows inside the selected class. -/
theorem grid_selection_with_transfer {a ρ H V : ℝ} (ha : 0 < a) (hρ : 0 < ρ)
    {K : ℕ} (hK : 0 < K) (s₀ : Finset (Fin 3 → ℤ))
    {n : ℕ} (Y : Fin n → Set Space) (hYm : ∀ i, MeasurableSet (Y i))
    (hcover : ∀ i, Y i ⊆ gridUnion a s₀)
    (hcap : (s₀.card : ℝ) * a ^ 3 ≤ V)
    (hH : H ≤ ∑ i, volume.real (Y i))
    (hlow : (n : ℝ) * ρ ^ K * V ≤ H / 2) :
    ∃ (s : Finset (Fin 3 → ℤ)) (t : ℝ), s ⊆ s₀ ∧ 0 < t ∧
      H / (2 * K) ≤ ∑ i, volume.real (Y i ∩ gridUnion a s) ∧
      (∀ z ∈ s, t * a ^ 3 ≤ volume.real ((⋃ i, Y i) ∩ gridCell a z)) ∧
      ρ * volume.real ((⋃ i, Y i) ∩ gridUnion a s) ≤ t * V ∧
      ∀ (N : ℕ) (U : Fin N → Set Space),
        ENNReal.ofReal t * volume (⋃ k, gridHull a s (U k)) ≤ volume (⋃ i, Y i) := by
  obtain ⟨s, t, hs, ht, hmass, hclass, hupper⟩ :=
    WangZahlLot.Obl.wz_flat_factored_improvement.grid_density_selection
      ha hρ hK s₀ Y hYm hcover hcap hH hlow
  exact ⟨s, t, hs, ht, hmass, hclass, hupper, fun N U =>
    fibre_gridHull_union_transfer ha ht.le s (MeasurableSet.iUnion hYm) hclass U⟩

end WangZahlLot.Obl.wz_multiscale_finite_tower
