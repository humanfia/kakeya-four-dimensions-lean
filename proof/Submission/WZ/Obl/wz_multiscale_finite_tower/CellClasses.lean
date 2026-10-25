-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.CellClasses.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.GridTransfer

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal
open WangZahlLot.Obl.wz_nonflat_factored_improvement
  (gridCell gridUnion gridCell_volumeReal gridCell_volume_ne_top
    gridUnion_volumeReal gridUnion_volume_ne_top volumeReal_inter_gridUnion)
open WangZahlLot.Obl.wz_flat_factored_improvement (gridHull subset_gridHull)

/-- Weighted density selection with both bounds in each selected cell. The cells
may have different capacities; the output retains a fixed fraction of total weight. -/
theorem weighted_cell_class {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (u v w : ι → ℝ) {N ρ H V : ℝ} {K : ℕ}
    (hv : ∀ i ∈ S, 0 < v i) (hu : ∀ i ∈ S, u i ≤ v i)
    (hw : ∀ i ∈ S, w i ≤ N * u i) (hN : 0 ≤ N) (hρ : 0 < ρ) (hK : 0 < K)
    (hcap : ∑ i ∈ S, v i ≤ V) (hmass : H ≤ ∑ i ∈ S, w i)
    (hlow : N * ρ ^ K * V ≤ H / 2) :
    ∃ (S' : Finset ι) (t : ℝ), S' ⊆ S ∧ 0 < t ∧
      H / (2 * K) ≤ ∑ i ∈ S', w i ∧
      ∀ i ∈ S', t * v i ≤ u i ∧ ρ * u i ≤ t * v i := by
  classical
  let d : ι → ℝ := fun i => u i / v i
  have hd : ∀ i ∈ S, d i ≤ 1 := fun i hi => (div_le_one (hv i hi)).mpr (hu i hi)
  have hsmall : (∑ i ∈ S.filter (fun i => d i < ρ ^ K), w i) ≤ H / 2 := by
    calc
      _ ≤ ∑ i ∈ S.filter (fun i => d i < ρ ^ K), (N * ρ ^ K) * v i := by
        apply Finset.sum_le_sum
        intro i hi
        have his := (Finset.mem_filter.mp hi).1
        have hui := (div_lt_iff₀ (hv i his)).mp (Finset.mem_filter.mp hi).2
        exact (hw i his).trans (by nlinarith [mul_le_mul_of_nonneg_left hui.le hN])
      _ ≤ ∑ i ∈ S, (N * ρ ^ K) * v i := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun i hi _ => mul_nonneg (mul_nonneg hN (pow_pos hρ K).le)
          (hv i hi).le)
      _ = (N * ρ ^ K) * ∑ i ∈ S, v i := (Finset.mul_sum _ _ _).symm
      _ ≤ (N * ρ ^ K) * V := mul_le_mul_of_nonneg_left hcap
        (mul_nonneg hN (pow_pos hρ K).le)
      _ ≤ _ := hlow
  obtain ⟨S', hsub, hmass', t, ht, hclass⟩ :=
    WangZahlLot.Obl.wz_nonflat_factored_improvement.density_selection
      S d w hρ hK hd hmass hsmall
  refine ⟨S', t, hsub, ht, hmass', ?_⟩
  intro i hi
  have hvi := hv i (hsub hi)
  obtain ⟨hl, hh⟩ := hclass i hi
  refine ⟨(le_div_iff₀ hvi).mp hl, ?_⟩
  apply (div_le_iff₀ hvi).mp
  simpa only [d, mul_div_assoc] using hh

/-- Spatial density regularization retaining both cell bounds, while measuring
the retained mass with multiplicity in the original family of shadings. -/
theorem grid_density_class_relative {a ρ H V : ℝ} (ha : 0 < a) (hρ : 0 < ρ)
    {K : ℕ} (hK : 0 < K) (S₀ : Finset (Fin 3 → ℤ))
    {n : ℕ} (Y : Fin n → Set Space) (hYm : ∀ i, MeasurableSet (Y i))
    {E : Set Space} (hYE : ∀ i, Y i ⊆ E)
    (hcover : ∀ i, Y i ⊆ gridUnion a S₀)
    (hcap : (S₀.card : ℝ) * a ^ 3 ≤ V)
    (hH : H ≤ ∑ i, volume.real (Y i)) (hlow : (n : ℝ) * ρ ^ K * V ≤ H / 2) :
    ∃ (S : Finset (Fin 3 → ℤ)) (t : ℝ), S ⊆ S₀ ∧ 0 < t ∧
      H / (2 * K) ≤ ∑ i, volume.real (Y i ∩ gridUnion a S) ∧
      ∀ z ∈ S, t * a ^ 3 ≤ volume.real (E ∩ gridCell a z) ∧
        ρ * volume.real (E ∩ gridCell a z) ≤ t * a ^ 3 := by
  classical
  let u := fun z => volume.real (E ∩ gridCell a z)
  let w := fun z => ∑ i, volume.real (Y i ∩ gridCell a z)
  have hufin (z : Fin 3 → ℤ) : volume (E ∩ gridCell a z) ≠ ⊤ :=
    ne_top_of_le_ne_top (gridCell_volume_ne_top ha z) (measure_mono inter_subset_right)
  have hu (z : Fin 3 → ℤ) : u z ≤ a ^ 3 := by
    calc
      _ ≤ volume.real (gridCell a z) :=
        measureReal_mono inter_subset_right (gridCell_volume_ne_top ha z)
      _ = _ := gridCell_volumeReal ha z
  have hw (z : Fin 3 → ℤ) : w z ≤ (n : ℝ) * u z := by
    calc
      _ ≤ ∑ _i : Fin n, u z := Finset.sum_le_sum (fun i _ =>
        measureReal_mono (inter_subset_inter_left _ (hYE i)) (hufin z))
      _ = _ := by simp
  have hsum (S : Finset (Fin 3 → ℤ)) :
      (∑ z ∈ S, w z) = ∑ i, volume.real (Y i ∩ gridUnion a S) := by
    dsimp [w]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => (volumeReal_inter_gridUnion ha S (hYm i)).symm)
  have hm : H ≤ ∑ z ∈ S₀, w z := by
    rw [hsum]
    simpa only [inter_eq_left.mpr (hcover _)] using hH
  obtain ⟨S, t, hS, ht, hmass, hclass⟩ := weighted_cell_class S₀ u (fun _ => a ^ 3) w
    (fun _ _ => pow_pos ha _) (fun z _ => hu z) (fun z _ => hw z)
    (Nat.cast_nonneg n) hρ hK (by simpa using hcap) hm hlow
  exact ⟨S, t, hS, ht, by simpa only [hsum] using hmass, hclass⟩

theorem grid_density_class {a ρ H V : ℝ} (ha : 0 < a) (hρ : 0 < ρ)
    {K : ℕ} (hK : 0 < K) (S₀ : Finset (Fin 3 → ℤ))
    {n : ℕ} (Y : Fin n → Set Space) (hYm : ∀ i, MeasurableSet (Y i))
    (hcover : ∀ i, Y i ⊆ gridUnion a S₀)
    (hcap : (S₀.card : ℝ) * a ^ 3 ≤ V)
    (hH : H ≤ ∑ i, volume.real (Y i)) (hlow : (n : ℝ) * ρ ^ K * V ≤ H / 2) :
    ∃ (S : Finset (Fin 3 → ℤ)) (t : ℝ), S ⊆ S₀ ∧ 0 < t ∧
      H / (2 * K) ≤ ∑ i, volume.real (Y i ∩ gridUnion a S) ∧
      ∀ z ∈ S, t * a ^ 3 ≤ volume.real ((⋃ i, Y i) ∩ gridCell a z) ∧
        ρ * volume.real ((⋃ i, Y i) ∩ gridCell a z) ≤ t * a ^ 3 :=
  grid_density_class_relative ha hρ hK S₀ Y hYm (fun i => subset_iUnion Y i)
    hcover hcap hH hlow

/-- A density class gives an upper estimate on any later restricted shading, in
terms of the grid shadow of its containing set. -/
theorem grid_class_upper {a ρ t : ℝ} (ha : 0 < a) (hρ : 0 ≤ ρ)
    (S : Finset (Fin 3 → ℤ)) {E F W : Set Space}
    (hE : MeasurableSet E) (hFE : F ⊆ E) (hFW : F ⊆ W) (hFS : F ⊆ gridUnion a S)
    (hclass : ∀ z ∈ S, ρ * volume.real (E ∩ gridCell a z) ≤ t * a ^ 3) :
    ENNReal.ofReal ρ * volume F ≤ ENNReal.ofReal t * volume (gridHull a S W) := by
  classical
  let S' := S.filter (fun z => (W ∩ gridCell a z).Nonempty)
  have hFS' : F ⊆ gridUnion a S' := by
    intro p hp
    obtain ⟨z, hz, hpz⟩ := mem_iUnion₂.mp (hFS hp)
    exact mem_iUnion₂.mpr ⟨z, Finset.mem_filter.mpr ⟨hz, p, hFW hp, hpz⟩, hpz⟩
  have hbound : ρ * volume.real (E ∩ gridUnion a S') ≤ t * volume.real (gridUnion a S') := by
    rw [volumeReal_inter_gridUnion ha S' hE, gridUnion_volumeReal ha, Finset.mul_sum]
    calc
      _ ≤ ∑ _z ∈ S', t * a ^ 3 :=
        Finset.sum_le_sum (fun z hz => hclass z (Finset.mem_filter.mp hz).1)
      _ = _ := by simp; ring
  have hEF : volume (E ∩ gridUnion a S') ≠ ⊤ :=
    ne_top_of_le_ne_top (gridUnion_volume_ne_top ha S') (measure_mono inter_subset_right)
  calc
    _ ≤ ENNReal.ofReal ρ * volume (E ∩ gridUnion a S') :=
      mul_le_mul' le_rfl (measure_mono (subset_inter hFE hFS'))
    _ = ENNReal.ofReal (ρ * volume.real (E ∩ gridUnion a S')) := by
      rw [ENNReal.ofReal_mul hρ, measureReal_def, ENNReal.ofReal_toReal hEF]
    _ ≤ ENNReal.ofReal (t * volume.real (gridUnion a S')) := ENNReal.ofReal_le_ofReal hbound
    _ = _ := by
      rw [ENNReal.ofReal_mul' (measureReal_nonneg), measureReal_def,
        ENNReal.ofReal_toReal (gridUnion_volume_ne_top ha S')]
      rfl

/-- The two sides of a density class combine an arbitrary local volume lower
bound with a global coarse-shadow transfer. -/
theorem grid_class_local_to_global {a ρ t A V : ℝ}
    (ha : 0 < a) (hρ : 0 ≤ ρ) (ht : 0 ≤ t) (hA : 0 ≤ A) (hV : 0 < V)
    (S : Finset (Fin 3 → ℤ)) {E F W C : Set Space}
    (hE : MeasurableSet E) (hFE : F ⊆ E) (hFW : F ⊆ W) (hFS : F ⊆ gridUnion a S)
    (hclass : ∀ z ∈ S, ρ * volume.real (E ∩ gridCell a z) ≤ t * a ^ 3)
    (hlocal : ENNReal.ofReal (A * V) ≤ volume F)
    (hcap : volume (gridHull a S W) ≤ ENNReal.ofReal V)
    (htransfer : ENNReal.ofReal t * volume C ≤ volume E) :
    ENNReal.ofReal (ρ * A) * volume C ≤ volume E := by
  have hupper := grid_class_upper ha hρ S hE hFE hFW hFS hclass
  have hineq : ENNReal.ofReal (ρ * (A * V)) ≤ ENNReal.ofReal (t * V) := by
    rw [ENNReal.ofReal_mul hρ, ENNReal.ofReal_mul ht]
    exact ((mul_le_mul' le_rfl hlocal).trans hupper).trans (mul_le_mul' le_rfl hcap)
  have hreal := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg ht hV.le)).mp hineq
  have hcoef : ρ * A ≤ t := (mul_le_mul_iff_left₀ hV).mp (by nlinarith)
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) le_rfl).trans htransfer

end WangZahlLot.Obl.wz_multiscale_finite_tower
