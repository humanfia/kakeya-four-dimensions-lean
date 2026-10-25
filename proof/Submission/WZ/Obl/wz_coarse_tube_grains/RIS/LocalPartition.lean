-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.LocalPartition.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.LocalCells
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.CellDensity

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_extremal_lipschitz_grains
open scoped ENNReal Classical

/-- Exact accounting of shading mass over a finite disjoint spatial partition. -/
theorem shading_mass_partition {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {n N : ℕ} (Y : Fin n → Set X) (D : Fin N → Set X)
    (hY : ∀ i, MeasurableSet (Y i)) (hD : ∀ j, MeasurableSet (D j))
    (hdisj : Pairwise fun j k => Disjoint (D j) (D k))
    (hcover : (⋃ i, Y i) ⊆ ⋃ j, D j) :
    (∑ j, ∑ i, μ (Y i ∩ D j)) = ∑ i, μ (Y i) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hsplit : (⋃ j, Y i ∩ D j) = Y i := by
    rw [← inter_iUnion]
    exact inter_eq_left.mpr ((subset_iUnion Y i).trans hcover)
  have hh := measure_iUnion
    (fun j k h => (hdisj h).mono inter_subset_right inter_subset_right)
    (fun j => (hY i).inter (hD j)) (μ := μ)
  rw [hsplit, tsum_fintype] at hh
  exact hh.symm

/-- Real-valued mass accounting for a finite disjoint spatial partition. -/
theorem shading_mass_partition_real {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {n N : ℕ} (Y : Fin n → Set X) (D : Fin N → Set X)
    (hY : ∀ i, MeasurableSet (Y i)) (hfin : ∀ i, μ (Y i) ≠ ⊤)
    (hD : ∀ j, MeasurableSet (D j))
    (hdisj : Pairwise fun j k => Disjoint (D j) (D k))
    (hcover : (⋃ i, Y i) ⊆ ⋃ j, D j) :
    (∑ j, ∑ i, (μ (Y i ∩ D j)).toReal) = ∑ i, (μ (Y i)).toReal := by
  have hf (j : Fin N) (i : Fin n) : μ (Y i ∩ D j) ≠ ⊤ :=
    ne_top_of_le_ne_top (hfin i) (measure_mono inter_subset_left)
  have hs (j : Fin N) : (∑ i, μ (Y i ∩ D j)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun i _ => hf j i)
  have hh := congrArg ENNReal.toReal (shading_mass_partition μ Y D hY hD hdisj hcover)
  simpa only [ENNReal.toReal_sum (fun j _ => hs j),
    ENNReal.toReal_sum (fun i _ => hf _ i), ENNReal.toReal_sum (fun i _ => hfin i)] using hh

/-- Convert a bounded spatial partition with a crossing bound into local-ball
pieces of average shading density. The common cut preserves pointwise
incidence and broadness, and all retained shading mass is exactly accounted. -/
theorem local_dense_refinement_of_partition {R r τ L : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hτ : 0 ≤ τ) {n G : ℕ}
    (Y : Fin n → Set Space) (E : Fin G → Set Space) (c : Fin G → Space)
    (hY : ∀ i, MeasurableSet (Y i)) (hfin : ∀ i, volume (Y i) ≠ ⊤)
    (hE : ∀ j, MeasurableSet (E j)) (hbound : ∀ j, E j ⊆ closedBall (c j) R)
    (hdisj : Pairwise fun j k => Disjoint (E j) (E k))
    (hcover : (⋃ i, Y i) ⊆ ⋃ j, E j)
    (hcross : ∀ i, ({j | (Y i ∩ E j).Nonempty}.ncard : ℝ) ≤ L)
    (hbudget : ENNReal.ofReal (τ * (n : ℝ) * ((12 * R / r) ^ 3 * L)) ≤
      (1 / 2 : ENNReal) * ∑ i, volume (Y i)) :
    ∃ (N : ℕ) (D : Fin N → Set Space) (q : Fin N → Space)
      (parent : Fin N → Fin G) (A : Set Space),
      MeasurableSet A ∧
      (∀ j, MeasurableSet (D j) ∧ D j ⊆ E (parent j) ∧ D j ⊆ ball (q j) r) ∧
      (Pairwise fun j k => Disjoint (D j) (D k)) ∧
      (⋃ j, D j) = ⋃ j, E j ∧
      (N : ℝ) ≤ G * (12 * R / r) ^ 3 ∧
      (∀ i, ({j | (Y i ∩ D j).Nonempty}.ncard : ℝ) ≤ (12 * R / r) ^ 3 * L) ∧
      (∑ j, ∑ i, volume ((Y i ∩ A) ∩ D j)) = ∑ i, volume (Y i ∩ A) ∧
      (1 / 2 : ENNReal) * (∑ i, volume (Y i)) ≤
        ∑ j, ∑ i, volume ((Y i ∩ A) ∩ D j) ∧
      ∀ j, ((⋃ i, Y i ∩ A) ∩ D j).Nonempty →
        ENNReal.ofReal (τ * ({i | (Y i ∩ D j).Nonempty}.ncard : ℝ)) ≤
          ∑ i, volume ((Y i ∩ A) ∩ D j) := by
  obtain ⟨N, D, q, parent, hD, hDdisj, hunion, hN, hcount⟩ :=
    bounded_partition_localization hr hrR E c hE hbound hdisj
  have hR : 0 < R := hr.trans_le hrR
  have hnewcross (i : Fin n) :
      ({j | (Y i ∩ D j).Nonempty}.ncard : ℝ) ≤ (12 * R / r) ^ 3 * L :=
    (hcount (Y i)).trans (mul_le_mul_of_nonneg_left (hcross i) (by positivity))
  obtain ⟨A, hA, hkeep, hdense⟩ := common_cell_density_refinement volume Y D
    hY (fun j => (hD j).1) hfin hτ hnewcross hbudget
  have htotal : (∑ j, ∑ i, volume ((Y i ∩ A) ∩ D j)) = ∑ i, volume (Y i ∩ A) := by
    apply shading_mass_partition volume (fun i => Y i ∩ A) D
      (fun i => (hY i).inter hA) (fun j => (hD j).1) hDdisj
    rw [hunion]
    exact (iUnion_mono fun _ => inter_subset_left).trans hcover
  exact ⟨N, D, q, parent, A, hA, hD, hDdisj, hunion, hN, hnewcross,
    htotal, htotal.symm ▸ hkeep, hdense⟩

/-- The volume bound inherited from a grain's local tubular-volume estimate. -/
theorem localized_piece_volume {G N : ℕ} (E : Fin G → Set Space)
    (D : Fin N → Set Space) (q : Fin N → Space) (parent : Fin N → Fin G)
    {r V : ℝ} (hD : ∀ j, D j ⊆ E (parent j) ∧ D j ⊆ ball (q j) r)
    (hvol : ∀ j p, volume (E j ∩ ball p r) ≤ ENNReal.ofReal V) :
    ∀ j, volume (D j) ≤ ENNReal.ofReal V := by
  intro j
  exact (measure_mono (subset_inter (hD j).1 (hD j).2)).trans (hvol (parent j) (q j))

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
