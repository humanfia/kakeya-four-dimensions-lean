-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.DensePacketAssembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SparsePackets

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement (Space)

local instance densePacketAssemblyDecidable (p : Prop) : Decidable p := Classical.propDecidable p

lemma sum_uniform_volume_weight {n : ℕ} (I : Finset (Fin n)) {D w : ℝ}
    (hD : 0 ≤ D) (hw : 0 ≤ w) :
    (∑ _i ∈ I, ENNReal.ofReal (D * w)) = ENNReal.ofReal (D * I.card * w) := by
  calc
    _ = (I.card : ℝ≥0∞) * ENNReal.ofReal (D * w) := by simp
    _ = ENNReal.ofReal ((I.card : ℝ) * (D * w)) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ = _ := by congr 1; ring

lemma bodyCount_mono {n : ℕ} {Y Z : Fin n → Set Space} (h : ∀ i, Y i ⊆ Z i) (p : Space) :
    bodyCount Y p ≤ bodyCount Z p := by
  apply Nat.cast_le.mpr
  exact Set.ncard_le_ncard (fun i hi => h i hi) (Set.toFinite _)

/-- Local refinements on packets above a density threshold combine into a
global quarter-mass refinement. Sparse packets cost only their thresholds. -/
theorem refine_dense_packets {n N : ℕ} (f : Fin n → Fin N) (Y : Fin n → Set Space)
    (hYm : ∀ i, MeasurableSet (Y i)) (hfin : (∑ i, volume (Y i)) ≠ ⊤)
    (cost : Fin n → ℝ≥0∞) (hcost : (∑ i, cost i) ≤ (1 / 2 : ℝ≥0∞) * ∑ i, volume (Y i))
    {B M : ℝ} (hB : 0 ≤ B) (hactive : ∀ p, bodyCount (assignedFiber f Y) p ≤ M)
    (hrefine : ∀ (k : Fin N) (V : Fin n → Set Space),
      (∀ i, MeasurableSet (V i) ∧ V i ⊆ Y i) →
      (∑ i ∈ Finset.univ.filter (fun i => f i = k), cost i) ≤
        ∑ i ∈ Finset.univ.filter (fun i => f i = k), volume (V i) →
      ∃ W : Fin n → Set Space,
        (∀ i, MeasurableSet (W i) ∧ W i ⊆ V i ∧ (f i ≠ k → W i = ∅)) ∧
        (1 / 2 : ℝ≥0∞) * (∑ i ∈ Finset.univ.filter (fun i => f i = k), volume (V i)) ≤
          ∑ i, volume (W i) ∧
        ∀ p, bodyCount W p ≤ B) :
    ∃ Z : Fin n → Set Space, (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      (1 / 4 : ℝ≥0∞) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i) ∧
      ∀ p, bodyCount Z p ≤ M * B := by
  obtain ⟨good, V, hV, hdense, hloss⟩ := select_dense_packets f Y hYm cost
  have hhalf := half_mass_after_loss hfin hloss hcost
  have hactiveV (p : Space) : bodyCount (assignedFiber f V) p ≤ M :=
    (bodyCount_mono (assignedFiber_mono f (fun i => (hV i).2.1)) p).trans (hactive p)
  have hlocal (k : Fin N) : ∃ W : Fin n → Set Space,
      (∀ i, MeasurableSet (W i) ∧ W i ⊆ V i ∧ (f i ≠ k → W i = ∅)) ∧
      (1 / 2 : ℝ≥0∞) * (∑ i ∈ Finset.univ.filter (fun i => f i = k), volume (V i)) ≤
        ∑ i, volume (W i) ∧
      ∀ p, bodyCount W p ≤ B := by
    by_cases hk : k ∈ good
    · exact hrefine k V (fun i => ⟨(hV i).1, (hV i).2.1⟩) (hdense k hk)
    · refine ⟨fun _ => ∅, fun i => ⟨MeasurableSet.empty, empty_subset _, fun _ => rfl⟩, ?_, ?_⟩
      · have he : (∑ i ∈ Finset.univ.filter (fun i => f i = k), volume (V i)) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have hfi := (Finset.mem_filter.mp hi).2
          rw [(hV i).2.2 (by simpa only [hfi] using hk), measure_empty]
        simp [he]
      · intro p
        simpa only [bodyCount, Set.mem_empty_iff_false, Set.setOf_false, Set.ncard_empty,
          Nat.cast_zero] using hB
  obtain ⟨Z, hZ, hmass, hcount⟩ := combine_packet_refinements f V hB hactiveV hlocal
  refine ⟨Z, fun i => ⟨(hZ i).1, (hZ i).2.trans (hV i).2.1⟩, ?_, hcount⟩
  calc
    (1 / 4 : ℝ≥0∞) * (∑ i, volume (Y i)) =
        (1 / 2 : ℝ≥0∞) * ((1 / 2 : ℝ≥0∞) * ∑ i, volume (Y i)) := by
      rw [← mul_assoc]
      congr 1
      rw [one_div, one_div, ← ENNReal.mul_inv] <;> norm_num
    _ ≤ (1 / 2 : ℝ≥0∞) * (∑ i, volume (V i)) := mul_le_mul' le_rfl hhalf
    _ ≤ _ := hmass

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
