-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.RootPacket.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.PacketData
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.UniformMass

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open Module MeasureTheory Set Metric
open scoped ENNReal

lemma initial_physical_packet {n : ℕ} {δ ρ τ : ℝ} {x v : Fin n → E} {Y : Fin n → Set E}
    (hA : Admissible ρ δ n x v Y) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hτ : 0 < τ) (hρ : 768 * τ ≤ ρ) :
    ∃ C : PhysicalPacket n, C.Valid δ τ x v Y ∧ C.region = closedBall (0 : E) 1 ∧
      τ * (n : ℝ) ≤ C.indices.card := by
  classical
  obtain ⟨hn, hv, hbound, hsep, hYm, hYU, hmass⟩ := hA
  let I := Finset.univ.filter fun i : Fin n =>
    ENNReal.ofReal τ * volume (closedTube δ (x i) (v i)) ≤ volume (Y i)
  have hIuniv : I ⊆ Finset.univ := Finset.subset_univ I
  have hV : ∀ i, volume (closedTube δ (x i) (v i)) ≤ ENNReal.ofReal (384 * δ ^ 2) :=
    fun i => (closedTube_volume_bounds hδ hδ1 (x i) (v i) (hv i)).2
  have hYV : ∀ i, volume (Y i) ≤ ENNReal.ofReal (384 * δ ^ 2) := fun i =>
    (measure_mono ((hYU i).trans (tube_subset_closedTube _ _ _))).trans (hV i)
  have hhigh : ∀ i ∈ I, ENNReal.ofReal τ * volume (closedTube δ (x i) (v i)) ≤ volume (Y i) :=
    fun i hi => (Finset.mem_filter.mp hi).2
  have hlow : ∀ i ∈ Finset.univ \ I, volume (Y i) ≤ ENNReal.ofReal (τ * (384 * δ ^ 2)) := by
    intro i hi
    have hnI := (Finset.mem_sdiff.mp hi).2
    have hsmall : volume (Y i) ≤ ENNReal.ofReal τ * volume (closedTube δ (x i) (v i)) := by
      apply le_of_not_ge
      intro h
      exact hnI (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    rw [ENNReal.ofReal_mul hτ.le]
    exact hsmall.trans (mul_le_mul_right (hV i) _)
  have hupper : (∑ i, volume (Y i)) ≤
      ENNReal.ofReal (384 * δ ^ 2 * (I.card : ℝ) + τ * (384 * δ ^ 2) * (n : ℝ)) := by
    have hpart := Finset.sum_sdiff (f := fun i => volume (Y i)) hIuniv
    rw [← hpart]
    have hlo := sum_le_uniform_mass (Finset.univ \ I) (fun i => volume (Y i)) (by positivity) hlow
    have hhi := sum_le_uniform_mass I (fun i => volume (Y i)) (by positivity) (fun i _ => hYV i)
    apply (add_le_add hlo hhi).trans
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hc : ((Finset.univ \ I).card : ℝ) ≤ n := by
      exact_mod_cast (show (Finset.univ \ I).card ≤ n by simpa using Finset.card_le_univ (Finset.univ \ I))
    nlinarith [mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ τ * (384 * δ ^ 2))]
  have hcount : τ * (n : ℝ) ≤ I.card := by
    have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hmass.trans hupper)
    have hscaled : ρ * (n : ℝ) ≤ 384 * (I.card : ℝ) + 384 * τ * (n : ℝ) := by
      apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hδ)).mp
      nlinarith [hreal]
    nlinarith [mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg n)]
  have hI : I.Nonempty := by
    apply Finset.card_pos.mp
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h := lt_of_lt_of_le (mul_pos hτ hn') hcount
    exact_mod_cast h
  let C : PhysicalPacket n := ⟨I, closedBall 0 1, Y⟩
  refine ⟨C, ?_, rfl, hcount⟩
  exact ⟨hI, isCompact_closedBall _ _, convex_closedBall _ _, Subset.rfl,
    fun i _ => closedTube_subset_closedBall (hbound i), fun i _ => hYm i,
    fun _ _ => Subset.rfl, fun i _ => (hYU i).trans (tube_subset_closedTube _ _ _), hhigh⟩

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
