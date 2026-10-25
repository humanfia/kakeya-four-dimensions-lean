import Submission.Obl.k4_scalar_conditional_crop_worlds.Partition
import Submission.Obl.k4_scalar_coefficient_clustering.Evaluation
import Submission.Obl.k4_discrete_of_terminal_charts.Horizon

open MeasureTheory Filter Set

namespace Submission.Obl.k4_scalar_conditional_crop_worlds

noncomputable section

/-- Positive prior-mass cells have centers within one cell width of the prior support. -/
lemma cell_center_coordinate_bound {N u R : ℝ} (hN : 0 < N) (ν : Measure Line)
    (hν : ∀ᵐ l ∂ν, ∀ e, |l.2 e| ≤ R) (q : Label)
    (hq : ν (scalarCell N u q) ≠ 0) :
    |N ^ (-u) * (q 0 : ℝ)| ≤ R + N ^ (-u) ∧
      |N ^ (-u) * (q 1 : ℝ)| ≤ R + N ^ (-u) := by
  obtain ⟨l, hl, hb⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hq (ae_restrict_of_ae hν)
  have ha : 0 < N ^ (-u) := Real.rpow_pos_of_pos hN _
  have h0 := k4_scalar_coefficient_clustering.floor_scaled_error ha (l.2 0)
  have h1 := k4_scalar_coefficient_clustering.floor_scaled_error ha (l.2 1)
  rw [hl.1] at h0
  rw [hl.2] at h1
  have key (x c : ℝ) (hx : |x| ≤ R) (hc : |x - c| ≤ N ^ (-u)) :
      |c| ≤ R + N ^ (-u) := by
    calc |c| = |x - (x - c)| := by congr 1; ring
      _ ≤ |x| + |x - c| := abs_sub _ _
      _ ≤ R + N ^ (-u) := add_le_add hx hc
  exact ⟨key _ _ (hb 0) h0, key _ _ (hb 1) h1⟩

lemma cell_center_bound {N u R : ℝ} (hN : 0 < N) (ν : Measure Line)
    (hν : ∀ᵐ l ∂ν, ∀ e, |l.2 e| ≤ R) (q : Label)
    (hq : ν (scalarCell N u q) ≠ 0) :
    |N ^ (-u) * (q 0 : ℝ)| + |N ^ (-u) * (q 1 : ℝ)| ≤ 2 * (R + N ^ (-u)) := by
  obtain ⟨h0, h1⟩ := cell_center_coordinate_bound hN ν hν q hq
  linarith

/-- A product of two positive subpower bounds, with a fixed constant, remains subpower. -/
lemma subpower_eight_mul {N X Y : ℕ → ℝ} (hNt : Tendsto N atTop atTop)
    (hN : ∀ k, 0 < N k) (hX : Subpower N X) (hY : Subpower N Y) :
    Subpower N (fun k => 8 * X k * Y k) := by
  constructor
  · intro k
    have := hX.1 k
    have := hY.1 k
    nlinarith
  · have hprod := k4_discrete_of_terminal_charts.subpower_mul hN
      (fun k => by linarith [hX.1 k]) (fun k => by linarith [hY.1 k]) hX.2 hY.2
    have hconst := k4_discrete_of_terminal_charts.subpower_const hNt (8 : ℝ)
    simpa only [k4_discrete_of_terminal_charts.SubpowerBound, mul_assoc] using
      k4_discrete_of_terminal_charts.subpower_mul hN (fun _ => by norm_num)
        (fun k => mul_nonneg (by linarith [hX.1 k]) (by linarith [hY.1 k])) hconst hprod

end

end Submission.Obl.k4_scalar_conditional_crop_worlds
