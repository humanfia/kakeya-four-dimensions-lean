-- Adapted from this LOT tree, o117, session x0390, commit 0d48789,
-- Submission/Obl/k4_quadratic_candidate_atlas_conversion/GainMenu.lean.

import Submission.Obl.k4_quadratic_finite_greedy_cover.Interface
import Submission.Obl.k4_finite_row_graph_assembly.Selection

namespace Submission.Obl.k4_quadratic_finite_greedy_cover

/-- Round down an actual gain to a fixed menu with spacing `step`. -/
noncomputable def gainMenuIndex (gain step h : ℝ) : ℕ := ⌊(h - gain) / step⌋₊

noncomputable def menuGain (gain step h : ℝ) : ℝ :=
  gain + (gainMenuIndex gain step h : ℝ) * step

theorem menuGain_bounds (gain step h : ℝ) (hstep : 0 < step) (hgain : gain ≤ h) :
    gain ≤ menuGain gain step h ∧ menuGain gain step h ≤ h ∧ h < menuGain gain step h + step := by
  have hx : 0 ≤ (h - gain) / step := div_nonneg (sub_nonneg.mpr hgain) hstep.le
  have hlo := (le_div_iff₀ hstep).mp (Nat.floor_le hx)
  have hhi := (div_lt_iff₀ hstep).mp (Nat.lt_floor_add_one ((h - gain) / step))
  have hpos : 0 ≤ (gainMenuIndex gain step h : ℝ) * step :=
    mul_nonneg (Nat.cast_nonneg _) hstep.le
  dsimp [menuGain, gainMenuIndex] at *
  constructor
  · linarith
  · constructor <;> nlinarith

theorem gainMenuIndex_bound (gain step h H : ℝ)
    (hstep : 0 < step) (hgain : 0 ≤ gain) (hh : h ≤ H) :
    gainMenuIndex gain step h < ⌈H / step⌉₊ + 1 := by
  have hr : (h - gain) / step ≤ H / step :=
    div_le_div_of_nonneg_right (by linarith) hstep.le
  exact Nat.lt_succ_of_le ((Nat.floor_mono hr).trans (Nat.floor_le_ceil _))

/-- A finite choice of path level and gain bin retains its share of the total
candidate mass. The menu is chosen before any asymptotic slack. -/
theorem finite_menu_mass {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (label : ι → Fin m × Fin n) (mass : ι → ℝ) (c : ℝ)
    (h : c ≤ ∑ a ∈ s, mass a) :
    ∃ i : Fin m, ∃ j : Fin n,
      c / ((m * n : ℕ) : ℝ) ≤ ∑ a ∈ s.filter (fun a => label a = (i, j)), mass a := by
  classical
  let f : Fin m × Fin n → ℝ := fun p => ∑ a ∈ s, if label a = p then mass a else 0
  have hsum : ∑ p, f p = ∑ a ∈ s, mass a := by
    rw [show (∑ p, f p) = ∑ p, ∑ a ∈ s, if label a = p then mass a else 0 from rfl,
      Finset.sum_comm]
    simp
  have hnonempty : (Finset.univ : Finset (Fin m × Fin n)).Nonempty :=
    ⟨(⟨0, hm⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
  obtain ⟨⟨i, j⟩, _, hp⟩ := Submission.Obl.k4_finite_row_graph_assembly.exists_ge_avg
    Finset.univ f c hnonempty (by rw [hsum]; exact h)
  exact ⟨i, j, by simpa [f, Finset.sum_filter] using hp⟩

end Submission.Obl.k4_quadratic_finite_greedy_cover
