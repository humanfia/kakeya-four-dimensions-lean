import Submission.Obl.k4_directional_jet_path_transfer.Powers

namespace Submission.Obl.k4_stable_native_signal_oscillation

lemma exists_nat_power_bound (B p : ℝ) : ∃ C : ℕ, 1 ≤ C ∧
    ∀ K : ℝ, 2 ≤ K → B * K ^ p ≤ K ^ C := by
  obtain ⟨L, hL, hbound⟩ :=
    Submission.Obl.k4_directional_jet_path_transfer.exists_power_bound B p
  refine ⟨⌈L⌉₊ + 1, by omega, ?_⟩
  intro K hK
  have hle : L ≤ ((⌈L⌉₊ + 1 : ℕ) : ℝ) := by
    exact (Nat.le_ceil L).trans (by push_cast; linarith)
  apply (hbound K hK).trans
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) hle

end Submission.Obl.k4_stable_native_signal_oscillation
