import Submission.Obl.k4_scalar_candidate_original_return.DataFacts
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Monotonicity

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open Filter

/-- A finite original-coordinate output before absorption into the guard.
The two powers and their constant depend only on the fixed candidate scenario. -/
noncomputable def RecoveredAt (a : PreparedData) (R δ C : ℝ) (q p : ℕ) (k : ℕ) : Prop :=
  ∃ (r h : ℝ) (B : ℕ) (ε : ℝ),
    R⁻¹ ≤ r ∧ r ≤ R ∧ h ≤ a.κ * r - δ ∧
    (B : ℝ) ≤ C * (1 + (a.rM k : ℝ)) ^ q ∧
    a.original k ^ ε ≤ C * (a.H k * Real.log (a.original k)) ^ p ∧
    Chart (a.p k) B (a.sc k * r) (L (a.p k)) (a.sc k * h) ε false (a.sm k)

/-- A fixed saving beats the vanishing buffer; the actual output slack and
polynomial complexity fit the budgets declared before sampling. -/
theorem not_frequently_recovered (a : PreparedData) (ha : a.Valid)
    (R δ C : ℝ) (q p : ℕ) (hR : 1 < R) (hδ : 0 < δ) :
    ¬∃ᶠ k in atTop, RecoveredAt a R δ C q p k := by
  have hcomplex : ∀ᶠ k : ℕ in atTop,
      C * (1 + (a.rM k : ℝ)) ^ q ≤ (a.guard k : ℝ) := by
    filter_upwards [Submission.Lib.K4MeshListRecovery.eventually_polynomial_le_complexity_guard C q]
      with k hk
    apply (hk (a.rM k)).trans
    dsimp only [PreparedData.guard]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    have : a.rM k + k ≤ a.rM k + k + 1 := by omega
    exact Nat.pow_le_pow_left this 2
  apply not_frequently.mpr
  filter_upwards [ha.excluded R hR,
    ha.buffer_tends.eventually (gt_mem_nhds hδ), hcomplex,
    ha.scales.eventually_fixed_power_le_allowance C p] with k hguard hbuffer hcomplex hslack
  rintro ⟨r, h, B, ε, hr0, hr1, hh, hB, he, hchart⟩
  have hB' : B ≤ a.guard k := by exact_mod_cast hB.trans hcomplex
  have hN0 : 0 < a.original k := ha.scales.original_pos k
  have hlogN0 : 0 < Real.log (a.original k) := ha.scales.log_original_pos k
  have he' : ε ≤ a.loss k := by
    have hpow : a.original k ^ ε ≤ a.original k ^ a.loss k := by
      have hid : a.original k ^ a.loss k = a.allowance k :=
        ha.scales.original_rpow_loss k
      rw [hid]
      exact he.trans hslack
    have hlog := Real.log_le_log (Real.rpow_pos_of_pos hN0 ε) hpow
    rw [Real.log_rpow hN0, Real.log_rpow hN0] at hlog
    exact (mul_le_mul_iff_left₀ hlogN0).mp hlog
  apply hguard r h hr0 hr1 (by linarith)
  exact Submission.Obl.k4_scalar_true_atlas_terminal_lists.Chart.mono
    (show 1 ≤ N (a.p k) (a.sm k) by
      change 1 ≤ a.original k
      exact (by norm_num : (1 : ℝ) ≤ 2).trans
        (show 2 ≤ a.original k from ha.scales.original_ge_two k))
    hB' le_rfl he' hchart

/-- The remaining geometric task: recover a fixed scenario's actual charts. -/
noncomputable def CandidateConversion : Prop :=
  ∀ a : PreparedData, a.Valid → STI →
    ∃ (R δ C : ℝ) (q p : ℕ), 1 < R ∧ 0 < δ ∧
      ∃ᶠ k in atTop, RecoveredAt a R δ C q p k

/-- All original-budget and guard bookkeeping is closed by this reduction. -/
theorem prepared_not_STI_of_conversion (hconvert : CandidateConversion) : Prepared → ¬STI := by
  intro hprepared hSTI
  obtain ⟨a, ha⟩ := prepared_iff_exists_data.mp hprepared
  obtain ⟨R, δ, C, q, p, hR, hδ, hout⟩ := hconvert a ha hSTI
  exact not_frequently_recovered a ha R δ C q p hR hδ hout

end Submission.Obl.k4_scalar_candidate_original_return
