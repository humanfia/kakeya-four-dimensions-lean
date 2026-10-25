import Submission.Obl.k4_matching_gap_regularization.Regularize

set_option autoImplicit false

namespace Submission.Obl.k4_matching_gap_regularization

open Filter
open scoped Topology

/-- Every fixed precision can use an arbitrarily late member of the input
sequence, so its finite conditioning loss is absorbed by a power of N. -/
lemma regularizations_sequence {D J : ℕ} (hDJ : D ≤ J) {d : ℝ}
    (hseq : ∃ N : ℕ → ℝ, ∀ k : ℕ, (k : ℝ) + 2 ≤ N k ∧ Bad D J d (1 / ((k : ℝ) + 1)) (N k)) :
    ∃ (β : ℕ → ℕ → ℝ) (N : ℕ → ℝ), ∀ m,
      Admissible D J (β m) ∧ (m : ℝ) + 2 ≤ N m ∧ Gap J d (β m) (2 / ((m : ℝ) + 1)) (N m) := by
  classical
  obtain ⟨N, hN⟩ := hseq
  have hNt : Tendsto N atTop atTop :=
    tendsto_atTop_mono (fun k => (hN k).1)
      (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  have havail : ∀ m : ℕ, ∃ (β : ℕ → ℝ) (M : ℝ),
      Admissible D J β ∧ (m : ℝ) + 2 ≤ M ∧ Gap J d β (2 / ((m : ℝ) + 1)) M := by
    intro m
    let n := m + 1
    have hn : 0 < n := by omega
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    let δ : ℝ := 1 / (n : ℝ)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hhalf : 0 < δ / 2 := by positivity
    have hηevent : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) ≤ δ / 2 :=
      (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hhalf)).mono fun _ hk => hk.le
    have h2event : ∀ᶠ k : ℕ in atTop, 2 ≤ N k ^ (δ / 2) :=
      ((tendsto_rpow_atTop hhalf).comp hNt).eventually_ge_atTop 2
    have hCevent : ∀ᶠ k : ℕ in atTop,
        ((2 * n + 1 : ℕ) : ℝ) ^ (J + 1) ≤ N k ^ δ :=
      ((tendsto_rpow_atTop hδ).comp hNt).eventually_ge_atTop _
    have hMevent : ∀ᶠ k : ℕ in atTop, (m : ℝ) + 2 ≤ N k :=
      hNt.eventually_ge_atTop _
    obtain ⟨k, hη, h2, hC, hM⟩ := (hηevent.and (h2event.and (hCevent.and hMevent))).exists
    have hNk : 1 ≤ N k := by
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      linarith [(hN k).1]
    have hNkpos : 0 < N k := lt_of_lt_of_le zero_lt_one hNk
    have hηδ : 1 / ((k : ℝ) + 1) ≤ δ := hη.trans (by linarith)
    have hsize : 2 * N k ^ (1 / ((k : ℝ) + 1)) ≤ N k ^ δ := by
      calc
        2 * N k ^ (1 / ((k : ℝ) + 1)) ≤ N k ^ (δ / 2) * N k ^ (δ / 2) :=
          mul_le_mul h2 (Real.rpow_le_rpow_of_exponent_le hNk hη)
            (Real.rpow_nonneg hNkpos.le _) (Real.rpow_nonneg hNkpos.le _)
        _ = N k ^ δ := by rw [← Real.rpow_add hNkpos, add_halves]
    obtain ⟨β, hβ, hgap⟩ := regularize_bad hDJ hn hNk hηδ hsize hC (hN k).2
    refine ⟨β, N k, hβ, hM, ?_⟩
    simpa only [n, Nat.cast_add, Nat.cast_one] using hgap
  choose β M hβ hM hgap using havail
  exact ⟨β, M, fun m => ⟨hβ m, hM m, hgap m⟩⟩

end Submission.Obl.k4_matching_gap_regularization
