import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet.Numerics

/-!
# Eventual power inequalities

`ev_rpow`: for `α < β` and any constant `C`, eventually `C N^α ≤ N^β`. The other lemmas are the
monotonicity facts for real powers of `N ≥ 1` used when choosing the constants of the cover,
and `Cover.mono` (the cover is monotone in the loss `ε`).
-/

open MeasureTheory Set Filter

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

theorem ev_rpow (C α β : ℝ) (h : α < β) : ∀ᶠ N : ℝ in atTop, C * N ^ α ≤ N ^ β := by
  have ht : Tendsto (fun N : ℝ => N ^ (β - α)) atTop atTop := tendsto_rpow_atTop (by linarith)
  filter_upwards [ht.eventually_ge_atTop C, eventually_gt_atTop (0 : ℝ)] with N hN hN0
  have e : N ^ β = N ^ (β - α) * N ^ α := by rw [← Real.rpow_add hN0]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hN0.le _)

theorem rpow_le_rpow_one {N a b : ℝ} (hN : 1 ≤ N) (hab : a ≤ b) : N ^ a ≤ N ^ b :=
  Real.rpow_le_rpow_of_exponent_le hN hab

theorem one_le_rpow_of {N a : ℝ} (hN : 1 ≤ N) (ha : 0 ≤ a) : 1 ≤ N ^ a :=
  Real.one_le_rpow hN ha

theorem rpow_neg_le_one {N a : ℝ} (hN : 1 ≤ N) (ha : 0 ≤ a) : N ^ (-a) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)

/-- The cover is monotone in the loss. -/
theorem Cover.mono {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {y : Ω → Fin 2 → ℝ}
    {β γ : Ω → ℝ} {E : Set (Ω × ℝ)} {F : ℝ → Fin 2 → ℝ} {d N ε ε' w : ℝ} (hN : 1 ≤ N)
    (hεε' : ε ≤ ε') (hw : 0 ≤ w ^ (-d)) (h : Cover ν y β γ E F d N ε w) :
    Cover ν y β γ E F d N ε' w := by
  obtain ⟨t, ht, A, hA, L, hL, hmass, P, hP, hmem⟩ := h
  refine ⟨t, ht, A, fun i => (hA i).trans (rpow_le_rpow_one hN hεε'), L, hL,
    le_trans (ENNReal.ofReal_le_ofReal (rpow_le_rpow_one hN (by linarith))) hmass, P,
    hP.trans (mul_le_mul_of_nonneg_right (rpow_le_rpow_one hN hεε') hw), hmem⟩

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

end
