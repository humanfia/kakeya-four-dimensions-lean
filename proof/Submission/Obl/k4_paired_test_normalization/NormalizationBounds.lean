-- Adapted from this LOT tree, o156, session x0524, commit86ade225;
-- Submission/Obl/k4_terminal_local_sheet_pairing/NormalizationBounds.lean. Existing attribution comments are retained below.

import Submission.Obl.k4_paired_test_normalization.NormalizationScalars

namespace Submission.Obl.k4_paired_test_normalization.NormalizationStep

open Filter

/-- The scalar hypotheses used to apply the finite normalizer to an exact sample. -/
structure NormalizationBounds (Nk L a C V : ℝ) (M M' : ℕ) : Prop where
  N_two : 2 ≤ Nk
  a_pos : 0 < a
  M_le : M ≤ M'
  δ_one : δ Nk L ≤ 1
  coeff : max (Nk ^ M) (2 * Nk ^ M / ((δ Nk L)⁻¹ * Nk ^ (-(30 * a)))) ≤ Nk ^ M'
  value : max (δ Nk L * Nk ^ a) (Nk ^ a / ((δ Nk L)⁻¹ * Nk ^ (-(30 * a)))) ≤
    δ Nk L * Nk ^ (100 * a)
  deriv : max (Nk ^ a) 1 ≤ Nk ^ (100 * a)
  curvature : (δ Nk L)⁻¹ * Nk ^ (-(30 * a)) ≤ (δ Nk L)⁻¹
  anchor : Nk ^ (-(3 * a)) ≤ (Nk ^ (-a)) ^ 2 / 2
  raw_error : 2 * Nk ^ (-(29 * a)) ≤ (Nk ^ (-a)) ^ 2 / 2
  sublevel : 1152 * C * Nk ^ (-(25 * a)) <
    min (Nk ^ (-(3 * a))) 1 * (Nk ^ (-(10 * a))) ^ 2
  mass : 2 * (Nk ^ a) ^ 2 * (128 * V * Nk ^ (-(10 * a))) ≤ Nk ^ (-(6 * a))
  cross_error : 2 * Nk ^ (-(29 * a)) ≤ Nk ^ (-(25 * a)) / 2
  derivative_square : Nk ^ (-(26 * a)) ≤ Nk ^ (-(25 * a)) / 2
  disc_floor : Nk ^ (-(100 * a)) ≤ Nk ^ (-(25 * a))
  deriv_floor_sq : (Nk ^ (-(100 * a))) ^ 2 ≤ Nk ^ (-(26 * a))

theorem eventually_normalization_bounds {N : ℕ → ℝ} (hN : ∀ k, 2 ≤ N k)
    (hNt : Tendsto N atTop atTop) {a L : ℝ} (ha : 0 < a) (hL : 0 < L)
    (C V : ℝ) (M : ℕ) :
    ∃ M' : ℕ, M ≤ M' ∧ ∀ᶠ k in atTop, NormalizationBounds (N k) L a C V M M' := by
  obtain ⟨M', hM', hscalar⟩ := eventually_normalization_scalars hN hNt ha hL M
  have hnumeric := eventually_normalization_budgets (fun k => by linarith [hN k]) hNt ha C V
  refine ⟨M', hM', ?_⟩
  filter_upwards [hscalar, hnumeric] with k hs hn
  rcases hs with ⟨hδ, hc, hv, hd, hcurv⟩
  rcases hn with ⟨_, hanc, hraw, hsub, _, hmass, hcross, hderiv, hdisc, hsq⟩
  exact ⟨hN k, ha, hM', hδ, hc, hv, hd, hcurv, hanc, hraw, hsub,
    hmass, hcross, hderiv, hdisc, hsq⟩

end Submission.Obl.k4_paired_test_normalization.NormalizationStep
