/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarUniformRangeBlockFit.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarUniformRangeBlockFit.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarNormalizedBlockFit

/-! One original block-fitting threshold for every prescribed power-range mesh. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

universe u


open MeasureTheory Set Filter
open Submission.Obl.k4_discrete_of_terminal_charts

theorem uniform_original_scalar_block_fit_between_powers_all_labels
    (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hsub : SubpowerBound N K)
    {a b d τ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hd0 : 0 ≤ d) (hd : d < 1) (hτ : 0 < τ) :
    ∀ᶠ k in atTop, ∀ (Λ : Type u) [MeasurableSpace Λ], ∀ p : ℝ, N k ^ (-b) ≤ p → p ≤ N k ^ (-a) →
      OriginalScalarBlockFitAt (d := d) Λ (K k) p (N k ^ (-τ)) := by
  let B : ℕ → ℝ := fun k => scalarBlockFitBound (K k)
  have hB : ∀ k, 1 ≤ B k := fun k => (scalarBlockFitBound_bounds (hK k)).1
  have hBsub : SubpowerBound N B := by
    exact subpower_mul (fun k => zero_lt_one.trans_le (hN k))
      (fun _ => by norm_num) (fun k => pow_nonneg (zero_le_one.trans (hK k)) 10)
      (subpower_const hNt 100000) (subpower_pow hN (fun k => zero_le_one.trans (hK k)) hsub 10)
  filter_upwards [uniform_original_scalar_affine_fit_between_powers_all_labels
      N B hN hNt hB hBsub ha hab hd0 hd hτ] with k hk
  intro Λ _ p hlow hhigh
  exact original_scalar_block_fit_of_normalized_fit (hK k)
    ((Real.rpow_pos_of_pos (zero_lt_one.trans_le (hN k)) (-b)).trans_le hlow)
    hd.le (hk Λ p hlow hhigh)

theorem uniform_original_scalar_block_fit_between_powers {Λ : Type*} [MeasurableSpace Λ]
    (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hsub : SubpowerBound N K)
    {a b d τ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hd0 : 0 ≤ d) (hd : d < 1) (hτ : 0 < τ) :
    ∀ᶠ k in atTop, ∀ p : ℝ, N k ^ (-b) ≤ p → p ≤ N k ^ (-a) →
      OriginalScalarBlockFitAt (d := d) Λ (K k) p (N k ^ (-τ)) := by
  filter_upwards [uniform_original_scalar_block_fit_between_powers_all_labels
    N K hN hNt hK hsub ha hab hd0 hd hτ] with k hk
  exact hk Λ

theorem uniform_subpower_original_scalar_block_fit_between_powers_all_labels
    (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hsub : SubpowerBound N K)
    {a b d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hd0 : 0 ≤ d) (hd : d < 1) :
    ∃ Q : ℕ → ℝ, (∀ k, 1 ≤ Q k) ∧ SubpowerBound N Q ∧
      ∀ᶠ k in atTop, ∀ (Λ : Type u) [MeasurableSpace Λ], ∀ p : ℝ, N k ^ (-b) ≤ p → p ≤ N k ^ (-a) →
        OriginalScalarBlockFitAt (d := d) Λ (K k) p (Q k)⁻¹ := by
  obtain ⟨τ, Q, _, _, hQeq, hQ, hQsub, hgood⟩ := exists_uniform_subpower_tolerance N hN
    (fun τ k => ∀ (Λ : Type u) [MeasurableSpace Λ], ∀ p : ℝ, N k ^ (-b) ≤ p → p ≤ N k ^ (-a) →
      OriginalScalarBlockFitAt (d := d) Λ (K k) p (N k ^ (-τ)))
    (fun τ hτ => uniform_original_scalar_block_fit_between_powers_all_labels N K hN hNt hK hsub ha hab hd0 hd hτ)
  refine ⟨Q, hQ, hQsub, ?_⟩
  filter_upwards [hgood] with k hk
  have he : N k ^ (-τ k) = (Q k)⁻¹ := by rw [hQeq k, Real.rpow_neg (zero_le_one.trans (hN k))]
  simpa only [he] using hk

theorem uniform_subpower_original_scalar_block_fit_between_powers {Λ : Type*} [MeasurableSpace Λ]
    (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hsub : SubpowerBound N K)
    {a b d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hd0 : 0 ≤ d) (hd : d < 1) :
    ∃ Q : ℕ → ℝ, (∀ k, 1 ≤ Q k) ∧ SubpowerBound N Q ∧
      ∀ᶠ k in atTop, ∀ p : ℝ, N k ^ (-b) ≤ p → p ≤ N k ^ (-a) →
        OriginalScalarBlockFitAt (d := d) Λ (K k) p (Q k)⁻¹ := by
  obtain ⟨Q, hQ, hQsub, hgood⟩ := uniform_subpower_original_scalar_block_fit_between_powers_all_labels
    N K hN hNt hK hsub ha hab hd0 hd
  refine ⟨Q, hQ, hQsub, ?_⟩
  filter_upwards [hgood] with k hk
  exact hk Λ

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
