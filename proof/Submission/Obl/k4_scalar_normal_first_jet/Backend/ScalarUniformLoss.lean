/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarUniformLoss.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarUniformLoss.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Lib.K4ModelReduction.Diagonal
import Submission.Obl.k4_scalar_mesh_block_reduction.Uniformity
import Submission.Obl.k4_discrete_of_terminal_charts.Horizon

/-! Choose one subpower loss after proving every fixed positive tolerance. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open Filter
open Submission.Obl.k4_discrete_of_terminal_charts

theorem exists_uniform_subpower_tolerance (N : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k)
    (P : ℝ → ℕ → Prop) (hP : ∀ τ : ℝ, 0 < τ → ∀ᶠ k in atTop, P τ k) :
    ∃ (τ Q : ℕ → ℝ), (∀ k, 0 < τ k) ∧ Tendsto τ atTop (nhds 0) ∧
      (∀ k, Q k = N k ^ τ k) ∧ (∀ k, 1 ≤ Q k) ∧ SubpowerBound N Q ∧
      ∀ᶠ k in atTop, P (τ k) k := by
  obtain ⟨m, τ, _, _, hτ, _, hτlim, hgood⟩ :=
    Submission.Lib.K4ModelReduction.exists_slow_tolerance
      (fun _ τ k => P τ k) (fun _ τ hτ => hP τ hτ)
  obtain ⟨hQ, hQsub⟩ :=
    Submission.Obl.k4_scalar_mesh_block_reduction.subpower_of_vanishing_exponent
      N τ hN (fun k => (hτ k).le) hτlim
  refine ⟨τ, (fun k => N k ^ τ k), hτ, hτlim, fun _ => rfl, hQ, hQsub, ?_⟩
  filter_upwards [hgood] with k hk
  exact hk 0 (Nat.zero_le _)

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
