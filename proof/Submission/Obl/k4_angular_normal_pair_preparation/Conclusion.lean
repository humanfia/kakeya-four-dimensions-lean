import Submission.Obl.k4_angular_normal_pair_preparation.Sequence
import Submission.Obl.k4_angular_normal_pair_preparation.Numerics
import Submission.Obl.k4_angular_normal_pair_preparation.ProblemFacts
import Submission.Obl.k4_scalar_initial_true_horizon.InitialAsymptotic

namespace Submission.Obl.k4_angular_normal_pair_preparation

open MeasureTheory Filter
open scoped ENNReal BigOperators

/-- The finite analytic estimate needed after the algebraic and measure budgets.
Every hypothesis concerns the unchanged frozen problem and one native sample. -/
noncomputable def NormalPointEstimate (A S R : ℝ) : Prop :=
  ∀ N K L d η W ω ν E P B f g G,
    prob N K L d S η W ω ν E P B f g G →
    ∀ h e : ℝ, 0 < e → R * e ≤ η * L →
    ∀ (M D : ℕ) (depths : Finset ℝ) (ε : ℝ), 0 < ε → ε ≤ e →
    ∀ k, (2 : ℝ) ^ (32 : ℕ) ≤ N k ^ e →
    ∀ q : NativeSample False 8 (N k) (W k) (ω k) (ν k) (E k) (P k) (B k)
      f (g k) (G k) L S (A * e) e (R * e) h M D depths ε,
      q.badMass (R * e) ≤ ENNReal.ofReal (4 * q.κ⁻¹)

/-- The corresponding eventual estimate on all native samples. -/
noncomputable def NormalEstimate (A S R : ℝ) : Prop :=
  ∀ N K L d η W ω ν E P B f g G,
    prob N K L d S η W ω ν E P B f g G →
    ∀ h e : ℝ, 0 < e → R * e ≤ η * L →
    ∀ (M D : ℕ) (depths : Finset ℝ) (ε : ℝ), 0 < ε → ε ≤ e →
    ∀ᶠ k in atTop,
    ∀ q : NativeSample False 8 (N k) (W k) (ω k) (ν k) (E k) (P k) (B k)
      f (g k) (G k) L S (A * e) e (R * e) h M D depths ε,
      q.badMass (R * e) ≤ ENNReal.ofReal (4 * q.κ⁻¹)

/-- The fixed numerical threshold is eventually met along the original resolution sequence. -/
theorem normalEstimate_of_pointEstimate {A S R : ℝ} (hpoint : NormalPointEstimate A S R) :
    NormalEstimate A S R := by
  intro N K L d η W ω ν E P B f g G hp h e he hu M D depths ε hε hεe
  have hlarge := Submission.Obl.k4_scalar_initial_true_horizon.eventually_const_le_rpow
    (prob_N_tendsto hp) he ((2 : ℝ) ^ (32 : ℕ))
  filter_upwards [hlarge] with k hk
  exact hpoint N K L d η W ω ν E P B f g G hp h e he hu M D depths ε hε hεe k hk

/-- All existential choices and cofinal bookkeeping in the frozen theorem follow
from the single eventual angular estimate. -/
theorem normal_preparation_of_estimate
    (hEstimate : ∀ A S R : ℝ, 0 < A → 0 < S → 3 * A + 20 ≤ S * R →
      NormalEstimate A S R) : NormalPreparationStatement := by
  intro A S hA hS
  obtain ⟨R, hR, hAR, hSR⟩ := normal_depth_multiplier A S hA hS
  refine ⟨R, hR, hAR, ?_⟩
  intro N K L d η W ω ν E P B f g G hp h e he hu hnative
  apply nativeSequence_prune (fun k => (by linarith [prob_N_ge hp k]))
    (fun k γ₀ => ((prob_sampleFacts hp k).scale_pos γ₀).le) he hAR hnative
  exact hEstimate A S R hA hS hSR N K L d η W ω ν E P B f g G hp h e he hu

/-- A finite-sample geometric estimate therefore proves exactly the frozen assertion. -/
theorem normal_preparation_of_pointEstimate
    (hEstimate : ∀ A S R : ℝ, 0 < A → 0 < S → 3 * A + 20 ≤ S * R →
      NormalPointEstimate A S R) : NormalPreparationStatement := by
  apply normal_preparation_of_estimate
  intro A S R hA hS hSR
  exact normalEstimate_of_pointEstimate (hEstimate A S R hA hS hSR)

end Submission.Obl.k4_angular_normal_pair_preparation
