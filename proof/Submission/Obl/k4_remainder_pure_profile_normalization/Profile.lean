/- Adapted from this LOT tree, o118, session x0400, Profile.lean,
commit bd322ee595fd; earlier from o105/x0351,x0367 Profile.lean at split/s042. -/
import Submission.Obl.k4_remainder_pure_profile_normalization.ProblemFields
import Submission.Obl.k4_native_grid_profile_extension.Profiles.ProfileCompactness
namespace Submission.Obl.k4_remainder_pure_profile_normalization
open Set
/-- Monotone unit-speed increments on the depth interval. -/
def ProfileIncrement (f : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ L → 0 ≤ f s - f r ∧ f s - f r ≤ s - r

/-- Reuse the accepted profile extension theorem to obtain continuity on the interval. -/
theorem ProfileIncrement.continuousOn {f : ℝ → ℝ} {L : ℝ}
    (hf : ProfileIncrement f L) : ContinuousOn f (Icc 0 L) := by
  obtain ⟨g, hg, heq, _⟩ :=
    Submission.Obl.k4_native_grid_profile_extension.Profiles.extend_profile_from_grid
      (s := Icc 0 L) (fun r => f r) (fun r s hrs => hf r s r.property.1 hrs s.property.2)
  exact hg.continuous.continuousOn.congr (fun r hr => (heq ⟨r, hr⟩).symm)

end Submission.Obl.k4_remainder_pure_profile_normalization
