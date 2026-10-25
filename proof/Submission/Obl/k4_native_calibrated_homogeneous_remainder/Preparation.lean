import Submission.Obl.k4_native_calibrated_homogeneous_remainder.PureHomogenization

/-! Prepare a raw calibrated-remainder candidate for selecting its world classes. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion

theorem RawRemainder.homogeneous_preparation {p q : Data} {r h w : ℝ}
    (a : RawRemainder p q r h w) :
    ∃ q₀ : Data, Nonempty (RawRemainder p q₀ r h w) ∧ WeightedPureHomogeneous q₀ := by
  obtain ⟨ψ, K', E', ρ₀, F, hψ, hρ₀, hvalid, hKdom, hsub, hreg, htyp⟩ :=
    a.raw_valid.weighted_homogenization q.L 1 a.raw_valid.2.2.2.1 zero_lt_one
  let q₁ := Submission.Obl.k4_native_calibrated_homogeneous_remainder.selectIncidences
    (q.reindex ψ) K' E'
  let a₁ : RawRemainder p q₁ r h w :=
    (a.reindex hψ).selectIncidences K' E' hsub hvalid
  refine ⟨canonicalProfile q₁ hvalid (fun s => F (ρ₀ + s) 0), ?_, ?_⟩
  · exact ⟨a₁.setProfile (fun s => F (ρ₀ + s) 0)
      (fun k b s => pureDensity hvalid k b (δ (q₁.N k) s))
      (fun k b u => jointDensity hvalid k b (δ (q₁.N k) q₁.L) (δ (q₁.N k) u))⟩
  · exact canonicalProfile_weighted_homogeneous hvalid hρ₀ hreg htyp

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
