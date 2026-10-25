import Submission.Obl.k4_scalar_linear_critical_extremizers.Profile
import Submission.Obl.k4_finite_width_output_exclusion.Interfaces
import Submission.Obl.k4_coarsened_outer_horizon_composition.Coarsening

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter Set
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- The tilted minimum is close to its requested endpoint when the relative
profile is uniformly close to a line. No absolute density offset is bounded. -/
lemma capped_depth_near {f : ℝ → ℝ} {L ds a e s : ℝ}
    (hf : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ L →
      0 ≤ f y - f x ∧ f y - f x ≤ y - x)
    (ha : 0 < a) (he : 0 < e) (hes : e < s) (hsL : s ≤ L)
    (hprofile : ∀ x : ℝ, 0 ≤ x → x ≤ L →
      |f x - f 0 - ds * x| ≤ a * e / 4) :
    ∃ r : ℝ, 0 < r ∧ r ≤ s ∧ |r - s| ≤ e ∧
      ∀ x : ℝ, 0 ≤ x → x ≤ r → f r - f x ≤ (ds + a) * (r - x) := by
  have hs : 0 < s := he.trans hes
  have hcont := (k4_scalar_linear_critical_extremizers.profile_lipschitzOn hf).continuousOn
  obtain ⟨r, hr, hmin, hcap⟩ :=
    k4_scalar_linear_critical_extremizers.exists_tilted_profile_minimum hs.le
      (hcont.mono (Icc_subset_Icc_right hsL)) (ds + a)
  have htilt := hmin s ⟨hs.le, le_rfl⟩
  have hrerr := abs_le.mp (hprofile r hr.1 (hr.2.trans hsL))
  have hserr := abs_le.mp (hprofile s hs.le hsL)
  have hgap : s - r ≤ e / 2 := by
    apply (mul_le_mul_iff_right₀ ha).1
    nlinarith
  refine ⟨r, by linarith, hr.2, ?_, fun x hx hxr => hcap x ⟨hx, hxr⟩⟩
  rw [abs_of_nonpos (sub_nonpos.mpr hr.2)]
  linarith

lemma valid_coarsened {p : Data} (hp : Valid p) {r d : ℝ}
    (hr : 0 < r) (hrL : r ≤ p.L) (hd : 0 < d) (hd1 : d < 1)
    (hcap : ∀ s : ℝ, 0 ≤ s → s ≤ r → p.f r - p.f s ≤ d * (r - s)) :
    ∃ G, Valid {p with L := r, d := d, G := G} := by
  exact k4_coarsened_outer_horizon_composition.coarsened_problem hp hr hrL hd hd1 hcap

end
end Submission.Obl.k4_raw_critical_segment_forests
