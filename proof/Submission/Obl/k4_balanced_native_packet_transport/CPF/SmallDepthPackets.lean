/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/SmallDepthPackets.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.Profile
import Submission.Obl.k4_balanced_native_packet_transport.CPF.CoarsenedProblem
import Submission.Obl.k4_scalar_linear_critical_extremizers.Profile

/-! Small positive coarsenings for balanced packets. Relative linearity permits
a nearby endpoint with a strict slope cap, so the frozen initial-horizon input
applies to an actual valid coarsening. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF
namespace SmallDepthPackets

open Set Filter

/-- A steeper tilted minimum stays in the right half of the small interval and
gives a cap on its entire preceding depth interval. -/
theorem exists_positive_cap {f : ℝ → ℝ} {b d D err : ℝ}
    (hb : 0 < b) (hdD : d < D)
    (hf : ContinuousOn f (Icc (0 : ℝ) (2 * b)))
    (hclose : ∀ t ∈ Icc (0 : ℝ) (2 * b), |f t - f 0 - d * t| ≤ err)
    (hsmall : 2 * err ≤ (D - d) * b) :
    ∃ r ∈ Icc b (2 * b), ∀ s ∈ Icc (0 : ℝ) r,
      f r - f s ≤ D * (r - s) := by
  have h0 : (0 : ℝ) ≤ 2 * b := by linarith
  obtain ⟨r, hr, hmin, hcap⟩ :=
    Submission.Obl.k4_scalar_linear_critical_extremizers.exists_tilted_profile_minimum
      h0 hf D
  have hnear : 2 * b - r ≤ 2 * err / (D - d) := by
    apply Submission.Obl.k4_scalar_linear_critical_extremizers.tilted_profile_minimum_near_endpoint
      (sub_pos.mpr hdD) (abs_le.mp (hclose r hr)).1
      (abs_le.mp (hclose (2 * b) ⟨h0, le_rfl⟩)).2
    convert hmin (2 * b) ⟨h0, le_rfl⟩ using 1 <;> ring
  have herror : 2 * err / (D - d) ≤ b :=
    (div_le_iff₀ (sub_pos.mpr hdD)).mpr (by nlinarith [hsmall])
  exact ⟨r, ⟨by linarith, hr.2⟩, hcap⟩

/-- The selected small endpoint is an actual valid problem, including its
coarsened angular laws and the strict subunit endpoint cap. -/
theorem exists_valid_coarsening {p : Data} (hp : p.Valid)
    {b d D err : ℝ} (hb : 0 < b) (hbL : 2 * b ≤ p.L)
    (hD : 0 < D) (hD₁ : D < 1) (hdD : d < D)
    (hclose : ∀ t ∈ Icc (0 : ℝ) (2 * b), |p.f t - p.f 0 - d * t| ≤ err)
    (hsmall : 2 * err ≤ (D - d) * b) :
    ∃ r ∈ Icc b (2 * b), (p.coarsen r D).Valid := by
  obtain ⟨r, hr, hcap⟩ := exists_positive_cap hb hdD
    (hp.profile.continuousOn.mono (Icc_subset_Icc le_rfl hbL)) hclose hsmall
  exact ⟨r, hr, hp.coarsen (hb.trans_le hr.1) (hr.2.trans hbL) hD hD₁
    (fun s hs hsr => hcap s ⟨hs, hsr⟩)⟩

/-- The frozen initial-horizon assumption therefore supplies genuine true
packets of arbitrarily small time cost in the original problem coordinates.
All formats precede every slack tolerance, as required by `Terminal`. -/
theorem exists_small_true_systems (hi : InitialHorizon) {p : Data} (hp : p.Valid)
    {b d D err : ℝ} (hb : 0 < b) (hbL : 2 * b ≤ p.L)
    (hD : 0 < D) (hD₁ : D < 1) (hdD : d < D)
    (hclose : ∀ t ∈ Icc (0 : ℝ) (2 * b), |p.f t - p.f 0 - d * t| ≤ err)
    (hsmall : 2 * err ≤ (D - d) * b) :
    ∃ r ∈ Icc b (2 * b), ∀ h : ℝ, 2 * b < h →
      ∃ M₁ D₁ : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
        ∃ a : Atlas p k, 1 ≤ a.κ ∧ p.K k ≤ a.κ ∧ a.κ ≤ p.N k ^ ε ∧
          (2 : ℝ) ^ a.T ≤ p.N k ^ h ∧ a.TrueAt M₁ D₁ r := by
  obtain ⟨r, hr, hvalid⟩ := exists_valid_coarsening hp hb hbL hD hD₁ hdD hclose hsmall
  refine ⟨r, hr, fun h hh => ?_⟩
  exact true_systems_of_coarsened_terminal
    (hi (p.coarsen r D) hvalid h (hr.2.trans_lt hh))

end SmallDepthPackets
end Submission.Obl.k4_balanced_native_packet_transport.CPF
