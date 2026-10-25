import Submission.Obl.k4_raw_localized_native_systems.Window.OriginalCaps
import Submission.Obl.k4_raw_localized_native_systems.Window.SpeedGood
import Submission.Obl.k4_raw_localized_native_systems.Pairing.ProblemDensities
import Submission.Obl.k4_uncapped_native_capping.UWE.DensityPreparedLaw

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory Set Filter
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_native_grid_profile_extension.Profiles

noncomputable section

/-- One common original-world density and speed event, before any chart is
selected or any prior is conditioned. -/
def densityGood (p : Data) (R A : Finset ℝ) (τ : ℝ) (k : ℕ) (γ : Fin (p.W k)) : Set Point :=
  (k4_uncapped_native_capping.UWE.densityPreparationBad
    (originalCapProblem p) p.S R A τ k γ)ᶜ ∩ speedGood (p.K k)

theorem measurableSet_densityGood {p : Data} (hp : Valid p) (R A : Finset ℝ)
    (hR : ∀ r ∈ R, 0 ≤ r ∧ r ≤ p.L)
    (hA : ∀ u ∈ A, 0 < u ∧ u ≤ p.η * p.L) (τ : ℝ) (k : ℕ) (γ : Fin (p.W k)) :
    MeasurableSet (densityGood p R A τ k γ) := by
  have hp' : (originalCapProblem p).Valid p.S p.η := hp
  exact (hp'.measurableSet_densityPreparationBad R A hR hA τ k γ).compl.inter
    (measurableSet_speedGood _)

theorem densityGood_speed {p : Data} {R A : Finset ℝ} {τ : ℝ} {k : ℕ}
    {γ : Fin (p.W k)} {z : Point} (hz : z ∈ densityGood p R A τ k γ) :
    ‖v z.1‖ ≤ p.K k := hz.2

theorem densityGood_pure {p : Data} {R A : Finset ℝ} {τ : ℝ} {k : ℕ}
    {γ : Fin (p.W k)} {z : Point} (hz : z ∈ densityGood p R A τ k γ)
    {r : ℝ} (hr : r ∈ insert p.L R) :
    ENNReal.ofReal (p.N k ^ (-p.f r - τ)) ≤
      p.g k γ r (obs (p.B k γ) (δ (p.N k) r) z) ∧
      p.g k γ r (obs (p.B k γ) (δ (p.N k) r) z) ≤
        ENNReal.ofReal (p.N k ^ (-p.f r + τ)) :=
  (originalCapProblem p).pure_density_band_of_not_bad p.S R A τ k γ z hz.1 hr

theorem densityGood_angular {p : Data} (hp : Valid p) {R A : Finset ℝ} {τ : ℝ} {k : ℕ}
    {γ : Fin (p.W k)} {z : Point} (hz : z ∈ densityGood p R A τ k γ)
    {u : ℝ} (hu : u ∈ A) :
    p.G k γ u (obs (p.B k γ) (δ (p.N k) p.L) z,
      fun j => ⌊v z.1 j / δ (p.N k) u⌋) ≤
      ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) *
        p.g k γ p.L (obs (p.B k γ) (δ (p.N k) p.L) z) :=
  (originalCapProblem p).angular_ratio_of_not_bad p.S R A τ k γ (hp.scale_pos k) z hz.1 hu

/-- The same common mask supplies the exact angular-good predicate used by
the finite good-set omission theorem. -/
theorem densityGood_angGood {p : Data} {R A : Finset ℝ} {τ : ℝ} {k : ℕ}
    {γ : Fin (p.W k)} {z : Point} (hz : z ∈ densityGood p R A τ k γ)
    {u : ℝ} (hu : u ∈ A) : Pairing.AngGood p k γ u τ z := by
  refine ⟨?_, (densityGood_pure hz (Finset.mem_insert_self _ _)).1⟩
  apply le_of_not_gt
  intro hbad
  apply hz.1
  apply Or.inr
  exact mem_iUnion.mpr ⟨u, mem_iUnion.mpr ⟨hu, hbad⟩⟩

theorem densityGood_loss_eq {p : Data} (hp : Valid p) (R A : Finset ℝ)
    (τ : ℝ) (k : ℕ) (γ : Fin (p.W k)) :
    selected p k γ (densityGood p R A τ k γ)ᶜ =
      selected p k γ (k4_uncapped_native_capping.UWE.densityPreparationBad
        (originalCapProblem p) p.S R A τ k γ) := by
  rw [densityGood, speedGood_inter_loss hp k γ le_rfl, compl_compl]

/-- All common density and speed cuts have one positive power tail under the
unchanged original weighted selected laws. -/
theorem densityGood_powerSmall {p : Data} (hp : Valid p) (R A : Finset ℝ)
    (hR : ∀ r ∈ R, 0 ≤ r ∧ r ≤ p.L)
    (hA : ∀ u ∈ A, 0 < u ∧ u ≤ p.η * p.L) {τ : ℝ} (hτ : 0 < τ) :
    IsPowerSmall p.N (fun k => ∑ γ, ENNReal.ofReal (p.ω k γ) *
      selected p k γ (densityGood p R A τ k γ)ᶜ) := by
  have hp' : (originalCapProblem p).Valid p.S p.η := hp
  have hh := hp'.finite_density_preparation R A hR hA hτ
  change IsPowerSmall p.N (fun k => ∑ γ, ENNReal.ofReal (p.ω k γ) *
    selected p k γ (k4_uncapped_native_capping.UWE.densityPreparationBad
      (originalCapProblem p) p.S R A τ k γ)) at hh
  simpa only [densityGood_loss_eq hp R A τ] using hh

end
end Submission.Obl.k4_raw_localized_native_systems.Window
