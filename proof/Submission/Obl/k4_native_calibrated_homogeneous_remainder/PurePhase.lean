import Submission.Obl.k4_native_calibrated_homogeneous_remainder.DyadicPhase
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.IntrinsicPure
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.CoarseningProfiles

/-! Transfer the pure weighted profile from the encoding phase to the exact
dyadic depth required by the native problem. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_native_grid_profile_extension.Profiles

theorem RawValid.pure_phase_typical {p : Data} (hp : RawValid p)
    {ρ s e : ℝ} (hρ : 0 ≤ ρ) (hs : 0 ≤ s)
    (ht : HasTypicalDensity p.N (familyLaw p)
      (fun k z => ENNReal.ofReal (p.ω k z.1) *
        pureDensity hp k z.1 (Comp.theta (p.N k) ρ s)
          (obs (p.B k z.1) (Comp.theta (p.N k) ρ s) z.2)) e) :
    HasTypicalDensity p.N (familyLaw p)
      (fun k z => ENNReal.ofReal (p.ω k z.1) * pureDensity hp k z.1 (δ (p.N k) s)
        (obs (p.B k z.1) (δ (p.N k) s) z.2)) e := by
  have hN : ∀ k, 1 ≤ p.N k := fun k => by linarith [hp.1 k]
  choose d hd hfactor using fun k => intrinsic_phase_factor (hN k) hρ hs
  let Q : (k : ℕ) → Fin (p.W k) → Incidence → Observation := fun k b =>
    obs (p.B k b) (Comp.theta (p.N k) ρ s)
  let h : ℕ → ℤ → ℤ := fun k n => n / (2 : ℤ) ^ d k
  have hobs : ∀ k b z, ((Q k b z).1, h k (Q k b z).2) =
      obs (p.B k b) (δ (p.N k) s) z := fun k b z =>
    (pure_obs_coarsening (hfactor k) (p.B k b) z).symm
  have hmap : ∀ k b, (selected p k b).map (fun z => ((Q k b z).1, h k (Q k b z).2)) =
      (volume.prod Measure.count).withDensity (pureDensity hp k b (δ (p.N k) s)) := by
    intro k b
    simp_rw [hobs]
    exact (pureDensity_spec hp k b _).2
  refine typical_of_coarsening p.N hN hp.2.1 (familyLaw p) _ _ e ht ?_ (fun _ => 2) ?_ ?_
  · intro k
    have hm := weighted_refinement_density_le volume
      (fun b => ENNReal.ofReal (p.ω k b)) (selected p k) (Q k)
      (fun b => measurable_nativeObs _ _) (h k)
      (fun b => pureDensity hp k b (δ (p.N k) s))
      (fun b => pureDensity hp k b (Comp.theta (p.N k) ρ s))
      (fun b => (pureDensity_spec hp k b _).1)
      (fun b => (pureDensity_spec hp k b _).1)
      (hmap k) (fun b => (pureDensity_spec hp k b _).2)
    simpa only [hobs, familyLaw, Q] using hm
  · intro ε hε
    exact ((tendsto_rpow_atTop hε).comp hp.2.1).eventually (eventually_ge_atTop 2)
  · intro ε hε k
    have hm := weighted_refinement_low_density_mass volume
      (fun b => ENNReal.ofReal (p.ω k b)) (selected p k) (Q k)
      (fun b => measurable_nativeObs _ _) (h k) (ENNReal.ofReal (p.N k ^ (-ε))) 2
      (count_int_div_two_pow_le (hd k))
      (fun b => pureDensity hp k b (δ (p.N k) s))
      (fun b => pureDensity hp k b (Comp.theta (p.N k) ρ s))
      (fun b => (pureDensity_spec hp k b _).1)
      (fun b => (pureDensity_spec hp k b _).1)
      (hmap k) (fun b => (pureDensity_spec hp k b _).2)
    simp only [hobs] at hm
    calc
      _ ≤ ENNReal.ofReal (p.N k ^ (-ε)) * 2 * familyLaw p k univ := hm
      _ ≤ ENNReal.ofReal (p.N k ^ (-ε)) * 2 * 1 :=
        mul_le_mul' le_rfl (hp.family_mass_le_one k)
      _ = _ := by rw [mul_one, ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith [hN k]) _)]; norm_num

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
