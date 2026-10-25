import Submission.Obl.k4_native_calibrated_homogeneous_remainder.IntrinsicPure

/-! Separate the raw native conditions from the density-profile conditions. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_native_grid_profile_extension.Profiles

structure ProfileLaws (p : Data) : Prop where
  pure : ∀ k b s, 0 ≤ s → s ≤ p.L → Measurable (p.g k b s) ∧
    (selected p k b).map (obs (p.B k b) (δ (p.N k) s)) =
      (volume.prod Measure.count).withDensity (p.g k b s)
  joint : ∀ k b u, 0 < u → u ≤ p.η * p.L → Measurable (p.G k b u) ∧
    (selected p k b).map (fun z => (obs (p.B k b) (δ (p.N k) p.L) z,
      fun j : Fin 2 => ⌊v z.1 j / δ (p.N k) u⌋)) =
      ((volume.prod Measure.count).prod Measure.count).withDensity (p.G k b u)
  increments : ∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ p.L →
    0 ≤ p.f s - p.f r ∧ p.f s - p.f r ≤ s - r
  typical : ∀ s : ℝ, 0 ≤ s → s ≤ p.L → HasTypicalDensity p.N (familyLaw p)
    (fun k z => p.g k z.1 s (obs (p.B k z.1) (δ (p.N k) s) z.2)) (p.f s)
  density_cap : ∀ s : ℝ, 0 ≤ s → s ≤ p.L → p.f p.L - p.f s ≤ p.d * (p.L - s)
  angular_cap : ∀ u τ : ℝ, 0 < u → u ≤ p.η * p.L → 0 < τ →
    IsPowerSmall p.N (fun k => familyLaw p k {z |
      ENNReal.ofReal (p.N k ^ (-p.f p.L - p.S * u + τ)) <
        p.G k z.1 u (obs (p.B k z.1) (δ (p.N k) p.L) z.2,
          fun j : Fin 2 => ⌊v z.2.1 j / δ (p.N k) u⌋)})

theorem raw_of_valid {p : Data} (hp : Valid p) : RawValid p := by
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hmodel, -⟩
  exact ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hmodel⟩

theorem profile_of_valid {p : Data} (hp : Valid p) : ProfileLaws p := by
  rcases hp with ⟨-, -, -, -, -, -, -, -, -, hg, hG, hinc, ht, hcap, hang⟩
  refine ⟨hg, hG, hinc, ?_, hcap, ?_⟩
  · intro s hs hsL τ hτ
    obtain ⟨c, hc, hev⟩ := ht s τ hs hsL hτ
    refine ⟨c, hc, ?_⟩
    filter_upwards [hev] with k hk
    simpa only [familyLaw, worldLaw_apply, mem_ofPred_eq, selected, priorMass] using hk
  · intro u τ hu huL hτ
    obtain ⟨c, hc, hev⟩ := hang u τ hu huL hτ
    refine ⟨c, hc, ?_⟩
    filter_upwards [hev] with k hk
    simpa only [familyLaw, worldLaw_apply, mem_ofPred_eq, selected, priorMass] using hk

theorem valid_of_raw_profile {p : Data} (hp : RawValid p) (hl : ProfileLaws p) : Valid p := by
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hmodel⟩
  refine ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hmodel, hl.pure, hl.joint, hl.increments,
    ?_, hl.density_cap, ?_⟩
  · intro s τ hs hsL hτ
    obtain ⟨c, hc, hev⟩ := hl.typical s hs hsL τ hτ
    refine ⟨c, hc, ?_⟩
    filter_upwards [hev] with k hk
    simpa only [familyLaw, worldLaw_apply, mem_ofPred_eq, selected, priorMass] using hk
  · intro u τ hu huL hτ
    obtain ⟨c, hc, hev⟩ := hl.angular_cap u τ hu huL hτ
    refine ⟨c, hc, ?_⟩
    filter_upwards [hev] with k hk
    simpa only [familyLaw, worldLaw_apply, mem_ofPred_eq, selected, priorMass] using hk

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
