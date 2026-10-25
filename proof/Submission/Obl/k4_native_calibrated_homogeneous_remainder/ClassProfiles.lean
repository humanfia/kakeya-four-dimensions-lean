import Submission.Obl.k4_native_calibrated_homogeneous_remainder.CommonClasses
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.PureHomogenization
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.ProfileDomination
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.UnweightProfiles

/-! Convert the selected common weighted profile into a within-world profile. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_native_grid_profile_extension.Profiles

noncomputable def SelectedClasses.data {p q : Data} {r h w : ℝ}
    {a : RemainderGeometry p q r h w} (c : SelectedClasses a) : Data :=
  keepWorlds (q.reindex c.ψ) c.keep c.K

noncomputable def SelectedClasses.profiledData {p q : Data} {r h w : ℝ}
    {a : RemainderGeometry p q r h w} (c : SelectedClasses a) : Data :=
  setProfile c.data (fun s => q.f s - c.β) c.data.g c.data.G

theorem SelectedClasses.pure_homogeneous {p q : Data} {r h w : ℝ}
    {a : RemainderGeometry p q r h w} (c : SelectedClasses a)
    (hq : WeightedPureHomogeneous q) : PureHomogeneous c.profiledData := by
  refine ⟨c.valid,
    (fun k b s => hq.2.1 (c.ψ k) (keptWorldIndex (c.keep k) b) s),
    (fun k b u => hq.2.2.1 (c.ψ k) (keptWorldIndex (c.keep k) b) u), ?_, ?_⟩
  · intro r s hr hrs hs
    change s ≤ q.L at hs
    have hh := hq.2.2.2.1 r s hr hrs hs
    change 0 ≤ (q.f s - c.β) - (q.f r - c.β) ∧
      (q.f s - c.β) - (q.f r - c.β) ≤ s - r
    constructor <;> linarith [hh.1, hh.2]
  · intro s hs hsL
    change s ≤ q.L at hsL
    have hN : ∀ k, 1 ≤ q.N k := fun k => by linarith [hq.1.1 k]
    have hB : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
        (keptWeightSum (q.reindex c.ψ) c.keep k)⁻¹ ≤ q.N (c.ψ k) ^ ε := by
      intro ε hε
      filter_upwards [c.subpower.2 ε hε] with k hk
      exact (c.inverse_weight_sum k).trans hk
    have hdom : ∀ k (A : Set (Fin (q.W (c.ψ k)) × Incidence)),
        familyLaw c.data k ((fun z => (keptWorldIndex (c.keep k) z.1, z.2)) ⁻¹' A) ≤
          ENNReal.ofReal ((keptWeightSum (q.reindex c.ψ) c.keep k)⁻¹) *
            familyLaw q (c.ψ k) A := by
      intro k A
      exact keepWorlds_law_domination (hq.1.reindex c.increasing.tendsto_atTop)
        c.keep c.K (fun k => (c.weight_sum k).1) k A
    have ht := typical_pullback_of_subpower_domination q.N hN (familyLaw q) (familyLaw c.data)
      c.ψ c.increasing.tendsto_atTop (fun k z => (keptWorldIndex (c.keep k) z.1, z.2))
      (fun k => (keptWeightSum (q.reindex c.ψ) c.keep k)⁻¹) hB hdom
      (fun k z => ENNReal.ofReal (q.ω k z.1) *
        q.g k z.1 s (obs (q.B k z.1) (δ (q.N k) s) z.2)) (q.f s)
      (hq.2.2.2.2 s hs hsL)
    apply typical_unweight (q.N ∘ c.ψ) (fun k => hN (c.ψ k)) (familyLaw c.data)
      (fun k z => q.ω (c.ψ k) (keptWorldIndex (c.keep k) z.1))
      (fun k z => q.g (c.ψ k) (keptWorldIndex (c.keep k) z.1) s
        (obs (q.B (c.ψ k) (keptWorldIndex (c.keep k) z.1)) (δ (q.N (c.ψ k)) s) z.2))
      (q.f s) c.β ht
    intro ε hε
    filter_upwards [c.weight_band ε hε] with k hk
    apply Eventually.of_forall
    intro z
    exact hk (keptWorldIndex (c.keep k) z.1) ((c.keep k).equivFin.symm z.1).property

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
