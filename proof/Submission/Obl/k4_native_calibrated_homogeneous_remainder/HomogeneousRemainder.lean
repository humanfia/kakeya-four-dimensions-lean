import Submission.Obl.k4_native_calibrated_homogeneous_remainder.RetainedGeometry
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.GeometrySlack
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.ClassProfiles
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.Preparation

/-! A genuine within-world pure profile together with its retained raw atlas
and one common chart density-ratio exponent. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set Filter
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_tempered_grid_selection (Subpower subpower_mul)

structure HomogeneousRemainder (p q : Data) (r h w : ℝ) extends RawRemainder p q r h w where
  homogeneous : PureHomogeneous q
  ratio_exponent : ℝ
  ratio_band : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ b,
    q.N k ^ (ratio_exponent - ε) ≤ toRemainderGeometry.densityRatio k b ∧
      toRemainderGeometry.densityRatio k b ≤ q.N k ^ (ratio_exponent + ε)

theorem selected_classes_remainder {p q : Data} {r h w : ℝ}
    (a : RawRemainder p q r h w) (hp : Valid p) (hq : WeightedPureHomogeneous q)
    (c : SelectedClasses a.toRemainderGeometry) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Nonempty (HomogeneousRemainder p (c.profiledData.reindex ψ) r h w) := by
  let a₁ := a.reindex c.increasing
  let κ : ℕ → ℝ := fun k => a₁.κ k * c.K k
  have hκdom : ∀ k, a₁.κ k ≤ κ k := fun k =>
    le_mul_of_one_le_right (by linarith [a₁.slack_one k]) (c.subpower.1 k)
  have hκsub : Subpower ((q.reindex c.ψ).N) κ :=
    subpower_mul (fun k => by change 0 < q.N (c.ψ k); linarith [hq.1.1 (c.ψ k)])
      (a₁.toRemainderGeometry.slack_subpower hp) c.subpower
  have htlower : ∀ k, (c.K k)⁻¹ ≤ keptWeightSum (q.reindex c.ψ) c.keep k := by
    intro k
    calc
      _ ≤ ((keptWeightSum (q.reindex c.ψ) c.keep k)⁻¹)⁻¹ :=
        inv_anti₀ (inv_pos.mpr (c.weight_sum k).1) (c.inverse_weight_sum k)
      _ = _ := inv_inv _
  have hZlower : ∀ k, (κ k)⁻¹ ≤ a₁.Z k * keptWeightSum (q.reindex c.ψ) c.keep k := by
    intro k
    calc
      _ = (a₁.κ k)⁻¹ * (c.K k)⁻¹ := by simp only [κ, mul_inv_rev]; ring
      _ ≤ _ := mul_le_mul (a₁.normalizer_lower k) (htlower k)
        (inv_nonneg.mpr (by linarith [c.subpower.1 k])) (a₁.normalizer_pos k).le
  obtain ⟨ψ, error, hψ, he0, he1, het, hbudget⟩ :=
    a₁.toRemainderGeometry.slack_error_subsequence κ hκsub.2
  let a₂ := (a₁.reindex hψ).enlarge hp (κ ∘ ψ) error (fun k => hκdom (ψ k))
    (fun k => (hbudget k).2) he0 he1 het (fun k => (hbudget k).1)
  let S₂ := fun k => c.keep (ψ k)
  let K₂ := c.K ∘ ψ
  let a₃ := a₂.retainWorlds S₂ K₂ (c.valid.reindex hψ.tendsto_atTop)
    (fun k => c.weight_sum (ψ k)) (fun k => hZlower (ψ k))
  let af : RawRemainder p (c.profiledData.reindex ψ) r h w :=
    a₃.setProfile (fun s => q.f s - c.β) (c.data.reindex ψ).g (c.data.reindex ψ).G
  refine ⟨ψ, hψ, ⟨{
    toRawRemainder := af
    homogeneous := (c.pure_homogeneous hq).reindex hψ
    ratio_exponent := c.A
    ratio_band := ?_ }⟩⟩
  intro ε hε
  filter_upwards [hψ.tendsto_atTop.eventually (c.ratio_band ε hε)] with k hk b
  have hh := hk (keptWorldIndex (c.keep (ψ k)) b) ((c.keep (ψ k)).equivFin.symm b).property
  exact hh

theorem RawRemainder.pure_preparation {p q : Data} {r h w : ℝ}
    (a : RawRemainder p q r h w) (hp : Valid p) :
    ∃ q₀ : Data, Nonempty (HomogeneousRemainder p q₀ r h w) := by
  obtain ⟨q₁, ⟨a₁⟩, hq₁⟩ := a.homogeneous_preparation
  obtain ⟨c⟩ := common_world_classes a₁.toRemainderGeometry hp a₁.raw_valid
  obtain ⟨ψ, hψ, ha⟩ := selected_classes_remainder a₁ hp hq₁ c
  exact ⟨c.profiledData.reindex ψ, ha⟩

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
