import Submission.Obl.k4_native_calibrated_homogeneous_remainder.GeometrySelection
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.VanishingError
import Submission.Obl.k4_quadratic_atlas_normalization.ChartMonotonicity

/-! Enlarge the chart slack while keeping a positive vanishing error budget. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set Filter
open Submission.Obl.k4_finite_width_output_exclusion

def RemainderGeometry.enlarge {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (hp : Valid p) (κ error : ℕ → ℝ)
    (hκ : ∀ k, a.κ k ≤ κ k) (he : ∀ k, a.error k ≤ error k)
    (he0 : ∀ k, 0 < error k) (he1 : ∀ k, error k ≤ 1)
    (het : Tendsto error atTop (nhds 0))
    (hbound : ∀ k, κ k ≤ q.N k ^ error k) : RemainderGeometry p q r h w :=
  { a with
    κ := κ
    error := error
    error_pos := he0
    error_le_one := he1
    error_limit := het
    parent_valid := fun k => ⟨(a.parent_valid k).1, (a.parent_valid k).2.1, fun b =>
      Submission.Obl.k4_quadratic_atlas_normalization.chart_mono
        (hp.scale_ge_one _) le_rfl le_rfl (by linarith [a.slack_one k]) (hκ k)
        (hp.B_pos _ _).le ((a.parent_valid k).2.2 b) id⟩
    slack_one := fun k => (a.slack_one k).trans (hκ k)
    old_slack := fun k => (a.old_slack k).trans (hκ k)
    slack_bound := fun k => by rw [← a.same_base k]; exact hbound k
    time_bound := fun k => (a.time_bound k).trans
      (Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one _) (by linarith [he k]))
    width_bound := fun k b => (a.width_bound k b).trans
      (Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one _) (by linarith [he k]))
    normalizer_lower := fun k =>
      (inv_anti₀ (by linarith [a.slack_one k]) (hκ k)).trans (a.normalizer_lower k) }

def RawRemainder.enlarge {p q : Data} {r h w : ℝ}
    (a : RawRemainder p q r h w) (hp : Valid p) (κ error : ℕ → ℝ)
    (hκ : ∀ k, a.κ k ≤ κ k) (he : ∀ k, a.error k ≤ error k)
    (he0 : ∀ k, 0 < error k) (he1 : ∀ k, error k ≤ 1)
    (het : Tendsto error atTop (nhds 0))
    (hbound : ∀ k, κ k ≤ q.N k ^ error k) : RawRemainder p q r h w where
  toRemainderGeometry := a.toRemainderGeometry.enlarge hp κ error hκ he he0 he1 het hbound
  raw_valid := a.raw_valid
  listed := a.listed
  list_bound k γ o := (a.list_bound k γ o).trans (hκ k)

theorem RemainderGeometry.slack_error_subsequence {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (κ : ℕ → ℝ)
    (hκ : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, κ k ≤ q.N k ^ ε) :
    ∃ (ψ : ℕ → ℕ) (error : ℕ → ℝ), StrictMono ψ ∧ (∀ k, 0 < error k) ∧
      (∀ k, error k ≤ 1) ∧ Tendsto error atTop (nhds 0) ∧
      ∀ k, κ (ψ k) ≤ q.N (ψ k) ^ error k ∧ a.error (ψ k) ≤ error k := by
  apply vanishing_error_subsequence (fun ε k => κ k ≤ q.N k ^ ε ∧ a.error k ≤ ε)
  intro ε hε
  filter_upwards [hκ ε hε, a.error_limit.eventually (gt_mem_nhds hε)] with k hk he
  exact ⟨hk, he.le⟩

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
