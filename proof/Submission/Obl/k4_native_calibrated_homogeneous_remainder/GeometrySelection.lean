import Submission.Obl.k4_native_calibrated_homogeneous_remainder.IncidenceSelection
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.WorldRestriction

/-! Geometry survives cofinal subsequences and further incidence restrictions. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set Filter
open Submission.Obl.k4_finite_width_output_exclusion

def RemainderGeometry.reindex {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    RemainderGeometry p (q.reindex ψ) r h w where
  φ := a.φ ∘ ψ
  increasing := a.increasing.comp hψ
  same_base k := a.same_base (ψ k)
  length := a.length
  density_cap := a.density_cap
  angular_rate := a.angular_rate
  angular_range := a.angular_range
  M := a.M
  D := a.D
  κ := a.κ ∘ ψ
  parent := fun k => a.parent (ψ k)
  worlds := fun k => a.worlds (ψ k)
  error := a.error ∘ ψ
  error_pos k := a.error_pos (ψ k)
  error_le_one k := a.error_le_one (ψ k)
  error_limit := a.error_limit.comp hψ.tendsto_atTop
  parent_valid k := a.parent_valid (ψ k)
  slack_one k := a.slack_one (ψ k)
  old_slack k := a.old_slack (ψ k)
  slack_bound k := a.slack_bound (ψ k)
  time_bound k := a.time_bound (ψ k)
  width_bound k := a.width_bound (ψ k)
  θ := fun k => a.θ (ψ k)
  index_preserved k := a.index_preserved (ψ k)
  planar_map k := a.planar_map (ψ k)
  hidden_map k := a.hidden_map (ψ k)
  prior_pos k := a.prior_pos (ψ k)
  prior_inverse_bound k := a.prior_inverse_bound (ψ k)
  conditioned_prior k := a.conditioned_prior (ψ k)
  selected_pullback k := a.selected_pullback (ψ k)
  derivative_unit k := a.derivative_unit (ψ k)
  Z := a.Z ∘ ψ
  normalizer_pos k := a.normalizer_pos (ψ k)
  normalizer_lower k := a.normalizer_lower (ψ k)
  normalizer_upper k := a.normalizer_upper (ψ k)
  normalizer_sum k := a.normalizer_sum (ψ k)
  world_weights k := a.world_weights (ψ k)

def RawRemainder.reindex {p q : Data} {r h w : ℝ}
    (a : RawRemainder p q r h w) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    RawRemainder p (q.reindex ψ) r h w where
  toRemainderGeometry := a.toRemainderGeometry.reindex hψ
  raw_valid := a.raw_valid.reindex hψ.tendsto_atTop
  listed k := a.listed (ψ k)
  list_bound k := a.list_bound (ψ k)

def RemainderGeometry.selectIncidences {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (K' : ℕ → ℝ)
    (E' : (k : ℕ) → Fin (q.W k) → Set Incidence) (hsub : ∀ k b, E' k b ⊆ q.E k b) :
    RemainderGeometry p (selectIncidences q K' E') r h w :=
  { a with selected_pullback := fun k b z hz => a.selected_pullback k b z (hsub k b hz) }

def RawRemainder.selectIncidences {p q : Data} {r h w : ℝ}
    (a : RawRemainder p q r h w) (K' : ℕ → ℝ)
    (E' : (k : ℕ) → Fin (q.W k) → Set Incidence) (hsub : ∀ k b, E' k b ⊆ q.E k b)
    (hvalid : RawValid (selectIncidences q K' E')) :
    RawRemainder p (selectIncidences q K' E') r h w where
  toRemainderGeometry := a.toRemainderGeometry.selectIncidences K' E' hsub
  raw_valid := hvalid
  listed := a.listed
  list_bound := a.list_bound

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
