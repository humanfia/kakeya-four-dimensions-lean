/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/CalibratedHorizon.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.BalancedNormalization
import Submission.Obl.k4_local_remainder_horizon_transfer.RemainderLifting

/-! Apply the accepted genuine terminal-lifting theorem to the calibrated
normalization certificate, retaining its exact density shift. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF
namespace CalibratedHorizon

open Submission.Obl.k4_remainder_pure_profile_normalization

abbrev SourceData := Submission.Obl.k4_remainder_pure_profile_normalization.Data
abbrev HorizonData := Submission.Obl.k4_local_remainder_horizon_transfer.Data

/-- The two accepted interfaces carry the same frozen fields. -/
def toData (p : SourceData) : HorizonData :=
  ⟨p.N, p.K, p.L, p.d, p.S, p.η, p.W, p.ω, p.ν, p.E, p.P, p.B, p.f, p.g, p.G⟩

theorem valid_toData (p : SourceData) : (toData p).Valid ↔ p.Valid := Iff.rfl

def toAtlas {p : SourceData} {k : ℕ} (a : Atlas p k) :
    Submission.Obl.k4_local_remainder_horizon_transfer.Atlas (toData p) k :=
  ⟨a.κ, a.T, a.C, a.γ, a.j, a.c, a.u, a.Q, a.R, a.A, a.F⟩

def toSequence {p : SourceData} {M D : ℕ} {r h : ℝ}
    (s : KnownSequence p M D r h) :
    Submission.Obl.k4_local_remainder_horizon_transfer.KnownSequence (toData p) M D r h where
  index := s.index
  strictMono := s.strictMono
  atlas := fun k => toAtlas (s.atlas k)
  slack_one := s.slack_one
  slack_ambient := s.slack_ambient
  slack_subpower := s.slack_subpower
  time_upper := s.time_upper
  valid := s.valid

/-- Repacking the certificate changes no prior, chart, event or native test. -/
def toRemainder {p : SourceData} {M D : ℕ} {r h cap : ℝ}
    {s : KnownSequence p M D r h} (q : NormalizedRemainder s cap) :
    Submission.Obl.k4_local_remainder_horizon_transfer.NormalizedRemainder
      (toSequence s) cap where
  K := q.K
  E := q.E
  f := q.f
  g := q.g
  G := q.G
  valid := q.valid
  event_subset := q.event_subset
  prior_positive := q.prior_positive
  normalizer_subpower := q.normalizer_subpower
  terminal_comparison := q.terminal_comparison

theorem toRemainder_data {p : SourceData} {M D : ℕ} {r h cap : ℝ}
    {s : KnownSequence p M D r h} (q : NormalizedRemainder s cap) :
    (toRemainder q).data = toData q.data := rfl

/-- The horizon is the accepted infimum of actual true terminal systems. -/
noncomputable def horizon (p : SourceData) : ℝ :=
  Submission.Obl.k4_local_remainder_horizon_transfer.horizon (toData p)

/-- The calibrated remainder retains the parent's lower horizon up to the known
atlas's time cost. The accepted lifting theorem supplies genuine terminal
floors, with fixed formats before every slack tolerance. -/
theorem horizon_bound
    (hi : Submission.Obl.k4_local_remainder_horizon_transfer.InitialHorizon)
    {p : SourceData} (hp : p.Valid) {r h cap : ℝ}
    (q : BalancedNormalization.CalibratedRemainder p r h cap) (hr : 0 ≤ r) :
    horizon p ≤ h + horizon q.remainder.data := by
  exact (toRemainder q.remainder).horizon_bound (p := toData p) hi hp hr

/-- The initial horizon bound after calibrated normalization has the same
remaining depth. This gives the universal upper endpoint for later squeezing. -/
theorem horizon_bounds
    (hi : Submission.Obl.k4_local_remainder_horizon_transfer.InitialHorizon)
    {p : SourceData} (hp : p.Valid) {r h cap : ℝ}
    (q : BalancedNormalization.CalibratedRemainder p r h cap) (hr : 0 ≤ r) :
    horizon p - h ≤ horizon q.remainder.data ∧ horizon q.remainder.data ≤ p.L - r := by
  refine ⟨by linarith [horizon_bound hi hp q hr], ?_⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  exact Submission.Obl.k4_local_remainder_horizon_transfer.horizon_le
    (p := toData q.remainder.data) q.remainder.valid
    (hi (toData q.remainder.data) q.remainder.valid (p.L - r + ε)
      (by change p.L - r < p.L - r + ε; linarith))

end CalibratedHorizon
end Submission.Obl.k4_balanced_native_packet_transport.CPF
