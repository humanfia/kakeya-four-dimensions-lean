import Submission.Obl.k4_raw_critical_segment_forests.PreparedInterface
import Submission.Obl.k4_remainder_pure_profile_normalization.AtlasSequence

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

abbrev PureData := Submission.Obl.k4_remainder_pure_profile_normalization.Data
abbrev PureAtlas := Submission.Obl.k4_remainder_pure_profile_normalization.Atlas

def toPure (p : Data) : PureData :=
  ⟨p.N, p.K, p.L, p.d, p.S, p.η, p.W, p.ω, p.ν, p.E, p.P, p.B, p.f, p.g, p.G⟩

def fromPure (p : PureData) : Data :=
  ⟨p.N, p.K, p.L, p.d, p.S, p.η, p.W, p.ω, p.ν, p.E, p.P, p.B, p.f, p.g, p.G⟩

theorem valid_toPure_iff (p : Data) : Valid p ↔ (toPure p).Valid := Iff.rfl
theorem valid_fromPure_iff (p : PureData) : Valid (fromPure p) ↔ p.Valid := Iff.rfl

def atlasToPure {p : Data} {k : ℕ} (a : Atlas p k) (κ : ℝ) : PureAtlas (toPure p) k :=
  ⟨κ, a.T, a.C, a.γ, a.j, a.c, a.u, a.Q, a.R, a.A, a.F⟩

def atlasFromPure {p : PureData} {k : ℕ} (a : PureAtlas p k) : Atlas (fromPure p) k :=
  ⟨a.T, a.C, a.γ, a.j, a.c, a.u, a.Q, a.R, a.A, a.F, fun _ _ => ∅⟩

theorem knownAt_toPure {p : Data} {k M D : ℕ} {a : Atlas p k} {κ r : ℝ}
    (ha : a.KnownAt M D κ r) : (atlasToPure a κ).KnownAt M D r := by
  obtain ⟨⟨hC, hsep, hchart, hmass⟩, hlist⟩ := ha
  exact ⟨a.lst, hC, hsep, hlist, hchart, hmass⟩

end Submission.Obl.k4_raw_critical_segment_forests
