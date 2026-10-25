/-
Adapted from this LOT tree, o147, session x0498, commit 5dd59d875729,
Submission/Obl/k4_local_remainder_horizon_transfer/SampleBridge.lean.
Earlier provenance is preserved below.
-/
import Submission.Obl.k4_remainder_pure_profile_normalization.AtlasSequence
import Submission.Obl.k4_remainder_pure_profile_normalization.Normalization.NormalizeProblem

/-! Bridges from the frozen predicates to finite chart normalization. -/

namespace Submission.Obl.k4_remainder_pure_profile_normalization

open MeasureTheory

/-- The finite system underlying the exact-sequence atlas record. -/
def Atlas.system {p : Data} {k : ℕ} (a : Atlas p k) :
    Normalization.ChartSystem (p.W k) a.T :=
  ⟨a.C, a.γ, a.j, a.c, a.u, a.Q, a.R, a.A, a.F⟩

/-- The genuine floor and every other chart condition agree definitionally. -/
theorem Atlas.trueAt_iff_valid {p : Data} {k : ℕ} (a : Atlas p k) (M D : ℕ) (r : ℝ) :
    a.TrueAt M D r ↔ a.system.Valid (p.N k) a.κ (p.f r) (δ (p.N k) r)
      M D (p.ω k) (p.ν k) (p.E k) (p.B k) := Iff.rfl

/-- A known atlas supplies the geometry used by chart normalization and lifting. -/
theorem Atlas.KnownAt.geometry {p : Data} {k M D : ℕ} {a : Atlas p k} {r : ℝ}
    (ha : a.KnownAt M D r) : a.system.Geometry (p.N k) a.κ M D := by
  obtain ⟨_, hC, hsep, _, hchart, _⟩ := ha
  refine ⟨hC, hsep, fun b => ?_⟩
  obtain ⟨hdet, hcu, hQ, hthin, _, _, hA, _, hfmt, hfit, _, _⟩ := hchart b
  exact ⟨hdet, hcu, hQ, hthin, hA, fun i => (hfmt i).1,
    fun l hl => ⟨(hfit l hl).1, (hfit l hl).2.1⟩⟩

/-- The exact problem gives one uniform pair of bounds for its finite samples. -/
theorem Data.Valid.sampleProblem {p : Data} (hp : p.Valid) :
    ∃ M D : ℕ, ∀ k, Normalization.SampleProblem (p.N k) (p.K k) M D
      (p.W k) (p.ω k) (p.ν k) (p.E k) (p.P k) (p.B k) := by
  obtain ⟨M, D, h⟩ := hp.2.2.2.2.2.2.2.2.1
  refine ⟨M, D, fun k => ?_⟩
  obtain ⟨hc, hω, hsum, hγ, hmass⟩ := h k
  refine ⟨hc, hω, hsum, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro γ
    exact (hγ γ).1
  · intro γ
    exact (hγ γ).2.1
  · intro γ
    exact (hγ γ).2.2.1
  · intro γ
    exact (hγ γ).2.2.2.1
  · intro γ
    exact (hγ γ).2.2.2.2.1
  · intro γ
    exact (hγ γ).2.2.2.2.2.1
  · intro γ
    exact (hγ γ).2.2.2.2.2.2.1
  · intro γ
    exact (hγ γ).2.2.2.2.2.2.2.1
  · intro γ
    exact (hγ γ).2.2.2.2.2.2.2.2.1
  · intro γ
    exact (hγ γ).2.2.2.2.2.2.2.2.2.1
  · intro γ
    exact (hγ γ).2.2.2.2.2.2.2.2.2.2.1
  · intro γ
    exact (hγ γ).2.2.2.2.2.2.2.2.2.2.2.1
  · intro γ
    exact (hγ γ).2.2.2.2.2.2.2.2.2.2.2.2
  · simpa only [Measure.restrict_apply_univ] using hmass

end Submission.Obl.k4_remainder_pure_profile_normalization
