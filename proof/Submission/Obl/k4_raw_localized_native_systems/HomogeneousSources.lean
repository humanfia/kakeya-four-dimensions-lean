import Submission.Obl.k4_raw_localized_native_systems.PrefixSources
import Submission.Obl.k4_finite_width_path_realization.WidthBridge
import Submission.Obl.k4_finite_forest_width_selection
import Submission.Obl.k4_true_forest_own_depth_preparation.IncidenceBudget

/-
Adapted from this LOT tree, o197, session x0690, `HomogeneousSources.lean` (commit
f7206748), renamed into this obligation's namespace.
-/

namespace Submission.Obl.k4_raw_localized_native_systems

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- The accepted finite-width forest package uses the same frozen data in a
separate record. This adapter changes no field. -/
def pathData (p : Data) : k4_finite_width_path_realization.Data :=
  ⟨p.N, p.K, p.L, p.d, p.S, p.η, p.W, p.ω, p.ν, p.E, p.P, p.B, p.f, p.g, p.G⟩

theorem pathData_valid {p : Data} (hp : Valid p) : (pathData p).Valid := hp

def pathForest {p : Data} {k : ℕ} (a : k4_raw_critical_segment_forests.Forest p k)
    (width : Fin a.C → ℝ)
    (lst : ℕ → Fin (p.W k) → Observation → Finset (Fin a.C)) :
    k4_finite_width_path_realization.Forest (pathData p) k :=
  ⟨a.κ, a.T, a.C, a.lev, a.par, a.γ, a.j, a.c, a.u, a.Q, a.R, a.A, a.F, width, lst⟩

def fromPathForest {p : Data} {k : ℕ}
    (a : k4_finite_width_path_realization.Forest (pathData p) k) :
    k4_raw_critical_segment_forests.Forest p k :=
  ⟨a.κ, a.T, a.C, a.lev, a.par, a.γ, a.j, a.c, a.u, a.Q, a.R, a.A, a.F⟩

/-- The child budget is a consequence of genuine event nesting and disjoint
assignments; it uses the unchanged original incidence masses. -/
theorem source_budget {p : Data} (hp : Valid p) {k M D m : ℕ} {r : ℕ → ℝ}
    (a : k4_raw_critical_segment_forests.Forest p k) (ha : a.Core M D m r)
    (width : Fin a.C → ℝ)
    (lst : ℕ → Fin (p.W k) → Observation → Finset (Fin a.C)) :
    (pathForest a width lst).Budget := by
  obtain ⟨Mb, Db, hbase⟩ := hp.2.2.2.2.2.2.2.2.1
  have hc (b) := (ha.2.2.2.2.2 b).2.2.1
  have hFm (b) : MeasurableSet (a.F b) := (hc b).2.2.2.2.2.2.2.1
  have hsel (b) (z) (hz : z ∈ a.F b) : z.1 ∈ a.A b ∧
      z.2 ∈ Set.Icc ((a.j b : ℝ) / (2 : ℝ) ^ a.T (a.lev b))
        (((a.j b : ℝ) + 1) / (2 : ℝ) ^ a.T (a.lev b)) := by
    have h := (hc b).2.2.2.2.2.2.2.2.2.2.1 z hz
    exact ⟨h.2.1, h.2.2.1⟩
  constructor
  · intro b
    haveI : IsProbabilityMeasure (p.ν k (a.γ b)) := ((hbase k).2.2.2.1 (a.γ b)).1
    have hE := ((hbase k).2.2.2.1 (a.γ b)).2.2.2.2.2.2.2.2.1
    have hsub : a.F b ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 := by
      intro z hz
      exact hE ((hc b).2.2.2.2.2.2.2.2.2.2.1 z hz).1
    have hmass : ((p.ν k (a.γ b)).prod volume) (a.F b) ≤ 1 := by
      apply (measure_mono hsub).trans_eq
      rw [Measure.prod_prod, Real.volume_Icc]
      simp
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top ENNReal.one_ne_top hmass)
  · exact k4_true_forest_own_depth_preparation.forest_child_budget
      (p.ν k) (fun γ => ENNReal.ofReal (p.ω k γ)) a.T a.lev a.par a.γ a.j a.A a.F hFm
      ha.2.2.2.2.1 hsel (fun b hb => by
        have h := (ha.2.2.2.2.2 b).2.2.2 hb
        exact ⟨h.1, h.2.1, h.2.2.2.1⟩)

/-- Common width bands are selected with accepted o193 and its exact finite
forest adapter. Both original witness geometry and whole assignments survive. -/
theorem select_source_widths (m M : ℕ) (ε : ℝ) (hm : 0 < m) (hε : 0 < ε) :
    ∃ B : ℕ, 0 < B ∧ ∀ {p : Data}, Valid p → ∀ {k M' D : ℕ}
      (a : k4_raw_critical_segment_forests.Forest p k)
      (width : Fin a.C → ℝ)
      (lst : ℕ → Fin (p.W k) → Observation → Finset (Fin a.C))
      (r : ℕ → ℝ) (w q : ℝ), 0 ≤ q → a.Core M' D m r → a.Prepared r lst →
      (∀ z, |width z| ≤ (M : ℝ) ∧
        p.N k ^ (-width z) = |Matrix.det (a.Q z)| * (4 : ℝ) ^ a.T (a.lev z) ∧
        (a.lev z = 0 → w * r 0 - q ≤ width z) ∧
        (0 < a.lev z → width (a.par z) +
          w * (r (a.lev z) - r (a.lev (a.par z))) - q ≤ width z)) →
      ∃ (b : k4_raw_critical_segment_forests.Forest p k)
        (vwidth : Fin b.C → ℝ) (nw : ℕ → ℝ),
        b.κ = (B : ℝ) * a.κ ∧ b.T = a.T ∧ b.Core M' D m r ∧
        b.Prepared r (sourceLists b r) ∧
        (∀ i γ z, MeasurableSet {o | z ∈ sourceLists b r i γ o}) ∧
        (∀ z, p.N k ^ (-vwidth z) = |Matrix.det (b.Q z)| * (4 : ℝ) ^ b.T (b.lev z)) ∧
        (∀ z, |vwidth z - nw (b.lev z)| ≤ ε) ∧
        (∀ i, i < m → w * r i - (m : ℝ) * (q + 2 * ε) ≤ nw i ∧
          nw i + w * (r (m - 1) - r i) - (m : ℝ) * (q + 2 * ε) ≤ nw (m - 1)) := by
  obtain ⟨B, hB, hselect⟩ := k4_finite_width_path_realization.select_forest_widths
    Submission.k4_finite_forest_width_selection m M ε hm hε
  refine ⟨B, hB, fun {p} hp {k M' D} a width lst r w q hq ha hprep hwidth => ?_⟩
  obtain ⟨b, nw, hκ, hT, hcore, hprepared, hexact, hbin, hlower⟩ :=
    hselect (pathData_valid hp) (pathForest a width lst) r w q hq ha hprep
      (source_budget hp a ha width lst) hwidth
  have hcore' : (fromPathForest b).Core M' D m r := hcore
  have hprepared' : (fromPathForest b).Prepared r b.lst := hprepared
  exact ⟨fromPathForest b, b.width, nw, hκ, hT, hcore',
    sourceLists_prepared hprepared',
    fun i γ z => sourceLists_measurable hcore' i γ z, hexact, hbin, hlower⟩

end
end Submission.Obl.k4_raw_localized_native_systems
