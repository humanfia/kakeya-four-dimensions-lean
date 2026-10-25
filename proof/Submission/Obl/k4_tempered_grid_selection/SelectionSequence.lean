import Submission.Obl.k4_tempered_grid_selection.Interface
import Submission.Obl.k4_tempered_grid_selection.SelectionFinite
import Submission.Lib.K4ModelReduction.Diagonal

namespace Submission.Obl.k4_tempered_grid_selection

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- Simultaneous concentration of countably many bounded label functions in
vanishing intervals, at a subpower loss of mass. -/
theorem countable_type_selection {Ω Λ : Type*} [MeasurableSpace Ω]
    (N : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (μ : ℕ → Measure Ω) (label : ℕ → Ω → Λ)
    (f : ℕ → ℕ → Λ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k j z, |f k j z| ≤ C) :
    ∃ (B : ℕ → ℕ) (T : ℕ → Set Λ) (a : ℕ → ℕ → ℝ) (δ : ℕ → ℝ),
      (∀ k, 0 < B k) ∧ Subpower N (fun k => (B k : ℝ)) ∧
      (∀ k j, |a k j| ≤ C) ∧
      (∀ k, 0 < δ k) ∧ Tendsto δ atTop (𝓝 0) ∧
      (∀ j, ∀ᶠ k in atTop, ∀ z ∈ T k, |f k j z - a k j| < δ k) ∧
      (∀ k, μ k univ ≤ (B k : ℝ≥0∞) * μ k (label k ⁻¹' T k)) := by
  classical
  have hfinite (m : ℕ) := finite_type_selection C (1 / ((m : ℝ) + 1)) hC
    (by positivity) m
  choose B hB hselect using hfinite
  let P (m k : ℕ) : Prop := (B m : ℝ) ≤ N k ^ (1 / ((m : ℝ) + 1))
  have hP (m : ℕ) : ∀ᶠ k in atTop, P m k := by
    have ht : Tendsto (fun k => N k ^ (1 / ((m : ℝ) + 1))) atTop atTop :=
      (tendsto_rpow_atTop (by positivity : 0 < 1 / ((m : ℝ) + 1))).comp hNt
    exact ht.eventually (eventually_ge_atTop (B m : ℝ))
  obtain ⟨l, _, hlt, _, hlP⟩ :=
    Submission.Lib.K4ModelReduction.exists_slow_diagonal P hP
  choose T a ha hfit hmass using fun k =>
    hselect (l k) Ω Λ (μ k) (label k) (f k) (hf k)
  let δ : ℕ → ℝ := fun k => 1 / ((l k : ℝ) + 1)
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat.comp hlt
  refine ⟨(fun k => B (l k)), T, a, δ, (fun k => hB _), ?_, ha,
    (fun k => by dsimp [δ]; positivity), hδ, ?_, hmass⟩
  · constructor
    · intro k
      change (1 : ℝ) ≤ (B (l k) : ℝ)
      exact_mod_cast (Nat.succ_le_iff.mpr (hB (l k)))
    · intro ε hε
      have hδε : ∀ᶠ k in atTop, δ k < ε := hδ.eventually (gt_mem_nhds hε)
      filter_upwards [hlP, hδε] with k hk hδε
      exact (hk (l k) le_rfl).trans
        (Real.rpow_le_rpow_of_exponent_le (by linarith [hN k]) hδε.le)
  · intro j
    filter_upwards [hlt.eventually (eventually_ge_atTop (j + 1))] with k hk z hz
    exact hfit k z hz j (by omega)

end Submission.Obl.k4_tempered_grid_selection
