-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.Problem, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/Problem.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/Problem.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/Problem.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/Problem.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Preparation
import Submission.Obl.k4_dk4_smoothed_problem.Observation

/-! Original problem data and the finite lists of pure and angular exceptions. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators
open Submission.Obl.k4_native_grid_profile_extension.Profiles

structure ProblemData where
  N : ℕ → ℝ
  K : ℕ → ℝ
  L : ℝ
  d : ℝ
  S : ℝ
  η : ℝ
  W : ℕ → ℕ
  ω : (k : ℕ) → Fin (W k) → ℝ
  ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))
  E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)
  P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ
  B : (k : ℕ) → Fin (W k) → ℝ
  f : ℝ → ℝ
  g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal
  G : (k : ℕ) → Fin (W k) → ℝ →
    ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal

def ProblemData.Valid (d : ProblemData) : Prop :=
  prob d.N d.K d.L d.d d.S d.η d.W d.ω d.ν d.E d.P d.B d.f d.g d.G

noncomputable def ProblemData.μ (d : ProblemData) (k : ℕ) (w : Fin (d.W k)) :
    Measure ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  ((d.ν k w).prod volume).restrict (d.E k w)

noncomputable def ProblemData.angularObs (d : ProblemData) (u : ℝ)
    (k : ℕ) (w : Fin (d.W k)) (p : (ℕ × (Fin 6 → ℝ)) × ℝ) :
    (EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ) :=
  (obs (d.B k w) (δ (d.N k) d.L) p, fun j => ⌊v p.1 j / δ (d.N k) u⌋)

def ProblemData.pureBad (d : ProblemData) (r τ : ℝ) (k : ℕ) (w : Fin (d.W k)) :
    Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  {p | d.g k w r (obs (d.B k w) (δ (d.N k) r) p) < ENNReal.ofReal (d.N k ^ (-d.f r - τ)) ∨
    ENNReal.ofReal (d.N k ^ (-d.f r + τ)) < d.g k w r (obs (d.B k w) (δ (d.N k) r) p)}

def ProblemData.angularBad (d : ProblemData) (u τ : ℝ) (k : ℕ) (w : Fin (d.W k)) :
    Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  {p | ENNReal.ofReal (d.N k ^ (-d.f d.L - d.S * u + τ)) < d.G k w u (d.angularObs u k w p)}

theorem ProblemData.Valid.tendsto {d : ProblemData} (h : d.Valid) :
    Tendsto d.N atTop atTop := h.2.1

/-- The fixed global profile tolerance costs twice that tolerance in a
parent-to-descendant comparison. -/
theorem linear_profile_difference_bound {f : ℝ → ℝ} {d₁ δ₀ L r r' : ℝ}
    (hfit : ∀ t : ℝ, 0 ≤ t → t ≤ L → |f t - f 0 - d₁ * t| ≤ δ₀ * L)
    (hr : 0 ≤ r) (hrL : r ≤ L) (hr' : 0 ≤ r') (hr'L : r' ≤ L) :
    |f r' - f r - d₁ * (r' - r)| ≤ 2 * δ₀ * L := by
  calc
    _ = |(f r' - f 0 - d₁ * r') - (f r - f 0 - d₁ * r)| := by congr 1; ring
    _ ≤ |f r' - f 0 - d₁ * r'| + |f r - f 0 - d₁ * r| := abs_sub _ _
    _ ≤ δ₀ * L + δ₀ * L := add_le_add (hfit r' hr' hr'L) (hfit r hr hrL)
    _ = _ := by ring

theorem ProblemData.Valid.weights {d : ProblemData} (h : d.Valid) (k : ℕ) :
    (∀ w, 0 ≤ d.ω k w) ∧ (∑ w, d.ω k w) = 1 ∧
      ∀ w, IsProbabilityMeasure (d.ν k w) := by
  rcases h with ⟨_, _, _, _, _, _, _, _, hformat, _⟩
  obtain ⟨M, D, hformat⟩ := hformat
  have hk := hformat k
  exact ⟨hk.2.1, hk.2.2.1, fun w => (hk.2.2.2.1 w).1⟩

theorem ProblemData.Valid.native_bounds {d : ProblemData} (h : d.Valid)
    (k : ℕ) (w : Fin (d.W k)) :
    ∀ᵐ l ∂d.ν k w, ∀ t ∈ Icc (0 : ℝ) 1, ‖y l t‖ + ‖v l‖ ≤ d.K k := by
  rcases h with ⟨_, _, _, _, _, _, _, _, hformat, _⟩
  obtain ⟨M, D, hformat⟩ := hformat
  rcases (hformat k).2.2.2.1 w with ⟨_, _, _, _, _, _, _, _, _, _, _, hnative, _⟩
  exact hnative.mono fun l hl t ht => (hl t ht).1

theorem ProblemData.Valid.pureBad_powerSmall {d : ProblemData} (h : d.Valid)
    (r τ : ℝ) (hr : 0 ≤ r) (hrL : r ≤ d.L) (hτ : 0 < τ) :
    IsPowerSmall d.N (fun k => ∑ w, ENNReal.ofReal (d.ω k w) * d.μ k w (d.pureBad r τ k w)) := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hpure, _⟩
  exact hpure r τ hr hrL hτ

theorem ProblemData.Valid.angularBad_powerSmall {d : ProblemData} (h : d.Valid)
    (u τ : ℝ) (hu : 0 < u) (huL : u ≤ d.η * d.L) (hτ : 0 < τ) :
    IsPowerSmall d.N (fun k => ∑ w, ENNReal.ofReal (d.ω k w) * d.μ k w (d.angularBad u τ k w)) := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hangular⟩
  exact hangular u τ hu huL hτ

theorem ProblemData.Valid.measurableSet_pureBad {d : ProblemData} (h : d.Valid)
    (r τ : ℝ) (hr : 0 ≤ r) (hrL : r ≤ d.L) (k : ℕ) (w : Fin (d.W k)) :
    MeasurableSet (d.pureBad r τ k w) := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, hg, _⟩
  have hobs : Measurable (obs (d.B k w) (δ (d.N k) r)) :=
    Submission.Obl.k4_dk4_smoothed_problem.Framework.measurable_pureObservation _ _
  have hg := (hg k w r hr hrL).1.comp hobs
  exact (measurableSet_lt hg measurable_const).union (measurableSet_lt measurable_const hg)

theorem ProblemData.Valid.measurableSet_angularBad {d : ProblemData} (h : d.Valid)
    (u τ : ℝ) (hu : 0 < u) (huL : u ≤ d.η * d.L) (k : ℕ) (w : Fin (d.W k)) :
    MeasurableSet (d.angularBad u τ k w) := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, hG, _⟩
  have hobs : Measurable (d.angularObs u k w) :=
    Submission.Obl.k4_dk4_smoothed_problem.Framework.measurable_angularObservation _ _ _
  exact measurableSet_lt measurable_const ((hG k w u hu huL).1.comp hobs)

theorem ProblemData.μ_apply_eq {d : ProblemData} (k : ℕ) (w : Fin (d.W k))
    {H : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} (hH : MeasurableSet H) (hsub : H ⊆ d.E k w) :
    d.μ k w H = ((d.ν k w).prod volume) H := by
  rw [μ, Measure.restrict_apply hH, inter_eq_left.mpr hsub]

def ProblemData.testBad {I J : Type*} (d : ProblemData) (r : I → ℝ) (u : J → ℝ)
    (τ : ℝ) (test : I ⊕ J) (k : ℕ) (w : Fin (d.W k)) :
    Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  Sum.elim (fun i => d.pureBad (r i) τ k w) (fun j => d.angularBad (u j) τ k w) test

def ProblemData.pruneTests {I J : Type*} (d : ProblemData) (r : I → ℝ) (u : J → ℝ)
    (τ : ℝ) (k : ℕ) (H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (w : Fin (d.W k)) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  H w \ ⋃ test, d.testBad r u τ test k w

/-- Simultaneous finite pure and angular preparation for every substantial
residual, in original coordinates and under the full original product laws. -/
theorem ProblemData.Valid.cleanup_tests {I J : Type*} [Fintype I] [Fintype J]
    {d : ProblemData} (h : d.Valid) (r : I → ℝ) (u : J → ℝ) (τ : ℝ) (hτ : 0 < τ)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ d.L) (hu : ∀ j, 0 < u j ∧ u j ≤ d.η * d.L) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ k in atTop, ∀ κ : ℝ, 1 ≤ κ → κ ≤ d.N k ^ σ →
      ∀ H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ),
      (∀ w, MeasurableSet (H w) ∧ H w ⊆ d.E k w) →
      ENNReal.ofReal (κ⁻¹ / 2) ≤
        ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (H w) →
      (∀ w, MeasurableSet (d.pruneTests r u τ k H w) ∧ d.pruneTests r u τ k H w ⊆ H w) ∧
      (∀ w p, p ∈ d.pruneTests r u τ k H w → ∀ i,
        ENNReal.ofReal (d.N k ^ (-d.f (r i) - τ)) ≤
          d.g k w (r i) (obs (d.B k w) (δ (d.N k) (r i)) p) ∧
        d.g k w (r i) (obs (d.B k w) (δ (d.N k) (r i)) p) ≤
          ENNReal.ofReal (d.N k ^ (-d.f (r i) + τ))) ∧
      (∀ w p, p ∈ d.pruneTests r u τ k H w → ∀ j,
        d.G k w (u j) (d.angularObs (u j) k w p) ≤
          ENNReal.ofReal (d.N k ^ (-d.f d.L - d.S * u j + τ))) ∧
      ENNReal.ofReal (κ⁻¹ / 4) ≤
        ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (d.pruneTests r u τ k H w) := by
  have hbad : ∀ test, IsPowerSmall d.N
      (fun k => ∑ w, ENNReal.ofReal (d.ω k w) * d.μ k w (d.testBad r u τ test k w)) := by
    intro test
    cases test with
    | inl i => exact h.pureBad_powerSmall (r i) τ (hr i).1 (hr i).2 hτ
    | inr j => exact h.angularBad_powerSmall (u j) τ (hu j).1 (hu j).2 hτ
  obtain ⟨σ, hσ, hcleanup⟩ := finite_exception_cleanup h.tendsto d.W d.μ
    (fun k w => ENNReal.ofReal (d.ω k w)) (d.testBad r u τ) hbad
  refine ⟨σ, hσ, hcleanup.mono ?_⟩
  intro k hk κ hκ hκN H hH hmass
  have hprune : ∀ w, MeasurableSet (d.pruneTests r u τ k H w) ∧
      d.pruneTests r u τ k H w ⊆ H w := by
    intro w
    refine ⟨(hH w).1.diff (MeasurableSet.iUnion fun test => ?_), sdiff_subset⟩
    cases test with
    | inl i => exact h.measurableSet_pureBad (r i) τ (hr i).1 (hr i).2 k w
    | inr j => exact h.measurableSet_angularBad (u j) τ (hu j).1 (hu j).2 k w
  have hselected : ENNReal.ofReal (κ⁻¹ / 2) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * d.μ k w (H w) := by
    convert hmass using 1
    apply Finset.sum_congr rfl
    intro w _
    rw [d.μ_apply_eq k w (hH w).1 (hH w).2]
  have hkeep := hk κ hκ hκN H hselected
  refine ⟨hprune, ?_, ?_, ?_⟩
  · intro w p hp i
    have hnot : p ∉ d.pureBad (r i) τ k w := by
      intro hbad
      exact hp.2 (mem_iUnion.mpr ⟨Sum.inl i, hbad⟩)
    exact ⟨le_of_not_gt (fun hlt => hnot (Or.inl hlt)),
      le_of_not_gt (fun hlt => hnot (Or.inr hlt))⟩
  · intro w p hp j
    apply le_of_not_gt
    intro hbad
    exact hp.2 (mem_iUnion.mpr ⟨Sum.inr j, hbad⟩)
  · convert hkeep using 1
    apply Finset.sum_congr rfl
    intro w _
    rw [← d.μ_apply_eq k w (hprune w).1 ((hprune w).2.trans (hH w).2)]
    rfl

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
