/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/OriginalSamples.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.FinitePaths

/-!
An actual finite path retains a strictly increasing original-sample map.
The map is obtained from the literal refinement witnesses, not from a
comparison between limiting resolutions.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

open Filter
open scoped Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- Every actual normalization retains an exact original resolution
identity along a strictly increasing subsequence. -/
theorem refinement_original_resolution (p q : Code) (r b h : ℝ)
    (href : Refinement p q r b h) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, N q k = N p (φ k) := by
  rcases href with ⟨φ, ε, B, T, γ, j, A, C, u, v, J, P, Λ, θ,
    hφ, hεpos, hεlim, hB, hcharts, hgeometry, hweights⟩
  exact ⟨φ, hφ, fun k => (hcharts k).1⟩

namespace GridPath

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ}

/-- The final exact sequence is still sampled on the original exact
sequence. The finitely many nested subsequences compose strictly. -/
theorem original_resolution (path : GridPath ctx source start targets)
    (i : ℕ) (hi : path.AllLayers i) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ k, N (path.finalFamily.problem i) k = N (source.problem i) (φ k) := by
  induction path with
  | nil source start => exact ⟨id, strictMono_id, fun _ => rfl⟩
  | cons r rs hstart hr node tail ih =>
    obtain ⟨ψ, hψ, hψN⟩ := ih hi.2
    obtain ⟨φ, hφ, hφN⟩ := refinement_original_resolution _ _ _ _ _ hi.1.refinement
    exact ⟨φ ∘ ψ, hφ.comp hψ, fun k => (hψN k).trans (hφN (ψ k))⟩

/-- Original eventual guards remain eventual on the actual final path
sequence, after its composed original-sample map has been fixed. -/
theorem exists_original_guard_pullback (path : GridPath ctx source start targets)
    (i : ℕ) (hi : path.AllLayers i) (guard : ℕ → Prop)
    (hguard : ∀ᶠ k in atTop, guard k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ k, N (path.finalFamily.problem i) k = N (source.problem i) (φ k)) ∧
      ∀ᶠ k in atTop, guard (φ k) := by
  obtain ⟨φ, hφ, hN⟩ := path.original_resolution i hi
  exact ⟨φ, hφ, hN, hφ.tendsto_atTop.eventually hguard⟩

end GridPath

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
