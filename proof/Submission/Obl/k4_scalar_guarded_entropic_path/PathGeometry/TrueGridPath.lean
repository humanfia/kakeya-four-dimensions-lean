/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/TrueGridPath.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrueCriticalStep
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.CriticalPaths
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.MeasuredWitnesses

/-! Finite critical paths retaining the actual true atlas at every
normalization. Forgetting these certificates gives the existing GridPath,
so its original-law, sample and frame APIs apply to the identical witnesses. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

open Set Filter
open scoped Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

inductive TrueGridPath (ctx : CriticalContext) :
    (source : MaximizingFamily ctx) → ℝ → List ℝ → Type where
  | nil (source : MaximizingFamily ctx) (start : ℝ) : TrueGridPath ctx source start []
  | cons {source : MaximizingFamily ctx} {start : ℝ} (r : ℝ) (rs : List ℝ)
      (hstart : start < r) (hr : r < 1)
      (node : TrueCriticalStep ctx source ((r - start) / (1 - start)))
      (tail : TrueGridPath ctx node.remaining r rs) : TrueGridPath ctx source start (r :: rs)

/-- Every finite ordered interior grid has a path through actual chosen
true source atlases, with all limits in the original exponent units. -/
theorem nonempty_trueGridPath (hcalc : Calculus)
    (ctx : CriticalContext) (source : MaximizingFamily ctx)
    (start : ℝ) (targets : List ℝ) (hstart : start < 1)
    (hordered : targets.Pairwise (· < ·))
    (htargets : ∀ r ∈ targets, start < r ∧ r < 1) :
    Nonempty (TrueGridPath ctx source start targets) := by
  induction targets generalizing source start with
  | nil => exact ⟨.nil source start⟩
  | cons r rs ih =>
    have hr := htargets r (by simp)
    have hθ₀ : 0 < (r - start) / (1 - start) :=
      div_pos (sub_pos.mpr hr.1) (sub_pos.mpr hstart)
    have hθ₁ : (r - start) / (1 - start) < 1 := by
      apply (div_lt_one (sub_pos.mpr hstart)).2
      linarith [hr.2]
    obtain ⟨node⟩ := nonempty_trueCriticalStep hcalc ctx source _ hθ₀ hθ₁
    have hpairs := List.pairwise_cons.mp hordered
    have htail : ∀ s ∈ rs, r < s ∧ s < 1 := by
      intro s hs
      exact ⟨hpairs.1 s hs, (htargets s (by simp [hs])).2⟩
    obtain ⟨tail⟩ := ih node.remaining r hr.2 hpairs.2 htail
    exact ⟨.cons r rs hr.1 hr.2 node tail⟩

namespace TrueGridPath

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ}

/-- The existing numerical path, on precisely the same intermediate codes. -/
def forget {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : TrueGridPath ctx source start targets) :
    GridPath ctx source start targets :=
  match path with
  | .nil source start => .nil source start
  | .cons r rs hstart hr node tail =>
      .cons r rs hstart hr node.toCriticalStep tail.forget

/-- All actual chosen-atlas normalizations at one common outer index. -/
def Certificates {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : TrueGridPath ctx source start targets)
    (i : ℕ) : Type :=
  match path with
  | .nil _ _ => PUnit
  | .cons _ _ _ _ node tail =>
      TrueNormalization (source.problem i) (node.remaining.problem i)
        (node.depth i) (node.depth i) (node.cost i) × tail.Certificates i

/-- All layers retain their true-atlas certificates on a single outer tail. -/
theorem eventually_certificates (path : TrueGridPath ctx source start targets) :
    ∀ᶠ i in atTop, Nonempty (path.Certificates i) := by
  induction path with
  | nil => exact Eventually.of_forall fun _ => ⟨PUnit.unit⟩
  | cons r rs hstart hr node tail ih =>
    filter_upwards [node.normalizations, ih] with i hn ht
    obtain ⟨cert⟩ := hn
    obtain ⟨rest⟩ := ht
    exact ⟨cert, rest⟩

/-- Choose the SAME retained literal witnesses for all existing original
frames, measured chains and common path reference laws. -/
def toLayerWitnesses {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : TrueGridPath ctx source start targets)
    (i : ℕ) : path.Certificates i → path.forget.LayerWitnesses i :=
  match path with
  | .nil _ _ => fun _ => PUnit.unit
  | .cons _ _ _ _ _ tail => fun certs =>
      (certs.1.witness, tail.toLayerWitnesses i certs.2)

/-- After at least one true normalization, the final exact problem has
absolute depth-zero profile zero, not only a relative profile identity. -/
theorem eventually_final_profile_zero (path : TrueGridPath ctx source start targets)
    (hadded : targets ≠ []) :
    ∀ᶠ i in atTop, f (path.forget.finalFamily.problem i) 0 = 0 := by
  induction path with
  | nil => exact (hadded rfl).elim
  | cons r rs hstart hr node tail ih =>
    by_cases hnil : rs = []
    · subst rs
      cases tail
      filter_upwards [node.normalizations, node.layers] with i hn hl
      obtain ⟨cert⟩ := hn
      exact cert.profile_zero (node.remaining.angular i).1 hl.remaining_length
        (node.depth_bounds i).1
    · exact ih hnil

end TrueGridPath

/-- The accepted critical certificate produces a true-atlas path on
every finite prescribed interior grid. All original-unit numerical and
measure interfaces remain available through its forget map. -/
theorem critical_has_true_finite_paths (hcalc : Calculus) (hcritical : Critical) :
    ∃ (ctx : CriticalContext) (source : MaximizingFamily ctx),
      0 < ctx.S₀ ∧ 0 < ctx.η ∧ 0 < ctx.κ ∧ ctx.κ ≤ 1 ∧
      source.length = 1 ∧ (∀ i, L (source.problem i) = 1) ∧
      Tendsto ctx.D atTop (𝓝 ctx.dstar) ∧
      ∀ targets : List ℝ, targets.Pairwise (· < ·) →
        (∀ r ∈ targets, r ∈ Ioo (0 : ℝ) 1) →
        Nonempty (TrueGridPath ctx source 0 targets) := by
  obtain ⟨ctx, source, hS, hη, hκ, hκ₁, hlength, hL, hD⟩ :=
    critical_has_maximizingFamily hcritical
  refine ⟨ctx, source, hS, hη, hκ, hκ₁, hlength, hL, hD, ?_⟩
  intro targets hordered htargets
  exact nonempty_trueGridPath hcalc ctx source 0 targets (by norm_num) hordered htargets

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
