import Submission.Obl.k4_scalar_guarded_entropic_path.EntropicFromStages
import Submission.Obl.k4_scalar_guarded_entropic_path.StageAssembly
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.CriticalPaths

/-! Close the original critical-certificate and diagonal quantifiers
once the concrete finite-stage window construction is available. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path

open PathGeometry.PathNodes
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

/-- It suffices to construct stages for exponents at most one. The
output angular exponent can be capped at one without changing any
original problem, guard, prior, weight or common-law restriction. -/
theorem entropicPathConstruction_of_critical_stages
    (hstages : ∀ (ctx : CriticalContext) (source : MaximizingFamily ctx),
      source.length = 1 → Calculus → 0 < ctx.κ → ctx.κ ≤ 1 →
      0 < ctx.η → 0 < ctx.S₀ →
      ∀ (k : ℕ) (R δ : ℝ), 1 < R → 0 < δ → δ ≤ 1 →
        ∃ st : RawStage, st.Good ctx.dstar ctx.κ (min ctx.S₀ 1) k R δ) :
    EntropicPathConstruction := by
  apply entropicPathConstruction_of_stages
  intro _ hcalc hcritical
  obtain ⟨ctx, source, hS, hη, hκ, hκ1, hlength, hL, hD⟩ :=
    critical_has_maximizingFamily hcritical
  refine ⟨ctx.dstar, ctx.κ, min ctx.S₀ 1, ctx.star_nonneg, ctx.star_lt_one,
    hκ, hκ1, lt_min hS (by norm_num), min_le_right _ _, ?_⟩
  intro k R δ hR hδ
  obtain ⟨st, hst⟩ := hstages ctx source hlength hcalc hκ hκ1 hη hS k R
    (min δ 1) hR (lt_min hδ (by norm_num)) (min_le_right _ _)
  exact ⟨st, hst.mono_delta (min_le_left _ _)⟩

end

end Submission.Obl.k4_scalar_guarded_entropic_path
