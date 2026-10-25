-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.NonStickyStmt.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.NonStickyAssembly
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.Branches
-- Copied from session x0318 (o070 branch, commit 2c4a35f, file NonStickyStmt.lean), namespace renamed.

/-!
# x0305's `NonStickyBranchStmt`, proved

The statement is x0305's (o038 branch x0305, `Branches.lean`, copied as `X305/Branches.lean`);
the proof unpacks `Prepared` and applies `nonsticky_branch`.
-/

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

/-- **The non-sticky branch**, exactly as stated by x0305. -/
theorem nonStickyBranchStmt_holds : WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.NonStickyBranchStmt := by
  intro ζ₁ ζ₂ ζ₃ ω hζ₃ h32 h21 hω Nmax Cp
  obtain ⟨ζF, hζF, δ₁, hδ₁, h⟩ := nonsticky_branch hζ₃ h32 h21 hω Cp
  refine ⟨ζF, hζF, δ₁, hδ₁, ?_⟩
  intro δ hδ hδδ₁ L top _ hLlow hLup _ htop m x v S a hm hprep i₀ j₂ hij hj₂ hprof hgap hsc
  obtain ⟨hv, hT, hsep, hcan, hanti, hS, hcls, hpop, hFG⟩ := hprep
  exact h δ hδ hδδ₁ L hLlow hLup top htop m x v S hm hS (fun i _ => hv i) (fun i _ => hT i)
    (fun i _ j _ hij => hsep i j hij) (fun i _ => hcan i) (fun i _ j _ => hanti i j) a hcls hpop
    hFG i₀ j₂ hij hj₂ hprof hgap hsc

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
