-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Cartesian.QualWitness, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Cartesian/QualWitness.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o285, session x1022, commit 3118a01b648b6fe31c1ad302109f3ffc3507ef6f,
Submission/Obl/k4_original_interpolated_field_source/Cart/QualWitness.lean.
This is the signal-independent interpolation kernel, not the refuted o285 theorem.
All earlier source attributions below are retained. -/
import Mathlib
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Cartesian.LiftFrame

/-!
# Qualified witnesses in normalized block time

A qualified witness `w = (l, t_w)` of a state carries a row-valued polynomial
`P` of degree at most `M`, in the normalized block time `s = (t - t0) / h`,
which fits the state row `Gs` at the witness itself and at the states that its
own line `l` visits during a measurable set of normalized times of measure at
least `dur`, all of them reference-labelled.  This is paper `a05:qualification`
(tex-06 l. 464-480) after the time normalization of the old packet; the
Cartesian interpolation consumes exactly this.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Cartesian

open MeasureTheory Set

noncomputable section

/-- A qualified witness in normalized block time `s = (t - t0) / h`. -/
def QualWitness {Λ σ : Type*} (Eref : Set (Λ × ℝ)) (st : Λ × ℝ → σ) (Gs : σ → Fin 3 → ℝ)
    (t0 h : ℝ) (M : ℕ) (Kq err dur : ℝ) (w : Λ × ℝ) : Prop :=
  ∃ P : Fin 3 → Polynomial ℝ, (∀ j, (P j).natDegree ≤ M) ∧ (∀ j k, |(P j).coeff k| ≤ Kq) ∧
    (∀ j, |Gs (st w) j - (P j).eval ((w.2 - t0) / h)| ≤ err) ∧
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc 0 1 ∧ ENNReal.ofReal dur ≤ volume E ∧
      ∀ s ∈ E, (w.1, t0 + h * s) ∈ Eref ∧
        ∀ j, |Gs (st (w.1, t0 + h * s)) j - (P j).eval s| ≤ err

/-- The point of the `axis`-fiber with grid key `key` at normalized time `t`:
the two key coordinates, and on the axis the time minus their sum. -/
def fiberPoint (axis : Fin 3) (key : ℝ × ℝ) (t : ℝ) : Fin 3 → ℝ :=
  ![![t - key.1 - key.2, key.1, key.2],
    ![key.1, t - key.1 - key.2, key.2],
    ![key.1, key.2, t - key.1 - key.2]] axis

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Cartesian
