-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/SeparatedGridTargets.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/- Adapted from this LOT tree, o285, session x1022, commit 3118a01b648b6fe31c1ad302109f3ffc3507ef6f,
Submission/Obl/k4_original_interpolated_field_source/Cart/SeparatedGridTargets.lean.
This is the signal-independent interpolation kernel, not the refuted o285 theorem.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, obligation o106 (k4_isotropic_path_improvement), session x0352,
-- branch x0352 at commit 1e57792e, file Submission/Obl/k4_isotropic_path_improvement/SeparatedGridTargets.lean;
-- only the namespace and module paths were renamed into o285's Cart namespace.
-- Existing source attributions of that file are preserved below.

import Submission.Obl.k4_physical_row_packet_potential.Cartesian.OriginalGridTargets
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.CartesianAnchorSeparation

/-!
Separated Cartesian anchors with actual heavy original-law vertices and
an original-mass floor for the target family. All collision probabilities
are derived from the finite real grid itself.
-/

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

open MeasureTheory Set Cartesian

noncomputable section

/-- The complete finite Cartesian sampling step for interpolation: actual
separated anchors, all mixed vertices heavy in the original law, and a
quantitative ORIGINAL target mass. The atom-size term is explicit. -/
theorem original_separated_grid_targets
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Finset ℝ) [Nonempty S]
    (code : Ω → S × S × S) (hcode : Measurable code)
    (a U δ ξ ρ : ℝ) (ha : 0 < a) (hU : 0 < U) (hδ : 0 ≤ δ)
    (hξ : 0 < ξ) (hρ : 0 < ρ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ξ ≤ dist x y)
    (hcap : ∀ i : S × S × S, μ.real {x | code x = i} ≤ U)
    (hbudget : δ * U * (S.card : ℝ) ^ 3 + (S.card : ℝ) ^ 3 * a ≤ μ.real univ)
    (k : ℕ)
    (hgap : 3 * (k : ℝ) ^ 2 * ((2 * ρ / ξ + 1) / (S.card : ℝ)) < δ ^ ((k + 1) ^ 3)) :
    ∃ (xs ys zs : Fin k → S) (G : Finset (S × S × S)),
      anchorsSeparated (fun x : S => (x : ℝ)) ρ (xs, ys, zs) ∧
      (∀ g ∈ G, ∀ i j l : Fin (k + 1),
        a ≤ μ.real {x | code x =
          ((Fin.snoc xs g.1 : Fin (k + 1) → S) i,
           (Fin.snoc ys g.2.1 : Fin (k + 1) → S) j,
           (Fin.snoc zs g.2.2 : Fin (k + 1) → S) l)}) ∧
      (δ ^ ((k + 1) ^ 3) - 3 * (k : ℝ) ^ 2 * ((2 * ρ / ξ + 1) / (S.card : ℝ))) / 2 *
        a * (S.card : ℝ) ^ 3 ≤ μ.real {x | code x ∈ G} := by
  have hcard : (Fintype.card S : ℝ) * Fintype.card S * Fintype.card S = (S.card : ℝ) ^ 3 := by
    rw [Fintype.card_coe]
    ring
  have hbudget' : δ * U * ((Fintype.card S : ℝ) * Fintype.card S * Fintype.card S) +
      ((Fintype.card S : ℝ) * Fintype.card S * Fintype.card S) * a ≤ μ.real univ := by
    rwa [hcard]
  have h := original_grid_complete_targets μ code hcode a U δ
    (3 * (k : ℝ) ^ 2 * ((2 * ρ / ξ + 1) / (S.card : ℝ))) ha hU hδ hcap hbudget'
    k (fun t => anchorsSeparated (fun x : S => (x : ℝ)) ρ t) hgap
    (uniform_grid_bad_anchor_expectation S k ξ ρ hξ hρ.le hsep)
  simpa only [hcard] using h

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
