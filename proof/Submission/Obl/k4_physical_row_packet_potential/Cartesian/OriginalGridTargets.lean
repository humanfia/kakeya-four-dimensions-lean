-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/OriginalGridTargets.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/- Adapted from this LOT tree, o285, session x1022, commit 3118a01b648b6fe31c1ad302109f3ffc3507ef6f,
Submission/Obl/k4_original_interpolated_field_source/Cart/OriginalGridTargets.lean.
This is the signal-independent interpolation kernel, not the refuted o285 theorem.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, obligation o106 (k4_isotropic_path_improvement), session x0352,
-- branch x0352 at commit 1e57792e, file Submission/Obl/k4_isotropic_path_improvement/OriginalGridTargets.lean;
-- only the namespace and module paths were renamed into o285's Cart namespace.
-- Existing source attributions of that file are preserved below.

import Submission.Obl.k4_physical_row_packet_potential.Cartesian.GridMass
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.CartesianTargets

/-!
A complete-grid anchor/target family with a floor in the ORIGINAL measure.
This connects finite Cartesian interpolation to actual prepared incidences.
-/

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

open MeasureTheory Set
open Cartesian

noncomputable section

open Classical in
/-- Original cell caps, an affordable light-cell threshold and a small
bad-anchor probability give dense complete targets with original mass.
Every mixed interpolation vertex is an actual heavy original code cell. -/
theorem original_grid_complete_targets
    {Ω X Y Z : Type*} [MeasurableSpace Ω]
    [Fintype X] [Fintype Y] [Fintype Z] [Nonempty X] [Nonempty Y] [Nonempty Z]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y] [MeasurableSingletonClass Z]
    (μ : Measure Ω) [IsFiniteMeasure μ] (code : Ω → X × Y × Z) (hcode : Measurable code)
    (a U δ β : ℝ) (ha : 0 < a) (hU : 0 < U) (hδ : 0 ≤ δ)
    (hcap : ∀ i : X × Y × Z, μ.real {x | code x = i} ≤ U)
    (hbudget : δ * U * ((Fintype.card X : ℝ) * Fintype.card Y * Fintype.card Z) +
      ((Fintype.card X : ℝ) * Fintype.card Y * Fintype.card Z) * a ≤ μ.real univ)
    (k : ℕ) (good : (Fin k → X) × (Fin k → Y) × (Fin k → Z) → Prop)
    (hgap : β < δ ^ ((k + 1) ^ 3))
    (hbad : mean (jointWeight (tupleWeight (uniformWeight X))
      (jointWeight (tupleWeight (uniformWeight Y)) (tupleWeight (uniformWeight Z))))
        (fun t => if good t then (0 : ℝ) else 1) ≤ β) :
    ∃ (xs : Fin k → X) (ys : Fin k → Y) (zs : Fin k → Z) (G : Finset (X × Y × Z)),
      good (xs, ys, zs) ∧
      (∀ g ∈ G, ∀ i j l : Fin (k + 1),
        a ≤ μ.real {x | code x =
          ((Fin.snoc xs g.1 : Fin (k + 1) → X) i,
           (Fin.snoc ys g.2.1 : Fin (k + 1) → Y) j,
           (Fin.snoc zs g.2.2 : Fin (k + 1) → Z) l)}) ∧
      (δ ^ ((k + 1) ^ 3) - β) / 2 * a *
        ((Fintype.card X : ℝ) * Fintype.card Y * Fintype.card Z) ≤
          μ.real {x | code x ∈ G} := by
  classical
  let n : ℝ := (Fintype.card X : ℝ) * Fintype.card Y * Fintype.card Z
  have hn : 0 < n := by dsimp [n]; positivity
  have hcard : (Fintype.card (X × Y × Z) : ℝ) = n := by simp [n]; ring
  obtain ⟨F, hF, -, hcount, hmass⟩ := prepare_original_grid_cells μ code hcode a U ha.le hU hcap
  have hcountF : δ * n ≤ (F.card : ℝ) := by
    apply le_trans ?_ hcount
    rw [hcard]
    apply (le_div_iff₀ hU).mpr
    nlinarith [hbudget]
  let R : X → Y → Z → Prop := gridTableMember F
  have hfilter : Finset.univ.filter (fun g : X × Y × Z => R g.1 g.2.1 g.2.2) = F := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, R, gridTableMember, Prod.eta]
  have hdensity : δ ≤ mean (uniformWeight X) (fun x => mean (uniformWeight Y)
      (fun y => mean (uniformWeight Z) (fun z => if R x y z then (1 : ℝ) else 0))) := by
    rw [uniform_triple_density R, hfilter]
    exact (le_div_iff₀ hn).mpr hcountF
  obtain ⟨xs, ys, zs, hgood, htargets⟩ := exists_good_anchors_dense_complete_targets
    (uniformWeight X) (uniformWeight Y) (uniformWeight Z)
    (by intro x; dsimp [uniformWeight]; positivity)
    (by intro y; dsimp [uniformWeight]; positivity)
    (by intro z; dsimp [uniformWeight]; positivity)
    sum_uniformWeight sum_uniformWeight sum_uniformWeight R k δ β hδ hdensity good hgap hbad
  let G := Finset.univ.filter fun g : X × Y × Z => completeTarget R xs ys zs g.1 g.2.1 g.2.2
  have hGF : G ⊆ F := by
    intro g hg
    have ht := (Finset.mem_filter.mp hg).2 (Fin.last k) (Fin.last k) (Fin.last k)
    simpa only [Fin.snoc_last, R, gridTableMember, Prod.eta] using ht
  have hGcount : (δ ^ ((k + 1) ^ 3) - β) / 2 * n ≤ (G.card : ℝ) := by
    rw [uniform_triple_density] at htargets
    exact (le_div_iff₀ hn).mp htargets
  refine ⟨xs, ys, zs, G, hgood, ?_, ?_⟩
  · intro g hg i j l
    exact (hF _).mp ((Finset.mem_filter.mp hg).2 i j l)
  · calc
      _ = a * ((δ ^ ((k + 1) ^ 3) - β) / 2 * n) := by ring
      _ ≤ a * (G.card : ℝ) := mul_le_mul_of_nonneg_left hGcount ha.le
      _ ≤ μ.real {x | code x ∈ G} := hmass G hGF

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
