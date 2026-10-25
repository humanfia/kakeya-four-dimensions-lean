-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.GrainState.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.GrainStateDefs
import Submission.WZ.Obl.wz_broad_grains_initialization.GrainFamily

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open wz_clustered_cover_volume_gain (T bodyCount)
open wz_measurable_angular_selection (pd)

/-- The elementary grain data, together with retained broad shading, give
the exact initialization state at coarse scale one. -/
theorem UnitGrainFamily.to_state {δ h ω ζ c : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hh : 0 ≤ h) (hω : ω ≤ 1) {n : ℕ} {x v : Fin n → Space}
    {Y Z : Fin n → Set Space} (G : UnitGrainFamily δ h x v Z c)
    (hYm : ∀ i, MeasurableSet (Y i))
    (hball : ∀ i, T δ (x i) (v i) ⊆ Metric.ball (0 : Space) 1)
    (hZ : ∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i)
    (hmass : ENNReal.ofReal (δ ^ h) * ∑ i, volume (Y i) ≤ ∑ i, volume (Z i))
    (hbroad : ∀ (p u : Space) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ 1 →
      ({i | p ∈ Z i ∧ pd (v i) u ≤ r}.ncard : ℝ) ≤
        δ ^ (-h) * r ^ (ω * ζ / 100) * bodyCount Z p) :
    State ω ζ δ h 1 c n x v Y false := by
  classical
  obtain ⟨y, w, hC, hcarrier⟩ := unit_scale_cover_with_ball hδ hδ1 hh x v Y hYm hball
  have hCZ : Cover δ h n x v Y Finset.univ Z 1 1 y w (fun _ => 0) True :=
    ⟨fun i => ⟨(hZ i).1, (hZ i).2, by simp⟩, by simpa using hmass, hC.2.2⟩
  have hc : 0 ≤ c := hδ.le.trans G.lower_side
  obtain ⟨g, hg, hlocal⟩ := initial_local_grain_count hc (by norm_num : (0 : ℝ) ≤ 1) hc
    G.center G.frame
  refine ⟨Finset.univ, Z, 1, y, w, fun _ => 0, c, g, hCZ,
    Real.rpow_le_one hδ.le hδ1 (by linarith), hg, ?_, ?_, by simp⟩
  · intro k p u r hu hr hr1
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    simpa only [Finset.mem_univ, true_and, div_one, bodyCount, pd] using hbroad p u r hu hr hr1
  · refine ⟨G.L, G.center, G.frame, G.shading, fun _ => 0, G.multiplicity, ?_⟩
    simp only [one_mul]
    refine ⟨G.lower_side, le_rfl, le_rfl, G.upper_side, ?_, ?_, ?_, ?_, ?_, ?_, hc, ?_⟩
    · intro j
      refine ⟨G.measurable j, G.subset_cube j, (G.cube_in_ball j).trans (hcarrier 0), ?_⟩
      have hcoord (i : Fin 3) : |G.frame j (w 0) i| ≤ 1 := by
        have ht := wz_balanced_cluster_cover.abs_apply_le_norm (G.frame j (w 0)) i
        simpa only [(G.frame j).norm_map, hCZ.2.2.1 0] using ht
      have h0 := (sq_le_one_iff_abs_le_one _).mpr (hcoord 0)
      have h1 := (sq_le_one_iff_abs_le_one _).mpr (hcoord 1)
      norm_num only
      linarith
    · intro j k hjk _
      exact G.disjoint hjk
    · intro k
      have hk : k = 0 := Subsingleton.elim _ _
      subst k
      ext p
      simpa only [mem_setOf_eq, Finset.mem_univ, true_and, mem_iUnion] using Set.ext_iff.mp G.cover p
    · convert G.mass using 1
      congr 1
      ring
    · intro k p hp
      have hk : k = 0 := Subsingleton.elim _ _
      subst k
      have hpZ : p ∈ ⋃ i, Z i := by simpa only [Finset.mem_univ, true_and, mem_iUnion] using hp
      simpa only [Finset.mem_univ, true_and, bodyCount] using G.level p hpZ
    · intro i _ j _ hne
      exact G.crossing i j hne
    · intro j W hW
      simpa only [one_mul, wz_clustered_cover_volume_gain.O, wz_clustered_cover_volume_gain.q,
        wz_clustered_cover_volume_gain.P, wz_clustered_cover_volume_gain.ι,
        wz_clustered_cover_volume_gain.μ, wz_clustered_cover_volume_gain.Parent.Factor.box] using hlocal j W hW

end WangZahlLot.Obl.wz_broad_grains_initialization
