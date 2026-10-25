-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.Frostman.G027.Glue.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.Frostman.G027.GrainInterfaces
import Submission.WZ.Obl.wz_separated_cover_refinement
import Submission.WZ.Obl.wz_extremal_lipschitz_grains
import Submission.WZ.Obl.wz_broad_grains_improvement.Frostman.Stmts
import Submission.WZ.Obl.wz_grains_nonsingular_slices

/- Adapted from the internal o015/x0589 assembly at effb3d2,
   WangZahlLot/Obl/wz_frostman_all_scales_volume/G027/Glue.lean; original session credits below are retained. -/

namespace WangZahlLot.Obl.wz_broad_grains_improvement.Frostman.G027

/-- Forgetting the additional separation recovers exactly the frozen covers. -/
theorem SeparatedScales.allScales {η δ : ℝ} {n : ℕ}
    {x v : Fin n → Space} (h : SeparatedScales η δ n x v) :
    AllScales η δ n x v := by
  intro r hδr hr1
  obtain ⟨ρ, hrρ, hρ1, hρ, k, hk, z, w, hw, hd, hu, ho, hb, hc, _⟩ :=
    h r hδr hr1
  exact ⟨ρ, hrρ, hρ1, hρ, k, hk, z, w, hw, hd, hu, ho, hb, hc⟩

theorem SeparatedExamples.volumeExamples {s : ℝ} (h : SeparatedExamples s) :
    VolumeExamples s := by
  intro η d0 hη hd0
  obtain ⟨δ, hδ, hδ0, hδ100, n, x, v, Y, hf, hs, hv⟩ := h η d0 hη hd0
  exact ⟨δ, hδ, hδ0, hδ100, n, x, v, Y, hf, hs.allScales, hv⟩

/-- The finite refinement preserves every persistent deficit exponent. -/
theorem VolumeExamples.separatedExamples {s : ℝ} (h : VolumeExamples s) :
    SeparatedExamples s := by
  intro ε d0 hε hd0
  obtain ⟨η, d1, hη, hd1, hrefine⟩ :=
    WangZahlLot.wz_separated_cover_refinement ε hε
  obtain ⟨δ, hδ, hδ0, hδ100, n, x, v, Y, hf, hs, hv⟩ :=
    h η (min d0 d1) hη (lt_min hd0 hd1)
  obtain ⟨m, a, _, hfamily, hscales⟩ :=
    hrefine δ hδ (hδ0.trans (min_le_right _ _)) hδ100 n x v Y hf hs
  refine ⟨δ, hδ, hδ0.trans (min_le_left _ _), hδ100, m,
    (fun i => x (a i)), (fun i => v (a i)), (fun i => Y (a i)),
    hfamily, hscales, ?_⟩
  apply le_trans (MeasureTheory.measure_mono ?_) hv
  exact Set.iUnion_subset (fun i => Set.subset_iUnion Y (a i))

/-- Composition of the four geometric interfaces and exact slice integration. -/
theorem extraction_of_children (h062 : WangZahlLot.Obl.wz_broad_grains_improvement.Frostman.Stmts.O062) :
    (∃ s : ℝ, 0 < s ∧ VolumeExamples s) →
      ∃ s : ℝ, 0 < s ∧ TwistedExamples s := by
  intro hex
  obtain ⟨σ, hσ, hσ2, hbelow, habove⟩ := exists_extremalDeficit hex
  have hbelowS : ∀ t : ℝ, t < σ → SeparatedExamples t :=
    fun t ht => (hbelow t ht).separatedExamples
  have haboveS : ∀ t : ℝ, σ < t → ¬ SeparatedExamples t :=
    fun t ht h => habove t ht h.volumeExamples
  obtain ⟨hσ1, hL⟩ :=
    WangZahlLot.wz_extremal_lipschitz_grains σ hσ hσ2 hbelowS haboveS
  have hC := h062 σ hσ hσ1 hbelowS haboveS hL
  have hQ : NonsingularSliceExamples σ :=
    WangZahlLot.wz_grains_nonsingular_slices σ hσ hσ1 hbelowS haboveS hC
  refine ⟨σ / 8, by positivity, ?_⟩
  intro η d0 hη hd0
  obtain ⟨δ, hδ, hδ0, hδ100, n, x, v, Y, hf, hc, ht, hg, f, hn, hslice⟩ :=
    hQ η d0 hη hd0
  refine ⟨δ, hδ, hδ0, hδ100, n, x, v, Y, hf, ht, hg, f, hn, ?_⟩
  exact twisted_volume_le_of_slices hc hf.union_subset_ball hn.1.continuous
    (Real.rpow_nonneg hδ.le _) hslice

end WangZahlLot.Obl.wz_broad_grains_improvement.Frostman.G027
