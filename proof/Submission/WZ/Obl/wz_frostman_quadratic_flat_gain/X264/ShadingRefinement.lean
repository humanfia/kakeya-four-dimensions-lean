-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.ShadingRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.DenseRefinement
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file ShadingRefinement.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set

open Classical in
/-- The measure-valued form of incidence density selection, ready for a common
cell restriction of the original shading. -/
theorem Factored.dense_shading_refinement {D b d Q : ℝ} {n p : ℕ}
    {T : Fin n → Set Space} {P : Fin p → Set Space}
    (hf : Factored D b T P) (hn : 0 < n) (hd : 0 < d) (hd1 : d ≤ 1) (hQ : 0 < Q)
    (Y : Fin n → Set Space) (hupper : ∀ i, volume (Y i) ≤ ENNReal.ofReal Q)
    (hmass : ENNReal.ofReal (d * Q * (∑ j, (Set.ncard {i | T i ⊆ P j} : ℝ))) ≤
      ∑ j, ∑ i ∈ {i | T i ⊆ P j}.toFinset, volume (Y i)) :
    ∃ (k q : ℕ) (g : Fin k → Fin n) (h : Fin q → Fin p),
      0 < k ∧ 0 < q ∧ Function.Injective g ∧ Function.Injective h ∧
      (∀ i, ENNReal.ofReal (d / 2 * Q) ≤ volume (Y (g i))) ∧
      Factored (4 * D ^ 2 / d) b (T ∘ g) (P ∘ h) ∧
      ∀ j, d ^ 2 / (16 * D) * n ≤
        (q : ℝ) * Set.ncard {i | T (g i) ⊆ P (h j)} := by
  have hfin (i : Fin n) : volume (Y i) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hupper i)
  have hsumfin (j : Fin p) : (∑ i ∈ {i | T i ⊆ P j}.toFinset, volume (Y i)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun i _ => hfin i)
  have htotalfin : (∑ j, ∑ i ∈ {i | T i ⊆ P j}.toFinset, volume (Y i)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun j _ => hsumfin j)
  have hreal : d * Q * (∑ j, (Set.ncard {i | T i ⊆ P j} : ℝ)) ≤
      ∑ j, ∑ i ∈ {i | T i ⊆ P j}.toFinset, (volume (Y i)).toReal := by
    have h := ENNReal.toReal_mono htotalfin hmass
    rw [ENNReal.toReal_ofReal (by positivity :
      0 ≤ d * Q * (∑ j, (Set.ncard {i | T i ⊆ P j} : ℝ)))] at h
    simpa only [ENNReal.toReal_sum (fun j _ => hsumfin j),
      ENNReal.toReal_sum (fun i _ => hfin i)] using h
  let w := fun i => (volume (Y i)).toReal / Q
  have hw (i : Fin n) : w i ≤ 1 := by
    apply (div_le_iff₀ hQ).mpr
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hupper i)
    simpa only [ENNReal.toReal_ofReal hQ.le, one_mul] using h
  have hwmass : d * (∑ j, (Set.ncard {i | T i ⊆ P j} : ℝ)) ≤
      ∑ j, ∑ i ∈ {i | T i ⊆ P j}.toFinset, w i := by
    dsimp [w]
    simp_rw [← Finset.sum_div]
    rw [le_div_iff₀ hQ]
    nlinarith only [hreal]
  obtain ⟨k, q, g, h, hk, hq, hg, hh, hden, hfact, hproduct⟩ :=
    hf.dense_refinement hn hd hd1 w hw hwmass
  refine ⟨k, q, g, h, hk, hq, hg, hh, ?_, hfact, hproduct⟩
  intro i
  rw [← ENNReal.ofReal_toReal (hfin (g i))]
  apply ENNReal.ofReal_le_ofReal
  exact (le_div_iff₀ hQ).mp (hden i)

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
