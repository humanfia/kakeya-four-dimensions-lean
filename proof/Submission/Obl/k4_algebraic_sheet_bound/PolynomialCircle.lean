import Mathlib

namespace Submission.Obl.k4_algebraic_sheet_bound

open Set Metric Polynomial

/-- Polynomial roots over a compact base stay in a common disk if the leading coefficient
does not vanish on that base. -/
theorem exists_root_free_circle (Q : Polynomial (Polynomial ℂ))
    {K : Set ℂ} (hK : IsCompact K) (hlead : ∀ t ∈ K, Q.leadingCoeff.eval t ≠ 0) :
    ∃ R : ℝ, 1 < R ∧ ∀ t ∈ K, ∀ w : ℂ, ‖w‖ = R →
      (Q.map (Polynomial.evalRingHom t)).eval w ≠ 0 := by
  let B : ℂ → ℝ := fun t =>
    (∑ i ∈ Finset.range Q.natDegree, ‖(Q.coeff i).eval t‖) /
      ‖Q.leadingCoeff.eval t‖ + 1
  have hB : ContinuousOn B K := by
    apply ContinuousOn.add _ continuousOn_const
    apply ContinuousOn.div
    · exact (continuous_finsetSum _ (fun i _ => (Q.coeff i).continuous.norm)).continuousOn
    · exact Q.leadingCoeff.continuous.norm.continuousOn
    · intro t ht
      exact norm_ne_zero_iff.mpr (hlead t ht)
  obtain ⟨M, hM⟩ := hK.bddAbove_image hB
  refine ⟨max M 1 + 1, by linarith [le_max_right M 1], ?_⟩
  intro t ht w hw hroot
  let p := Q.map (Polynomial.evalRingHom t)
  have hpdeg : p.natDegree = Q.natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ (hlead t ht)
  have hplc : p.leadingCoeff = Q.leadingCoeff.eval t :=
    Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ (hlead t ht)
  have hp : p ≠ 0 := by
    intro h
    exact hlead t ht (by simpa [h] using hplc.symm)
  have hroot' : p.IsRoot w := hroot
  have hnorm := hroot'.norm_lt_cauchyBound hp
  have hsum : (((Finset.range p.natDegree).sup (fun i => ‖p.coeff i‖₊) : NNReal) : ℝ) ≤
      ∑ i ∈ Finset.range Q.natDegree, ‖(Q.coeff i).eval t‖ := by
    rw [hpdeg]
    have hs : (Finset.range Q.natDegree).sup (fun i => ‖p.coeff i‖₊) ≤
        ∑ i ∈ Finset.range Q.natDegree, ‖p.coeff i‖₊ := by
      apply Finset.sup_le
      intro i hi
      exact Finset.single_le_sum (f := fun i => ‖p.coeff i‖₊) (fun _ _ => by positivity) hi
    have hs' : (((Finset.range Q.natDegree).sup (fun i => ‖p.coeff i‖₊) : NNReal) : ℝ) ≤
        ∑ i ∈ Finset.range Q.natDegree, ‖p.coeff i‖ := by
      simpa only [NNReal.coe_sum, coe_nnnorm] using (NNReal.coe_le_coe.mpr hs)
    simpa only [p, Polynomial.coeff_map, Polynomial.coe_evalRingHom] using hs'
  have hbound : (p.cauchyBound : ℝ) ≤ B t := by
    simp only [Polynomial.cauchyBound, NNReal.coe_add, NNReal.coe_div,
      NNReal.coe_one, coe_nnnorm, hplc]
    dsimp only [B]
    gcongr
  have hBM : B t ≤ M := hM (mem_image_of_mem B ht)
  have hnorm' : ‖w‖ < (p.cauchyBound : ℝ) := hnorm
  have hMR : M < max M 1 + 1 := by linarith [le_max_left M 1]
  linarith

end Submission.Obl.k4_algebraic_sheet_bound
