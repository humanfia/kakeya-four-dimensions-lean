import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.SourceTube

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory MvPolynomial PhysicalPotentialData

noncomputable section

namespace PhysicalSource

/-- The original chart and the physical source give two-sided physical
group windows around every retained event, including events at old block
endpoints. The physical parent and the independent old test stay separate. -/
theorem exists_extrapolated_group_window (q:ℕ) :
    ∃ Cx:ℝ, 1 ≤ Cx ∧
    ∀ {Nk:ℝ} {Mp Dp T j:ℕ} {ν:Measure Ln} {κ B a ζ d rr:ℝ} {c u:P2}
      {Qm:Matrix (Fin 2) (Fin 2) ℝ} {P0 Rb:Po} {A:Set Ln} {F H:Set Ev} {ex:Prop}
      (source:PhysicalSource q ν B a ζ d T j c u P0 A F H),
    P0.totalDegree ≤ 2 → 0<B → j<2^T → 1 ≤ κ → κ ≤ source.K →
    ch Nk Mp Dp κ T (j:ℝ) rr B Set.univ c u Qm Rb A F ex →
    ∀ {w:ℝ}, 0<w → ∀ (g:ℤ) (β:Bool) (e:Ev), e∈source.S →
      e.1∈source.groupLines w g → parentBranch P0 e=β →
    ∀ t:ℝ, |t-e.2|  ≤  ((2:ℝ)^T)⁻¹/(4*source.K^2) →
      Analytic.PhysicalGroupPoint B⁻¹ (P0-C (physicalGroupCenter a w g)) Rb
        (Broad.parentPotentialPullback T j c u source.Pot)
        (Cx*(a*ζ)+a*w) (2*source.K) (branchSign β) (Cx*(κ*δ Nk rr))
        (Analytic.graphPoint e.1 t) := by
  obtain ⟨Cx,hCx,hwindow⟩ := Broad.physicalGroupPoint_of_normalized_parent_potential q
  refine ⟨Cx,hCx,?_⟩
  intro Nk Mp Dp T j ν κ B a ζ d rr c u Qm P0 Rb A F H ex source hP0 hB hj hκ hκK hch
    w hw g β e he hl hβ t ht
  have hK : 0<source.K := by linarith [source.K_two]
  have hζ : 0<ζ := source.ε_pos.trans_le source.ε_le
  have ha : 0<a := source.a_pos
  have hsign : branchSign β*eval (xp e.1 e.2) (pderiv 3 P0) =
      |eval (xp e.1 e.2) (pderiv 3 P0)| := by
    rw [←hβ]
    by_cases hd : 0<eval (xp e.1 e.2) (pderiv 3 P0)
    · simp [parentBranch,branchSign,hd,abs_of_pos hd]
    · simp [parentBranch,branchSign,hd,abs_of_nonpos (le_of_not_gt hd)]
  have hsign2 : (branchSign β)^2=1 := by cases β <;> norm_num [branchSign]
  have hfit (s:ℝ) (hs:s∈Icc ((j:ℝ)*((2:ℝ)^T)⁻¹) (((j:ℝ)+1)*((2:ℝ)^T)⁻¹)) :
      |(eval (xp e.1 s) P0-eval (fun i => packetBase T j c u (e.1,s) i) source.Pot)-
        Broad.parentIntercept T j c u P0 source.Pot e.1|  ≤  a*ζ := by
    simpa only [Broad.parentIntercept,ownIntercept,packetOrigin,packetSignal] using
      source.line_fit e.1 hl.1 s hs
  have hparent (s:ℝ) (hs:s∈Icc ((j:ℝ)/(2:ℝ)^T) (((j:ℝ)+1)/(2:ℝ)^T)) :
      |eval (xp e.1 s) (pderiv 3 P0)|  ≤  source.K*B := by
    have hunit := old_block_subset_unit T j hj (by simpa only [div_eq_mul_inv] using hs)
    exact (source.line_jets e.1 hl.1 s hunit).2.1
  have hwin : |Broad.parentIntercept T j c u P0 source.Pot e.1-
      physicalGroupCenter a w g|  ≤  a*w := by
    simpa only [Broad.parentIntercept,ownIntercept,packetOrigin,packetSignal] using
      physical_intercept_bin_window source.a_pos hw hl.2
  exact hwindow hch hκ hB P0 source.Pot hP0 source.degree e.1 source.K
    (physicalGroupCenter a w g) (a*ζ) (a*w) (branchSign β) e.2 hκK (by positivity)
    hfit hparent hwin hsign2 (source.subset_S he).2
    (by rw [hsign]; exact (source.point_bounds e he).2.2.2.1) t ht

end PhysicalSource

end

end Submission.Obl.k4_physical_parent_potential_candidates
