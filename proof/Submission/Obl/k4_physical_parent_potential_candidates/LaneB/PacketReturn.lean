import Submission.Obl.k4_physical_parent_potential_candidates.Restoration
import Submission.Obl.k4_pair_bin_atlas_assembly.Interpolation

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory MvPolynomial

noncomputable section

namespace PacketReturn

/-- A quadratic on an actual original trajectory is controlled on the
whole old block by any fixed relative window about one event. -/
theorem trajectory_short_bound {R : Po} (hR : R.totalDegree ≤ 2) (l : Ln)
    {lo hi te θ V : ℝ} (hlen : 0 < hi-lo) (hte : te ∈ Icc lo hi)
    (hθ : 0 < θ) (hθ2 : θ ≤ 1/2)
    (hb : ∀ t ∈ Icc lo hi, |t-te| ≤ θ*(hi-lo) → |eval (xp l t) R| ≤ V) :
    ∀ t ∈ Icc lo hi, |eval (xp l t) R| ≤ 32*V/θ^2 := by
  have hquad : Submission.Obl.k4_eligibility_sign_description.Quadratic
      (fun t => eval (xp l t) R) :=
    Submission.Obl.k4_pair_bin_atlas_assembly.quadratic_eval_x R hR l
  have hx := Submission.Obl.k4_pair_bin_atlas_assembly.interval_bound_of_short hquad
    hte (mul_pos hθ hlen) (by nlinarith [hθ2]) hb
  intro t ht
  convert hx t ht using 1
  field_simp
  <;> ring

/-- Local quadratic certificates on retained events give the whole-block
restoration output. Passing to positive-duration original lines preserves
the exact original event law and makes the retained line set measurable. -/
theorem restoration_of_event_windows (ν : Measure Ln) [IsFiniteMeasure ν]
    (R : Po) {Mcoef Cv Cmass Cr B a w θ : ℝ} (T j : ℕ) (Gl : Set Ln) (G G0 : Set Ev)
    (hR : R.totalDegree ≤ 2) (hcoeff : ∀ m, |R.coeff m| ≤ Mcoef)
    (hCv : 0 < Cv) (hB : 0 < B) (ha : 0 < a) (hw : 0 < w)
    (hθ : 0 < θ) (hθ2 : θ ≤ 1/2) (hCvCr : Cv ≤ Cr)
    (hwindow : 32*Cv/θ^2 ≤ Cr) (hmassCr : Cmass ≤ Cr)
    (hG0 : MeasurableSet G0) (hsub : G0 ⊆ G)
    (hevents : ∀ e ∈ G0, e.1 ∈ Gl ∧
      e.2 ∈ Icc ((j:ℝ)/(2:ℝ)^T) (((j:ℝ)+1)/(2:ℝ)^T))
    (hlow : ∀ e ∈ G0, B/Cv ≤ |eval (xp e.1 e.2) (pderiv 3 R)|)
    (hlocal : ∀ e ∈ G0, ∀ t ∈ Icc ((j:ℝ)/(2:ℝ)^T) (((j:ℝ)+1)/(2:ℝ)^T),
      |t-e.2| ≤ θ*((2:ℝ)^T)⁻¹ →
      |eval (xp e.1 t) R| ≤ Cv*(a*w) ∧
      |eval (xp e.1 t) (pderiv 3 R)| ≤ Cv*B ∧
      |eval (xp e.1 t) (pderiv 3 (pderiv 3 R))| ≤ Cv*B^2/(a*w))
    (hmass : (ν.prod volume) G ≤ ENNReal.ofReal Cmass*(ν.prod volume) G0) :
    RestorationOutput (ν.prod volume) Mcoef Cr B a w T j Gl G := by
  let A' := positiveSourceLines G0
  let G' := G0 ∩ Prod.fst ⁻¹' A'
  have hA' : MeasurableSet A' := measurableSet_positiveSourceLines G0 hG0
  have hG' : MeasurableSet G' := hG0.inter (hA'.preimage measurable_fst)
  have hlaw : (ν.prod volume) G' = (ν.prod volume) G0 := by
    have hx := congrArg (fun μ:Measure Ev => μ univ) (restrict_source_positive_lines ν G0 hG0)
    simpa only [Measure.restrict_apply_univ] using hx
  have hdeg1 : (pderiv 3 R).totalDegree ≤ 2 :=
    (Submission.Lib.K4QuadraticSheets.totalDegree_pderiv_le' R 3 (d:=1) hR).trans
      (by norm_num)
  have hdeg2 : (pderiv 3 (pderiv 3 R)).totalDegree ≤ 2 :=
    (Submission.Lib.K4QuadraticSheets.totalDegree_pderiv_le' (pderiv 3 R) 3 (d:=1) hdeg1).trans
      (by norm_num)
  let lo := (j:ℝ)/(2:ℝ)^T
  let hi := ((j:ℝ)+1)/(2:ℝ)^T
  have hlen : hi-lo = ((2:ℝ)^T)⁻¹ := by dsimp [lo,hi]; ring
  have hlenpos : 0 < hi-lo := by rw [hlen]; positivity
  refine ⟨R,A',G',hR,hcoeff,hA',positiveSourceLines_subset G0 Gl
    (fun e he => (hevents e he).1),hG',inter_subset_left.trans hsub,
    (fun e he => he.2),?_,?_,?_⟩
  · intro l hl t ht
    obtain ⟨te,hte⟩ := exists_source_event_of_positive_line hl
    have het := (hevents (l,te) hte).2
    have hlocal' (s:ℝ) (hs:s∈Icc lo hi) (hne:|s-te|≤θ*(hi-lo)) :=
      hlocal (l,te) hte s hs (by simpa only [hlen] using hne)
    have hv := trajectory_short_bound hR l hlenpos het hθ hθ2
      (fun s hs hne => (hlocal' s hs hne).1) t ht
    have hd := trajectory_short_bound hdeg1 l hlenpos het hθ hθ2
      (fun s hs hne => (hlocal' s hs hne).2.1) t ht
    have hc := trajectory_short_bound hdeg2 l hlenpos het hθ hθ2
      (fun s hs hne => (hlocal' s hs hne).2.2) t ht
    refine ⟨hv.trans ?_,hd.trans ?_,hc.trans ?_⟩
    · calc 32*(Cv*(a*w))/θ^2 = (32*Cv/θ^2)*(a*w) := by ring
        _ ≤ Cr*(a*w) := mul_le_mul_of_nonneg_right hwindow (by positivity)
    · calc 32*(Cv*B)/θ^2 = (32*Cv/θ^2)*B := by ring
        _ ≤ Cr*B := mul_le_mul_of_nonneg_right hwindow hB.le
    · calc 32*(Cv*B^2/(a*w))/θ^2 = (32*Cv/θ^2)*B^2/(a*w) := by ring
        _ ≤ Cr*B^2/(a*w) := by gcongr
  · intro e he
    exact (div_le_div_of_nonneg_left hB.le hCv hCvCr).trans (hlow e he.1)
  · rw [hlaw]
    exact hmass.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hmassCr) le_rfl)

end PacketReturn

end

end Submission.Obl.k4_physical_parent_potential_candidates
