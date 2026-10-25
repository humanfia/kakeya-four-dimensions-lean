import Submission.Obl.k4_physical_parent_potential_candidates.SourceLines
import Submission.Lib.K4GlobalParentSignal

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory MvPolynomial PhysicalPotentialData
open scoped ENNReal

noncomputable section

/-- Exact original-time quadratic remainder on a block, with its genuine
parent rate and coefficient. -/
theorem parent_block_remainder {P : Po} (hP : P.totalDegree ≤ 2)
    (l : Ln) (t0 h s : ℝ) :
    eval (xp l (t0+h*s)) P - eval (xp l t0) P =
      h*Submission.Lib.K4GlobalParentSignal.rate P l t0*s +
        h^2*Submission.Lib.K4ProjectedGroups.sc2 P l.2*s^2 := by
  have hsig (t : ℝ) : eval (xp l t) P =
      Submission.Lib.K4ProjectedGroups.sc0 P l.2 +
        t*Submission.Lib.K4ProjectedGroups.sc1 P l.2 +
        t^2*Submission.Lib.K4ProjectedGroups.sc2 P l.2 :=
    Submission.Lib.K4ProjectedGroups.sig_eq hP l.2 t
  rw [hsig, hsig, Submission.Lib.K4GlobalParentSignal.rate_eq_coefficients hP]
  ring

namespace PhysicalSource

variable {q T j : ℕ} {ν : Measure Ln}
  {B a ζ d : ℝ} {c u : P2} {P0 : Po} {A : Set Ln} {F H : Set Ev}
  (source : PhysicalSource q ν B a ζ d T j c u P0 A F H)

/-- The short physical clock and the full-time parent bound improve the
normalized potential's whole-line quadratic fit to an affine fit. -/
theorem normalized_affine_line_fit (hP0 : P0.totalDegree ≤ 2)
    (l : Ln) (hl : l ∈ source.lineSet) :
    ∀ s ∈ Icc (0:ℝ) 1,
      |eval (fun i => packetBase T j c u
          (l, (j:ℝ)*((2:ℝ)^T)⁻¹+((2:ℝ)^T)⁻¹*s) i) source.Pot/((2:ℝ)^T)⁻¹ -
        (eval (fun i => packetOrigin T j c u l i) source.Pot/((2:ℝ)^T)⁻¹ +
          Submission.Lib.K4GlobalParentSignal.rate P0 l ((j:ℝ)*((2:ℝ)^T)⁻¹)*s)| ≤
        9*source.K*ζ := by
  intro s hs
  let h : ℝ := ((2:ℝ)^T)⁻¹
  let t0 : ℝ := (j:ℝ)*h
  have hh : 0 < h := by dsimp [h]; positivity
  have hK : 0 < source.K := by linarith [source.K_two]
  have hζ : 0 < ζ := source.ε_pos.trans_le source.ε_le
  have ht : t0+h*s ∈ Icc ((j:ℝ)*h) (((j:ℝ)+1)*h) := by
    dsimp only [t0]
    constructor <;> nlinarith [hs.1, hs.2]
  have hf := source.line_fit l hl (t0+h*s) ht
  have hparent : ∀ t ∈ Icc (0:ℝ) 1,
      |Submission.Lib.K4ProjectedGroups.sig P0 l.2 t| ≤ source.K :=
    fun t ht => (source.line_jets l hl t ht).1
  have hsc := Submission.Lib.K4ProjectedGroups.abs_sc2_le hparent
  have hs2 : |s|^2 ≤ 1 := by
    have habs : |s| ≤ 1 := by simpa only [abs_of_nonneg hs.1] using hs.2
    simpa using pow_le_pow_left₀ (abs_nonneg s) habs 2
  have hrem := parent_block_remainder hP0 l t0 h s
  have hfit : |eval (fun i => packetBase T j c u (l,t0+h*s) i) source.Pot -
      (eval (fun i => packetOrigin T j c u l i) source.Pot +
        h*Submission.Lib.K4GlobalParentSignal.rate P0 l t0*s)| ≤ a*ζ+8*source.K*h^2 := by
    have heq : eval (fun i => packetBase T j c u (l,t0+h*s) i) source.Pot -
        (eval (fun i => packetOrigin T j c u l i) source.Pot +
          h*Submission.Lib.K4GlobalParentSignal.rate P0 l t0*s) =
      -((eval (xp l (t0+h*s)) P0-
          eval (fun i => packetBase T j c u (l,t0+h*s) i) source.Pot)-
        ownIntercept T j c u P0 source.Pot l) +
      h^2*Submission.Lib.K4ProjectedGroups.sc2 P0 l.2*s^2 := by
      unfold ownIntercept packetSignal
      dsimp only [t0, h] at hrem ⊢
      linarith
    rw [heq]
    calc
      _ ≤ |(eval (xp l (t0+h*s)) P0-
            eval (fun i => packetBase T j c u (l,t0+h*s) i) source.Pot)-
          ownIntercept T j c u P0 source.Pot l|+
        |h^2*Submission.Lib.K4ProjectedGroups.sc2 P0 l.2*s^2| := by
          simpa only [abs_neg] using abs_add_le
            (-((eval (xp l (t0+h*s)) P0-
              eval (fun i => packetBase T j c u (l,t0+h*s) i) source.Pot)-
              ownIntercept T j c u P0 source.Pot l))
            (h^2*Submission.Lib.K4ProjectedGroups.sc2 P0 l.2*s^2)
      _ ≤ a*ζ+8*source.K*h^2 := by
        apply add_le_add hf
        rw [abs_mul, abs_mul, abs_sq, abs_sq]
        calc
          h^2*|Submission.Lib.K4ProjectedGroups.sc2 P0 l.2| * s^2 ≤
              h^2*(8*source.K)*1 := by gcongr; simpa only [sq_abs] using hs2
          _ = _ := by ring
  have herror : a*ζ+8*source.K*h^2 ≤ (9*source.K*ζ)*h := by
    have ha : a ≤ source.K*h := source.a_le
    have hhζ : h ≤ ζ := source.clock_le
    nlinarith [mul_le_mul_of_nonneg_right ha hζ.le,
      mul_le_mul_of_nonneg_left hhζ (show 0 ≤ 8*source.K*h by positivity)]
  have hdiv := (div_le_iff₀ hh).2 (hfit.trans herror)
  change |eval (fun i => packetBase T j c u (l,t0+h*s) i) source.Pot/h -
    (eval (fun i => packetOrigin T j c u l i) source.Pot/h +
      Submission.Lib.K4GlobalParentSignal.rate P0 l t0*s)| ≤ 9*source.K*ζ
  calc
    _ = |(eval (fun i => packetBase T j c u (l,t0+h*s) i) source.Pot -
        (eval (fun i => packetOrigin T j c u l i) source.Pot +
          h*Submission.Lib.K4GlobalParentSignal.rate P0 l t0*s))/h| := by
      congr 1
      field_simp
    _ = |eval (fun i => packetBase T j c u (l,t0+h*s) i) source.Pot -
        (eval (fun i => packetOrigin T j c u l i) source.Pot +
          h*Submission.Lib.K4GlobalParentSignal.rate P0 l t0*s)|/h := by
      rw [abs_div, abs_of_pos hh]
    _ ≤ 9*source.K*ζ := hdiv

end PhysicalSource

end

end Submission.Obl.k4_physical_parent_potential_candidates
