import Submission.Obl.k4_physical_parent_potential_candidates.PhysicalCatalogue
import Submission.Lib.K4GlobalParentSignal

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory MvPolynomial

noncomputable section

namespace PhysicalSource

variable {q T j : ℕ} {ν : Measure Ln}
  {B a ζ d : ℝ} {c u : P2} {P0 : Po} {A : Set Ln} {F H : Set Ev}
  (source : PhysicalSource q ν B a ζ d T j c u P0 A F H)

/-- The old global parent bounds control its hidden derivative along
ordinary physical time, without a hidden-velocity or coefficient loss. -/
theorem parent_hidden_variation (hP0 : P0.totalDegree ≤ 2)
    (e:Ev) (he:e∈source.S) {t:ℝ} (hetime:e.2∈Icc (0:ℝ) 1) (ht:t∈Icc (0:ℝ) 1) :
    |eval (xp e.1 t) (pderiv 3 P0)-eval (xp e.1 e.2) (pderiv 3 P0)| ≤
      24*source.K*B*|t-e.2| := by
  simpa only [Submission.Lib.K4GlobalParentSignal.xp, xp, mul_assoc] using
    Submission.Lib.K4GlobalParentSignal.signal_variation
    ((Submission.Lib.K4QuadraticSheets.totalDegree_pderiv_le' P0 3
      (d := 1) hP0).trans (by norm_num))
    (fun s hs => (source.point_bounds e he).2.2.1 s hs |>.2.1) hetime ht

/-- A source event's old hidden derivative remains regular, with the same
branch sign, throughout a fixed-power ordinary-time window. -/
theorem parent_hidden_regular_near (hP0 : P0.totalDegree ≤ 2) (hB:0<B)
    (e:Ev) (he:e∈source.S) {t:ℝ} (hetime:e.2∈Icc (0:ℝ) 1) (ht:t∈Icc (0:ℝ) 1)
    (hnear:|t-e.2|≤(48*source.K^2)⁻¹) :
    B/(2*source.K) ≤ |eval (xp e.1 t) (pderiv 3 P0)| ∧
    |eval (xp e.1 t) (pderiv 3 P0)| ≤ source.K*B ∧
    parentBranch P0 (e.1,t) = parentBranch P0 e := by
  have hK : 0 < source.K := by linarith [source.K_two]
  let Ds := eval (xp e.1 e.2) (pderiv 3 P0)
  let Dt := eval (xp e.1 t) (pderiv 3 P0)
  have hDslow : B/source.K ≤ |Ds| := (source.point_bounds e he).2.2.2.1
  have hd : |Dt-Ds| ≤ B/(2*source.K) := by
    calc _ ≤ 24*source.K*B*|t-e.2| := source.parent_hidden_variation hP0 e he hetime ht
      _ ≤ 24*source.K*B*(48*source.K^2)⁻¹ :=
        mul_le_mul_of_nonneg_left hnear (by positivity)
      _ = _ := by field_simp; ring
  have hhalf : B/source.K = 2*(B/(2*source.K)) := by field_simp
  have hBhalf : 0 < B/(2*source.K) := by positivity
  have htri : |Ds| ≤ |Dt-Ds|+|Dt| := by
    calc |Ds| = |(Ds-Dt)+Dt| := by congr 1; ring
      _ ≤ |Ds-Dt|+|Dt| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm]
  have hDtlow : B/(2*source.K) ≤ |Dt| := by linarith only [hDslow,hd,htri,hhalf]
  refine ⟨hDtlow,(source.point_bounds e he).2.2.1 t ht |>.2.1,?_⟩
  have hsgn : (0<Dt) ↔ (0<Ds) := by
    constructor
    · intro ht0
      by_contra hs0
      have hsle : Ds ≤ 0 := le_of_not_gt hs0
      rw [abs_of_nonpos hsle] at hDslow
      have hle := le_abs_self (Dt-Ds)
      linarith only [hDslow,hd,hhalf,hBhalf,ht0,hle]
    · intro hs0
      have hle := neg_abs_le (Dt-Ds)
      rw [abs_of_pos hs0] at hDslow
      linarith only [hDslow,hd,hhalf,hBhalf,hle]
  simp only [parentBranch]
  change (if 0<Dt then true else false) = (if 0<Ds then true else false)
  simp only [hsgn]

end PhysicalSource

end

end Submission.Obl.k4_physical_parent_potential_candidates
