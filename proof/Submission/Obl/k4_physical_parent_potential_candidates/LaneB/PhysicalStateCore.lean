import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.StateCore
import Submission.Obl.k4_physical_parent_potential_candidates.PhysicalBranch
import Submission.Lib.K4NativePreparationNumerics.Frames

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory PhysicalPotentialData

noncomputable section

namespace PhysicalSource

variable {q T j : ℕ} {ν : Measure Ln}
  {B a ζ d : ℝ} {c u : P2} {P0 : Po} {A : Set Ln} {F H : Set Ev}
  (source : PhysicalSource q ν B a ζ d T j c u P0 A F H)

/-- Original fine states have their literal physical diameter, independently
of the number of occupied states or the later selected group. -/
theorem fine_state_close {e f : Ev} (hc : source.fineState e = source.fineState f) :
    ‖packetBase T j c u e - packetBase T j c u f‖ ≤ 3*source.ε ∧
    |packetSignal P0 e/a-packetSignal P0 f/a| ≤ source.ε := by
  have hcoord (i:Fin 3) :
      |packetBase T j c u e i-packetBase T j c u f i| ≤ source.ε := by
    have hfloor := congrArg (fun k : (Fin 3 → ℤ) × ℤ => k.1 i) hc
    change ⌊packetBase T j c u e i/source.ε⌋ =
      ⌊packetBase T j c u f i/source.ε⌋ at hfloor
    have hx := (Int.abs_sub_lt_one_of_floor_eq_floor hfloor).le
    rw [← sub_div,abs_div,abs_of_pos source.ε_pos,div_le_one source.ε_pos] at hx
    exact hx
  refine ⟨?_,?_⟩
  · calc
      _ ≤ ∑ i:Fin 3, |(packetBase T j c u e-packetBase T j c u f) i| :=
        Submission.Lib.K4NativePreparationNumerics.euclidean_norm_le_sum_abs _
      _ ≤ ∑ _i:Fin 3, source.ε := Finset.sum_le_sum fun i _ => hcoord i
      _ = _ := by simp
  · have hfloor := congrArg Prod.snd hc
    change ⌊(packetSignal P0 e/a)/source.ε⌋ =
      ⌊(packetSignal P0 f/a)/source.ε⌋ at hfloor
    have hx := (Int.abs_sub_lt_one_of_floor_eq_floor hfloor).le
    rw [← sub_div,abs_div,abs_of_pos source.ε_pos,div_le_one source.ε_pos] at hx
    exact hx

/-- Seven actual events of the same original state at every point of a
full-measure core. The samples stay in the prelocalization group, so a later
ball cut does not have to preserve its breadth. -/
theorem seven_event_core [IsFiniteMeasure ν]
    (G:Set Ev) (hG:MeasurableSet G) (hGS:G ⊆ source.S) (hfin:(ν.prod volume) G ≠ ⊤)
    (hb : ∀ L : Set ((Fin 3 → ℤ) × ℤ), ∀ n : P2, ∀ t : ℝ, ‖n‖ = 1 →
      ((ν.prod volume).restrict G)
        {e | source.fineState e ∈ L ∧ |inner ℝ n (v e.1)-t| ≤ source.K^(-100:ℝ)} ≤
      ENNReal.ofReal ((1:ℝ)/1000000)*
        ((ν.prod volume).restrict G) {e | source.fineState e ∈ L}) :
    ∃ U:Set Ev, MeasurableSet U ∧ U ⊆ G ∧
      (ν.prod volume).restrict U = (ν.prod volume).restrict G ∧
      ∀ x ∈ U, ∃ e:Fin 7 → Ev,
        (∀ i, e i ∈ G ∧ source.fineState (e i) = source.fineState x ∧
          ‖packetBase T j c u (e i)-packetBase T j c u x‖ ≤ 3*source.ε ∧
          ‖Analytic.GeneralPositionSampling.lift (v (e i).1)‖ ≤ 1+2*source.K) ∧
        ∀ i j k:Fin 7, i≠j → i≠k → j≠k →
          (source.K^(-100:ℝ))^2 ≤ |Matrix.det (Matrix.of fun r t:Fin 3 =>
            (![Analytic.GeneralPositionSampling.lift (v (e i).1),
              Analytic.GeneralPositionSampling.lift (v (e j).1),
              Analytic.GeneralPositionSampling.lift (v (e k).1)] r) t)| := by
  have hK : 0 < source.K := by linarith [source.K_two]
  have hcell (k:(Fin 3 → ℤ) × ℤ) (n:P2) (t:ℝ) (hn:‖n‖=1) :
      (ν.prod volume) ((G ∩ source.fineState ⁻¹' {k}) ∩
        (fun e:Ev => v e.1) ⁻¹' {x | |inner ℝ n x-t| ≤ source.K^(-100:ℝ)}) ≤
      ENNReal.ofReal ((1:ℝ)/1000000)*(ν.prod volume) (G ∩ source.fineState ⁻¹' {k}) := by
    have hx := hb {k} n t hn
    rw [Measure.restrict_apply' hG,Measure.restrict_apply' hG] at hx
    have hleft : (G ∩ source.fineState ⁻¹' {k}) ∩
        (fun e:Ev => v e.1) ⁻¹' {x | |inner ℝ n x-t| ≤ source.K^(-100:ℝ)} =
        {e:Ev | source.fineState e ∈ ({k}:Set ((Fin 3 → ℤ) × ℤ)) ∧
          |inner ℝ n (v e.1)-t| ≤ source.K^(-100:ℝ)} ∩ G := by
      ext e
      simp only [mem_inter_iff,mem_preimage,mem_setOf_eq,mem_singleton_iff]
      tauto
    have hright : G ∩ source.fineState ⁻¹' {k} =
        {e:Ev | source.fineState e ∈ ({k}:Set ((Fin 3 → ℤ) × ℤ))} ∩ G :=
      inter_comm _ _
    rw [hleft,hright]
    exact hx
  have hκ : (686:ENNReal)*ENNReal.ofReal ((1:ℝ)/1000000) < 1 := by
    calc (686:ENNReal)*ENNReal.ofReal ((1:ℝ)/1000000) =
        ENNReal.ofReal ((686:ℝ)*(1/1000000)) := by
          rw [ENNReal.ofReal_mul (by norm_num)]
          norm_num
      _ < ENNReal.ofReal 1 := ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.2 (by norm_num)
      _ = 1 := ENNReal.ofReal_one
  obtain ⟨U,hUm,hUG,hlaw,hseven⟩ := Analytic.exists_seven_state_core
    (ν.prod volume) G hG hfin source.fineState source.measurable_fineState
    (fun e:Ev => v e.1) (measurable_velocity.comp measurable_fst)
    (Real.rpow_pos_of_pos hK _) hκ hcell
  refine ⟨U,hUm,hUG,hlaw,?_⟩
  intro x hx
  obtain ⟨e,he,hdet⟩ := hseven x hx
  refine ⟨e,fun i => ?_,hdet⟩
  have hv := (source.point_bounds (e i) (hGS (he i).1)).2.1
  have hc (k:Fin 2) : |v (e i).1 k| ≤ source.K :=
    (PiLp.norm_apply_le (v (e i).1) k).trans hv
  refine ⟨(he i).1,(he i).2,(source.fine_state_close (he i).2).1,?_⟩
  calc
    _ ≤ ∑ k:Fin 3, |Analytic.GeneralPositionSampling.lift (v (e i).1) k| :=
      Submission.Lib.K4NativePreparationNumerics.euclidean_norm_le_sum_abs _
    _ = 1+|v (e i).1 0|+|v (e i).1 1| := by
      simp [Fin.sum_univ_three,Analytic.GeneralPositionSampling.lift]
    _ ≤ 1+2*source.K := by linarith [hc 0,hc 1]

end PhysicalSource

end

end Submission.Obl.k4_physical_parent_potential_candidates
