import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.ParentTube
import Submission.Obl.k4_physical_parent_potential_candidates.PhysicalGroup
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.ParentPotentialPullback

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory MvPolynomial PhysicalPotentialData

noncomputable section

def branchSign (β : Bool) : ℝ := if β then 1 else -1

theorem old_block_subset_unit (T j : ℕ) (hj : j < 2^T) :
    Icc ((j:ℝ)*((2:ℝ)^T)⁻¹) (((j:ℝ)+1)*((2:ℝ)^T)⁻¹) ⊆ Icc (0:ℝ) 1 := by
  have hp : 0 < (2:ℝ)^T := by positivity
  have hj' : (j:ℝ)+1 ≤ (2:ℝ)^T := by exact_mod_cast hj
  have hu : ((j:ℝ)+1)*((2:ℝ)^T)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hp]
    exact hj'
  intro t ht
  exact ⟨(mul_nonneg (Nat.cast_nonneg j) (inv_nonneg.mpr hp.le)).trans ht.1,
    ht.2.trans hu⟩

namespace PhysicalSource

variable {q T j : ℕ} {ν : Measure Ln}
  {B a ζ d : ℝ} {c u : P2} {P0 : Po} {A : Set Ln} {F H : Set Ev}
  (source : PhysicalSource q ν B a ζ d T j c u P0 A F H)

/-- Every heavy-group line gives group points throughout an ordinary-time
window. The auxiliary certificate is the globally bounded physical parent;
this window requires no regularity assumption about an independent test. -/
theorem physical_group_point_near (hP0 : P0.totalDegree ≤ 2) (hB : 0 < B)
    (hj : j < 2^T) {w : ℝ} (hw : 0 < w) (hζw : ζ ≤ w) {g : ℤ} {β : Bool}
    (e : Ev) (he : e ∈ source.S) (hl : e.1 ∈ source.groupLines w g)
    (hetime : e.2 ∈ Icc ((j:ℝ)*((2:ℝ)^T)⁻¹) (((j:ℝ)+1)*((2:ℝ)^T)⁻¹))
    (hβ : parentBranch P0 e = β) {t : ℝ}
    (ht : t ∈ Icc ((j:ℝ)*((2:ℝ)^T)⁻¹) (((j:ℝ)+1)*((2:ℝ)^T)⁻¹))
    (hnear : |t-e.2| ≤ (48*source.K^2)⁻¹) :
    Analytic.PhysicalGroupPoint B⁻¹ (P0-C (physicalGroupCenter a w g)) P0
      (Broad.parentPotentialPullback T j c u source.Pot)
      (2*a*w) (2*source.K) (branchSign β) source.K (Analytic.graphPoint e.1 t) := by
  have hK : 0 < source.K := by linarith [source.K_two]
  have hte := old_block_subset_unit T j hj hetime
  have htt := old_block_subset_unit T j hj ht
  obtain ⟨hlo,hhi,hbr⟩ := source.parent_hidden_regular_near hP0 hB e he hte htt hnear
  let Dt := eval (xp e.1 t) (pderiv 3 P0)
  have hlow : (2*source.K)⁻¹ ≤ |B⁻¹*Dt| := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hB)]
    calc (2*source.K)⁻¹ = B⁻¹*(B/(2*source.K)) := by field_simp
      _ ≤ B⁻¹*|Dt| := mul_le_mul_of_nonneg_left hlo (inv_nonneg.mpr hB.le)
  have hupp : |B⁻¹*Dt| ≤ 2*source.K := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hB)]
    calc B⁻¹*|Dt| ≤ B⁻¹*(source.K*B) :=
        mul_le_mul_of_nonneg_left hhi (inv_nonneg.mpr hB.le)
      _ = source.K := by field_simp
      _ ≤ 2*source.K := by linarith
  have hnonzero : Dt ≠ 0 := by
    intro hz
    have hp : 0 < B/(2*source.K) := by positivity
    change B/(2*source.K) ≤ |Dt| at hlo
    rw [hz,abs_zero] at hlo
    exact (not_lt_of_ge hlo) hp
  have hsign : 0 < Dt*branchSign β := by
    have hb : parentBranch P0 (e.1,t) = β := hbr.trans hβ
    cases β with
    | false =>
      have hn : ¬0<Dt := by
        intro hp
        change (if 0<Dt then true else false) = false at hb
        rw [if_pos hp] at hb
        contradiction
      have hneg : Dt < 0 := lt_of_le_of_ne (le_of_not_gt hn) hnonzero
      simpa [branchSign] using neg_pos.mpr hneg
    | true =>
      have hp : 0<Dt := by
        by_contra hn
        change (if 0<Dt then true else false) = true at hb
        rw [if_neg hn] at hb
        contradiction
      simpa [branchSign] using hp
  have hsign' : 0 < B⁻¹*Dt*branchSign β := by
    simpa only [mul_assoc] using mul_pos (inv_pos.mpr hB) hsign
  have hfit := source.group_lines_fit hw hζw g e.1 hl t ht
  change |eval (xp e.1 t) (P0-C (physicalGroupCenter a w g)) -
      eval (fun i:Fin 3 => xp e.1 t i.castSucc)
        (Broad.parentPotentialPullback T j c u source.Pot)| ≤ 2*a*w ∧ _
  simp only [map_sub, eval_C, pderiv_C, sub_zero,
    Broad.eval_parentPotentialPullback T j c u source.Pot (e.1,t)]
  refine ⟨?_,hsign',hlow,hupp,hlow,hupp,(source.point_bounds e he).2.2.1 t htt |>.1⟩
  convert hfit using 1 <;> congr 1 <;> ring

end PhysicalSource

end

end Submission.Obl.k4_physical_parent_potential_candidates
