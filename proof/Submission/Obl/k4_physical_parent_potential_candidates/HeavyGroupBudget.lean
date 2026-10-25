-- Adapted from this LOT tree, o286, branch x1021, commit 128bb7e2,
-- Submission/Obl/k4_native_field_original_candidates/HeavyGroupBudget.lean,
-- and its cell_count_floor_of_prior_efficiency from InterceptFilling.lean.
-- Original session x1021. Accepted efficient selection remains imported.
import Submission.Obl.k4_scalar_capped_heavy_potential.EfficientSelection

open Set MeasureTheory

namespace Submission.Obl.k4_physical_parent_potential_candidates

/-- A group which retains an `α` fraction of its own original line prior
has the same base-cell floor, independently of its absolute group mass. -/
theorem cell_count_floor_of_prior_efficiency {m : ℕ}
    {η α c V M Q : ℝ} (hη : 0 ≤ η) (hα : 0 ≤ α) (hM : 0 < M)
    (hefficient : α*M ≤ Q)
    (hfilling : η*Q^3 ≤ (m : ℝ)*V*c^3*M^3) :
    η*α^3 ≤ (m : ℝ)*V*c^3 := by
  have hq : 0 ≤ Q := (mul_nonneg hα hM.le).trans hefficient
  have hpower := pow_le_pow_left₀ (mul_nonneg hα hM.le) hefficient 3
  have hbound := (mul_le_mul_of_nonneg_left hpower hη).trans hfilling
  rw [mul_pow] at hbound
  apply (mul_le_mul_iff_left₀ (pow_pos hM 3)).mp
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hbound


/-- Cancelling a group's own original prior and the old block length
leaves a cubic coarse-cell floor. -/
theorem original_cubic_cell_count_floor {m : ℕ} {η h p K C mass prior : ℝ}
    (hη : 0 ≤ η) (hh : 0 < h) (hp : 0 < p) (hK : 0 < K) (hC : 0 < C)
    (hprior : 0 < prior) (hefficient : h/(8*K)*prior ≤ mass)
    (hfilling : η*mass^3 ≤ (m : ℝ)*C^2*(2*h*p)^3*prior^3) :
    η/(4096*C^2*K^3*p^3) ≤ (m : ℝ) := by
  have hhfill := cell_count_floor_of_prior_efficiency (m := m) hη
    (show 0 ≤ h/(8*K) by positivity) hprior hefficient hfilling
  have hscale : 0 < (h/(8*K))^3 := by positivity
  have hquot : η ≤ ((m : ℝ)*C^2*(2*h*p)^3)/(h/(8*K))^3 :=
    (le_div_iff₀ hscale).mpr (by simpa only [mul_comm] using hhfill)
  have heq : ((m : ℝ)*C^2*(2*h*p)^3)/(h/(8*K))^3 =
      (m : ℝ)*(4096*C^2*K^3*p^3) := by
    field_simp [hh.ne', hK.ne']
    ring
  rw [heq] at hquot
  exact (div_le_iff₀ (by positivity : 0 < 4096*C^2*K^3*p^3)).mpr hquot

/-- The original joint census and a three-dimensional cell floor select
one efficient intercept group at the exact width gain `w^d`. -/
theorem three_dimensional_heavy_group_selection {ι β : Type*}
    (F : Finset ι) (mass prior : ι → ℝ) (cells : ι → Finset β)
    {h K C p w d η priorTotal : ℝ}
    (hh : 0 < h) (hK : 0 < K) (hC : 0 < C) (hp : 0 < p) (hw : 0 < w)
    (hη : 0 < η) (hprior : 0 < priorTotal)
    (hmass0 : ∀ g ∈ F, 0 ≤ mass g) (hprior0 : ∀ g ∈ F, 0 ≤ prior g)
    (hpriorsum : ∑ g ∈ F, prior g ≤ priorTotal)
    (hmass : h*priorTotal/(4*K) ≤ ∑ g ∈ F, mass g)
    (hfloor : ∀ g ∈ F, 0 < mass g → h/(8*K)*prior g ≤ mass g →
      η/(4096*C^2*K^3*p^3) ≤ (cells g).card)
    (hbudget : (∑ g ∈ F, ((cells g).card : ℝ)) ≤ 243*K/(p^3*w^d)) :
    ∃ g ∈ F, 0 < mass g ∧ h/(8*K)*prior g ≤ mass g ∧
      h*priorTotal*η*w^d/(7962624*C^2*K^5) ≤ mass g := by
  have hmasspos : h/(8*K)*priorTotal < h*priorTotal/(4*K) := by
    have hpos : 0 < h*priorTotal/(8*K) := by positivity
    have heq : h*priorTotal/(4*K) = 2*(h*priorTotal/(8*K)) := by ring
    rw [heq]
    nlinarith [show h/(8*K)*priorTotal = h*priorTotal/(8*K) by ring]
  obtain ⟨g, hg, hmg, heff, hheavy⟩ :=
    Submission.Obl.k4_scalar_capped_heavy_potential.efficient_heavy_group_of_cell_budget
      F mass prior cells (by positivity : 0 ≤ h/(8*K)) hmasspos
      (by positivity : 0 < η/(4096*C^2*K^3*p^3))
      hmass0 hprior0 hpriorsum hmass hfloor hbudget
  refine ⟨g, hg, hmg, heff, ?_⟩
  have hT : 0 < 243*K/(p^3*w^d) := by positivity
  have hquot : ((h*priorTotal/(4*K)-h/(8*K)*priorTotal)*
      (η/(4096*C^2*K^3*p^3)))/(243*K/(p^3*w^d)) ≤ mass g :=
    (div_le_iff₀ hT).mpr (by simpa only [mul_comm] using hheavy)
  convert hquot using 1 <;>
    field_simp [hK.ne', hC.ne', hp.ne', (Real.rpow_pos_of_pos hw d).ne'] <;> ring

end Submission.Obl.k4_physical_parent_potential_candidates
