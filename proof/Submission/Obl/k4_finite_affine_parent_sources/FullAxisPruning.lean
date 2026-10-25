-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.MajorAxisFullness
import Submission.Obl.k4_finite_positive_mixed_cover_realization.CodedFamilies
import Submission.Obl.k4_scalar_true_terminal_lifting.RefinementData
import Submission.Obl.k4_true_forest_own_depth_preparation.LayerSums

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set
open Submission.Obl.k4_compatible_pair_frame_preparation.Construction
open scoped Classical

noncomputable section

/-- Delete deficient original counted labels simultaneously at eligible
path levels. The per-level angular charge is paid only once, with the
unchanged original world weights and full trajectory assignments.
Eligibility allows restricting to the early depths used by the model. -/
theorem prune_original_full_axes
    {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (Hset : Fin W → Set Incidence) (hHm : ∀ w, MeasurableSet (Hset w))
    (eligible : ℕ → Prop)
    (ρ H : ℝ) (hH : 0 < H) (hfull : 4 / H ≤ ρ * p.κ)
    (loss : ENNReal)
    (hbad : ∀ i : ℕ, i < m → eligible i →
      (∑ b, if p.lev b = i ∧ p.axisDeficient ρ b then
        ENNReal.ofReal (ω (p.world b)) * (ν (p.world b)).prod volume (p.counted b)
        else 0) ≤ loss) :
    ∃ H' : Fin W → Set Incidence,
      (∀ w, MeasurableSet (H' w) ∧ H' w ⊆ Hset w) ∧
      (∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (Hset w)) ≤
        (∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (H' w)) + (m : ENNReal) * loss ∧
      ∀ b, eligible (p.lev b) → (H' (p.world b) ∩ p.counted b).Nonempty →
        ¬p.axisDeficient ρ b ∧
          (((2 : ℝ) ^ p.T (p.lev b))⁻¹) / H ≤ r₁ (p.frame b) := by
  classical
  let Fbad : Fin p.C → Set Incidence := fun b =>
    if eligible (p.lev b) ∧ p.axisDeficient ρ b then p.counted b else ∅
  let bad : Fin W → Set Incidence :=
    Submission.Obl.k4_finite_positive_mixed_cover_realization.codedUnion p.world Fbad
  have hFbad (b : Fin p.C) : MeasurableSet (Fbad b) := by
    dsimp only [Fbad]
    split_ifs
    · exact hp.counted_measurable b
    · exact MeasurableSet.empty
  have hbadm (w : Fin W) : MeasurableSet (bad w) :=
    Submission.Obl.k4_finite_positive_mixed_cover_realization.codedUnion_measurable
      p.world Fbad hFbad w
  let mass : Fin p.C → ENNReal := fun b =>
    ENNReal.ofReal (ω (p.world b)) * (ν (p.world b)).prod volume (Fbad b)
  have hlevel (i : ℕ) (hi : i < m) :
      (∑ b, if p.lev b = i then mass b else 0) ≤ loss := by
    by_cases he : eligible i
    · convert hbad i hi he using 1
      apply Finset.sum_congr rfl
      intro b _
      by_cases hd : p.axisDeficient ρ b <;> by_cases hl : p.lev b = i <;>
        simp [mass, Fbad, hd, hl, he]
    · have hz : (∑ b, if p.lev b = i then mass b else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro b _
        by_cases hl : p.lev b = i <;> simp [mass, Fbad, hl, he]
      rw [hz]
      exact zero_le
  have htotal : (∑ b, mass b) ≤ (m : ENNReal) * loss :=
    Submission.Obl.k4_true_forest_own_depth_preparation.sum_le_depth_mul
      p.lev (fun b => hp.label_level b) mass loss hlevel
  have hbadMass : (∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (bad w)) ≤
      (m : ENNReal) * loss := by
    exact (Submission.Obl.k4_scalar_true_terminal_lifting.weighted_union_mass_le_sum
      (fun w => (ν w).prod volume) (fun w => ENNReal.ofReal (ω w)) p.world Fbad).trans htotal
  let H' : Fin W → Set Incidence := fun w => Hset w \ bad w
  have hH' (w : Fin W) : MeasurableSet (H' w) := (hHm w).diff (hbadm w)
  refine ⟨H', fun w => ⟨hH' w, sdiff_subset⟩, ?_, ?_⟩
  · calc
      _ ≤ ∑ w, ENNReal.ofReal (ω w) *
          ((ν w).prod volume (H' w) + (ν w).prod volume (bad w)) := by
        apply Finset.sum_le_sum
        intro w _
        exact mul_le_mul' le_rfl
          ((measure_mono (show Hset w ⊆ H' w ∪ bad w by
            intro z hz
            by_cases hb : z ∈ bad w
            · exact Or.inr hb
            · exact Or.inl ⟨hz, hb⟩)).trans (measure_union_le _ _))
      _ = (∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (H' w)) +
          ∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (bad w) := by
        simp only [mul_add, Finset.sum_add_distrib]
      _ ≤ _ := add_le_add le_rfl hbadMass
  · intro b he hne
    have hkeep : ¬p.axisDeficient ρ b := by
      intro hb
      obtain ⟨z, hzH, hzF⟩ := hne
      apply hzH.2
      exact ⟨b, rfl, by simpa [Fbad, he, hb] using hzF⟩
    exact ⟨hkeep, p.major_fullness_of_not_deficient b ρ H hH hfull hkeep⟩

end

end Submission.Obl.k4_finite_affine_parent_sources
