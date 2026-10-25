-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceSchedule
import Submission.Obl.k4_finite_affine_parent_sources.SourceDensityMasks

/-!
# The prepared residual after removing exceptional sets

* `densMask_loss_upper`: the incidences outside a density mask (x0812's `densMask`) on a depth
  menu weigh at most the sum of the UPPER pure-density tails of the menu, i.e. exactly the
  quantities bounded by `LateFacts.pure`.
* `residual_after_removal`: removing from a half-mass residual any set of weighted original
  mass at most `(4κ)⁻¹` keeps weighted mass at least `(4κ)⁻¹`.

Written by x0891 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set

noncomputable section

/-- Outside the density mask, some menu depth has an upper pure-density exception. -/
theorem densMask_compl_subset_upper {G : ℕ} (g : ℝ → EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal)
    (Bw Nk τ : ℝ) (f : ℝ → ℝ) (r : Fin G → ℝ) :
    (densMask g Bw Nk τ f r)ᶜ ⊆ ⋃ j, {p | ENNReal.ofReal (Nk ^ (-f (r j) + τ)) <
      g (r j) (obs Bw (δ Nk (r j)) p)} := by
  intro p hp
  simp only [densMask, mem_compl_iff, mem_iInter, not_forall, mem_ofPred_eq, not_le] at hp
  obtain ⟨j, hj⟩ := hp
  exact mem_iUnion.mpr ⟨j, hj⟩

/-- **The density mask loss in upper tails** (the form of `LateFacts.pure`). -/
theorem densMask_loss_upper {W G : ℕ} (ω : Fin W → ℝ)
    (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))) (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (g : Fin W → ℝ → EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal) (B : Fin W → ℝ) (Nk τ : ℝ)
    (f : ℝ → ℝ) (r : Fin G → ℝ) :
    (∑ w, ENNReal.ofReal (ω w) * (((ν w).prod volume).restrict (E w))
      (densMask (g w) (B w) Nk τ f r)ᶜ) ≤
      ∑ j, k4_fixed_menu_density_pruning.upperTail Nk W ω ν E B f g τ (r j) := by
  unfold k4_fixed_menu_density_pruning.upperTail
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [← Finset.mul_sum]
  gcongr
  exact (measure_mono (densMask_compl_subset_upper (g w) (B w) Nk τ f r)).trans
    (measure_iUnion_fintype_le _ _)

section Path

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- **The residual after removal.** Removing from a half-mass terminal residual `H` any
measurable `X` of weighted original (`E`-restricted) mass at most `(4κ)⁻¹` keeps weighted mass
at least `(4κ)⁻¹`. -/
theorem residual_after_removal (hm : 0 < m) (H X : Fin W → Set Incidence)
    (hHT : ∀ w, H w ⊆ TerminalInc W p.C m p.lev p.world p.counted w)
    (hX : ∀ w, MeasurableSet (X w))
    (hmass : (1 / 2 : ENNReal) * (∑ w, ENNReal.ofReal (ω w) *
        (ν w).prod volume (TerminalInc W p.C m p.lev p.world p.counted w)) ≤
      ∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (H w))
    (hloss : (∑ w, ENNReal.ofReal (ω w) * (((ν w).prod volume).restrict (E w)) (X w)) ≤
      ENNReal.ofReal ((4 * p.κ)⁻¹)) :
    ENNReal.ofReal ((4 * p.κ)⁻¹) ≤
      ∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (H w \ X w) := by
  have hκ : 0 < p.κ := lt_of_lt_of_le zero_lt_one hp.one_le_slack
  have hres := hp.residual_mass_lower hm H hmass
  -- each world: H ⊆ (H \ X) ∪ (X ∩ E)
  have hHE : ∀ w, H w ⊆ E w := by
    intro w z hz
    obtain ⟨b, -, hbw, hzb⟩ := hHT w hz
    have := (hp.counted_support b z hzb).1
    rwa [hbw] at this
  have hsplit : (∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (H w)) ≤
      (∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (H w \ X w)) +
        ∑ w, ENNReal.ofReal (ω w) * (((ν w).prod volume).restrict (E w)) (X w) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun w _ => ?_
    rw [← mul_add]
    refine mul_le_mul' le_rfl ?_
    rw [Measure.restrict_apply (hX w)]
    calc (ν w).prod volume (H w)
        ≤ (ν w).prod volume ((H w \ X w) ∪ (X w ∩ E w)) := by
          apply measure_mono
          intro z hz
          by_cases hzX : z ∈ X w
          · exact Or.inr ⟨hzX, hHE w hz⟩
          · exact Or.inl ⟨hz, hzX⟩
      _ ≤ _ := measure_union_le _ _
  have h2 : ENNReal.ofReal ((4 * p.κ)⁻¹) + ENNReal.ofReal ((4 * p.κ)⁻¹) =
      ENNReal.ofReal ((2 * p.κ)⁻¹) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  have h3 : ENNReal.ofReal ((4 * p.κ)⁻¹) + ENNReal.ofReal ((4 * p.κ)⁻¹) ≤
      (∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (H w \ X w)) +
        ENNReal.ofReal ((4 * p.κ)⁻¹) := by
    rw [h2]
    exact hres.trans (hsplit.trans (add_le_add le_rfl hloss))
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp h3

end Path

end

end Submission.Obl.k4_finite_affine_parent_sources
