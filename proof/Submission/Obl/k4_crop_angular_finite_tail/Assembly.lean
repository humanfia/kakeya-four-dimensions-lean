import Submission.Obl.k4_crop_angular_finite_tail.TailTransfer
import Submission.Obl.k4_crop_angular_finite_tail.RawDensity
import Submission.Obl.k4_crop_angular_finite_tail.Coarsening

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_crop_angular_finite_tail

open Submission.Obl.k4_profile_density_bounds (width observe selected reference)

/-- Finite angular tail transport through exact dyadic conditional crops. -/
theorem angular_finite_tail (n r u₀ u : ℝ)
    (ν₀ : Measure Line) [IsProbabilityMeasure ν₀] (E₀ : Set State)
    (w : ℕ) (p : Fin w → ℝ) (q : Fin w → Fin 4 → ℤ)
    (ν : Fin w → Measure Line) (E : Fin w → Set State)
    (g : Fin w → Observation → ENNReal) (H : Observation → ENNReal)
    (hn : 1 ≤ n) (hu₀ : 0 ≤ u₀) (hu : 0 ≤ u)
    (hE₀ : MeasurableSet E₀) (htime : E₀ ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hq : Function.Injective q)
    (hcrop : ∀ γ, 0 < p γ ∧
      ν γ = (ENNReal.ofReal (p γ))⁻¹ • (ν₀.restrict (cropBox (width n u₀) (q γ))).map
        (cropLine (width n u₀) (q γ)) ∧
      E γ = cropState (width n u₀) (q γ) '' (E₀ ∩ (cropBox (width n u₀) (q γ) ×ˢ univ)))
    (hH : Measurable H)
    (hsource : (selected ν₀ E₀).map (observe n r (u₀ + u)) = reference.withDensity H)
    (hg : ∀ γ, Measurable (g γ) ∧
      (selected (ν γ) (E γ)).map (observe n r u) = reference.withDensity (g γ))
    (lo hi δ : ℝ) (hlo : 0 < lo) (hhi : 0 < hi) (hδ : 0 < δ) :
    (∑ γ, ENNReal.ofReal (p γ) * (selected (ν γ) (E γ))
      {x | g γ (observe n r u x) < ENNReal.ofReal ((width n u₀ ^ 2 / p γ) * δ * lo) ∨
        ENNReal.ofReal ((width n u₀ ^ 2 / p γ) * hi / δ) < g γ (observe n r u x)}) ≤
      (selected ν₀ E₀) {x | H (observe n r (u₀ + u) x) < ENNReal.ofReal lo ∨
        ENNReal.ofReal hi < H (observe n r (u₀ + u) x)} + ENNReal.ofReal (32 * δ) := by
  classical
  letI : SigmaFinite reference := by unfold reference; infer_instance
  let μ := selected ν₀ E₀
  let a := width n u₀
  have ha : 0 < a := Submission.Obl.k4_profile_density_bounds.width_pos n u₀
  obtain ⟨d, hd₁, hd, _⟩ := width_product hn hu₀ hu
  let Φ := observeWidth n r (a * width n u)
  have hΦ : Measurable Φ := measurable_observeWidth _ _ _
  have hconj : Φ = coarsenObservation d ∘ observe n r (u₀ + u) := by
    funext x
    exact observeWidth_product hn hu₀ hu hd r x
  let h : VelocityBin → VelocityBin := fun v j => v j / (2 : ℤ)^d
  let K := Submission.Obl.k4_native_grid_profile_extension.fiberDensity h H
  have hK : Measurable K :=
    Submission.Obl.k4_native_grid_profile_extension.measurable_fiberDensity h H hH
  have hfull : μ.map Φ = reference.withDensity K := by
    rw [hconj, ← Measure.map_map (measurable_coarsenObservation d)
      (Submission.Obl.k4_profile_density_bounds.measurable_observe _ _ _), hsource]
    exact map_coarsen_withDensity d H hH
  let S : Fin w → Set State := fun γ => cropBox a (q γ) ×ˢ univ
  have hS (γ : Fin w) : MeasurableSet (S γ) :=
    (measurableSet_cropBox _ _).prod MeasurableSet.univ
  have hdisj : Pairwise (fun γ γ' => Disjoint (S γ) (S γ')) := by
    intro γ γ' hne
    rw [Set.disjoint_left]
    intro x hx hx'
    exact Set.disjoint_left.mp (cropBox_disjoint a (fun heq => hne (hq heq))) hx.1 hx'.1
  let e (γ : Fin w) := observationCropEquiv ha.ne' (q γ) (height n u)
  let D (γ : Fin w) (z : Observation) :=
    (ENNReal.ofReal (p γ) / ENNReal.ofReal (a^2)) * g γ (e γ z)
  have hD (γ : Fin w) : Measurable (D γ) :=
    measurable_const.mul ((hg γ).1.comp (e γ).measurable)
  have hselected (γ : Fin w) : selected (ν γ) (E γ) =
      (ENNReal.ofReal (p γ))⁻¹ • (μ.restrict (S γ)).map (cropState a (q γ)) := by
    rw [(hcrop γ).2.1, (hcrop γ).2.2]
    exact selected_crop ha.ne' (q γ) ν₀ E₀ _
  have hpart (γ : Fin w) : (μ.restrict (S γ)).map Φ = reference.withDensity (D γ) := by
    apply raw_angular_density_law hn hu₀ hu hd (q γ) r (p γ) (hcrop γ).1
      (μ.restrict (S γ)) (g γ) (hg γ).1
    rw [← hselected γ]
    exact (hg γ).2
  have ht : ∀ᵐ x ∂μ, x.2 ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [ae_restrict_mem hE₀] with x hx
    exact (htime hx).2
  have hlow := crop_low_ratio_sum hn hu₀ hu r μ ht q hq K hK hfull D hD hpart
    (ENNReal.ofReal δ)
  have htail := sum_restricted_density_tails_le reference μ S hS hdisj Φ hΦ D hD K hK
    hpart hfull (ENNReal.ofReal δ) (ENNReal.ofReal lo) (ENNReal.ofReal hi)
    (4 * ENNReal.ofReal δ * μ univ) (ENNReal.ofReal_ne_zero_iff.mpr hδ)
    ENNReal.ofReal_ne_top hlow
  have hcoarse := coarsening_tail_bound μ (observe n r (u₀ + u))
    (Submission.Obl.k4_profile_density_bounds.measurable_observe _ _ _) hd₁ H K hH hK
    hsource (hconj ▸ hfull) (ENNReal.ofReal δ) (ENNReal.ofReal lo) (ENNReal.ofReal hi)
  have hmass : μ univ ≤ 1 :=
    Submission.Obl.k4_profile_density_bounds.selected_mass_le_one ν₀ E₀ htime
  have hsum : (∑ γ, ENNReal.ofReal (p γ) * (selected (ν γ) (E γ))
      {x | g γ (observe n r u x) < ENNReal.ofReal ((a ^ 2 / p γ) * δ * lo) ∨
        ENNReal.ofReal ((a ^ 2 / p γ) * hi / δ) < g γ (observe n r u x)}) =
      ∑ γ, (μ.restrict (S γ)) {x | D γ (Φ x) < ENNReal.ofReal δ * ENNReal.ofReal lo ∨
        ENNReal.ofReal hi / ENNReal.ofReal δ < D γ (Φ x)} := by
    apply Finset.sum_congr rfl
    intro γ _
    rw [(hcrop γ).2.1, (hcrop γ).2.2]
    have hh := crop_angular_bad_mass_eq hn hu₀ hu hd (q γ) r (p γ) (hcrop γ).1
      ν₀ E₀ (g γ) lo hi δ
    simpa only [ENNReal.ofReal_mul hδ.le, ENNReal.ofReal_div_of_pos hδ] using hh
  rw [hsum]
  calc
    _ ≤ μ {x | K (Φ x) < ENNReal.ofReal lo ∨ ENNReal.ofReal hi < ENNReal.ofReal δ * K (Φ x)} +
        4 * ENNReal.ofReal δ * μ univ := htail
    _ ≤ (μ {x | H (observe n r (u₀ + u) x) < ENNReal.ofReal lo ∨
        ENNReal.ofReal hi < H (observe n r (u₀ + u) x)} +
        ENNReal.ofReal δ * 4 * μ univ) + 4 * ENNReal.ofReal δ * μ univ := by
      apply add_le_add_left
      simpa only [hconj, Function.comp_apply] using hcoarse
    _ ≤ μ {x | H (observe n r (u₀ + u) x) < ENNReal.ofReal lo ∨
        ENNReal.ofReal hi < H (observe n r (u₀ + u) x)} + ENNReal.ofReal (32 * δ) := by
      rw [add_assoc]
      apply add_le_add_right
      calc
        _ = 8 * ENNReal.ofReal δ * μ univ := by ring
        _ ≤ 8 * ENNReal.ofReal δ * 1 := mul_le_mul' le_rfl hmass
        _ ≤ 32 * ENNReal.ofReal δ := by simp only [mul_one]; gcongr; norm_num
        _ = ENNReal.ofReal (32 * δ) := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num

end Submission.Obl.k4_crop_angular_finite_tail
