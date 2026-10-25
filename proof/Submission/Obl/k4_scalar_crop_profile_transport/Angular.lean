import Submission.Obl.k4_scalar_crop_profile_transport.Affine
import Submission.Obl.k4_scalar_crop_profile_transport.Geometry
import Submission.Obl.k4_scalar_crop_profile_transport.TwoShift

/-!
# Joint observations of the scalar crop worlds

On the source line, the crop world's joint observation at velocity width `N^(-u)` is the source
pure observation together with the bin `⌊(l₁/a - z₁)/N^(-u)⌋`, `a = N^(-u₀)`. This bin is the
source velocity bin at the finer width `N^(-(u₀+u)) = a * N^(-u)`, shifted by
`m = ⌊-z₁/N^(-u)⌋` or by `m + 1` (`cropAug_shift`). Hence the crop world's joint law is
absolutely continuous (`crop_joint_ac`), and any of its densities pulls back to a density of the
source restriction (`raw_joint_density_law`).
-/

noncomputable section

namespace Submission.Obl.k4_scalar_crop_profile_transport

open MeasureTheory Set Filter
open scoped ENNReal

local instance : SigmaFinite BaseRef := by unfold BaseRef; infer_instance
local instance : SigmaFinite JointRef := by unfold JointRef; infer_instance

/-- The crop world's velocity bin at width `w`, read on the source line. -/
def cropBin (a w : ℝ) (z : Fin 2 → ℤ) (p : Inc) : ℤ := ⌊(p.1.2 1 / a - (z 1 : ℝ)) / w⌋

/-- The source pure observation together with the crop world's velocity bin. -/
def CropAug (N r u a : ℝ) (z : Fin 2 → ℤ) (p : Inc) : Joint :=
  (Obs N r p, cropBin a (N ^ (-u)) z p)

lemma measurable_CropAug (N r u a : ℝ) (z : Fin 2 → ℤ) : Measurable (CropAug N r u a z) := by
  unfold CropAug cropBin
  exact (measurable_Obs N r).prodMk (by fun_prop)

/-- The affine crop coordinates on joint observations. -/
def jointEquiv (a : ℝ) (ha : a ≠ 0) (z : Fin 2 → ℤ) : Joint ≃ᵐ Joint :=
  (obsEquiv a ha z).prodCongr (MeasurableEquiv.refl ℤ)

lemma aug_crop (a : ℝ) (ha : a ≠ 0) (z : Fin 2 → ℤ) (N r u : ℝ) (p : Inc) :
    Aug N r u (CropInc a z p) = jointEquiv a ha z (CropAug N r u a z p) := by
  change (Obs N r (CropInc a z p), ⌊(CropInc a z p).1.2 1 / N ^ (-u)⌋) =
    (obsEquiv a ha z (Obs N r p), cropBin a (N ^ (-u)) z p)
  rw [obs_crop a ha z N r p]
  simp [CropInc, Crop, cropBin]

lemma map_joint_reference (a : ℝ) (ha : 0 < a) (z : Fin 2 → ℤ) :
    JointRef.map (jointEquiv a ha.ne' z) = ENNReal.ofReal a • JointRef := by
  unfold JointRef
  exact k4_dyadic_crop_affine_laws.Framework.map_prod_count_equiv _ _ _ _
    (map_obs_reference a ha z)

/-- The supplied lift writes the crop world's joint law through the source restriction. -/
lemma map_aug_lift (a p : ℝ) (ha : a ≠ 0) (hp : 0 < p) (z : Fin 2 → ℤ)
    (N r u : ℝ) (μ₀ μ : Measure Inc)
    (hlift : ∀ Z, MeasurableSet Z → ENNReal.ofReal p * μ Z =
      μ₀ {b | b.1 ∈ Cell a z ∧ CropInc a z b ∈ Z}) :
    μ.map (Aug N r u) = (ENNReal.ofReal p)⁻¹ •
      ((μ₀.restrict (Cell a z ×ˢ univ)).map (CropAug N r u a z)).map (jointEquiv a ha z) := by
  rw [lift_map_eq a p hp z μ₀ μ hlift,
    Measure.map_smul _ (measurable_Aug N r u).aemeasurable,
    Measure.map_map (measurable_Aug N r u) (measurable_CropInc a z),
    show Aug N r u ∘ CropInc a z = jointEquiv a ha z ∘ CropAug N r u a z
      from funext (aug_crop a ha z N r u),
    ← Measure.map_map (jointEquiv a ha z).measurable (measurable_CropAug N r u a z)]

/-- A cropped joint density gives a density of the source restriction with crop labels. -/
lemma raw_joint_density_law (a p : ℝ) (ha : 0 < a) (hp : 0 < p) (z : Fin 2 → ℤ)
    (N r u : ℝ) (μ₀ μ : Measure Inc) (G : Joint → ENNReal) (hG : Measurable G)
    (hlift : ∀ Z, MeasurableSet Z → ENNReal.ofReal p * μ Z =
      μ₀ {b | b.1 ∈ Cell a z ∧ CropInc a z b ∈ Z})
    (hlaw : μ.map (Aug N r u) = JointRef.withDensity G) :
    (μ₀.restrict (Cell a z ×ˢ univ)).map (CropAug N r u a z) =
      JointRef.withDensity (fun b => (ENNReal.ofReal p / ENNReal.ofReal a) *
        G (jointEquiv a ha.ne' z b)) := by
  apply k4_crop_base_finite_tail.BaseTransport.pullback_density_law
    (jointEquiv a ha.ne' z) JointRef JointRef (ENNReal.ofReal a) (ENNReal.ofReal p)
    (ENNReal.ofReal_ne_zero_iff.mpr ha) ENNReal.ofReal_ne_top
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top
    (map_joint_reference a ha z)
    ((μ₀.restrict (Cell a z ×ˢ univ)).map (CropAug N r u a z)) G hG
  rw [← map_aug_lift a p ha.ne' hp z N r u μ₀ μ hlift]
  exact hlaw

lemma floor_sub_cases (X c : ℝ) :
    ⌊X - c⌋ = ⌊X⌋ + ⌊-c⌋ ∨ ⌊X - c⌋ = ⌊X⌋ + (⌊-c⌋ + 1) := by
  have h1 : ⌊X⌋ + ⌊-c⌋ ≤ ⌊X - c⌋ := by
    rw [sub_eq_add_neg]
    exact Int.le_floor_add _ _
  have h2 : ⌊X - c⌋ - 1 ≤ ⌊X⌋ + ⌊-c⌋ := by
    rw [sub_eq_add_neg]
    exact Int.le_floor_add_floor _ _
  omega

/-- The crop world's velocity bin is a shift of the finer source velocity bin. -/
lemma cropAug_shift {N : ℝ} (hN : 0 < N) (r u₀ u : ℝ) (z : Fin 2 → ℤ) (p : Inc) :
    CropAug N r u (N ^ (-u₀)) z p =
        labelShift ⌊-((z 1 : ℝ) / N ^ (-u))⌋ (Aug N r (u₀ + u) p) ∨
      CropAug N r u (N ^ (-u₀)) z p =
        labelShift (⌊-((z 1 : ℝ) / N ^ (-u))⌋ + 1) (Aug N r (u₀ + u) p) := by
  have ha : 0 < N ^ (-u₀) := Real.rpow_pos_of_pos hN _
  have hw : 0 < N ^ (-u) := Real.rpow_pos_of_pos hN _
  have hprod : N ^ (-u₀) * N ^ (-u) = N ^ (-(u₀ + u)) := by
    rw [← Real.rpow_add hN]
    ring_nf
  have hX : (p.1.2 1 / N ^ (-u₀) - (z 1 : ℝ)) / N ^ (-u) =
      p.1.2 1 / N ^ (-(u₀ + u)) - (z 1 : ℝ) / N ^ (-u) := by
    rw [← hprod]
    field_simp
  rcases floor_sub_cases (p.1.2 1 / N ^ (-(u₀ + u))) ((z 1 : ℝ) / N ^ (-u)) with h | h
  · left
    refine Prod.ext rfl ?_
    change ⌊(p.1.2 1 / N ^ (-u₀) - (z 1 : ℝ)) / N ^ (-u)⌋ =
      ⌊p.1.2 1 / N ^ (-(u₀ + u))⌋ + ⌊-((z 1 : ℝ) / N ^ (-u))⌋
    rw [hX, h]
  · right
    refine Prod.ext rfl ?_
    change ⌊(p.1.2 1 / N ^ (-u₀) - (z 1 : ℝ)) / N ^ (-u)⌋ =
      ⌊p.1.2 1 / N ^ (-(u₀ + u))⌋ + (⌊-((z 1 : ℝ) / N ^ (-u))⌋ + 1)
    rw [hX, h]

/-- The crop world's joint observation law is absolutely continuous whenever the source joint
law at the finer velocity width has a density. -/
lemma crop_joint_ac {N : ℝ} (hN : 0 < N) (p : ℝ) (hp : 0 < p) (z : Fin 2 → ℤ)
    (r u₀ u : ℝ) (μ₀ μ : Measure Inc)
    (hlift : ∀ Z, MeasurableSet Z → ENNReal.ofReal p * μ Z =
      μ₀ {b | b.1 ∈ Cell (N ^ (-u₀)) z ∧ CropInc (N ^ (-u₀)) z b ∈ Z})
    (H : Joint → ENNReal) (hHlaw : μ₀.map (Aug N r (u₀ + u)) = JointRef.withDensity H) :
    μ.map (Aug N r u) ≪ JointRef := by
  have ha : 0 < N ^ (-u₀) := Real.rpow_pos_of_pos hN _
  rw [map_aug_lift (N ^ (-u₀)) p ha.ne' hp z N r u μ₀ μ hlift]
  have hsrc : (μ₀.restrict (Cell (N ^ (-u₀)) z ×ˢ univ)).map (Aug N r (u₀ + u)) ≪
      BaseRef.prod Measure.count := by
    have hle : (μ₀.restrict (Cell (N ^ (-u₀)) z ×ˢ univ)).map (Aug N r (u₀ + u)) ≤
        μ₀.map (Aug N r (u₀ + u)) :=
      Measure.map_mono Measure.restrict_le_self (measurable_Aug N r (u₀ + u))
    refine (Measure.absolutelyContinuous_of_le hle).trans ?_
    rw [hHlaw]
    exact withDensity_absolutelyContinuous _ _
  have hcrop := two_shift_absolutelyContinuous BaseRef _ (measurable_Aug N r (u₀ + u))
    (measurable_CropAug N r u (N ^ (-u₀)) z) hsrc _ (fun q => cropAug_shift hN r u₀ u z q)
  have hmap := hcrop.map (jointEquiv (N ^ (-u₀)) ha.ne' z).measurable
  change _ ≪ JointRef.map _ at hmap
  rw [map_joint_reference _ ha z] at hmap
  exact Measure.smul_absolutelyContinuous.trans (hmap.trans Measure.smul_absolutelyContinuous)

end Submission.Obl.k4_scalar_crop_profile_transport
