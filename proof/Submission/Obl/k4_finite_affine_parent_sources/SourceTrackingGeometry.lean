-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceLabelGeometry
import Submission.Obl.k4_finite_affine_parent_sources.SourceTrackingNumerics
import Submission.Obl.k4_finite_affine_parent_sources.OriginalScaleBounds

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Submission.Lib.K4XInterface
open Submission.Obl.k4_compatible_pair_frame_preparation.Construction

noncomputable section

namespace SourceData

variable {W : ℕ} {p : PathData W} (D : SourceData p)

/-- Fullness of the original parent and every full old label met by the
selected incidences. This is preserved by subsequent incidence pruning. -/
def FullAxes (n : ℕ) (ρaxis : ℝ) : Prop :=
  ¬p.axisDeficient ρaxis D.parent ∧
    ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 →
      ∀ i : Fin (p.activeCount D.Hm (D.depth s)), ¬p.axisDeficient ρaxis (D.old s i)

/-- An original-axis mask continues to control every model formed from
a smaller nonempty incidence set. Only the model's eligible levels are used. -/
theorem fullAxes_of_mask (n : ℕ) (ρaxis : ℝ) (eligible : ℕ → Prop)
    (G : Set Incidence) (hSG : D.S ⊆ G) (hne : D.S.Nonempty)
    (hparent : D.S ⊆ p.counted D.parent)
    (heParent : eligible D.i₀)
    (heDepth : ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 → eligible (D.depth s))
    (hgood : ∀ b : Fin p.C, p.world b = D.w₀ → eligible (p.lev b) →
      (G ∩ p.counted b).Nonempty → ¬p.axisDeficient ρaxis b) :
    D.FullAxes n ρaxis := by
  refine ⟨?_, ?_⟩
  · apply hgood D.parent rfl heParent
    obtain ⟨z, hz⟩ := hne
    exact ⟨z, hSG hz, hparent hz⟩
  · intro s hslo hshi i
    obtain ⟨hw, z, hzS, hzF⟩ := D.old_world s i
    apply hgood (D.old s i) hw
    · rw [D.old_level s i]
      exact heDepth s hslo hshi
    · exact ⟨z, hSG hzS, hzF⟩

section Valid

variable {m Mp Dp : ℕ} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- Cumulative narrowness gives the parent's normalized physical area,
with the two original profile errors displayed. -/
theorem parent_normalized_area (hNk : 1 ≤ Nk) :
    |(p.frame D.parent).det| ≤
      D.q₀ ^ 2 * Nk ^ (-((ℓ * sg D.i₀ - 2 * δ₀) * L)) := by
  have hb := normalized_area_of_cumulative_narrowness Nk (p.nw D.i₀)
    (ℓ * sg D.i₀ * L) (δ₀ * L) |(p.frame D.parent).det| (p.T D.i₀) hNk
    (hp.narrowness D.parent).2 (hp.level_bounds D.i₀ (hp.label_level D.parent)).2.2.2.2.1
  have heq : -(ℓ * sg D.i₀ * L - 2 * (δ₀ * L)) = -((ℓ * sg D.i₀ - 2 * δ₀) * L) := by ring
  simpa only [q₀, heq] using hb

/-- The actual source schedule and a global original-axis mask supply
all geometric hypotheses of the tracking wrapper. -/
theorem trackingGeometry_of_full_axes
    (hNk : 1 ≤ Nk) (hℓ : 0 ≤ ℓ) (hL : 0 ≤ L) (hm : 0 < m)
    (n : ℕ) (unit mesh β H : ℝ) (hu : 0 ≤ unit) (hβ : 0 ≤ β)
    (hsmall : 1000 * β ≤ ℓ) (hparent : unit ≤ sg D.i₀)
    (hδ : 4 * δ₀ ≤ unit * β)
    (hmesh0 : 0 ≤ mesh) (hmesh : ∀ i, i + 1 < m → sg (i + 1) - sg i ≤ mesh)
    (hroom : sg D.i₀ + unit ≤ sg (m - 1))
    (hdepth : D.depth = sourceDepth m sg D.i₀ unit)
    (hframe : D.D₀ = MajorFrame.frame (p.frame D.parent))
    (hH : H = Nk ^ (unit * L * β)) (hHone : 1 ≤ H)
    (hslack : 18 * p.κ ≤ H) (hmodel : 16 * H ^ 4 ≤ D.K)
    (hconstant : 4 ≤ Nk ^ ((unit * L * β) / 2))
    (hdet : 4 * δ₀ + ℓ * mesh ≤ unit * β)
    (haxes : D.FullAxes n (Nk ^ (-((unit * L * β) / 2)))) :
    D.TrackingGeometry n ℓ unit Nk L H := by
  have hN0 : 0 < Nk := lt_of_lt_of_le zero_lt_one hNk
  have hH0 : 0 < H := zero_lt_one.trans_le hHone
  have haxis : 4 / H ≤ Nk ^ (-((unit * L * β) / 2)) * p.κ := by
    rw [hH]
    exact tracking_axis_fullness_budget Nk p.κ (unit * L * β) hNk hp.one_le_slack hconstant
  have hparentFull := p.major_fullness_of_not_deficient D.parent
    (Nk ^ (-((unit * L * β) / 2))) H hH0 haxis haxes.1
  have hparentArea : |(p.frame D.parent).det| ≤ D.q₀ ^ 2 / (2 * H ^ 3) := by
    have hmargin := tracking_parent_area_margin β ℓ unit (sg D.i₀) δ₀ L
      hβ hℓ hu hL hsmall hparent hδ
    have ha := tracking_parent_area_budget Nk D.q₀ (unit * L * β)
      ((ℓ * sg D.i₀ - 2 * δ₀) * L) |(p.frame D.parent).det| hNk hmargin hconstant
      (D.parent_normalized_area hp hNk)
    simpa only [← hH] using ha
  have hfactor : Nk ^ ((4 * δ₀ + ℓ * mesh) * L) ≤ H := by
    rw [hH]
    apply Real.rpow_le_rpow_of_exponent_le hNk
    have hh := mul_le_mul_of_nonneg_right hdet hL
    nlinarith only [hh]
  refine ⟨hHone, hslack, hmodel, hparentFull, hparentArea, ?_, ?_⟩
  · intro s hslo hshi i
    exact p.major_fullness_of_not_deficient (D.old s i)
      (Nk ^ (-((unit * L * β) / 2))) H hH0 haxis (haxes.2 s hslo hshi i)
  · intro s hslo hshi i
    have hi₀ : D.i₀ < m := hp.label_level D.parent
    have hs0 : 0 ≤ s := (inv_nonneg.mpr (Nat.cast_nonneg n)).trans hslo
    have hnom := sourceDepth_nominal hm hi₀ hu hmesh0 hmesh hroom hs0 hshi
    rw [← hdepth] at hnom
    have hnom' : sg (D.depth s) ≤ sg (p.lev D.parent) + unit * s ∧
        sg (p.lev D.parent) + unit * s ≤ sg (D.depth s) + mesh := hnom
    have hgrid : |sg (p.lev (D.old s i)) - sg (p.lev D.parent) - unit * s| ≤ mesh := by
      rw [D.old_level s i, abs_le]
      constructor <;> linarith [hnom'.1, hnom'.2]
    have hb := hp.relative_native_determinant_of_grid hNk hℓ hL D.parent (D.old s i)
      unit s mesh H hgrid hfactor
    simpa only [← hframe, q₀, i₀] using hb.2

end Valid

end SourceData

end

end Submission.Obl.k4_finite_affine_parent_sources
