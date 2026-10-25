-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceTrackingGeometry

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Submission.Lib.K4XInterface

noncomputable section

namespace SourceData

variable {W : ℕ} {p : PathData W} (D : SourceData p)

section Valid

variable {m Mp Dp : ℕ} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- All tracking coefficients of a prepared source, uniformly over its
full old labels, after original-axis pruning. Only a single eventual
constant bound and the displayed small path exponent remain numerical inputs. -/
theorem tracks_of_full_axes
    (hNk : 2 ≤ Nk) (hℓ : 0 < ℓ) (hL : 0 < L)
    (n Mc : ℕ) (d₁ ρ gain ε unit β τ : ℝ)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1 / 4) (hε : 0 < ε)
    (hunit : 0 < unit) (hunitβ : unit * β ≤ 1) (hβ : 0 < β)
    (hβmodel : 5 * β ≤ ρ / (1000000 * ((n : ℝ) + 1)))
    (hβℓ : 1000 * β ≤ ℓ)
    (hgain : 0 < gain) (hgainAux : gain ≤ unit * β / 16)
    (hgainGeom : gain ≤ unit * β / (4 + ℓ))
    (hgrid : FineGrid m sg gain ρ) (hδ : 0 < δ₀) (hδgain : δ₀ ≤ ρ * gain)
    (hσ : σ ≤ unit * L * β / 8) (hconstant : 36 ≤ Nk ^ (unit * L * β / 8))
    (Hres : Fin W → Set Incidence)
    (hno : ¬MixedCandidate Nk L W ν B Mc d₁ ρ gain ε p.r p.T p.C p.lev p.world
      p.bin p.velocity p.frame p.assigned Hres)
    (hbias : 2 * p.κ ≤ Nk ^ Mc)
    (hframe : D.D₀ = MajorFrame.frame (p.frame D.parent))
    (hmodel : D.K = (Nk ^ (unit * L)) ^ (ρ / (1000000 * ((n : ℝ) + 1))))
    (hdepth : D.depth = sourceDepth m sg D.i₀ unit)
    (hparent : unit ≤ sg D.i₀) (hroom : sg D.i₀ + unit + δ₀ ≤ 1 / 2)
    (haxes : D.FullAxes n (Nk ^ (-(unit * L * β / 2))))
    (hSres : D.S ⊆ Hres D.w₀)
    (hSo : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀))
    (hτ : 0 < τ) (hτε : τ⁻¹ ≤ Nk ^ (ε / 4000000))
    (hfloors : ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 →
      ∀ i : Fin (p.activeCount D.Hm (D.depth s)),
        ENNReal.ofReal τ * ((ν D.w₀).prod volume) (p.packet (D.old s i)) ≤
          ((ν D.w₀).prod volume) (D.S ∩ p.counted (D.old s i))) :
    ∃ c, D.Tracks n ℓ unit Nk L ν B c := by
  let X := unit * L * β
  let H := Nk ^ X
  let h := unit * β / 16
  have hX : 0 < X := by dsimp [X]; positivity
  have hh : 0 < h := by dsimp [h]; positivity
  have hN1 : 1 ≤ Nk := by linarith
  have hN0 : 0 < Nk := by linarith
  have hκ : 0 ≤ p.κ := zero_le_one.trans hp.one_le_slack
  have hH : 1 ≤ H := Real.one_le_rpow hN1 hX.le
  have hHN : H = (Nk ^ (unit * L)) ^ β := by
    dsimp only [H, X]
    exact Real.rpow_mul hN0.le _ _
  have h36 : 36 ≤ H := hconstant.trans
    (Real.rpow_le_rpow_of_exponent_le hN1 (by dsimp only [X] at hX ⊢; linarith))
  have h4 : 4 ≤ Nk ^ (X / 2) := (by norm_num : (4 : ℝ) ≤ 36).trans
    (hconstant.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hX])))
  have hκpow : p.κ ≤ Nk ^ (X / 8) := hp.slack_le.trans
    (Real.rpow_le_rpow_of_exponent_le hN1 hσ)
  have h18κ : 18 * p.κ ≤ Nk ^ (X / 4) := tracking_parent_slack_budget Nk p.κ X hN1 hκ
    hκpow ((by norm_num : (18 : ℝ) ≤ 36).trans hconstant)
  have hslack : 18 * p.κ ≤ H := h18κ.trans
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hX]))
  have hmodelBudget : 16 * H ^ 4 ≤ D.K := by
    rw [hmodel]
    have hnative : 1 ≤ Nk ^ (unit * L) := Real.one_le_rpow hN1 (by positivity)
    have h16 : 16 ≤ (Nk ^ (unit * L)) ^ β := by
      rw [← hHN]
      linarith only [h36]
    exact (geometric_row_power_budget (Nk ^ (unit * L)) H β hnative
      (zero_le_one.trans hH) hHN.le h16).trans
        (Real.rpow_le_rpow_of_exponent_le hnative hβmodel)
  have hhL : h * L = X / 16 := by dsimp only [h, X]; ring
  have hh8 : h ≤ 1 / 8 := by dsimp only [h]; linarith only [hunitβ]
  have hrow : 36 * p.κ / (Nk ^ (ρ * h * L + ε) * Nk ^ (-h * L)) ≤ H :=
    tracking_relative_row_budget Nk p.κ X h L (ρ * h * L + ε) hN1 hκ
      (by positivity) h18κ (by rw [hhL]; linarith only [hX])
      ((by norm_num : (2 : ℝ) ≤ 4).trans h4)
  have hρ1 : ρ ≤ 1 := by linarith only [hρsmall]
  have hργ : ρ * gain ≤ gain := mul_le_of_le_one_left hgain.le hρ1
  have hgainProduct : gain * (4 + ℓ) ≤ unit * β :=
    (le_div_iff₀ (by linarith : 0 < 4 + ℓ)).mp hgainGeom
  have hproduct := mul_le_mul_of_nonneg_left hργ (by linarith : 0 ≤ 4 + ℓ)
  have hdet : 4 * δ₀ + ℓ * (ρ * gain) ≤ unit * β := by
    nlinarith only [hδgain, hproduct, hgainProduct]
  have hδsmall : 4 * δ₀ ≤ unit * β := by
    nlinarith only [hdet, mul_nonneg hℓ.le (mul_nonneg hρ.le hgain.le)]
  have hm : 0 < m := hgrid.1.1
  have hi₀ : D.i₀ < m := hp.label_level D.parent
  have hmesh : ∀ i, i + 1 < m → sg (i + 1) - sg i ≤ ρ * gain := fineGrid_mesh hgrid
  have hroomNom : sg D.i₀ + unit ≤ sg (m - 1) := by
    rw [hgrid.1.2.2.2]
    linarith only [hroom, hδ]
  have hgeometry := D.trackingGeometry_of_full_axes hp hN1 hℓ.le hL.le hm n unit
    (ρ * gain) β H hunit.le hβ.le hβℓ hparent hδsmall (by positivity) hmesh hroomNom
    hdepth hframe rfl hH hslack hmodelBudget h4 hdet haxes
  have hdepthGe : ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 → D.i₀ ≤ D.depth s := by
    intro s _ _
    rw [hdepth]
    exact sourceDepth_ge sg hi₀ hunit.le s
  have hchildRoom : ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 →
      p.r (D.depth s) + 2 * h * L ≤ L := by
    intro s hslo hshi
    have hs0 : 0 ≤ s := (inv_nonneg.mpr (Nat.cast_nonneg n)).trans hslo
    have ha := (sourceDepth_actual hp hm hi₀ hunit.le (by positivity) hmesh hroomNom
      hL.le hs0 hshi).2
    rw [← hdepth] at ha
    have hr := mul_le_mul_of_nonneg_right hroom hL.le
    have hh' := mul_le_mul_of_nonneg_right hh8 hL.le
    nlinarith only [ha, hr, hh', hL]
  have hfloorBudget : Nk ^ (-ρ * h * L - ε) ≤ τ := by
    simpa only [neg_mul] using candidate_floor_of_inverse_budget Nk (ρ * h * L) ε τ
      hN1 (by positivity) hε hτ hτε
  exact D.tracks_of_geometric_budgets hp hN0 Mc d₁ ρ gain ε unit τ h H Hres hno hframe
    hSres hSo hτ hfloorBudget hgainAux hh8 hbias hrow n hgeometry hdepthGe hchildRoom hfloors

end Valid

end SourceData

end

end Submission.Obl.k4_finite_affine_parent_sources
