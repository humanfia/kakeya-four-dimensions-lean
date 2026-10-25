/- Adapted from: here:o223
   (session x0927, branch x0927).
   This is the library export of the o223 adapter, first committed at b6fc491c.
   Earlier source: here:o241, session x0842, branch x0842, for
   k4_contact_equal_rate_affine_palettes. Original authorship is retained:
   x0842 wrote the cube/budget adapter; x0927 adapted its namespaces and imports
   to the gate-accepted Submission.Lib.K4QuadraticSheetCore. -/
import Mathlib
import Submission.Lib.K4HiddenQuadratic
import Submission.Lib.K4QuadraticSheetCore.SheetAffine

/-!
# Three affine predictors in the normalized cube

This file assembles x0777's deterministic core (`sff_frame_bound`, `tangent_plane_bound`,
`line_near_affine_branches`, `line_near_affine_centre`) into one statement: under the witness
hypotheses of `sff_frame_bound`, three affine functions of the base point (the tangent plane
of an anchor, its far branch, and the high-curvature centre) fit, on the whole unit time
interval, every line of the cube that fits the test and has one event. The error is the
explicit polynomial `cubeErr Cs Λ`.

The anchor root (`exists_anchor_root`) comes from the nearest-root lemma of
`Submission.Lib.K4HiddenQuadratic`.
-/

namespace Submission.Lib.K4ContactAffine.Adapter

open Submission.Lib.K4QuadraticSheetCore

open MvPolynomial Set MeasureTheory

noncomputable section

/-- **Anchor.** At a good point of small curvature there is a root within `2K²`, at which the
hidden derivative `s` satisfies `s² ≥ 1/(2K²)`. -/
theorem exists_anchor_root (g b a w K : ℝ) (hK : 1 ≤ K)
    (hval : |g + b * w + a * w ^ 2| ≤ K) (hder : K⁻¹ ≤ |b + 2 * a * w|)
    (hcurv : |a| ≤ 1 / (8 * K ^ 3)) :
    ∃ f : ℝ, g + b * f + a * f ^ 2 = 0 ∧ |f - w| ≤ 2 * K ^ 2 ∧
      1 / (2 * K ^ 2) ≤ (b + 2 * a * f) ^ 2 := by
  have hK0 : 0 < K := by linarith
  have hKne : K ≠ 0 := hK0.ne'
  set q := b + 2 * a * w with hq
  set p := g + b * w + a * w ^ 2 with hp
  have hq0 : q ≠ 0 := by
    intro h; rw [h, abs_zero] at hder; exact absurd hder (not_le.mpr (by positivity))
  have hq2 : (K⁻¹) ^ 2 ≤ q ^ 2 := by
    rw [← sq_abs q]; exact pow_le_pow_left₀ (by positivity) hder 2
  have hsmall : 2 * |(2 * a) * p| ≤ q ^ 2 / 2 := by
    rw [abs_mul, abs_mul, abs_two]
    have h1 : |a| * |p| ≤ 1 / (8 * K ^ 3) * K :=
      mul_le_mul hcurv hval (abs_nonneg _) (by positivity)
    have h2 : 1 / (8 * K ^ 3) * K = (K⁻¹) ^ 2 / 8 := by field_simp
    nlinarith
  obtain ⟨_, s₀, hroot, _, hsq, _, hs₀⟩ := Submission.Lib.K4HiddenQuadratic.quadratic_nearest_root
    p q (2 * a) hq0 hsmall
  refine ⟨w + s₀, ?_, ?_, ?_⟩
  · have : g + b * (w + s₀) + a * (w + s₀) ^ 2 = p + q * s₀ + 2 * a / 2 * s₀ ^ 2 := by
      simp only [hp, hq]; ring
    rw [this, hroot]
  · have : w + s₀ - w = s₀ := by ring
    rw [this]
    refine hs₀.trans ?_
    rw [div_le_iff₀ (abs_pos.mpr hq0)]
    have h1 : 1 ≤ K * |q| := by
      have := mul_le_mul_of_nonneg_left hder hK0.le
      rwa [mul_inv_cancel₀ hK0.ne'] at this
    have h2 : K ≤ K ^ 2 * |q| := by nlinarith
    linarith [hval]
  · have hD : (b + 2 * a * (w + s₀)) = q + 2 * a * s₀ := by simp only [hq]; ring
    have hle : 2 * (2 * a) * p ≤ q ^ 2 / 2 := by
      have := le_abs_self ((2 * a) * p)
      nlinarith
    have hnn : 0 ≤ q ^ 2 - 2 * (2 * a) * p := by linarith
    have hsq2 : (q + 2 * a * s₀) ^ 2 = q ^ 2 - 2 * (2 * a) * p := by
      rw [← sq_abs (q + 2 * a * s₀), hsq, Real.sq_sqrt hnn]
    rw [hD, hsq2]
    have : 1 / (2 * K ^ 2) = (K⁻¹) ^ 2 / 2 := by field_simp
    rw [this]
    linarith

section Affine

variable (β γ : BasePoly)

/-- A base polynomial of degree at most one is an affine function. -/
theorem eval_eq_affineFn_of_deg_le_one (hβ : β.totalDegree ≤ 1) (p : Fin 3 → ℝ) :
    eval p β = affineFn (eval 0 β) (gradAt β 0) p := by
  have h := eval_line_affine β hβ 0 p 1
  have hp : (fun i => (0 : Fin 3 → ℝ) i + 1 * p i) = p := by funext i; simp
  rw [hp] at h
  rw [h, affineFn]
  ring

theorem tangentPlane_eq_affineFn (p₀ : Fin 3 → ℝ) (f₀ s₀ : ℝ) (p : Fin 3 → ℝ) :
    tangentPlane β γ p₀ f₀ s₀ p =
      affineFn (f₀ - dot3 (fun i => -(f₀ * gradAt β p₀ i + gradAt γ p₀ i) / s₀) p₀)
        (fun i => -(f₀ * gradAt β p₀ i + gradAt γ p₀ i) / s₀) p := by
  simp only [tangentPlane, affineFn, dot3]
  ring

theorem farBranch_eq_affineFn (hβ : β.totalDegree ≤ 1) (α c₀ : ℝ) (c p : Fin 3 → ℝ) :
    affineFn c₀ c p - (eval p β + 2 * α * affineFn c₀ c p) / α =
      affineFn (c₀ - (eval 0 β + 2 * α * c₀) / α)
        (fun i => c i - (gradAt β 0 i + 2 * α * c i) / α) p := by
  rw [eval_eq_affineFn_of_deg_le_one β hβ p]
  simp only [affineFn, dot3]
  ring

theorem centre_eq_affineFn (hβ : β.totalDegree ≤ 1) (α : ℝ) (p : Fin 3 → ℝ) :
    -(eval p β) / (2 * α) =
      affineFn (-(eval 0 β) / (2 * α)) (fun i => -(gradAt β 0 i) / (2 * α)) p := by
  rw [eval_eq_affineFn_of_deg_le_one β hβ p]
  simp only [affineFn, dot3]
  ring

end Affine

/-- The tangent-plane budget `B₁` (with the doubled constant from the anchor). -/
def cubeB₁ (Cs Λ : ℝ) : ℝ := 13 * (2 * Λ) ^ 2 * (400 * Λ ^ 3 * sffKappa Cs Λ)

/-- The error of the three cube predictors. -/
def cubeErr (Cs Λ : ℝ) : ℝ := 30 * Λ ^ 3 * (Λ + cubeB₁ Cs Λ)

theorem cubeB₁_nonneg {Cs Λ : ℝ} (hCs : 0 ≤ Cs) (hΛ : 0 ≤ Λ) : 0 ≤ cubeB₁ Cs Λ := by
  unfold cubeB₁
  have := sffKappa_nonneg hCs hΛ
  positivity

section Palette

variable (α : ℝ) (β γ : BasePoly) (hβ : β.totalDegree ≤ 1) (hγ : γ.totalDegree ≤ 2)
include hβ hγ

set_option maxHeartbeats 4000000 in
/-- **Cube palette.** Under the witness hypotheses of `sff_frame_bound`, three affine functions
fit, on the whole unit time interval, every line of the cube that fits the test and has one
event, with error `cubeErr Cs Λ`. -/
theorem cube_palette (Cs Λ ε ρ : ℝ) (S T : Set (Fin 6 → ℝ)) (E : Set (Fin 3 → ℝ))
    (hCs : CoefCtrl Cs) (hCs0 : 0 < Cs) (hΛ : 1 ≤ Λ) (hα : |2 * α| ≤ Λ)
    (hfit : ∀ b ∈ S, ∀ σ ∈ Icc (0 : ℝ) 1, |testVal α β γ b σ| ≤ Λ ∧ |testDer α β b σ| ≤ Λ)
    (hcube : ∀ b ∈ S, ∀ σ ∈ Icc (0 : ℝ) 1, lineP b σ ∈ Icc (0 : Fin 3 → ℝ) 1)
    (hcon : ∀ b ∈ S, |b 4 + b 0| ≤ ε) (hvel : ∀ b ∈ S, |b 3| ≤ Λ)
    (hEc : E ⊆ Icc (0 : Fin 3 → ℝ) 1) (hEv : ENNReal.ofReal Λ⁻¹ ≤ volume E)
    (hwit : ∀ p ∈ E, ∃ b₁ ∈ S, ∃ b₂ ∈ S, ∃ b₃ ∈ S,
      ∃ σ₁ ∈ Icc (0 : ℝ) 1, ∃ σ₂ ∈ Icc (0 : ℝ) 1, ∃ σ₃ ∈ Icc (0 : ℝ) 1,
        l1dist (lineP b₁ σ₁) p ≤ ρ ∧ l1dist (lineP b₂ σ₂) p ≤ ρ ∧ l1dist (lineP b₃ σ₃) p ≤ ρ ∧
        Λ⁻¹ ≤ |b₁ 3 - b₂ 3| ∧ Λ⁻¹ ≤ |b₁ 3 - b₃ 3| ∧ Λ⁻¹ ≤ |b₂ 3 - b₃ 3| ∧
        Λ⁻¹ ≤ |testDer α β b₁ σ₁|)
    (hε1 : ε ≤ 1) (hρ : 0 ≤ ρ)
    (hs1 : 4 * Cs * remezC 4 Λ * ρ ≤ 1) (hs2 : 8 * discBudget Cs Λ * ρ * Λ ^ 2 ≤ 1)
    (hs3 : 192 * Cs * sffKappa Cs Λ * (ε + ρ) * Λ ^ 2 ≤ 1)
    (T : Set (Fin 6 → ℝ))
    (hfitT : ∀ b ∈ T, ∀ σ ∈ Icc (0 : ℝ) 1, |testVal α β γ b σ| ≤ Λ ∧ |testDer α β b σ| ≤ Λ)
    (hcubeT : ∀ b ∈ T, ∀ σ ∈ Icc (0 : ℝ) 1, lineP b σ ∈ Icc (0 : Fin 3 → ℝ) 1) :
    ∃ (c₀ : Fin 3 → ℝ) (c : Fin 3 → Fin 3 → ℝ), ∀ b ∈ T, ∀ σe ∈ Icc (0 : ℝ) 1,
      Λ⁻¹ ≤ |testDer α β b σe| → ∃ u : Fin 3, ∀ σ ∈ Icc (0 : ℝ) 1,
        |lineW b σ - affineFn (c₀ u) (c u) (lineP b σ)| ≤ cubeErr Cs Λ := by
  have hΛ0 : 0 < Λ := by linarith
  have hB₁ : 0 ≤ cubeB₁ Cs Λ := cubeB₁_nonneg hCs0.le hΛ0.le
  set B₁ := cubeB₁ Cs Λ with hB₁def
  have hQ : 0 < Λ + B₁ := by linarith
  have hErr : 8 * Λ ^ 3 * (Λ + B₁) ≤ cubeErr Cs Λ := by
    unfold cubeErr
    rw [← hB₁def]
    have : 0 ≤ Λ ^ 3 * (Λ + B₁) := by positivity
    linarith
  by_cases hcurv : |α| * (16 * Λ ^ 2 * (Λ + B₁)) ≤ 1
  · -- low curvature: the frame bound, an anchor and the two branches
    have hαs : |α| * (8 * Λ ^ 3) ≤ 1 := by
      have h1 : 8 * Λ ^ 3 ≤ 16 * Λ ^ 2 * (Λ + B₁) := by nlinarith
      calc |α| * (8 * Λ ^ 3) ≤ |α| * (16 * Λ ^ 2 * (Λ + B₁)) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ ≤ 1 := hcurv
    have hframe := sff_frame_bound α β γ hβ hγ Cs Λ ε ρ S E hCs hCs0 hΛ hα hαs hfit hcube
      hcon hvel hEc hEv hwit hε1 hρ hs1 hs2 hs3
    -- an anchor: a witness event
    have hEne : E.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      rw [h, measure_empty] at hEv
      exact absurd hEv (not_le.mpr (ENNReal.ofReal_pos.mpr (inv_pos.mpr hΛ0)))
    obtain ⟨pE, hpE⟩ := hEne
    obtain ⟨b₁, hb₁, -, -, -, -, σ₁, hσ₁, -, -, -, -, -, -, -, -, -, -, hev₁⟩ := hwit pE hpE
    set p₀ := lineP b₁ σ₁ with hp₀
    have hp₀c : p₀ ∈ Icc (0 : Fin 3 → ℝ) 1 := hcube b₁ hb₁ σ₁ hσ₁
    have hval₀ : |eval p₀ γ + eval p₀ β * lineW b₁ σ₁ + α * lineW b₁ σ₁ ^ 2| ≤ Λ :=
      (hfit b₁ hb₁ σ₁ hσ₁).1
    have hder₀ : Λ⁻¹ ≤ |eval p₀ β + 2 * α * lineW b₁ σ₁| := hev₁
    have hcurv₀ : |α| ≤ 1 / (8 * Λ ^ 3) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    obtain ⟨f₀, hroot, -, hs2⟩ := exists_anchor_root (eval p₀ γ) (eval p₀ β) α
      (lineW b₁ σ₁) Λ hΛ hval₀ hder₀ hcurv₀
    set s₀ := eval p₀ β + 2 * α * f₀ with hs₀
    have hs₀' : (2 * Λ)⁻¹ ≤ |s₀| := by
      have h4 : ((2 * Λ)⁻¹) ^ 2 ≤ |s₀| ^ 2 := by
        rw [sq_abs]
        calc ((2 * Λ)⁻¹) ^ 2 = 1 / (4 * Λ ^ 2) := by field_simp; ring
          _ ≤ 1 / (2 * Λ ^ 2) := by
            apply one_div_le_one_div_of_le (by positivity); nlinarith
          _ ≤ s₀ ^ 2 := hs2
      by_contra hcon
      push Not at hcon
      have hx : 0 < (2 * Λ)⁻¹ := by positivity
      nlinarith [abs_nonneg s₀]
    have hMb := hframe p₀ hp₀c
    have htan : ∀ p ∈ Icc (0 : Fin 3 → ℝ) 1,
        |testAt α β γ p (tangentPlane β γ p₀ f₀ s₀ p)| ≤ B₁ := by
      intro p hp
      have h := tangent_plane_bound α β γ hβ hγ (2 * Λ) (400 * Λ ^ 3 * sffKappa Cs Λ)
        (by linarith) p₀ hp₀c f₀ s₀ hroot hs₀ hs₀' hMb p hp
      simpa only [hB₁def, cubeB₁] using h
    set cc : Fin 3 → ℝ := fun i => -(f₀ * gradAt β p₀ i + gradAt γ p₀ i) / s₀ with hcc
    set c0 : ℝ := f₀ - dot3 cc p₀ with hc0
    have hL : ∀ p ∈ Icc (0 : Fin 3 → ℝ) 1, |testAt α β γ p (affineFn c0 cc p)| ≤ B₁ := by
      intro p hp
      rw [← tangentPlane_eq_affineFn β γ p₀ f₀ s₀ p]
      exact htan p hp
    obtain ⟨c0', cc', hfar⟩ : ∃ c0' cc', ∀ p,
        affineFn c0 cc p - (eval p β + 2 * α * affineFn c0 cc p) / α = affineFn c0' cc' p :=
      ⟨_, _, farBranch_eq_affineFn β hβ α c0 cc⟩
    refine ⟨![c0, c0', c0], ![cc, cc', cc], fun b hb σe hσe hev => ?_⟩
    rcases line_near_affine_branches α β γ hβ hγ Λ B₁ c0 cc hΛ hB₁ hL hcurv b (hfitT b hb)
      (hcubeT b hb) σe hσe hev with h | h
    · refine ⟨0, fun σ hσ => (h σ hσ).trans ?_⟩
      exact le_rfl
    · refine ⟨1, fun σ hσ => ?_⟩
      have := h σ hσ
      rw [hfar] at this
      exact this
  · -- high curvature: the affine centre
    push Not at hcurv
    set α₀ := 1 / (16 * Λ ^ 2 * (Λ + B₁)) with hα₀
    have hα₀pos : 0 < α₀ := by positivity
    have hα₀le : α₀ ≤ |α| := by
      rw [hα₀, div_le_iff₀ (by positivity)]; linarith
    obtain ⟨c0, cc, hcen⟩ : ∃ c0 cc, ∀ p, -(eval p β) / (2 * α) = affineFn c0 cc p :=
      ⟨_, _, centre_eq_affineFn β hβ α⟩
    refine ⟨![c0, c0, c0], ![cc, cc, cc], fun b hb σe hσe hev => ⟨0, fun σ hσ => ?_⟩⟩
    have h := line_near_affine_centre β γ hβ hγ α β Λ α₀ hα₀pos hα₀le b
      (fun σ hσ => (hfitT b hb σ hσ).2) σ hσ
    rw [hcen] at h
    refine h.trans ?_
    have : Λ / (2 * α₀) = 8 * Λ ^ 3 * (Λ + B₁) := by
      rw [hα₀]; field_simp; ring
    rw [this]
    exact hErr

end Palette

end

end Submission.Lib.K4ContactAffine.Adapter
