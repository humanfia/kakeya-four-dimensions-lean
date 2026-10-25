import Submission.Lib.K4QuadraticSheetCore

/-!
# Two affine branches from the affine-sheet core

In the normalized unit cube, the witness hypotheses of `sff_frame_bound` produce at most two
affine functions of the base point such that every full-time line with an event stays within
`coreLoss Cs Λ` of one of them. Low curvature uses the tangent plane at an exact regular root
found next to a witness; high curvature uses the affine centre.
-/

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep

open MvPolynomial Set MeasureTheory
open Submission.Lib.K4QuadraticSheetCore

noncomputable section

/-- The final loss of the core in normalized hidden units. -/
def coreLoss (Cs Λ : ℝ) : ℝ :=
  30 * Λ ^ 3 * (Λ + 13 * (2 * Λ) ^ 2 * (400 * Λ ^ 3 * sffKappa Cs Λ))

/-- A quadratic with a small value and a regular derivative at `y₀` and low curvature has an
exact root nearby, still regular. -/
theorem exists_regular_root (a b α Λ y₀ : ℝ) (hΛ : 1 ≤ Λ)
    (hval : |a + b * y₀ + α * y₀ ^ 2| ≤ Λ) (hder : Λ⁻¹ ≤ |b + 2 * α * y₀|)
    (hα : |α| * (8 * Λ ^ 3) ≤ 1) :
    ∃ f : ℝ, a + b * f + α * f ^ 2 = 0 ∧ (2 * Λ)⁻¹ ≤ |b + 2 * α * f| := by
  have hΛ0 : 0 < Λ := by linarith
  set e : ℝ := (4 * Λ)⁻¹ with he
  have he0 : 0 < e := by positivity
  have hΛe : Λ⁻¹ = 4 * e := by rw [he]; field_simp
  have h2Λe : (2 * Λ)⁻¹ = 2 * e := by rw [he]; field_simp; ring
  set D : ℝ := 2 * Λ ^ 2 with hD
  have hD0 : 0 < D := by positivity
  have hDe : D * e = Λ / 2 := by rw [hD, he]; field_simp; ring
  have hαD : |α| * D ≤ e := by
    have h4 : 0 < 4 * Λ := by positivity
    have hprod : |α| * D * (4 * Λ) ≤ 1 := by
      have e1 : |α| * D * (4 * Λ) = |α| * (8 * Λ ^ 3) := by rw [hD]; ring
      rw [e1]; exact hα
    calc |α| * D = |α| * D * (4 * Λ) * (4 * Λ)⁻¹ := by field_simp
      _ ≤ 1 * (4 * Λ)⁻¹ := by gcongr
      _ = e := by rw [one_mul]
  set h : ℝ → ℝ := fun y => a + b * y + α * y ^ 2 with hh
  have hcont : Continuous h := by fun_prop
  set d₀ : ℝ := b + 2 * α * y₀ with hd₀
  have hdiff : ∀ y, h y - h y₀ = (y - y₀) * (d₀ + α * (y - y₀)) := by
    intro y; simp only [hh, hd₀]; ring
  have hbound : ∀ y, |y - y₀| ≤ D → |α * (y - y₀)| ≤ e := by
    intro y hy
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hy (abs_nonneg _)).trans hαD
  have hderiv : ∀ y, |y - y₀| ≤ D → (2 * Λ)⁻¹ ≤ |b + 2 * α * y| := by
    intro y hy
    have h1 := hbound y hy
    have e1 : b + 2 * α * y = d₀ + 2 * (α * (y - y₀)) := by rw [hd₀]; ring
    rw [e1, h2Λe]
    have h2 := abs_sub_abs_le_abs_sub d₀ (-(2 * (α * (y - y₀))))
    rw [sub_neg_eq_add, abs_neg, abs_mul, abs_two] at h2
    rw [hΛe] at hder
    linarith
  have hval' := abs_le.mp hval
  have hDD : |y₀ + D - y₀| ≤ D := by rw [show y₀ + D - y₀ = D by ring, abs_of_pos hD0]
  have hDD' : |y₀ - D - y₀| ≤ D := by
    rw [show y₀ - D - y₀ = -D by ring, abs_neg, abs_of_pos hD0]
  have hbp := abs_le.mp (hbound (y₀ + D) hDD)
  have hbm := abs_le.mp (hbound (y₀ - D) hDD')
  rw [show y₀ + D - y₀ = D by ring] at hbp
  rw [show y₀ - D - y₀ = -D by ring] at hbm
  have ep := hdiff (y₀ + D)
  have em := hdiff (y₀ - D)
  rw [show y₀ + D - y₀ = D by ring] at ep
  rw [show y₀ - D - y₀ = -D by ring] at em
  have hΛhalf : Λ ≤ 3 * (D * e) := by rw [hDe]; linarith
  rcases le_or_gt 0 d₀ with hpos | hneg
  · have hd : 4 * e ≤ d₀ := by rw [hΛe] at hder; rwa [abs_of_nonneg hpos] at hder
    have hup : 0 ≤ h (y₀ + D) := by
      have : D * (3 * e) ≤ D * (d₀ + α * D) := by
        apply mul_le_mul_of_nonneg_left _ hD0.le; linarith
      have hy0 : h y₀ = a + b * y₀ + α * y₀ ^ 2 := rfl
      nlinarith
    have hdown : h (y₀ - D) ≤ 0 := by
      have : D * (3 * e) ≤ D * (d₀ + α * (-D)) := by
        apply mul_le_mul_of_nonneg_left _ hD0.le; linarith
      have hy0 : h y₀ = a + b * y₀ + α * y₀ ^ 2 := rfl
      nlinarith
    obtain ⟨f, hf, hf0⟩ := intermediate_value_Icc (by linarith : y₀ - D ≤ y₀ + D)
      hcont.continuousOn ⟨hdown, hup⟩
    refine ⟨f, hf0, hderiv f ?_⟩
    rw [abs_le]; constructor <;> linarith [hf.1, hf.2]
  · have hd : 4 * e ≤ -d₀ := by rw [hΛe] at hder; rwa [abs_of_neg hneg] at hder
    have hup : h (y₀ + D) ≤ 0 := by
      have : D * (d₀ + α * D) ≤ D * (-(3 * e)) := by
        apply mul_le_mul_of_nonneg_left _ hD0.le; linarith
      have hy0 : h y₀ = a + b * y₀ + α * y₀ ^ 2 := rfl
      nlinarith
    have hdown : 0 ≤ h (y₀ - D) := by
      have : D * (d₀ + α * (-D)) ≤ D * (-(3 * e)) := by
        apply mul_le_mul_of_nonneg_left _ hD0.le; linarith
      have hy0 : h y₀ = a + b * y₀ + α * y₀ ^ 2 := rfl
      nlinarith
    obtain ⟨f, hf, hf0⟩ := intermediate_value_Icc' (by linarith : y₀ - D ≤ y₀ + D)
      hcont.continuousOn ⟨hup, hdown⟩
    refine ⟨f, hf0, hderiv f ?_⟩
    rw [abs_le]; constructor <;> linarith [hf.1, hf.2]

/-- An affine base polynomial is an affine function. -/
theorem eval_affine_eq_affineFn (β : BasePoly) (hβ : β.totalDegree ≤ 1) (p : Fin 3 → ℝ) :
    eval p β = affineFn (eval 0 β) (gradAt β 0) p := by
  have h := eval_line_affine β hβ 0 p 1
  have e : (fun i => (0 : Fin 3 → ℝ) i + 1 * p i) = p := by funext i; simp
  rw [e] at h
  rw [h, affineFn, one_mul]

theorem tangentPlane_eq_affineFn (β γ : BasePoly) (p₀ : Fin 3 → ℝ) (f₀ s₀ : ℝ)
    (p : Fin 3 → ℝ) :
    tangentPlane β γ p₀ f₀ s₀ p =
      affineFn (f₀ + (f₀ * dot3 (gradAt β p₀) p₀ + dot3 (gradAt γ p₀) p₀) / s₀)
        (fun i => -(f₀ * gradAt β p₀ i + gradAt γ p₀ i) / s₀) p := by
  simp only [tangentPlane, affineFn, dot3]
  ring

theorem coreLoss_nonneg {Cs Λ : ℝ} (hCs : 0 ≤ Cs) (hΛ : 0 ≤ Λ) : 0 ≤ coreLoss Cs Λ := by
  unfold coreLoss
  have := sffKappa_nonneg hCs hΛ
  positivity

set_option maxHeartbeats 4000000 in
/-- **Two affine branches.** -/
theorem core_two_branches (Cs : ℝ) (hCs : CoefCtrl Cs) (hCs0 : 0 < Cs)
    (α : ℝ) (β γ : BasePoly) (hβ : β.totalDegree ≤ 1) (hγ : γ.totalDegree ≤ 2)
    (Λ ε ρ : ℝ) (S T : Set (Fin 6 → ℝ)) (E : Set (Fin 3 → ℝ))
    (hΛ : 1 ≤ Λ) (hα : |2 * α| ≤ Λ)
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
    (hT : ∀ b ∈ T, (∀ σ ∈ Icc (0 : ℝ) 1, |testVal α β γ b σ| ≤ Λ ∧ |testDer α β b σ| ≤ Λ) ∧
      (∀ σ ∈ Icc (0 : ℝ) 1, lineP b σ ∈ Icc (0 : Fin 3 → ℝ) 1) ∧
      ∃ σe ∈ Icc (0 : ℝ) 1, Λ⁻¹ ≤ |testDer α β b σe|) :
    ∃ (a₁ a₂ : ℝ) (v₁ v₂ : Fin 3 → ℝ), ∀ b ∈ T,
      (∀ σ ∈ Icc (0 : ℝ) 1, |lineW b σ - affineFn a₁ v₁ (lineP b σ)| ≤ coreLoss Cs Λ) ∨
      (∀ σ ∈ Icc (0 : ℝ) 1, |lineW b σ - affineFn a₂ v₂ (lineP b σ)| ≤ coreLoss Cs Λ) := by
  have hΛ0 : 0 < Λ := by linarith
  set Mb : ℝ := 400 * Λ ^ 3 * sffKappa Cs Λ with hMb
  have hMb0 : 0 ≤ Mb := by have := sffKappa_nonneg hCs0.le hΛ0.le; positivity
  set B₁ : ℝ := 13 * (2 * Λ) ^ 2 * Mb with hB₁
  have hB₁0 : 0 ≤ B₁ := by positivity
  have hloss : coreLoss Cs Λ = 30 * Λ ^ 3 * (Λ + B₁) := by
    simp only [coreLoss, hB₁, hMb]
  by_cases hcase : |α| * (16 * Λ ^ 2 * (Λ + B₁)) ≤ 1
  · -- low curvature: frame bounds, an exact regular root, its tangent plane
    have hαs : |α| * (8 * Λ ^ 3) ≤ 1 := by
      refine le_trans ?_ hcase
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg α)
      nlinarith
    have hframe := sff_frame_bound α β γ hβ hγ Cs Λ ε ρ S E hCs hCs0 hΛ hα hαs hfit hcube
      hcon hvel hEc hEv hwit hε1 hρ hs1 hs2 hs3
    -- a witness point: E is nonempty
    have hEne : E.Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne, measure_empty] at hEv
      exact absurd hEv (not_le.mpr (ENNReal.ofReal_pos.mpr (inv_pos.mpr hΛ0)))
    obtain ⟨p, hp⟩ := hEne
    obtain ⟨b₁, hb₁, -, -, -, -, σ₁, hσ₁, -, -, -, -, -, -, -, -, -, -, hev⟩ := hwit p hp
    set p₀ := lineP b₁ σ₁ with hp₀
    have hp₀c : p₀ ∈ Icc (0 : Fin 3 → ℝ) 1 := hcube b₁ hb₁ σ₁ hσ₁
    obtain ⟨f₀, hroot, hs₀⟩ := exists_regular_root (eval p₀ γ) (eval p₀ β) α Λ (lineW b₁ σ₁) hΛ
      (by simpa [testVal, hp₀] using (hfit b₁ hb₁ σ₁ hσ₁).1)
      (by simpa [testDer, hp₀] using hev) hαs
    have htp := tangent_plane_bound α β γ hβ hγ (2 * Λ) Mb (by linarith) p₀ hp₀c f₀
      (eval p₀ β + 2 * α * f₀) hroot rfl hs₀ (hframe p₀ hp₀c)
    set c₀ := f₀ + (f₀ * dot3 (gradAt β p₀) p₀ + dot3 (gradAt γ p₀) p₀) /
      (eval p₀ β + 2 * α * f₀)
    set c : Fin 3 → ℝ := fun i => -(f₀ * gradAt β p₀ i + gradAt γ p₀ i) /
      (eval p₀ β + 2 * α * f₀)
    have hL : ∀ q ∈ Icc (0 : Fin 3 → ℝ) 1, |testAt α β γ q (affineFn c₀ c q)| ≤ B₁ := by
      intro q hq
      rw [← tangentPlane_eq_affineFn]
      exact htp q hq
    refine ⟨c₀, c₀ - (eval 0 β + 2 * α * c₀) / α, c,
      fun i => c i - (gradAt β 0 i + 2 * α * c i) / α, ?_⟩
    intro b hb
    obtain ⟨hbfit, hbcube, σe, hσe, hbev⟩ := hT b hb
    rcases line_near_affine_branches α β γ hβ hγ Λ B₁ c₀ c hΛ hB₁0 hL hcase b hbfit hbcube
      σe hσe hbev with h1 | h2
    · left
      intro σ hσ
      rw [hloss]
      exact h1 σ hσ
    · right
      intro σ hσ
      rw [hloss]
      have e : affineFn c₀ c (lineP b σ) -
          (eval (lineP b σ) β + 2 * α * affineFn c₀ c (lineP b σ)) / α =
          affineFn (c₀ - (eval 0 β + 2 * α * c₀) / α)
            (fun i => c i - (gradAt β 0 i + 2 * α * c i) / α) (lineP b σ) := by
        rw [eval_affine_eq_affineFn β hβ (lineP b σ)]
        simp only [affineFn, dot3]
        ring
      rw [← e]
      exact h2 σ hσ
  · -- high curvature: the affine centre
    have hcase' : 1 < |α| * (16 * Λ ^ 2 * (Λ + B₁)) := lt_of_not_ge hcase
    have hpos : 0 < 16 * Λ ^ 2 * (Λ + B₁) := by positivity
    set α₀ : ℝ := (16 * Λ ^ 2 * (Λ + B₁))⁻¹ with hα₀
    have hα₀0 : 0 < α₀ := inv_pos.mpr hpos
    have hα₀le : α₀ ≤ |α| := by
      rw [hα₀, inv_le_iff_one_le_mul₀' hpos]
      linarith [hcase']
    refine ⟨-(eval 0 β) / (2 * α), 0, fun i => -(gradAt β 0 i) / (2 * α), 0, ?_⟩
    intro b hb
    obtain ⟨hbfit, -, -, -, -⟩ := hT b hb
    left
    intro σ hσ
    have h := line_near_affine_centre β γ hβ hγ α β Λ α₀ hα₀0 hα₀le b
      (fun σ hσ => (hbfit σ hσ).2) σ hσ
    have e : -(eval (lineP b σ) β) / (2 * α) =
        affineFn (-(eval 0 β) / (2 * α)) (fun i => -(gradAt β 0 i) / (2 * α)) (lineP b σ) := by
      rw [eval_affine_eq_affineFn β hβ (lineP b σ)]
      simp only [affineFn, dot3]
      ring
    rw [← e]
    refine h.trans ?_
    rw [hloss]
    have hΛα : Λ / (2 * α₀) = 8 * Λ ^ 3 * (Λ + B₁) := by
      rw [hα₀]; field_simp; ring
    rw [hΛα]
    have : 0 ≤ Λ ^ 3 * (Λ + B₁) := by positivity
    nlinarith

end

end Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep
