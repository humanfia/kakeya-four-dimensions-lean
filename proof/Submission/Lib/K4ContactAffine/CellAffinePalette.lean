/- Adapted from: here:o223
   (x0927; countable-cell threshold extends x0775). -/
import Submission.Lib.K4ContactAffine.MeshWitnessRegion
import Submission.Lib.K4ContactAffine.Adapter.CubePalette

/-!+# Affine predictors directly from original cell and velocity caps

This combines the countable-cell measure argument with the accepted quadratic
sheet core, through the cube adapter. All source events keep their original
mass and their original velocity numerator.
-/

namespace Submission.Lib.K4ContactAffine

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4QuadraticSheetCore
open Submission.Lib.K4AffineMeshCaps
open Adapter

/-- In the normalized cube, the original pure and joint mesh caps produce
three affine predictors for every good full-time line with an event. -/
theorem affine_palette_of_original_cell_caps {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (b : Ω → Fin 6 → ℝ) (time : Ω → ℝ)
    (a : ℝ) (β γ : BasePoly) (hβ : β.totalDegree ≤ 1) (hγ : γ.totalDegree ≤ 2)
    (Cs Λ ε δ η h m B : ℝ) (pmax : ENNReal)
    (hCs : CoefCtrl Cs) (hCs0 : 0 < Cs) (hΛ : 1 ≤ Λ)
    (hm : 0 < m) (hB : 0 < B) (hδ : 0 < δ) (hη : 0 < η)
    (hδh : δ ≤ h) (hgap : Λ⁻¹ ≤ η) (hdensity : Λ⁻¹ ≤ m / (2 * B))
    (hα : |2 * a| ≤ Λ) (hε : ε ≤ 1)
    (hs1 : 4 * Cs * remezC 4 Λ * (3 * δ) ≤ 1)
    (hs2 : 8 * discBudget Cs Λ * (3 * δ) * Λ ^ 2 ≤ 1)
    (hs3 : 192 * Cs * sffKappa Cs Λ * (ε + 3 * δ) * Λ ^ 2 ≤ 1)
    (G : Set Ω) (hG : ∀ᵐ p ∂μ, p ∈ G)
    (hgood : ∀ p ∈ G,
      time p ∈ Icc (0 : ℝ) 1 ∧
      (∀ σ ∈ Icc (0 : ℝ) 1,
        |testVal a β γ (b p) σ| ≤ Λ ∧ |testDer a β (b p) σ| ≤ Λ) ∧
      (∀ σ ∈ Icc (0 : ℝ) 1, lineP (b p) σ ∈ Icc (0 : Fin 3 → ℝ) 1) ∧
      |b p 4 + b p 0| ≤ ε ∧ |b p 3| ≤ Λ ∧
      Λ⁻¹ ≤ |testDer a β (b p) (time p)|)
    (S : Set (Fin 3 → ℝ)) (hsource : ∀ᵐ p ∂μ, lineP (b p) (time p) ∈ S)
    (hmargin : ∀ x ∈ S, ∀ e, h ≤ x e ∧ x e ≤ 1 - h)
    (hmass : ENNReal.ofReal m ≤ μ univ)
    (hcap : ∀ q : Fin 3 → ℤ,
      μ {p | baseMesh δ (lineP (b p) (time p)) = q} ≤ ENNReal.ofReal (B * δ ^ 3))
    (hbin : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      μ {p | baseMesh δ (lineP (b p) (time p)) = q ∧ ⌊b p 3 / η⌋ = j} ≤
        ENNReal.ofReal (B * δ ^ 3) * pmax)
    (hsmall : 6 * ENNReal.ofReal B * pmax < ENNReal.ofReal (m / 2)) :
    ∃ (c₀ : Fin 3 → ℝ) (c : Fin 3 → Fin 3 → ℝ),
      ∀ p ∈ G, ∃ u : Fin 3, ∀ σ ∈ Icc (0 : ℝ) 1,
        |lineW (b p) σ - affineFn (c₀ u) (c u) (lineP (b p) σ)| ≤ cubeErr Cs Λ := by
  classical
  obtain ⟨E, hEmeas, hEc, hEV, hwitness⟩ := cube_mesh_witness_region
    μ (fun p => lineP (b p) (time p)) (fun p => b p 3) S G hm hB hδ hη hδh
      pmax hmass hsource hG hmargin hcap hbin hsmall
  let lines : Set (Fin 6 → ℝ) := {b' | ∃ p ∈ G, b p = b'}
  have hfit : ∀ b' ∈ lines, ∀ σ ∈ Icc (0 : ℝ) 1,
      |testVal a β γ b' σ| ≤ Λ ∧ |testDer a β b' σ| ≤ Λ := by
    rintro b' ⟨p, hp, rfl⟩ σ hσ
    exact (hgood p hp).2.1 σ hσ
  have hcube : ∀ b' ∈ lines, ∀ σ ∈ Icc (0 : ℝ) 1,
      lineP b' σ ∈ Icc (0 : Fin 3 → ℝ) 1 := by
    rintro b' ⟨p, hp, rfl⟩ σ hσ
    exact (hgood p hp).2.2.1 σ hσ
  have hcontact : ∀ b' ∈ lines, |b' 4 + b' 0| ≤ ε := by
    rintro b' ⟨p, hp, rfl⟩
    exact (hgood p hp).2.2.2.1
  have hvelocity : ∀ b' ∈ lines, |b' 3| ≤ Λ := by
    rintro b' ⟨p, hp, rfl⟩
    exact (hgood p hp).2.2.2.2.1
  have hEv : ENNReal.ofReal Λ⁻¹ ≤ volume E :=
    (ENNReal.ofReal_le_ofReal hdensity).trans hEV
  have hwit : ∀ x ∈ E, ∃ b₀ ∈ lines, ∃ b₁ ∈ lines, ∃ b₂ ∈ lines,
      ∃ σ₀ ∈ Icc (0 : ℝ) 1, ∃ σ₁ ∈ Icc (0 : ℝ) 1, ∃ σ₂ ∈ Icc (0 : ℝ) 1,
        l1dist (lineP b₀ σ₀) x ≤ 3 * δ ∧ l1dist (lineP b₁ σ₁) x ≤ 3 * δ ∧
        l1dist (lineP b₂ σ₂) x ≤ 3 * δ ∧
        Λ⁻¹ ≤ |b₀ 3 - b₁ 3| ∧ Λ⁻¹ ≤ |b₀ 3 - b₂ 3| ∧ Λ⁻¹ ≤ |b₁ 3 - b₂ 3| ∧
        Λ⁻¹ ≤ |testDer a β b₀ σ₀| := by
    intro x hx
    obtain ⟨p₀, p₁, p₂, hp₀, hp₁, hp₂, hd₀, hd₁, hd₂, h₀₁, h₀₂, h₁₂⟩ := hwitness x hx
    have hd (p : Ω) (hp : ∀ e, |lineP (b p) (time p) e - x e| ≤ δ) :
        l1dist (lineP (b p) (time p)) x ≤ 3 * δ := by
      unfold l1dist
      linarith [hp 0, hp 1, hp 2]
    exact ⟨b p₀, ⟨p₀, hp₀.2, rfl⟩, b p₁, ⟨p₁, hp₁.2, rfl⟩, b p₂, ⟨p₂, hp₂.2, rfl⟩,
      time p₀, (hgood p₀ hp₀.2).1, time p₁, (hgood p₁ hp₁.2).1,
      time p₂, (hgood p₂ hp₂.2).1,
      hd p₀ hd₀, hd p₁ hd₁, hd p₂ hd₂, hgap.trans h₀₁.le, hgap.trans h₀₂.le,
      hgap.trans h₁₂.le, (hgood p₀ hp₀.2).2.2.2.2.2⟩
  obtain ⟨c₀, c, hpalette⟩ := cube_palette a β γ hβ hγ Cs Λ ε (3 * δ)
    lines lines E hCs hCs0 hΛ hα hfit hcube hcontact hvelocity hEc hEv hwit hε
      (by positivity) hs1 hs2 hs3 lines hfit hcube
  refine ⟨c₀, c, ?_⟩
  intro p hp
  exact hpalette (b p) ⟨p, hp, rfl⟩ (time p) (hgood p hp).1
    (hgood p hp).2.2.2.2.2

end Submission.Lib.K4ContactAffine
