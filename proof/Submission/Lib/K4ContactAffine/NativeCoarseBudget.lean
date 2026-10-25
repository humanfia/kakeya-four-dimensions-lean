/- Adapted from: here:o223
   (x0927; countable-cell threshold extends x0775). -/
import Submission.Lib.K4ContactAffine.NativeCoarsePalette
import Submission.Lib.K4ContactAffine.Adapter.CoreBudget

/-! A single polynomial budget for the original native coarse cover. -/

namespace Submission.Lib.K4ContactAffine

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4QuadraticSheetCore
open Submission.Lib.K4AffineMeshCaps
open Adapter

structure NativeSample (Ω : Type*) [MeasurableSpace Ω] where
  μ : Measure Ω
  π : Measure ℝ
  b : Ω → Fin 6 → ℝ
  time : Ω → ℝ
  P : MvPolynomial (Fin 4) ℝ

namespace NativeSample

variable {Ω : Type*} [MeasurableSpace Ω] (s : NativeSample Ω)

def Good (K E : ℝ) (p : Ω) : Prop :=
  s.time p ∈ Icc (0 : ℝ) 1 ∧
  |s.b p 0| + |s.b p 1| + |s.b p 3| + |s.b p 4| ≤ K ∧
  (∀ t ∈ Icc (0 : ℝ) 1, |eval (point (s.b p) t) s.P| ≤ K ∧
    |eval (point (s.b p) t) (pderiv 3 s.P)| ≤ K ∧
    |eval (point (s.b p) t) (pderiv 3 (pderiv 3 s.P))| ≤ K) ∧
  K⁻¹ ≤ |eval (point (s.b p) (s.time p)) (pderiv 3 s.P)| ∧
  |s.b p 4 + s.b p 0| ≤ E

def PureCap (δ C : ℝ) : Prop :=
  ∀ q : Fin 3 → ℤ, s.μ {p | baseMesh δ (lineP (s.b p) (s.time p)) = q} ≤
    ENNReal.ofReal (C * δ ^ 3)

def JointCap (δ η C : ℝ) : Prop :=
  ∀ (q : Fin 3 → ℤ) (j : ℤ),
    s.μ {p | baseMesh δ (lineP (s.b p) (s.time p)) = q ∧ ⌊s.b p 3 / η⌋ = j} ≤
      ENNReal.ofReal (C * δ ^ 3) * s.π {w | ⌊w / η⌋ = j}

def Cover (error : ℝ) : Prop :=
  ∃ L : Fin 3 → Fin 4 → ℝ, ∀ᵐ p ∂s.μ, ∃ u : Fin 3, ∀ t ∈ Icc (0 : ℝ) 1,
    |point (s.b p) t 3 - (L u 0 + L u 1 * t + L u 2 * point (s.b p) t 1 +
      L u 3 * point (s.b p) t 2)| ≤ error

theorem Cover.mono {a b : ℝ} (ha : s.Cover a) (hab : a ≤ b) : s.Cover b := by
  obtain ⟨L, hL⟩ := ha
  refine ⟨L, ?_⟩
  filter_upwards [hL] with p hp
  obtain ⟨u, hu⟩ := hp
  exact ⟨u, fun t ht => (hu t ht).trans hab⟩

end NativeSample

/-- The finite native coarse cover has one universal polynomial cost. All
mesh, contact and curvature conditions are paid by this same cost. -/
theorem native_coarse_cover_with_polynomial_budget :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (s : NativeSample Ω)
      [IsFiniteMeasure s.π] (K R Λ E δ η m C pmax : ℝ),
      1 ≤ K → 32 * K ≤ R → 1 ≤ Λ → 432 * K ≤ Λ → 0 < C → 0 < m →
      0 < δ → δ ≤ 1 / 4 → 0 < η → Λ⁻¹ ≤ 3 * η / R →
      Λ⁻¹ ≤ m / (2 * (243 * C * R ^ 2)) → 0 ≤ E →
      s.P.totalDegree ≤ 2 → (∀ᵐ p ∂s.μ, s.Good K E p) →
      ENNReal.ofReal m ≤ s.μ univ → s.PureCap δ C → s.JointCap δ η C →
      (∀ j : ℤ, s.π {w | ⌊w / η⌋ = j} ≤ ENNReal.ofReal pmax) →
      6 * ENNReal.ofReal (243 * C * R ^ 2) * ENNReal.ofReal pmax < ENNReal.ofReal (m / 2) →
      D * Λ ^ 80 * (E / R + 3 * δ) ≤ 1 → s.Cover (D * Λ ^ 80) := by
  obtain ⟨Cs, hCs0, hCs⟩ := exists_coefCtrl
  obtain ⟨D, hD, hbudget⟩ := core_budgets Cs hCs0
  refine ⟨D, hD, ?_⟩
  intro Ω _ s _ K R Λ E δ η m C pmax hK hR hΛ hΛK hC hm hδ hδquarter hη hgap
    hdensity hE hP hgood hmass hcap hbin hπ hsmall hmargin
  have hR0 : 0 < R := by linarith
  have hε : 0 ≤ E / R := by positivity
  have hρ : 0 ≤ 3 * δ := by positivity
  obtain ⟨herr, hconditions⟩ := hbudget Λ (E / R) (3 * δ) hΛ hε hρ
  obtain ⟨hs1, hs2, hs3⟩ := hconditions hmargin
  have hDΛ : 1 ≤ D * Λ ^ 80 := one_le_mul_of_one_le_of_one_le hD (one_le_pow₀ hΛ)
  have hE1 : E / R ≤ 1 := by
    have hle : E / R ≤ D * Λ ^ 80 * (E / R + 3 * δ) := by
      calc
        E / R ≤ E / R + 3 * δ := by linarith
        _ = 1 * (E / R + 3 * δ) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hDΛ (by positivity)
    exact hle.trans hmargin
  obtain ⟨L, hL⟩ := native_coarse_palette_of_caps s.μ s.b s.time s.π s.P hP
    Cs K R Λ E δ η m C pmax hCs hCs0 hK hR hΛ hΛK hC hm hδ hδquarter hη hgap hdensity
    hE hE1 hs1 hs2 hs3 {p | s.Good K E p} hgood (fun p hp => hp) hmass hcap hbin hπ hsmall
  refine ⟨L, ?_⟩
  filter_upwards [hgood] with p hp
  obtain ⟨u, hu⟩ := hL p hp
  exact ⟨u, fun t ht => (hu t ht).trans herr⟩

end Submission.Lib.K4ContactAffine
