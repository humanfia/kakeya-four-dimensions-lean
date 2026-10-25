-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/DepthPreparation.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.PaletteAssembly
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.HighCurvature
import Submission.Lib.K4ContactNormalization.RowNormalization
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover

open MeasureTheory Set Filter MvPolynomial
open Submission.Lib.K4ContactNormalization
open Submission.Obl.k4_quadratic_atlas_normalization

/-- The exact closed time blocks of the frozen prepared model. -/
def timeBlock (T : ℕ) (j : Fin (2 ^ T)) : Set ℝ :=
  Icc ((j : ℕ) / (2 : ℝ) ^ T) (((j : ℕ) + 1) / (2 : ℝ) ^ T)

/-- A collection of full-block affine entries at a single depth, with the
failure budget charged to the unchanged incidence law. -/
def depthPrepared {α : Type*} [MeasurableSpace α]
    (N K : ℕ → ℝ) (μ : ℕ → Measure (α × ℝ))
    (b : ℕ → α → Fin 6 → ℝ) (T n : ℕ → ℝ → ℕ)
    (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s))
    (B : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set α) (s : ℝ) : Prop :=
  ∀ ε η : ℝ, 0 < ε → 0 < η → ∀ᶠ k in atTop,
    ∃ (M : ℕ) (L : Fin (n k s) → Fin M → Fin 4 → ℝ),
      (M : ℝ) ≤ N k ^ ε ∧
      μ k (paletteEvent (fun l t => point (b k l) t) (B k s)
        (fun i => timeBlock (T k s) (j k s i)) L (N k ^ (-s)) (N k ^ ε))ᶜ ≤
        ENNReal.ofReal (η * (K k)⁻¹)

/-- The fixed-depth geometric preparation is the only input needed beyond
the original domination and residual floor to obtain simultaneous palettes. -/
theorem finite_palettes_of_depth_prepared {α : Type*} [MeasurableSpace α]
    (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hK : ∀ k, 0 < K k)
    (μ ρ : ℕ → Measure (α × ℝ)) (hρ : ∀ k, ρ k ≤ μ k)
    (hfloor : ∀ k, ENNReal.ofReal (K k)⁻¹ ≤ ρ k univ)
    (b : ℕ → α → Fin 6 → ℝ) (T n : ℕ → ℝ → ℕ)
    (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s))
    (B : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set α)
    {U U₁ : ℝ} (hU₁ : 0 < U₁) (hU₁U : U₁ ≤ U)
    (hdepth : ∀ s : ℝ, 0 < s → s ≤ U₁ → depthPrepared N K μ b T n j B s) :
    ∃ U₁ : ℝ, 0 < U₁ ∧ U₁ ≤ U ∧
      ∀ (m : ℕ) (σ : Fin m → ℝ), (∀ h, 0 < σ h ∧ σ h ≤ U₁) →
        ∃ H : ℕ → ℝ, (∀ k, 1 ≤ H k) ∧
          (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε) ∧
          ∀ᶠ k in atTop, ∃ (M : Fin m → ℕ)
            (L : (h : Fin m) → Fin (n k (σ h)) → Fin (M h) → Fin 4 → ℝ),
            (∀ h, (M h : ℝ) ≤ H k) ∧
            ENNReal.ofReal ((K k)⁻¹ / 2) ≤ ρ k {p | ∀ h,
              ∃ (i : Fin (n k (σ h))) (u : Fin (M h)),
                p.1 ∈ B k (σ h) i ∧ p.2 ∈ timeBlock (T k (σ h)) (j k (σ h) i) ∧
                ∀ t ∈ timeBlock (T k (σ h)) (j k (σ h) i),
                  |point (b k p.1) t 3 -
                    (L h i u 0 + L h i u 1 * t + L h i u 2 * point (b k p.1) t 1 +
                      L h i u 3 * point (b k p.1) t 2)| ≤ H k * N k ^ (-σ h)} := by
  refine ⟨U₁, hU₁, hU₁U, fun m σ hσ => ?_⟩
  exact finite_depth_assembly N K hN hK μ ρ hρ hfloor
    (fun k l t => point (b k l) t) (fun k h => n k (σ h))
    (fun k h => B k (σ h)) (fun k h i => timeBlock (T k (σ h)) (j k (σ h) i))
    (fun k h => N k ^ (-σ h))
    (fun h => hdepth (σ h) (hσ h).1 (hσ h).2)

/-- If every test at one depth has large hidden curvature, one entry per
true label covers every incidence outside the original null exceptions. -/
theorem high_curvature_palette_ae {α : Type*} [MeasurableSpace α]
    (μ : Measure (α × ℝ)) (b : α → Fin 6 → ℝ) {n : ℕ}
    (B : Fin n → Set α) (I : Fin n → Set ℝ) (F : Fin n → MvPolynomial (Fin 4) ℝ)
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    (hF : ∀ i, (F i).totalDegree ≤ 2)
    (hlarge : ∀ i, (K ^ 5 * a)⁻¹ ≤ |curvature (F i) 3|)
    (hfit : ∀ i l, l ∈ B i → ∀ t ∈ I i,
      |eval (point (b l) t) (pderiv 3 (F i))| ≤ K)
    (hcover : ∀ᵐ p ∂μ, ∃ i, p.1 ∈ B i ∧ p.2 ∈ I i) :
    ∃ L : Fin n → Fin 1 → Fin 4 → ℝ,
      ∀ᵐ p ∂μ, p ∈ paletteEvent (fun l t => point (b l) t) B I L a (K ^ 6) := by
  classical
  choose L hL using fun i => high_curvature_affine_entry (F i) (hF i) hK ha (hlarge i)
  refine ⟨fun i _ => L i, ?_⟩
  filter_upwards [hcover] with p hp
  obtain ⟨i, hi, ht⟩ := hp
  refine ⟨i, 0, hi, ht, fun t ht => ?_⟩
  simpa only [point, Matrix.cons_val_zero] using hL i (point (b p.1) t) (hfit i p.1 hi t ht)

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover
