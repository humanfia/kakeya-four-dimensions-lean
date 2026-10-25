-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.RelativeFullness
import Submission.Obl.k4_finite_affine_parent_sources.RelativeDeterminants
import Submission.Obl.k4_finite_affine_parent_sources.NativeChildFrame
import Submission.Obl.k4_finite_affine_parent_sources.NoCandidateFrames

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Submission.Lib.K4XInterface
open Submission.Obl.k4_compatible_pair_frame_preparation.Construction

noncomputable section

/-- Quantitative spatial EH3 geometry for a full original child assignment.
The no-candidate input bounds the relative velocity rows using the actual
original residual and its full-prior floor. Physical fullness and positive
parent narrowness then bound the major row below. The native time factor
is included before producing the five bounded tilted coefficients. -/
theorem PFrame.original_label_geometric_rows
    {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sgrid : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sgrid δ₀ Mp Dp σ)
    (hNk : 0 < Nk) (Mc : ℕ) (d₁ ρ gain ε : ℝ) (Hset : Fin W → Set Incidence)
    (hno : ¬MixedCandidate Nk L W ν B Mc d₁ ρ gain ε p.r p.T p.C p.lev p.world
      p.bin p.velocity p.frame p.assigned Hset)
    (parent child : Fin p.C) (h : ℝ) (hgain : gain ≤ h) (hupper : h ≤ 1 / 8)
    (hroom : p.r (p.lev child) + 2 * h * L ≤ L)
    (hprior : 0 < ν (p.world child) (p.assigned child))
    (hbias : 2 * p.κ ≤ Nk ^ Mc)
    (V : Set Incidence) (hne : V.Nonempty)
    (hV : ∀ z ∈ V, z ∈ Hset (p.world child) ∧ z.1 ∈ p.assigned child ∧
      z.2 ∈ Icc ((p.bin child : ℝ) / (2 : ℝ) ^ p.T (p.lev child))
        (((p.bin child : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev child)))
    (hfloor : ENNReal.ofReal (Nk ^ (-ρ * h * L - ε) / (2 : ℝ) ^ p.T (p.lev child)) *
      ν (p.world child) (p.assigned child) ≤ (ν (p.world child)).prod volume V)
    (Φ : PFrame) (Kparent H g : ℝ) (hKparent : 0 ≤ Kparent)
    (hH : 1 ≤ H) (hκH : p.κ ≤ H) (hg : 0 ≤ g)
    (hq₀ : 0 < Φ.F.q)
    (hD : Φ.F.D = MajorFrame.frame (p.frame parent))
    (hparentVelocity : ∀ z ∈ V, ∀ e : Fin 2,
      |(WithLp.toLp 2 ![Φ.eb z.1 3, Φ.eb z.1 4]) e| ≤ Kparent)
    (hrowBudget : 2 * Kparent / (Nk ^ (ρ * h * L + ε) * Nk ^ (-h * L)) ≤ H)
    (hparentFull : Φ.F.q / H ≤ r₁ (p.frame parent))
    (hparentUpper : r₁ (p.frame parent) ≤ H * Φ.F.q)
    (hparentArea : |(p.frame parent).det| ≤ Φ.F.q ^ 2 / (2 * H ^ 3))
    (hchildFull : (((2 : ℝ) ^ p.T (p.lev child))⁻¹) / H ≤ r₁ (p.frame child))
    (hrelativeDet : |(relativeVelocityFrame Φ.F.q
      (((2 : ℝ) ^ p.T (p.lev child))⁻¹) Φ.F.D (p.frame child)).det| ≤ H * g)
    (T : ℕ) (j : Fin (2 ^ T))
    (hblockLength : ((2 : ℝ) ^ T)⁻¹ =
      (((2 : ℝ) ^ p.T (p.lev child))⁻¹) / Φ.F.q)
    (hblock : ∀ t ∈ IS T j, Φ.F.t₀ + Φ.F.q * t ∈
      Icc ((p.bin child : ℝ) / (2 : ℝ) ^ p.T (p.lev child))
        (((p.bin child : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev child)))
    (l₀ : Trajectory) (hl₀ : l₀ ∈ p.assigned child)
    (hcoeff : |Φ.eb l₀ 0| ≤ H ∧ |Φ.eb l₀ 1| ≤ H ∧
      |Φ.eb l₀ 3| ≤ H ∧ |Φ.eb l₀ 4| ≤ H) :
    ∃ c : Fin 5 → ℝ, (∀ e, |c e| ≤ 16 * H ^ 4) ∧
      ∀ l ∈ p.assigned child,
        (∀ t ∈ IS T j,
          |(exS Φ.eb l t) 1 - c 0 - t * c 1| ≤ 16 * H ^ 4 / (2 : ℝ) ^ T ∧
          |(exS Φ.eb l t) 2 - c 2 - t * c 3 - c 4 * (exS Φ.eb l t) 1| ≤
            16 * H ^ 4 / (2 : ℝ) ^ T * g) ∧
        |Φ.eb l 4 - c 3 - c 4 * Φ.eb l 3| ≤ 16 * H ^ 4 * g := by
  let q₁ := ((2 : ℝ) ^ p.T (p.lev child))⁻¹
  have hq₁ : 0 < q₁ := by dsimp [q₁]; positivity
  have hQ₀ := (hp.chart parent).1
  have hQ₁ := (hp.chart child).1
  have hΦD : Φ.F.D.det ≠ 0 := by rw [hD]; exact MajorFrame.det_ne_zero hQ₀
  have hrows := relative_rows_of_no_original_candidate hp hNk Mc d₁ ρ gain ε Hset hno
    child h hgain hupper hroom hprior hbias V hne hV hfloor Φ Kparent hKparent hparentVelocity
  have hrowsH : ∀ e : Fin 2,
      ‖frameRow (relativeVelocityFrame Φ.F.q q₁ (MajorFrame.frame (p.frame parent))
        (p.frame child)) e‖ ≤ H := by
    intro e
    have hh := (hrows e).trans hrowBudget
    simpa only [← hD, frameRow, q₁] using hh
  have hminor := MajorFrame.minor_le_of_normalized_area (p.frame parent) hQ₀
    Φ.F.q H hq₀ hH hparentFull hparentArea
  have hdet : |(relativeVelocityFrame Φ.F.q q₁ (MajorFrame.frame (p.frame parent))
      (p.frame child)).det| ≤ H * g := by
    simpa only [← hD, q₁] using hrelativeDet
  have hbudgets := MajorFrame.relative_position_row_budgets (p.frame parent) (p.frame child)
    hQ₀ Φ.F.q q₁ H g hq₀ hq₁ hH hparentUpper hminor hchildFull hrowsH hdet
  have hfit := Φ.child_fit hq₀.ne' hΦD (p.frame child) (p.center child) (p.velocity child)
    (p.assigned child) _ (IS T j) p.κ hblock
    (fun l hl t ht => (((hp.chart child).2.2.2.2.2.2.2.2.2.1 l hl).2.2 t ht).1)
  apply quantitative_tilted_label Φ.eb (p.assigned child) l₀ hl₀ T j
    (Φ.childMatrix (p.frame child)) (Φ.childMatrix_det_ne_zero hΦD _ hQ₁)
    (Φ.childCenter (p.center child) (p.velocity child)) (Φ.childSpeed (p.velocity child))
    p.κ H g (zero_le_one.trans hp.one_le_slack) hκH hH hg hfit hcoeff
  · simpa only [PFrame.childMatrix, hD, hblockLength, q₁] using hbudgets.1
  · simpa only [PFrame.childMatrix, hD, hblockLength, q₁] using hbudgets.2.1
  · simpa only [PFrame.childMatrix, hD, hblockLength, q₁] using hbudgets.2.2

/-- Put the geometric output into the exact coefficient/tracking shape
of the source-stage facts, at any larger final model slack. -/
theorem tilted_label_with_model_slack
    {α : Type} (b : α → Fin 6 → ℝ) (A : Set α) (T : ℕ) (j : Fin (2 ^ T))
    (Kgeom K g : ℝ) (hK : Kgeom ≤ K) (hg : 0 ≤ g)
    (hgeometry : ∃ c : Fin 5 → ℝ, (∀ e, |c e| ≤ Kgeom) ∧
      ∀ l ∈ A,
        (∀ t ∈ IS T j,
          |(exS b l t) 1 - c 0 - t * c 1| ≤ Kgeom / (2 : ℝ) ^ T ∧
          |(exS b l t) 2 - c 2 - t * c 3 - c 4 * (exS b l t) 1| ≤
            Kgeom / (2 : ℝ) ^ T * g) ∧
        |b l 4 - c 3 - c 4 * b l 3| ≤ Kgeom * g) :
    ∃ c : Fin 5 → ℝ, (∀ e, |c e| ≤ K) ∧
      ∀ l ∈ A, ∀ t ∈ IS T j,
        |(exS b l t) 1 - c 0 - t * c 1| ≤ K * (2 : ℝ) ^ (-(T : ℤ)) ∧
        |(exS b l t) 2 - c 2 - t * c 3 - c 4 * (exS b l t) 1| ≤
          K * (2 : ℝ) ^ (-(T : ℤ)) * g ∧
        |b l 4 - c 3 - c 4 * b l 3| ≤ K * g := by
  obtain ⟨c, hc, htrack⟩ := hgeometry
  refine ⟨c, fun e => (hc e).trans hK, fun l hl t ht => ?_⟩
  obtain ⟨hpos, hvel⟩ := htrack l hl
  obtain ⟨hpos₀, hpos₁⟩ := hpos t ht
  have hq : 0 ≤ ((2 : ℝ) ^ T)⁻¹ := by positivity
  have hwidth : Kgeom / (2 : ℝ) ^ T ≤ K * (2 : ℝ) ^ (-(T : ℤ)) := by
    simpa only [zpow_neg, zpow_natCast, div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right hK hq
  exact ⟨hpos₀.trans hwidth,
    hpos₁.trans (mul_le_mul_of_nonneg_right hwidth hg),
    hvel.trans (mul_le_mul_of_nonneg_right hK hg)⟩

end

end Submission.Obl.k4_finite_affine_parent_sources
