-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.FullAxisPruning
import Submission.Obl.k4_finite_affine_parent_sources.AxisChargeNumerics
import Submission.Obl.k4_quadratic_finite_greedy_cover.ScaleTransfer

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Submission.Lib.K4XInterface
open scoped Classical ENNReal

noncomputable section

section Valid

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- Every eligible nominal half-depth lies in the interval where the
original terminal angular law can charge it. -/
theorem PathData.Valid.nominal_half_depth_bounds (hL : 0 ≤ L) (hδ : δ₀ ≤ 1 / 2)
    (i : ℕ) (hi : i < m) (hsg : sg i ≤ 1 / 2) : 0 < p.r i ∧ p.r i ≤ L := by
  have hb := hp.level_bounds i hi
  have h1 := (abs_le.mp hb.1).2
  have h2 := mul_le_mul_of_nonneg_right hsg hL
  have h3 := mul_le_mul_of_nonneg_right hδ hL
  exact ⟨hb.2.1, by linarith⟩

/-- A power-sized axis deficiency has an explicit original-law charge.
The cell count costs at most `130 κ^5`; the two terminal density
exceptions are charged under the same original world weights. -/
theorem PathData.Valid.deficient_level_power_charge
    [∀ w, IsProbabilityMeasure (ν w)]
    (hE : ∀ w, E w ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hNk : 1 ≤ Nk) (i : ℕ) (hr : 0 ≤ p.r i) (hrL : p.r i ≤ L)
    (a S τ : ℝ)
    (g : Fin W → Observation → ℝ≥0∞) (hg : ∀ w, Measurable (g w))
    (hmap : ∀ w, Measure.map (gobs (B w) (gδ Nk L))
      (((ν w).prod volume).restrict (E w)) =
        (volume.prod Measure.count).withDensity (g w))
    (G : Fin W → Observation × (Fin 2 → ℤ) → ℝ≥0∞)
    (hG : ∀ w, Measurable (G w))
    (hmapG : ∀ w, Measure.map (fun z : Incidence =>
      (gobs (B w) (gδ Nk L) z, fun e : Fin 2 => ⌊gv z.1 e / gδ Nk a⌋))
      (((ν w).prod volume).restrict (E w)) =
        ((volume.prod Measure.count).prod Measure.count).withDensity (G w)) :
    (∑ b, if p.lev b = i ∧ p.axisDeficient (Nk ^ (-a)) b then
      ENNReal.ofReal (ω (p.world b)) * (ν (p.world b)).prod volume (p.counted b) else 0) ≤
      ENNReal.ofReal (130 * p.κ ^ 5 * Nk ^ (-S * a + 2 * τ)) *
        (∑ w, ENNReal.ofReal (ω w) * (((ν w).prod volume).restrict (E w)) univ) +
      ENNReal.ofReal (2 * p.κ) *
        ∑ w, ENNReal.ofReal (ω w) * (((ν w).prod volume).restrict (E w))
          {z | ENNReal.ofReal (Nk ^ (-f L - S * a + τ)) <
              G w (gobs (B w) (gδ Nk L) z, fun e : Fin 2 => ⌊gv z.1 e / gδ Nk a⌋) ∨
            g w (gobs (B w) (gδ Nk L) z) < ENNReal.ofReal (Nk ^ (-f L - τ))} := by
  classical
  have hN0 : 0 < Nk := lt_of_lt_of_le zero_lt_one hNk
  have hκ : 0 ≤ p.κ := zero_le_one.trans hp.one_le_slack
  have hmesh : Nk ^ (-a) ≤ gδ Nk a :=
    (Submission.Obl.k4_quadratic_finite_greedy_cover.δ_bounds hN0 a).1
  have hmesh0 : 0 < gδ Nk a := (Real.rpow_pos_of_pos hN0 _).trans_le hmesh
  obtain ⟨Kc, M, hKc, hKreal, hcells, hMreal⟩ :=
    axis_integer_budgets p.κ (Nk ^ (-a)) (gδ Nk a) hp.one_le_slack
      (Real.rpow_nonneg hN0.le _) hmesh0 hmesh
  have hK : (Kc : ℝ≥0∞) ≤ ENNReal.ofReal (2 * p.κ) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hKreal
  have hM : (M : ℝ≥0∞) ≤ ENNReal.ofReal (65 * p.κ ^ 4) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hMreal
  let α := ENNReal.ofReal (Nk ^ (-f L - S * a + τ))
  let β := ENNReal.ofReal (Nk ^ (-f L - τ))
  have hβ : β ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hN0 _)).ne'
  have hratio : α / β = ENNReal.ofReal (Nk ^ (-S * a + 2 * τ)) :=
    axis_angular_reference_ratio hN0 (f L) S a τ
  have hcoef : (Kc : ℝ≥0∞) * M * (α / β) ≤
      ENNReal.ofReal (130 * p.κ ^ 5 * Nk ^ (-S * a + 2 * τ)) := by
    rw [hratio]
    calc
      _ ≤ ENNReal.ofReal (2 * p.κ) * ENNReal.ofReal (65 * p.κ ^ 4) *
          ENNReal.ofReal (Nk ^ (-S * a + 2 * τ)) :=
        mul_le_mul' (mul_le_mul' hK hM) le_rfl
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  have hcharge := hp.deficient_level_mass_le hE hNk i hr hrL (gδ Nk a) hmesh0
    (Nk ^ (-a)) (Real.rpow_nonneg hN0.le _) g hg hmap G hG hmapG Kc M hKc hcells α β hβ
  exact hcharge.trans (add_le_add (mul_le_mul' hcoef le_rfl) (mul_le_mul' hK le_rfl))

end Valid

end

end Submission.Obl.k4_finite_affine_parent_sources
