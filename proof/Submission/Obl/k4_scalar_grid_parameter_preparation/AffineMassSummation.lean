import Submission.Obl.k4_scalar_grid_parameter_preparation.PaletteCellMass
import Submission.Lib.K4QuadraticSublevel

/-! Sum conditional affine estimates with the original probability palette. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped Classical BigOperators ENNReal

theorem affine_cell_mass_sum {X : Type*} [MeasurableSpace X]
    (μ : Measure (X × ℝ)) (π : Measure ℝ) [IsProbabilityMeasure π]
    (a : X → Fin 5 → ℝ) (E : Set (X × ℝ)) (ξ B δ : ℝ)
    (hξ : 0 < ξ) (hξ₁ : ξ ≤ 1) (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hbounded : ∀ p ∈ E, |a p.1 0| ≤ B ∧ |a p.1 1| ≤ B)
    (hcap : ∀ q c : ℤ,
      μ {p | p ∈ E ∧ (⌊a p.1 0 / ξ⌋ : ℤ) = q ∧ (⌊a p.1 1 / ξ⌋ : ℤ) = c} ≤
        ENNReal.ofReal (ξ * δ) * π (scalarVelocityBin ξ c)) :
    μ E ≤ ENNReal.ofReal (6 * B * δ) := by
  classical
  obtain ⟨hfinite,hcount⟩ := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    (Set.Icc (-B) B) (by linarith : 0 ≤ 2 * B) hξ 0 (by
      intro x hx y hy
      rw [Real.dist_eq]
      exact abs_le.mpr ⟨by linarith [hx.1,hy.2],by linarith [hx.2,hy.1]⟩)
  simp only [sub_zero] at hfinite hcount
  let D : Finset ℤ := hfinite.toFinset
  let F : Finset (ℤ × ℤ) := D ×ˢ D
  let code : X × ℝ → ℤ × ℤ := fun p => (⌊a p.1 0 / ξ⌋,⌊a p.1 1 / ξ⌋)
  have hD (x : ℝ) (hx : |x| ≤ B) : (⌊x / ξ⌋ : ℤ) ∈ D :=
    hfinite.mem_toFinset.mpr ⟨x,abs_le.mp hx,rfl⟩
  have hDcard : (D.card : ℝ) ≤ 6 * B / ξ := by
    rw [← Set.ncard_eq_toFinset_card _ hfinite]
    have hr : 1 ≤ B / ξ := (one_le_div hξ).mpr (hξ₁.trans hB)
    apply hcount.trans
    calc
      _ = 4 * (B / ξ) + 2 := by ring
      _ ≤ 6 * (B / ξ) := by linarith
      _ = _ := by ring
  have hcover (p : X × ℝ) (hp : p ∈ E) : code p ∈ F :=
    Finset.mem_product.mpr ⟨hD _ (hbounded p hp).1,hD _ (hbounded p hp).2⟩
  have hcap' (qc : ℤ × ℤ) (hqc : qc ∈ F) :
      μ {p | p ∈ E ∧ code p = qc} ≤
        ENNReal.ofReal (ξ * δ) * π (scalarVelocityBin ξ qc.2) := by
    rcases qc with ⟨q,c⟩
    simpa only [code,Prod.mk.injEq] using hcap q c
  have hmass := joint_palette_cell_mass_le μ E code F hcover
    (fun c => π (scalarVelocityBin ξ c))
    (sum_scalar_velocity_bin_masses_le_one π ξ _) (ENNReal.ofReal (ξ * δ)) hcap'
  have hfst : F.image Prod.fst ⊆ D := by
    intro q hq
    obtain ⟨qc,hqc,rfl⟩ := Finset.mem_image.mp hq
    exact (Finset.mem_product.mp hqc).1
  calc
    μ E ≤ ENNReal.ofReal (ξ * δ) * ((F.image Prod.fst).card : ℝ≥0∞) := by
      convert hmass using 1
      congr 3
      ext q
      simp only [Finset.mem_image]
    _ ≤ ENNReal.ofReal (ξ * δ) * (D.card : ℝ≥0∞) :=
      mul_le_mul' le_rfl (Nat.cast_le.mpr (Finset.card_le_card hfst))
    _ ≤ ENNReal.ofReal (ξ * δ) * ENNReal.ofReal (6 * B / ξ) := by
      apply mul_le_mul' le_rfl
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hDcard
    _ = ENNReal.ofReal ((ξ * δ) * (6 * B / ξ)) :=
      (ENNReal.ofReal_mul (mul_nonneg hξ.le hδ)).symm
    _ = ENNReal.ofReal (6 * B * δ) := by
      congr 1
      field_simp

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
