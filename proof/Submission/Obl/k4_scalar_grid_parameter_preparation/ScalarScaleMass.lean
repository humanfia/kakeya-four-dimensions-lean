/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/ScalarScaleMass.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.ScalarScalePackets
import Submission.Obl.k4_scalar_grid_parameter_preparation.ScalarPacketSteep
import Submission.Obl.k4_scalar_grid_parameter_preparation.PacketCount

/-! Original-law omission budget for the measurable scalar core at one thickness. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory MvPolynomial
open Submission.Obl.k4_fixed_budget_quadratic_recovery
open scoped ENNReal

theorem exists_scalar_scale_core_mass_bound {X : Type*}
    [MeasurableSpace X] : ∃ C₀ : ℝ, 1 ≤ C₀ ∧
    ∀ (G : Type*) [DecidableEq G] (K ξ : ℝ) (n q : ℕ) (a : X → Fin 5 → ℝ)
      (D : ScalarScalePackets X G a K ξ n q)
      (ν : Measure X), IsProbabilityMeasure ν →
    ∀ (μ : Measure (X × ℝ)) (E : Set (X × ℝ)) (g : G) (π : Measure ℝ)
      (δ β M U W : ℝ) (P : ℝ≥0∞),
      1 ≤ K → 0 < ξ → 0 < q → 0 < δ → δ ≤ (q : ℝ)⁻¹ → ξ ≤ K * (q : ℝ)⁻¹ →
      0 < M → 0 < β → 0 ≤ U → 0 < W →
      C₀ * K ^ 2 + 1 + K ≤ M * β →
      162 * (1200 * K * (2 * K / (q : ℝ)⁻¹) ^ 4) * (2 * K) ^ 4 * δ ≤ 1 →
      162 * (1200 * K * (2 * K / (q : ℝ)⁻¹) ^ 4) * (2 * K) ^ 4 * δ ≤ ξ →
      (∀ p ∈ E, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |a p.1 e| ≤ K) →
      (∀ i, D.world i = g → ENNReal.ofReal (W / (K * (q : ℝ))) ≤ ν (D.labels i)) →
      μ (scalarScaleCovered D g)ᶜ = 0 →
      (∀ i j b c : ℤ, μ {p | (⌊p.2 / δ⌋ : ℤ) = i ∧
        (⌊scalarY (a p.1) p.2 / δ⌋ : ℤ) = j ∧ (⌊scalarX (a p.1) p.2 / ξ⌋ : ℤ) = b ∧
        a p.1 1 ∈ scalarVelocityBin β c} ≤ ENNReal.ofReal (U * δ ^ 2 * W) * π (scalarVelocityBin β c)) →
      (∀ c : ℤ, π (scalarVelocityBin β c) ≤ P) →
      μ (E \ scalarScaleCore D E M g) ≤
        ENNReal.ofReal (1600 * (8 * K + 2) * (4 * K + 4) * U * K) * P := by
  obtain ⟨C₀, hC₀, hpacket⟩ := exists_scalar_steep_packet_mass_bound (X := X)
  refine ⟨C₀, hC₀, ?_⟩
  intro G _ K ξ n q a D ν hν μ E g π δ β M U W P hK hξ hq hδ hδq hrate
    hM hβ hU hW hforecast hfreeze hvalue hE hfloor hcovered hjoint hangular
  letI : IsProbabilityMeasure ν := hν
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  let C := 1600 * (8 * K + 2) * (4 * K + 4) * U
  have hbad (i : Fin n) (hi : D.world i = g) :
      μ (scalarScaleBad D E M i) ≤ ENNReal.ofReal (C * W / (q : ℝ) ^ 2) * P := by
    have hm := hpacket μ E a (D.labels i) (D.predictor i) π K
      (((D.block i : ℕ) : ℝ) / q) (q : ℝ)⁻¹ (D.centerY i) (D.centerV i)
      δ ξ β M U W P (D.predictor_degree i) hK (scalarPacketBlock_start_unit hq (D.block i))
      (scalarPacketBlock_end_le_one hq (D.block i)) (inv_pos.mpr hqR) hδ hξ hδq hrate
      hM hβ hU hW.le (D.center_bound i) hforecast hfreeze hvalue hE
      (D.predictor_norm i) (D.trajectory_fit i) hjoint hangular
    have he : 1600 * (8 * K + 2) * (4 * K + 4) * U * ((q : ℝ)⁻¹) ^ 2 * W =
        C * W / (q : ℝ) ^ 2 := by
      dsimp [C]
      rw [div_eq_mul_inv, inv_pow]
      ring
    simpa only [scalarScaleBad, scalarPacketBlock, he] using hm
  have hunion := saturated_packet_exception_mass_le ν μ D.world D.block D.labels
    (scalarScaleBad D E M) g K W C hKpos hW (by dsimp [C]; positivity) hq
    D.labels_measurable D.labels_disjoint hfloor P hbad
  have hsub : E \ scalarScaleCore D E M g ⊆ (scalarScaleCovered D g)ᶜ ∪
      ⋃ i ∈ (Finset.univ.filter fun i => D.world i = g), scalarScaleBad D E M i := by
    intro p hp
    by_cases hc : p ∈ scalarScaleCovered D g
    · by_cases hb : p ∈ ⋃ i ∈ (Finset.univ.filter fun i => D.world i = g), scalarScaleBad D E M i
      · exact Or.inr hb
      · exact False.elim (hp.2 ⟨⟨hp.1,hc⟩,hb⟩)
    · exact Or.inl hc
  calc
    _ ≤ μ ((scalarScaleCovered D g)ᶜ ∪
        ⋃ i ∈ (Finset.univ.filter fun i => D.world i = g), scalarScaleBad D E M i) := measure_mono hsub
    _ ≤ μ (scalarScaleCovered D g)ᶜ +
        μ (⋃ i ∈ (Finset.univ.filter fun i => D.world i = g), scalarScaleBad D E M i) := measure_union_le _ _
    _ ≤ _ := by simpa only [hcovered, zero_add, C] using hunion

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
