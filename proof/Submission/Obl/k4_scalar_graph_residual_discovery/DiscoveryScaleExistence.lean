import Submission.Obl.k4_scalar_graph_residual_discovery.DiscoveryPrecision
import Submission.Obl.k4_scalar_graph_residual_discovery.DiscoveryPowerBounds

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Filter
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

/-- Fixed graph precision and two fixed integer scale depths suffice for
all later physical scale records, independently of their power budgets. -/
theorem exists_discovery_scale_parameters (M : ℕ) (hM : 2 ≤ M)
    {κ cζ L : ℝ} (hκ : 0 < κ) (hcζ : 0 < cζ) (hL : 0 < L) :
    ∃ C C₁ : ℕ, 1 ≤ C ∧ 1 ≤ C₁ ∧ ∃ L' : ℝ,
      L ≤ L' ∧ 0 < L' ∧ (C₁ : ℝ) ≤ L' ∧
      ∀ (N H Hg K h : ℕ → ℝ) (m : ℕ → ℕ),
        (∀ k, 1 ≤ N k) → Tendsto N atTop atTop →
        Subpower N H → Subpower N Hg → Subpower N K →
        (∀ k, 1 ≤ m k) → (∀ k, 0 < h k) →
        (∀ᶠ k in atTop, N k ^ (-κ) / K k ≤ h k) →
        ∀ B : ℝ, L' + 10 ≤ B → ∀ J₁ : ℕ, 2 / (J₁ : ℝ) < 1 →
        ∀ τ : ℝ, 0 < τ → ∃ T : ℝ, 1 < T ∧
          ∀ᶠ k in atTop, Nonempty (DiscoveryScaleBounds (N k) (H k) (Hg k) L' B (h k)
            cζ T τ (m k) M C₁ C J₁) := by
  obtain ⟨C, hCgt⟩ := exists_nat_gt (max (κ * cζ + 2) 1)
  have hC1 : (1 : ℝ) < C := (le_max_right _ _).trans_lt hCgt
  have hC : 1 ≤ C := by exact_mod_cast hC1.le
  have hC0 : 0 ≤ (C : ℝ) := Nat.cast_nonneg _
  have hCκ : κ * cζ < C := by
    have hh := (le_max_left _ _).trans_lt hCgt
    linarith
  obtain ⟨C₁, hC₁gt⟩ := exists_nat_gt (max ((C : ℝ) + 10)
    (κ * ((M : ℝ) + 1 / 8) + 10))
  have hC₁C : (C : ℝ) + 2 ≤ C₁ := by
    have hh := (le_max_left _ _).trans_lt hC₁gt
    linarith
  have hC₁κ : κ * ((M : ℝ) + 1 / 8) + 2 ≤ C₁ := by
    have hh := (le_max_right _ _).trans_lt hC₁gt
    linarith
  have hC₁1 : (1 : ℝ) ≤ C₁ := by linarith
  have hC₁ : 1 ≤ C₁ := by exact_mod_cast hC₁1
  let L' := max L ((C₁ : ℝ) + C + 10)
  have hLL' : L ≤ L' := le_max_left _ _
  have hL' : 0 < L' := hL.trans_le hLL'
  have hL'margin : (C₁ : ℝ) + C + 2 ≤ L' := by
    have hh := le_max_right L ((C₁ : ℝ) + C + 10)
    change (C₁ : ℝ) + C + 2 ≤ max L _
    linarith
  have hC₁L : (C₁ : ℝ) ≤ L' := by linarith
  refine ⟨C, C₁, hC, hC₁, L', hLL', hL', hC₁L, ?_⟩
  intro N H Hg K h m hN hNt hH hHg hK hm hh hscale B hB J₁ hJ τ hτ
  let T : ℝ := (C₁ : ℝ) + C + τ + τ⁻¹ + 10
  have hτinv : 0 < τ⁻¹ := inv_pos.mpr hτ
  have hT : 1 < T := by dsimp only [T]; linarith
  have hT1 : 1 ≤ T := hT.le
  have hTinv : T⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one hT1
  have hτT : τ ≤ T := by dsimp only [T]; linarith
  have hτinvT : τ⁻¹ ≤ T := by dsimp only [T]; linarith
  have hTτ : T⁻¹ ≤ τ := by
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le (inv_pos.mpr hτ) hτinvT
  have hCfineT : (C₁ : ℝ) + C + 1 ≤ T := by
    dsimp only [T]
    have hi : 0 < τ⁻¹ := inv_pos.mpr hτ
    linarith
  refine ⟨T, hT, ?_⟩
  filter_upwards [eventually_discovery_precision hN hNt hH hHg hK hh hM hcζ hCκ hC0
    hC₁C hC₁κ hL'margin hB hJ hscale] with k hp
  have hmR : (1 : ℝ) ≤ m k := by exact_mod_cast hm k
  have hmpos : (0 : ℝ) < m k := zero_lt_one.trans_le hmR
  have hinv : 1 / (m k : ℝ) ≤ 1 := by
    simpa only [one_div_one] using one_div_le_one_div_of_le zero_lt_one hmR
  refine ⟨{
    a := (C₁ : ℝ)
    coarse_mesh := ⟨C₁ * m k, ?_⟩
    coarse_lower := hTinv.trans hC₁1
    fine_upper := by linarith
    tau_lower := hTτ
    tau_upper := hτT
    coarse_floor := by linarith
    row_precision := le_rfl
    graph_precision := hC₁L
    fine_precision := by linarith
    point_precision := hp.point_precision
    variation := hp.variation
    residual_precision := hp.residual_precision
    support_precision := hp.support_precision
    graph_margin := hp.graph_margin
    row_margin := hp.row_margin
    floor_margin := hp.floor_margin
  }⟩
  rw [Nat.cast_mul, mul_div_cancel_right₀ _ hmpos.ne']

end Submission.Obl.k4_scalar_graph_residual_discovery
