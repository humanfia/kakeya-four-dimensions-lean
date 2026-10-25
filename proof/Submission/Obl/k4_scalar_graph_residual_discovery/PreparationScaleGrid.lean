/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file PreparationScaleGrid.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.PowerScaleGrid
import Submission.Obl.k4_scalar_graph_residual_discovery.ExponentGrid
import Submission.Obl.k4_scalar_grid_parameter_preparation.CommonScaleMasks

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set
open Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

/-- Round only the selected finite exponent grid onto the preparation
mesh. Its cardinality does not depend on M. -/
def preparationScaleGrid (M J C : ℕ) (a : ℝ) : Finset ℝ :=
  (insert 0 (positiveScaleGrid J C)).image (fun s => upperGridExponent M (a + s))

theorem preparationScaleGrid_card_le (M J C : ℕ) (a : ℝ) :
    (preparationScaleGrid M J C a).card ≤ C * J + 1 :=
  Finset.card_image_le.trans ((Finset.card_insert_le _ _).trans
    (Nat.add_le_add_right (positiveScaleGrid_card_le J C) 1))

theorem preparationScaleGrid_on_mesh {M J C : ℕ} {a u : ℝ}
    (hu : u ∈ preparationScaleGrid M J C a) :
    ∃ m : ℕ, u = (m : ℝ) / (M : ℝ) := by
  obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hu
  exact upperGridExponent_on_grid M (a + s)

/-- Every relative real scale uses one of only C*J+1 preparation levels.
The finer original coefficient width is at most rho*r and at least
rho*r/(H*N^(1/J)); here rho=N^-a uses the ACTUAL coarse exponent a. -/
theorem exists_prepared_relative_scale {N H a : ℝ} (hN : 1 < N)
    (M J C : ℕ) (hM : 1 ≤ M) (hJ : 1 ≤ J)
    (hcost : N ^ (1 / (M : ℝ)) ≤ H) (ha : 0 ≤ a)
    {r : ℝ} (hr : N ^ (-(C : ℝ)) ≤ r) (hr₁ : r ≤ 1) :
    ∃ u ∈ preparationScaleGrid M J C a,
      (∃ m : ℕ, u = (m : ℝ) / (M : ℝ)) ∧ a ≤ u ∧
        u ≤ a + (C : ℝ) + 1 / (M : ℝ) ∧
          N ^ (-u) ≤ N ^ (-a) * r ∧
            N ^ (-a) * r ≤ (H * N ^ (1 / (J : ℝ))) * N ^ (-u) := by
  classical
  have hN₀ : 0 < N := by linarith
  have hJ₀ : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  obtain ⟨s, hsg, _, hsr, hrs⟩ := (powerScaleGrid_rounding hN J C hJ).finer r hr hr₁
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hsg
  have htbound : 0 ≤ t ∧ t ≤ (C : ℝ) := by
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact ⟨le_rfl, Nat.cast_nonneg C⟩
    · have hb := positiveScaleGrid_mem_bounds (by omega : 0 < J) ht
      exact ⟨(one_div_pos.mpr hJ₀).le.trans hb.1, hb.2.1⟩
  let u := upperGridExponent M (a + t)
  have hu := upperGridExponent_bounds hM (add_nonneg ha htbound.1)
  have hwidth := grid_width_comparison hN.le hM hcost (add_nonneg ha htbound.1)
  have hpow : N ^ (-(a + t)) = N ^ (-a) * N ^ (-t) := by
    rw [neg_add, Real.rpow_add hN₀]
  rw [hpow] at hwidth
  have hβ : 0 < N ^ (-u) := Real.rpow_pos_of_pos hN₀ _
  have hρ : 0 < N ^ (-a) := Real.rpow_pos_of_pos hN₀ _
  have hraw : N ^ (-a) * N ^ (-t) ≤ H * N ^ (-u) :=
    (div_le_iff₀ hβ).mp hwidth.2
  refine ⟨u, Finset.mem_image.mpr ⟨t, ht, rfl⟩,
    upperGridExponent_on_grid M (a + t), by linarith only [hu.1, htbound.1],
    by linarith only [hu.2, htbound.2], ?_, ?_⟩
  · exact hwidth.1.trans (mul_le_mul_of_nonneg_left hsr hρ.le)
  · calc
      N ^ (-a) * r ≤ N ^ (-a) * (N ^ (1 / (J : ℝ)) * N ^ (-t)) :=
        mul_le_mul_of_nonneg_left hrs hρ.le
      _ = N ^ (1 / (J : ℝ)) * (N ^ (-a) * N ^ (-t)) := by ring
      _ ≤ N ^ (1 / (J : ℝ)) * (H * N ^ (-u)) :=
        mul_le_mul_of_nonneg_left hraw (Real.rpow_nonneg hN₀.le _)
      _ = _ := by ring

end

end Submission.Obl.k4_scalar_graph_residual_discovery
