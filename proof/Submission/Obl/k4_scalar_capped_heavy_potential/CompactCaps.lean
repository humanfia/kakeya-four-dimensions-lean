import Submission.Obl.k4_tempered_grid_selection.Exponents
import Submission.Obl.k4_scalar_capped_heavy_potential.Scales

namespace Submission.Obl.k4_scalar_capped_heavy_potential

open Set MeasureTheory Filter
open Submission.Obl.k4_tempered_grid_selection

noncomputable section

theorem eventually_radius_ge (J : ℕ → ℕ) (hJ : Tendsto J atTop atTop) (R : ℝ) :
    ∀ᶠ k in atTop, R ≤ (J k : ℝ) + 2 := by
  filter_upwards [hJ.eventually (eventually_ge_atTop ⌈R⌉₊)] with k hk
  have hR := Nat.le_ceil R
  have hc : (⌈R⌉₊ : ℝ) ≤ (J k : ℝ) := by exact_mod_cast hk
  linarith

theorem compact_exponent_range_mono {R U r : ℝ} (hR : 0 < R) (hRU : R ≤ U)
    (hr₀ : R⁻¹ ≤ r) (hr₁ : r ≤ R) : U⁻¹ ≤ r ∧ r ≤ U := by
  have hInv : U⁻¹ ≤ R⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hR hRU
  exact ⟨hInv.trans hr₀, hr₁.trans hRU⟩

/-- An exact physical mesh has an exponent in one fixed compact range;
the horizon loss does not force the original cap to be rounded. -/
theorem exists_physical_mesh_exponent {N H h κ Z : ℝ}
    (hN : 1 < N) (hH : 0 < H) (hHN : H ≤ N) (hh : 0 < h)
    (hκ : 0 ≤ κ) (hZ : 2 ≤ Z)
    (hlo : N ^ (-κ) / H ≤ h) (hup : h ≤ H * N ^ (-κ)) :
    ∃ r : ℝ, 1 ≤ r ∧ r ≤ Z + κ + 1 ∧ N ^ (-r) = h * N ^ (-Z) := by
  have hN₀ : 0 < N := by linarith
  let r := logarithmicExponent N (h * N ^ (-Z))
  have hid : N ^ (-r) = h * N ^ (-Z) :=
    rpow_neg_logarithmicExponent hN (by positivity)
  have hr := normalized_mesh_exponent_bounds hN hH hHN hlo hup hid
  exact ⟨r, by linarith [hr.1], hr.2, hid⟩

/-- Original caps on a compact exponent interval give the cap at the
exact normalized-cell physical mesh and target hidden width. -/
theorem original_rectangle_at_target_mesh {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) (base : Ω → Fin 2 → ℝ) (X : Ω → ℝ)
    {N H h κ Z R c d K L : ℝ}
    (hN : 1 < N) (hH : 0 < H) (hHN : H ≤ N) (hh : 0 < h)
    (hκ : 0 ≤ κ) (hZ : 2 ≤ Z) (hR₂ : 2 ≤ R) (hRmesh : Z + κ + 1 ≤ R)
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) (hKL : K ≤ L)
    (hlo : N ^ (-κ) / H ≤ h) (hup : h ≤ H * N ^ (-κ))
    (hcap : ∀ r s : ℝ, R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R →
      ∀ (q : Fin 2 → ℤ) (j : ℤ),
        ρ {p | (fun i => (⌊base p i / (N ^ (-r))⌋ : ℤ)) = q ∧
          (⌊X p / (N ^ (-s))⌋ : ℤ) = j} ≤ ENNReal.ofReal (K * N ^ (-2 * r - d * s)))
    (q : Fin 2 → ℤ) (j : ℤ) :
    ρ {p | (fun i => (⌊base p i / (h * N ^ (-Z))⌋ : ℤ)) = q ∧
      (⌊X p / (N ^ (-1 - c))⌋ : ℤ) = j} ≤
        ENNReal.ofReal (L * (h * N ^ (-Z)) ^ 2 * (N ^ (-1 - c)) ^ d) := by
  obtain ⟨r, hr₀, hr₁, hpow⟩ := exists_physical_mesh_exponent hN hH hHN hh hκ hZ hlo hup
  have hInv : R⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (by linarith : 1 ≤ R)
  have hs₀ : R⁻¹ ≤ 1 + c := hInv.trans (by linarith)
  have hs₁ : 1 + c ≤ R := by linarith
  have hN₀ : 0 < N := by linarith
  have hw : N ^ (-(1 + c)) = N ^ (-1 - c) := by congr 1; ring
  have ht := hcap r (1 + c) (hInv.trans hr₀) (hr₁.trans hRmesh) hs₀ hs₁ q j
  rw [rectangular_power_factor hN₀ r (1 + c) d, hpow, hw] at ht
  apply ht.trans
  apply ENNReal.ofReal_le_ofReal
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hKL (sq_nonneg (h * N ^ (-Z))))
    (by positivity : 0 ≤ (N ^ (-1 - c)) ^ d)

end
end Submission.Obl.k4_scalar_capped_heavy_potential
