/-
Adapted from: here:o018
-/
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.DensityClasses
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SmallPowers

/-!
The finite density-type selection in Lemma `a01:homogenization`.
The simultaneous pigeonhole and logarithmic counting estimates are imported
from WangZahlLot rather than reproved here.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Lib.K4Homogenization

open WangZahlLot.Obl.wz_clustered_cover_volume_gain

/-- Finitely many logarithmic density classes cost less than any prescribed power. -/
theorem dyadic_density_loss_subpower (k : ℕ) {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      (((Scale.dyExp (N ^ C) (N ^ (-C)) + 1) ^ k : ℕ) : ℝ) ≤ N ^ ε := by
  let θ : ℝ := ε / ((k : ℝ) + 1)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  obtain ⟨d, hd, hbound⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.dyadic_size_power_bound
      (M := 1) (k := 2 * C) (ν := θ) le_rfl (by positivity) hθ
  refine ⟨max 2 d⁻¹, le_max_left _ _, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hdinv : d⁻¹ ≤ N := (le_max_right _ _).trans hN
  have hδd : N⁻¹ ≤ d := (inv_le_comm₀ hN0 hd).mpr hdinv
  have hratio : N ^ C / N ^ (-C) = 1 / (N⁻¹) ^ (2 * C) := by
    calc
      N ^ C / N ^ (-C) = N ^ C * N ^ C := by
        rw [Real.rpow_neg hN0.le, div_inv_eq_mul]
      _ = N ^ (2 * C) := by rw [← Real.rpow_add hN0]; congr 1; ring
      _ = 1 / (N⁻¹) ^ (2 * C) := by rw [Real.inv_rpow hN0.le, one_div, inv_inv]
  have hscale : Scale.dyExp (N ^ C) (N ^ (-C)) =
      Scale.dyExp 1 ((N⁻¹) ^ (2 * C)) := by
    unfold Scale.dyExp
    rw [hratio]
  have hinv : (N⁻¹) ^ (-θ) = N ^ θ := by
    rw [Real.inv_rpow hN0.le, Real.rpow_neg hN0.le, inv_inv]
  have hsize := hbound N⁻¹ (inv_pos.mpr hN0) (inv_le_one_of_one_le₀ hN1) hδd
  rw [hinv, ← hscale] at hsize
  have hD : ((Scale.dyExp (N ^ C) (N ^ (-C)) + 1 : ℕ) : ℝ) ≤ N ^ θ := by
    push_cast
    linarith [show 0 ≤ (Scale.dyExp (N ^ C) (N ^ (-C)) : ℝ) by positivity]
  have hexp : θ * (k : ℝ) ≤ ε := by
    dsimp [θ]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).mpr
    nlinarith
  calc
    (((Scale.dyExp (N ^ C) (N ^ (-C)) + 1) ^ k : ℕ) : ℝ) =
        ((Scale.dyExp (N ^ C) (N ^ (-C)) + 1 : ℕ) : ℝ) ^ k := by push_cast; rfl
    _ ≤ (N ^ θ) ^ k := pow_le_pow_left₀ (by positivity) hD k
    _ = N ^ (θ * (k : ℝ)) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    _ ≤ N ^ ε := Real.rpow_le_rpow_of_exponent_le hN1 hexp

/-- A finite family of polynomially bounded positive densities can be made simultaneously
constant up to a factor two, while losing at most a prescribed power of total selected mass. -/
theorem finite_density_selection (k : ℕ) {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (α : Type*) [MeasurableSpace α] (ν : Measure α)
        (f : Fin k → α → ℝ) (F : Set α),
        (∀ j, Measurable (f j)) → MeasurableSet F →
        (∀ x ∈ F, ∀ j, N ^ (-C) ≤ f j x ∧ f j x ≤ N ^ C) →
        ∃ (lam : Fin k → ℝ) (Z : Set α),
          MeasurableSet Z ∧ Z ⊆ F ∧
          (∀ j, N ^ (-C) / 2 ≤ lam j ∧ lam j ≤ N ^ C / 2) ∧
          (∀ x ∈ Z, ∀ j, lam j ≤ f j x ∧ f j x ≤ 2 * lam j) ∧
          ν F ≤ ENNReal.ofReal (N ^ ε) * ν Z := by
  obtain ⟨N₀, hN₀, hcount⟩ := dyadic_density_loss_subpower k hC hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN α _ ν f F hf hF hbounds
  have hN1 : 1 ≤ N := by linarith [(hN₀.trans hN : 2 ≤ N)]
  have hN0 : 0 < N := by linarith
  obtain ⟨lam, Z, hZm, hZF, hlam, hfZ, hmass⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.finite_density_pigeonhole
      ν f hf hF (Real.rpow_pos_of_pos hN0 _) (Real.rpow_pos_of_pos hN0 _)
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : -C ≤ C)) hbounds
  refine ⟨lam, Z, hZm, hZF, hlam, hfZ, hmass.trans ?_⟩
  gcongr
  exact_mod_cast (ENNReal.ofReal_le_ofReal (hcount N hN))

end Submission.Lib.K4Homogenization
