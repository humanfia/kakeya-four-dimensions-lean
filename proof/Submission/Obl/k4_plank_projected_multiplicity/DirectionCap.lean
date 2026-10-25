import Submission.Obl.k4_plank_projected_multiplicity.DirectionPacking
import Submission.Obl.k4_scalar_coefficient_clustering.Input

namespace Submission.Obl.k4_plank_projected_multiplicity

open Set Finset

noncomputable section

/-- Containment at the two endpoints confines a projected velocity. -/
theorem velocity_strip_of_fulltime_strip (b u c w e : E2) (a : ℝ)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |inner ℝ (b + t • u - c - t • w) e| ≤ a) :
    |inner ℝ (u - w) e| ≤ 2 * a := by
  have h₀ := h 0 (by simp)
  have h₁ := h 1 (by simp)
  simp only [zero_smul, one_smul, add_zero, sub_zero] at h₀ h₁
  have hid : inner ℝ (u - w) e =
      inner ℝ (b + u - c - w) e - inner ℝ (b - c) e := by
    simp only [inner_sub_left, inner_add_left]
    ring
  rw [hid]
  have h₀' := abs_le.mp h₀
  have h₁' := abs_le.mp h₁
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Three-dimensional separation gives the required full-time projected plank cap. -/
theorem fulltime_plank_cap_of_separated_slopes {ι : Type*} [Fintype ι]
    (D : ℕ) (hD : 1 ≤ D) {R : ℝ} (hR : 1 ≤ R)
    (b : ι → E2) (s : ι → E3) (hs : ∀ i, |s i 2| ≤ R)
    (hsep : ∀ i j, i ≠ j → (D : ℝ)⁻¹ ≤ ‖s i - s j‖) :
    Submission.Obl.k4_scalar_coefficient_clustering.PlankCap D b
      (fun i => planarPart (s i)) (fun _ => 1) (2000000 * R * (D : ℝ)) := by
  classical
  intro c w e₁ e₂ a β he₁ he₂ ho ha haβ hβ S hS
  have hDp : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hD₁ : 1 ≤ (D : ℝ) := by exact_mod_cast hD
  have hδ : 0 < (D : ℝ)⁻¹ := inv_pos.mpr hDp
  have hδ₁ : (D : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD₁
  have hβ₁ : 1 ≤ β := ha.trans haβ
  have hrect : ∀ i ∈ S,
      |inner ℝ (planarPart (s i) - w) e₁| ≤ (2 * a) * (D : ℝ)⁻¹ ∧
      |inner ℝ (planarPart (s i) - w) e₂| ≤ (2 * β) * (D : ℝ)⁻¹ ∧ |s i 2| ≤ R := by
    intro i hi
    have hh₁ := velocity_strip_of_fulltime_strip (b i) (planarPart (s i)) c w e₁
      (a / (D : ℝ)) (fun t ht => (hS i hi t ht).1)
    have hh₂ := velocity_strip_of_fulltime_strip (b i) (planarPart (s i)) c w e₂
      (β / (D : ℝ)) (fun t ht => (hS i hi t ht).2)
    refine ⟨?_, ?_, hs i⟩
    · simpa only [div_eq_mul_inv, mul_assoc] using hh₁
    · simpa only [div_eq_mul_inv, mul_assoc] using hh₂
  have hh := separated_slopes_plank_card S s hδ
    (show 1 ≤ 2 * a by linarith) (show 1 ≤ 2 * β by linarith) (hδ₁.trans hR)
    e₁ e₂ w he₁ he₂ ho (fun i _ j _ hij => hsep i j hij) hrect
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  calc
    (S.card : ℝ) ≤ 314432 * (2 * a) * (2 * β) * R / (D : ℝ)⁻¹ := hh
    _ = 1257728 * R * (D : ℝ) * a * β := by rw [div_inv_eq_mul]; ring
    _ ≤ (2000000 * R * (D : ℝ)) * a * β := by
      have hpos : 0 ≤ R * (D : ℝ) * a * β := by positivity
      nlinarith

end

end Submission.Obl.k4_plank_projected_multiplicity
