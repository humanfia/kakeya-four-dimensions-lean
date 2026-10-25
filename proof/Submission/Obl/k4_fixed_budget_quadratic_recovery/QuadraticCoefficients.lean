/- Adapted within this LOT tree from o120/x0402, commit 81f800489248f55eaf1c2da13f86ceff0ee98719,
Submission/Obl/k4_unbounded_width_exclusion/QuadraticCoefficients.lean. -/
import Submission.Obl.k4_fixed_budget_quadratic_recovery.ScalarCandidates
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.QuadBounds

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open Set
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction

def quadraticValue (c : Fin 6 → ℝ) (t z : ℝ) : ℝ :=
  c 0 + c 1 * t + c 2 * z + c 3 * t ^ 2 + c 4 * (t * z) + c 5 * z ^ 2

/-- Six fixed samples bound all ordinary coefficients of a quadratic on
the unit-time, symmetric-space rectangle. -/
theorem quadratic_coefficients_bound {c : Fin 6 → ℝ} {H : ℝ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (-1 : ℝ) 1,
      |quadraticValue c t z| ≤ H) : ∀ i, |c i| ≤ 8 * H := by
  have h00 := h 0 (by norm_num) 0 (by norm_num)
  have h01 := h 0 (by norm_num) 1 (by norm_num)
  have h0m := h 0 (by norm_num) (-1) (by norm_num)
  have h10 := h 1 (by norm_num) 0 (by norm_num)
  have hh0 := h (1 / 2) (by norm_num) 0 (by norm_num)
  have h11 := h 1 (by norm_num) 1 (by norm_num)
  norm_num [quadraticValue, abs_le] at h00 h01 h0m h10 hh0 h11
  intro i
  fin_cases i <;> dsimp <;> rw [abs_le] <;> constructor <;> linarith

theorem isQuad2_affine_second {f : ℝ → ℝ → ℝ} (hf : IsQuad2 f) (u v β : ℝ) :
    IsQuad2 (fun t z => f t (u + t * v + β * z)) := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨![c 0 + c 2 * u + c 5 * u ^ 2,
    c 1 + c 2 * v + c 4 * u + 2 * c 5 * u * v,
    c 2 * β + 2 * c 5 * u * β,
    c 3 + c 4 * v + c 5 * v ^ 2,
    c 4 * β + 2 * c 5 * v * β,
    c 5 * β ^ 2], ?_⟩
  intro t z
  simp [hc]
  ring

def undoQuadraticFrame (c : Fin 6 → ℝ) (u v β : ℝ) : Fin 6 → ℝ :=
  ![c 0 - c 2 * (u / β) + c 5 * (u / β) ^ 2,
    c 1 - c 2 * (v / β) - c 4 * (u / β) + 2 * c 5 * (u / β) * (v / β),
    (c 2 - 2 * c 5 * (u / β)) / β,
    c 3 - c 4 * (v / β) + c 5 * (v / β) ^ 2,
    (c 4 - 2 * c 5 * (v / β)) / β,
    c 5 / β ^ 2]

theorem undoQuadraticFrame_value (c : Fin 6 → ℝ) (u v : ℝ) {β : ℝ} (hβ : β ≠ 0)
    (t z : ℝ) :
    quadraticValue c t ((z - u - t * v) / β) =
      quadraticValue (undoQuadraticFrame c u v β) t z := by
  simp [quadraticValue, undoQuadraticFrame]
  field_simp [hβ]
  ring

theorem undoQuadraticFrame_bound {c : Fin 6 → ℝ} {H R u v β : ℝ}
    (hH : 0 ≤ H) (hR : 1 ≤ R) (hc : ∀ i, |c i| ≤ H)
    (hu : |u / β| ≤ R) (hv : |v / β| ≤ R) (hβ : |β⁻¹| ≤ R) :
    ∀ i, |undoQuadraticFrame c u v β i| ≤ 5 * H * R ^ 2 := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hR2 : R ≤ R ^ 2 := by nlinarith
  have hR21 : 1 ≤ R ^ 2 := by nlinarith
  have habs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)
  have hc0 := hc 0
  have hc1 := hc 1
  have hc2 := hc 2
  have hc3 := hc 3
  have hc4 := hc 4
  have hc5 := hc 5
  intro i
  fin_cases i <;> simp [undoQuadraticFrame]
  · calc
      |c 0 - c 2 * (u / β) + c 5 * (u / β) ^ 2| ≤ H + H * R + H * R ^ 2 := by
        calc
          _ ≤ |c 0| + |c 2 * (u / β)| + |c 5 * (u / β) ^ 2| :=
            (abs_add_le _ _).trans (add_le_add (habs _ _) le_rfl)
          _ ≤ _ := by simp only [abs_mul, abs_pow]; gcongr
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hR2 hH,
        mul_le_mul_of_nonneg_left hR21 hH]
  · calc
      |c 1 - c 2 * (v / β) - c 4 * (u / β) + 2 * c 5 * (u / β) * (v / β)| ≤
          H + H * R + H * R + 2 * H * R * R := by
        calc
          _ ≤ |c 1| + |c 2 * (v / β)| + |c 4 * (u / β)| +
              |2 * c 5 * (u / β) * (v / β)| := by
                grw [abs_add_le, habs, habs]
          _ ≤ _ := by norm_num only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; gcongr
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hR2 hH,
        mul_le_mul_of_nonneg_left hR21 hH]
  · calc
      |(c 2 - 2 * c 5 * (u / β)) / β| ≤ (H + 2 * H * R) * R := by
        rw [div_eq_mul_inv, abs_mul]
        apply mul_le_mul _ hβ (abs_nonneg _) (by positivity)
        calc
          _ ≤ |c 2| + |2 * c 5 * (u / β)| := habs _ _
          _ ≤ _ := by norm_num only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; gcongr
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hR2 hH]
  · calc
      |c 3 - c 4 * (v / β) + c 5 * (v / β) ^ 2| ≤ H + H * R + H * R ^ 2 := by
        calc
          _ ≤ |c 3| + |c 4 * (v / β)| + |c 5 * (v / β) ^ 2| :=
            (abs_add_le _ _).trans (add_le_add (habs _ _) le_rfl)
          _ ≤ _ := by simp only [abs_mul, abs_pow]; gcongr
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hR2 hH,
        mul_le_mul_of_nonneg_left hR21 hH]
  · calc
      |(c 4 - 2 * c 5 * (v / β)) / β| ≤ (H + 2 * H * R) * R := by
        rw [div_eq_mul_inv, abs_mul]
        apply mul_le_mul _ hβ (abs_nonneg _) (by positivity)
        calc
          _ ≤ |c 4| + |2 * c 5 * (v / β)| := habs _ _
          _ ≤ _ := by norm_num only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; gcongr
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hR2 hH]
  · calc
      |c 5 / β ^ 2| ≤ H * R ^ 2 := by
        simpa only [div_eq_mul_inv, ← inv_pow, abs_mul, abs_pow] using
          mul_le_mul hc5 (pow_le_pow_left₀ (abs_nonneg _) hβ 2)
            (sq_nonneg _) hH
      _ ≤ _ := by nlinarith [mul_nonneg hH (sq_nonneg R)]

/-- The adapted norm supplied by scalar projection controls the six
ordinary coefficients. The loss is a fixed fifth power. -/
theorem adapted_quadratic_coefficients (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) {H u v β : ℝ} (hH : 1 ≤ H)
    (hcenter : |u| + |v| ≤ H) (hβpos : 0 < β) (hβinv : β⁻¹ ≤ H)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (-1 : ℝ) 1,
      |MvPolynomial.eval ![t, u + t * v + β * z] P| ≤ H) :
    ∃ c : Fin 6 → ℝ,
      (∀ t z, MvPolynomial.eval ![t, z] P = quadraticValue c t z) ∧
      ∀ i, |c i| ≤ 40 * H ^ 5 := by
  obtain ⟨c, hc⟩ := isQuad2_affine_second (isQuad2_eval P hP) u v β
  have hcform : ∀ t z, MvPolynomial.eval ![t, u + t * v + β * z] P =
      quadraticValue c t z := hc
  have hcbd : ∀ i, |c i| ≤ 8 * H := quadratic_coefficients_bound (by
    intro t ht z hz
    rw [← hcform]
    exact hbound t ht z hz)
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hH2 : H ≤ H ^ 2 := by nlinarith
  have hu : |u / β| ≤ H ^ 2 := by
    rw [abs_div, abs_of_pos hβpos, div_eq_mul_inv]
    exact (mul_le_mul (by linarith [abs_nonneg v] : |u| ≤ H) hβinv
      (inv_nonneg.mpr hβpos.le) hH0).trans_eq (by ring)
  have hv : |v / β| ≤ H ^ 2 := by
    rw [abs_div, abs_of_pos hβpos, div_eq_mul_inv]
    exact (mul_le_mul (by linarith [abs_nonneg u] : |v| ≤ H) hβinv
      (inv_nonneg.mpr hβpos.le) hH0).trans_eq (by ring)
  refine ⟨undoQuadraticFrame c u v β, ?_, ?_⟩
  · intro t z
    have heq : u + t * v + β * ((z - u - t * v) / β) = z := by
      field_simp
      ring
    calc
      _ = MvPolynomial.eval ![t, u + t * v + β * ((z - u - t * v) / β)] P := by rw [heq]
      _ = quadraticValue c t ((z - u - t * v) / β) := hcform _ _
      _ = _ := undoQuadraticFrame_value c u v hβpos.ne' t z
  · intro i
    have h := undoQuadraticFrame_bound (by positivity : 0 ≤ 8 * H)
      (show 1 ≤ H ^ 2 by nlinarith) hcbd hu hv
      (by rw [abs_of_nonneg (inv_nonneg.mpr hβpos.le)]; exact hβinv.trans hH2) i
    convert h using 1
    ring

theorem ScalarCandidate.exists_coefficients {N s m ε : ℝ}
    (F : ScalarCandidate N s m ε) (hN : 1 ≤ N) (hε : 0 ≤ ε) :
    ∃ c : Fin 6 → ℝ,
      (∀ t z, MvPolynomial.eval ![t, z] F.P = quadraticValue c t z) ∧
      ∀ i, |c i| ≤ 40 * (N ^ ε) ^ 5 := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hβpos : 0 < F.β := (Real.rpow_pos_of_pos hNpos _).trans_le F.β_lower
  have hβinv : F.β⁻¹ ≤ N ^ ε := by
    have h := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hNpos (-ε)) F.β_lower
    simpa only [one_div, Real.rpow_neg hNpos.le, inv_inv] using h
  exact adapted_quadratic_coefficients F.P F.degree (Real.one_le_rpow hN hε)
    F.center_bound hβpos hβinv F.adapted_bound

theorem quadraticValue_bound {c : Fin 6 → ℝ} {H R t z : ℝ}
    (hH : 0 ≤ H) (hR : 1 ≤ R) (hc : ∀ i, |c i| ≤ H)
    (ht : |t| ≤ R) (hz : |z| ≤ R) : |quadraticValue c t z| ≤ 6 * H * R ^ 2 := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hR2 : R ≤ R ^ 2 := by nlinarith
  have hR21 : 1 ≤ R ^ 2 := by nlinarith
  unfold quadraticValue
  calc
    _ ≤ |c 0| + |c 1 * t| + |c 2 * z| + |c 3 * t ^ 2| +
        |c 4 * (t * z)| + |c 5 * z ^ 2| := by
      grw [abs_add_le, abs_add_le, abs_add_le, abs_add_le, abs_add_le]
    _ ≤ H + H * R + H * R + H * R ^ 2 + H * (R * R) + H * R ^ 2 := by
      simp only [abs_mul, abs_pow]
      gcongr <;> exact hc _
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hR2 hH,
      mul_le_mul_of_nonneg_left hR21 hH]

/-- Coefficient binning changes values by a controlled amount on the
bounded comparison domain. -/
theorem quadraticValue_sub_bound {c c' : Fin 6 → ℝ} {H R t z : ℝ}
    (hH : 0 ≤ H) (hR : 1 ≤ R) (hc : ∀ i, |c i - c' i| ≤ H)
    (ht : |t| ≤ R) (hz : |z| ≤ R) :
    |quadraticValue c t z - quadraticValue c' t z| ≤ 6 * H * R ^ 2 := by
  have heq : quadraticValue c t z - quadraticValue c' t z =
      quadraticValue (c - c') t z := by
    simp only [quadraticValue, Pi.sub_apply]
    ring
  rw [heq]
  exact quadraticValue_bound hH hR hc ht hz

end Submission.Obl.k4_fixed_budget_quadratic_recovery
