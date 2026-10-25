/-
Adapted from this LOT tree o203, session x0699, commit 4341160d,
Submission/Obl/k4_horizontal_supercritical_rate_candidates/Boxes.lean (namespace
Submission.Obl.k4_horizontal_supercritical_rate_candidates renamed to
Submission.Obl.k4_horizontal_supercritical_three_projections.Parent).
-/
import Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.Geometry

namespace Submission.Obl.k4_horizontal_supercritical_three_projections.Parent

private theorem affine_step_bound {a b t t₀ H M q : ℝ}
    (hb : |b| ≤ H) (h₀ : |a + t₀ * b| ≤ M) (ht : |t - t₀| ≤ q) :
    |a + t * b| ≤ M + q * H := by
  have hq : 0 ≤ q := (abs_nonneg _).trans ht
  calc
    _ = |(a + t₀ * b) + (t - t₀) * b| := by congr 1; ring
    _ ≤ |a + t₀ * b| + |(t - t₀) * b| := abs_add_le _ _
    _ ≤ M + q * H := by
      rw [abs_mul]
      exact add_le_add h₀ (mul_le_mul ht hb (abs_nonneg _) hq)

/-- A true horizontal box that meets a small horizontal perturbation of a
reference motion has its entire domain in one enlarged reference box.
This uses the whole box, not merely its incidences at the contact time. -/
theorem horizontal_box_from_contact
    (c : Fin 5 → ℝ) (p r v τ t t₀ Z Y Z₀ Y₀ K q : ℝ)
    (hK : 1 ≤ K) (hq : 0 ≤ q)
    (hc₁ : |c 1| ≤ K) (hv : |v| ≤ K)
    (halign : |c 3 + c 0 + τ * c 1| ≤ K * q)
    (htilt : |c 4 - τ| ≤ K * q)
    (ht : |t - t₀| ≤ q) (hτ : |τ - t₀| ≤ q)
    (hZ : |Z - c 0 - t * c 1| ≤ K * q)
    (hY : |Y - c 2 - t * c 3 - c 4 * Z| ≤ K * q ^ 2)
    (hZ₀ : |Z₀ - c 0 - t₀ * c 1| ≤ K * q)
    (hY₀ : |Y₀ - c 2 - t₀ * c 3 - c 4 * Z₀| ≤ K * q ^ 2)
    (hcontactZ : |Z₀ - (p + t₀ * v)| ≤ K * q)
    (hcontactY : |Y₀ - (r - t₀ * p) - τ * (Z₀ - (p + t₀ * v))| ≤ K * q ^ 2) :
    |Z - (p + t * v)| ≤ 5 * K * q ∧
      |Y - (r - t * p) - τ * (Z - (p + t * v))| ≤ 12 * K ^ 2 * q ^ 2 := by
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hKsq : K ≤ K ^ 2 := by nlinarith only [hK]
  let g : ℝ → ℝ := fun s => (c 0 - p) + s * (c 1 - v)
  have hg₀ : |g t₀| ≤ 2 * K * q := by
    have heq : g t₀ = -(Z₀ - c 0 - t₀ * c 1) + (Z₀ - (p + t₀ * v)) := by
      dsimp [g]; ring
    rw [heq]
    have h := abs_add_le (-(Z₀ - c 0 - t₀ * c 1)) (Z₀ - (p + t₀ * v))
    rw [abs_neg] at h
    linarith only [h, hZ₀, hcontactZ]
  have hslope : |c 1 - v| ≤ 2 * K := (abs_sub _ _).trans (by linarith only [hc₁, hv])
  have hgt : |g t| ≤ 4 * K * q := by
    have h := affine_step_bound hslope hg₀ ht
    dsimp only [g] at *
    nlinarith only [h]
  have hgτ : |g τ| ≤ 4 * K * q := by
    have h := affine_step_bound hslope hg₀ hτ
    dsimp only [g] at *
    nlinarith only [h]
  have hZout : |Z - (p + t * v)| ≤ 5 * K * q := by
    have heq : Z - (p + t * v) = (Z - c 0 - t * c 1) + g t := by
      dsimp [g]; ring
    rw [heq]
    exact (abs_add_le _ _).trans (by linarith only [hZ, hgt])
  let h : ℝ → ℝ := fun s =>
    (c 2 + (c 4 - τ) * c 0 - r + τ * p) +
      s * (c 3 + (c 4 - τ) * c 1 + p + τ * v)
  have herror (s Z' Y' : ℝ)
      (heZ : |Z' - c 0 - s * c 1| ≤ K * q)
      (heY : |Y' - c 2 - s * c 3 - c 4 * Z'| ≤ K * q ^ 2) :
      |(Y' - (r - s * p) - τ * (Z' - (p + s * v))) - h s| ≤
        2 * K ^ 2 * q ^ 2 := by
    have heq : (Y' - (r - s * p) - τ * (Z' - (p + s * v))) - h s =
        (Y' - c 2 - s * c 3 - c 4 * Z') +
          (c 4 - τ) * (Z' - c 0 - s * c 1) := by
      dsimp [h]; ring
    rw [heq]
    calc
      _ ≤ |Y' - c 2 - s * c 3 - c 4 * Z'| +
          |(c 4 - τ) * (Z' - c 0 - s * c 1)| := abs_add_le _ _
      _ ≤ K * q ^ 2 + (K * q) * (K * q) := by
        rw [abs_mul]
        exact add_le_add heY (mul_le_mul htilt heZ (abs_nonneg _) (by positivity))
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hKsq (sq_nonneg q)]
  have hh₀ : |h t₀| ≤ 3 * K ^ 2 * q ^ 2 := by
    have he := herror t₀ Z₀ Y₀ hZ₀ hY₀
    have htri := abs_sub_le (h t₀)
      (Y₀ - (r - t₀ * p) - τ * (Z₀ - (p + t₀ * v))) 0
    simp only [sub_zero] at htri
    have htri' : |h t₀| ≤
        |Y₀ - (r - t₀ * p) - τ * (Z₀ - (p + t₀ * v))| +
          |(Y₀ - (r - t₀ * p) - τ * (Z₀ - (p + t₀ * v))) - h t₀| := by
      simpa only [abs_sub_comm, add_comm] using htri
    nlinarith only [htri', he, hcontactY, mul_le_mul_of_nonneg_right hKsq (sq_nonneg q)]
  have hhslope : |c 3 + (c 4 - τ) * c 1 + p + τ * v| ≤ 6 * K ^ 2 * q := by
    have heq : c 3 + (c 4 - τ) * c 1 + p + τ * v =
        (c 3 + c 0 + τ * c 1) - g τ + (c 4 - τ) * c 1 := by
      dsimp [g]; ring
    rw [heq]
    calc
      _ ≤ |c 3 + c 0 + τ * c 1| + |g τ| + |(c 4 - τ) * c 1| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ K * q + 4 * K * q + (K * q) * K := by
        rw [abs_mul]
        exact add_le_add (add_le_add halign hgτ)
          (mul_le_mul htilt hc₁ (abs_nonneg _) (by positivity))
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hKsq hq]
  have hht : |h t| ≤ 9 * K ^ 2 * q ^ 2 := by
    have hb := affine_step_bound hhslope hh₀ ht
    dsimp only [h] at *
    nlinarith only [hb]
  refine ⟨hZout, ?_⟩
  have he := herror t Z Y hZ hY
  have htri := abs_add_le
    ((Y - (r - t * p) - τ * (Z - (p + t * v))) - h t) (h t)
  simp only [sub_add_cancel] at htri
  nlinarith only [htri, he, hht, mul_nonneg (sq_nonneg K) (sq_nonneg q)]

end Submission.Obl.k4_horizontal_supercritical_three_projections.Parent
