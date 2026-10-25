import Submission.Obl.k4_scalar_coefficient_clustering.Cells
import Submission.Obl.k4_scalar_coefficient_clustering.LiftCap

namespace Submission.Obl.k4_scalar_coefficient_clustering

open Submission.Lib.K4PlankGeometry (binTime cellCode)

noncomputable section

theorem floor_error (x : ℝ) : |(⌊x⌋ : ℝ) - x| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [Int.floor_le x, Int.lt_floor_add_one x]

theorem normalized_cell_compatible {D : ℕ} (hD : 1 ≤ D) {p R : ℝ}
    (hp : 0 < p) (hR : 0 < R) (hmesh : (D : ℝ) * p ≤ 2 * R)
    (a : Coeff) (s : ℝ) (j : Fin D) (f : ℤ × ℤ)
    (ht : |binTime D j - p * (f.1 : ℝ)| ≤ 2 * p)
    (hx : |quadratic a (binTime D j) - p * (f.2 : ℝ)| ≤ 12 * p) :
    ScalarCellCompatible D p R f (cellCode D (normalizedBase R a s) (normalizedSlope R a s) j) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  let t := binTime D j
  let z := normalizedBase R a s + t • normalizedSlope R a s
  have htunit := Submission.Lib.K4PlankGeometry.binTime_mem_Icc hD j
  have he0 := floor_error ((D : ℝ) * z 0)
  have he1 := floor_error ((D : ℝ) * z 1)
  have htime : |t| ≤ 1 := by rw [abs_of_nonneg htunit.1]; exact htunit.2
  have htimeerr : |t * ((⌊(D : ℝ) * z 1⌋ : ℝ) - (D : ℝ) * z 1)| ≤ 1 := by
    rw [abs_mul]
    nlinarith [mul_le_mul htime he1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  have hxerr : |((D : ℝ) / R) * (quadratic a t - p * (f.2 : ℝ))| ≤ 24 := by
    rw [abs_mul, abs_of_pos (div_pos hDpos hR)]
    have hh := mul_le_mul_of_nonneg_left hx (div_pos hDpos hR).le
    have hratio : (D : ℝ) * p / R ≤ 2 := (div_le_iff₀ hR).mpr (by linarith)
    have heq : (D : ℝ) / R * (12 * p) = 12 * ((D : ℝ) * p / R) := by ring
    rw [heq] at hh
    linarith
  refine ⟨ht, ?_⟩
  change |(⌊(D : ℝ) * z 0⌋ : ℝ) + t * (⌊(D : ℝ) * z 1⌋ : ℝ) -
    ((D : ℝ) / R) * (p * (f.2 : ℝ))| ≤ 30
  have heq : (⌊(D : ℝ) * z 0⌋ : ℝ) + t * (⌊(D : ℝ) * z 1⌋ : ℝ) -
      ((D : ℝ) / R) * (p * (f.2 : ℝ)) =
      ((⌊(D : ℝ) * z 0⌋ : ℝ) - (D : ℝ) * z 0) +
      t * ((⌊(D : ℝ) * z 1⌋ : ℝ) - (D : ℝ) * z 1) +
      ((D : ℝ) / R) * (quadratic a t - p * (f.2 : ℝ)) := by
    have hs : z 0 + t * z 1 = R⁻¹ * quadratic a t := normalized_lift_scalar R a s t
    dsimp [z] at hs
    dsimp [z]
    linear_combination (D : ℝ) * hs
  rw [heq]
  have hh := abs_add_three
    ((⌊(D : ℝ) * z 0⌋ : ℝ) - (D : ℝ) * z 0)
    (t * ((⌊(D : ℝ) * z 1⌋ : ℝ) - (D : ℝ) * z 1))
    (((D : ℝ) / R) * (quadratic a t - p * (f.2 : ℝ)))
  linarith

theorem marked_normalized_cells_bound {ι : Type*} [Fintype ι] {D : ℕ} (hD : 1 ≤ D)
    {p R : ℝ} (hp : 0 < p) (hR : 1 ≤ R) (hmesh : (D : ℝ) * p ≤ 2 * R)
    (a : ι → Coeff) (s : ι → ℝ) (J : ι → Finset (Fin D)) (F : Finset (ℤ × ℤ))
    (hbu : ∀ i, ‖normalizedBase R (a i) (s i)‖ ≤ 1 ∧ ‖normalizedSlope R (a i) (s i)‖ ≤ 1)
    (hF : ∀ i j, j ∈ J i → ∃ f ∈ F, |binTime D j - p * (f.1 : ℝ)| ≤ 2 * p ∧
      |quadratic (a i) (binTime D j) - p * (f.2 : ℝ)| ≤ 12 * p) :
    ((markedCells (fun i => normalizedBase R (a i) (s i))
      (fun i => normalizedSlope R (a i) (s i)) J).card : ℝ) ≤
      100000 * R * (D : ℝ) * (F.card : ℝ) := by
  classical
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  apply cells_card_of_scalar_support hD hp hR hmesh F
  · intro q hq
    rcases Finset.mem_image.mp hq with ⟨⟨i, j⟩, hij, rfl⟩
    rcases hF i j (Finset.mem_sigma.mp hij).2 with ⟨f, hf, ht, hx⟩
    exact ⟨f, hf, normalized_cell_compatible hD hp (by linarith) hmesh (a i) (s i) j f ht hx⟩
  · intro q hq
    rcases Finset.mem_image.mp hq with ⟨⟨i, j⟩, hij, rfl⟩
    let z := normalizedBase R (a i) (s i) + binTime D j • normalizedSlope R (a i) (s i)
    have ht := Submission.Lib.K4PlankGeometry.binTime_mem_Icc hD j
    have hn : ‖z‖ ≤ 2 := by
      have hh := norm_add_le (normalizedBase R (a i) (s i))
        (binTime D j • normalizedSlope R (a i) (s i))
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at hh
      have hm := mul_le_mul ht.2 (hbu i).2 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      dsimp [z]
      nlinarith [(hbu i).1]
    have hz : |z 1| ≤ 2 := (PiLp.norm_apply_le z 1).trans hn
    have he := floor_error ((D : ℝ) * z 1)
    change |(⌊(D : ℝ) * z 1⌋ : ℝ)| ≤ 3 * (D : ℝ)
    have hh := abs_add_le ((⌊(D : ℝ) * z 1⌋ : ℝ) - (D : ℝ) * z 1) ((D : ℝ) * z 1)
    rw [sub_add_cancel, abs_mul, abs_of_pos hDpos] at hh
    have hd1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
    nlinarith

end
end Submission.Obl.k4_scalar_coefficient_clustering
