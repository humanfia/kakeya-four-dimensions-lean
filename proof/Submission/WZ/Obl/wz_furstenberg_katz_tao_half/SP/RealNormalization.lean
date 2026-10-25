-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.RealNormalization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.CartesianFrostman

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open scoped Pointwise

/-- Division by a number at most one preserves normalized Frostman bounds
at scales whose inverse images are above the original cutoff. -/
theorem RealFiniteFrostman.div_image {δ ρ C σ t : ℝ} {A : Finset ℝ}
    (hA : RealFiniteFrostman δ C σ A) (hδ : 0 < δ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hC : 0 ≤ C) (hσ : 0 ≤ σ) (hscale : δ ≤ t * ρ) :
    RealFiniteFrostman ρ C σ (A.image (fun a => a / t)) := by
  classical
  intro x r hr
  have htr : δ ≤ t * r := hscale.trans (mul_le_mul_of_nonneg_left hr ht.le)
  have hrpos : 0 < r := by nlinarith
  have hinj : Function.Injective (fun a : ℝ => a / t) := by
    intro a b hab
    exact (div_left_inj' ht.ne').mp hab
  have hcap (a : ℝ) : dist (a / t) x ≤ r ↔ dist a (t * x) ≤ t * r := by
    have hid : dist (a / t) x = dist a (t * x) / t := by
      rw [Real.dist_eq, Real.dist_eq,
        show a / t - x = (a - t * x) / t by field_simp, abs_div, abs_of_pos ht]
    rw [hid, div_le_iff₀ ht]
    constructor <;> intro hh <;> nlinarith
  rw [Finset.filter_image]
  simp_rw [hcap]
  rw [Finset.card_image_of_injective _ hinj, Finset.card_image_of_injective _ hinj]
  have hc := hA (t * x) (t * r) htr
  exact hc.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by nlinarith : t * r ≤ r) hσ) hC)
    (Nat.cast_nonneg _))

/-- A cover of the sum of two products rescales exactly under division. -/
theorem Covers.div_product_sum {δ t : ℝ} {A : Finset ℝ} (ht : 0 < t)
    {m : ℕ} {cc : Fin m → ℝ} (hcov : Covers δ (↑(A * A + A * A) : Set ℝ) cc) :
    Covers (δ / t ^ 2)
      (↑((A.image (fun a => a / t)) * (A.image (fun a => a / t)) +
        (A.image (fun a => a / t)) * (A.image (fun a => a / t))) : Set ℝ)
      (fun j => cc j / t ^ 2) := by
  classical
  intro x hx
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hx
  obtain ⟨a', ha', b', hb', rfl⟩ := Finset.mem_mul.mp hu
  obtain ⟨c', hc', d', hd', rfl⟩ := Finset.mem_mul.mp hv
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ha'
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb'
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hc'
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcov (Finset.add_mem_add
    (Finset.mul_mem_mul ha hb) (Finset.mul_mem_mul hc hd)))
  refine Set.mem_iUnion.mpr ⟨j, ?_⟩
  change dist (a / t * (b / t) + c / t * (d / t)) (cc j / t ^ 2) ≤ δ / t ^ 2
  have hid : a / t * (b / t) + c / t * (d / t) - cc j / t ^ 2 =
      (a * b + c * d - cc j) / t ^ 2 := by field_simp
  rw [Real.dist_eq, hid, abs_div, abs_of_pos (by positivity : 0 < t ^ 2)]
  exact div_le_div_of_nonneg_right (show |a * b + c * d - cc j| ≤ δ by
    simpa only [Metric.mem_closedBall, Real.dist_eq] using hj) (sq_nonneg t)

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
