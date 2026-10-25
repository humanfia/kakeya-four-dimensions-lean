import Submission.Obl.k4_scalar_conditional_crop_worlds.CropPrior

/-!
# The finite density format of a cropped marked prior

Each cropped box is cut out by fourteen affine tests in single coordinates: the two unit
intervals of the normalized intercept and velocity, and the ten bounds of the translated noise
cube. With the cell centre bounded by `K + 2` and the source coefficients by `K`, all of them
have coefficients at most `2 K + 4`.
-/

namespace Submission.Obl.k4_scalar_conditional_crop_worlds

open MeasureTheory Set

noncomputable section

/-- The scales of the uncropping, coordinate by coordinate. -/
def uncropScale (a : ℝ) : Coeff := ![a, a, 1, 1, 1]

/-- The offsets of the uncropping relative to a noise corner `b`. -/
def uncropOffset (a : ℝ) (z : Label) (b : Coeff) : Coeff :=
  ![a * (z 0 : ℝ) - b 0, a * (z 1 : ℝ) - b 1, -b 2, -b 3, -b 4]

lemma uncropCoeff_sub (a : ℝ) (z : Label) (b c : Coeff) (e : Fin 5) :
    uncropCoeff a z c e - b e = uncropScale a e * c e + uncropOffset a z b e := by
  fin_cases e <;> simp [uncropCoeff, uncropScale, uncropOffset] <;> ring

lemma uncrop_mem_coeffCell_iff {a : ℝ} (ha : a ≠ 0) (z : Label) (c : Coeff) :
    uncropCoeff a z c ∈ coeffCell a z ↔ c 0 ∈ Ico (0 : ℝ) 1 ∧ c 1 ∈ Ico (0 : ℝ) 1 := by
  have key : ∀ (v : ℝ) (n : ℤ), ⌊(v + (n : ℝ)) * a / a⌋ = n ↔ v ∈ Ico (0 : ℝ) 1 := by
    intro v n
    rw [mul_div_assoc, div_self ha, mul_one, Int.floor_eq_iff, mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  change ⌊uncropCoeff a z c 0 / a⌋ = z 0 ∧ ⌊uncropCoeff a z c 1 / a⌋ = z 1 ↔ _
  simp only [uncropCoeff, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [key, key]

lemma mem_cropBox_iff {σ a : ℝ} (ha : a ≠ 0) (z : Label) (b c : Coeff) :
    c ∈ cropBox σ a z b ↔ (c 0 ∈ Ico (0 : ℝ) 1 ∧ c 1 ∈ Ico (0 : ℝ) 1) ∧
      ∀ e, 0 ≤ uncropScale a e * c e + uncropOffset a z b e ∧
        uncropScale a e * c e + uncropOffset a z b e ≤ σ := by
  change uncropCoeff a z c ∈ coeffCell a z ∧ (∀ e, uncropCoeff a z c e - b e ∈ Icc (0 : ℝ) σ) ↔ _
  rw [uncrop_mem_coeffCell_iff ha]
  simp only [uncropCoeff_sub, mem_Icc]

lemma cropBox_eq {σ a : ℝ} (ha : a ≠ 0) (z : Label) (b : Coeff) :
    cropBox σ a z b = ({c : Coeff | c 0 ∈ Ico (0 : ℝ) 1} ∩ {c : Coeff | c 1 ∈ Ico (0 : ℝ) 1}) ∩
      ⋂ e, {c : Coeff | 0 ≤ uncropScale a e * c e + uncropOffset a z b e ∧
        uncropScale a e * c e + uncropOffset a z b e ≤ σ} := by
  ext c
  rw [mem_cropBox_iff ha]
  simp only [mem_inter_iff, mem_iInter, mem_ofPred_eq]

/-- The coefficient bound of the fourteen affine tests. -/
lemma uncrop_test_bound {σ a K : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (ha0 : 0 < a) (ha1 : a ≤ 1)
    {z : Label} (hz0 : |a * (z 0 : ℝ)| ≤ K + 2) (hz1 : |a * (z 1 : ℝ)| ≤ K + 2)
    {b : Coeff} (hb : ∀ e, |b e| ≤ K) (e : Fin 5) :
    |uncropScale a e| + |uncropOffset a z b e| + |σ| ≤ 2 * K + 4 := by
  have hσa : |σ| ≤ 1 := by rw [abs_of_pos hσ]; exact hσ1
  have haa : |a| ≤ 1 := by rw [abs_of_pos ha0]; exact ha1
  have hK : 0 ≤ K := (abs_nonneg _).trans (hb 0)
  fin_cases e
  · show |a| + |a * (z 0 : ℝ) - b 0| + |σ| ≤ 2 * K + 4
    have h := abs_sub (a * (z 0 : ℝ)) (b 0)
    linarith [hb 0]
  · show |a| + |a * (z 1 : ℝ) - b 1| + |σ| ≤ 2 * K + 4
    have h := abs_sub (a * (z 1 : ℝ)) (b 1)
    linarith [hb 1]
  · show |(1 : ℝ)| + |-b 2| + |σ| ≤ 2 * K + 4
    rw [abs_one, abs_neg]
    linarith [hb 2]
  · show |(1 : ℝ)| + |-b 3| + |σ| ≤ 2 * K + 4
    rw [abs_one, abs_neg]
    linarith [hb 3]
  · show |(1 : ℝ)| + |-b 4| + |σ| ≤ 2 * K + 4
    rw [abs_one, abs_neg]
    linarith [hb 4]

/-- Each cropped box is in the polynomial sign format. -/
lemma cropBox_format {σ a K : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (ha0 : 0 < a) (ha1 : a ≤ 1)
    {z : Label} (hz0 : |a * (z 0 : ℝ)| ≤ K + 2) (hz1 : |a * (z 1 : ℝ)| ≤ K + 2)
    {b : Coeff} (hb : ∀ e, |b e| ≤ K) :
    Format 5 (70 * (K + 1)) 1 (cropBox σ a z b) := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hb 0)
  have hB₀ : (1 : ℝ) ≤ 2 * K + 4 := by linarith
  have hbox : ∀ e : Fin 5, Format 5 ((2 * K + 4) + (2 * K + 4)) 1
      {c : Coeff | 0 ≤ uncropScale a e * c e + uncropOffset a z b e ∧
        uncropScale a e * c e + uncropOffset a z b e ≤ σ} := fun e =>
    Format.affine_Icc e _ _ σ hB₀ le_rfl (uncrop_test_bound hσ hσ1 ha0 ha1 hz0 hz1 hb e)
  have hall := Format.iInter_fin (by linarith) 5 _ hbox
  have hunit := (Format.coord_Ico (n := 5) (D := 1) 0 le_rfl).inter
    (Format.coord_Ico (n := 5) (D := 1) 1 le_rfl)
  rw [cropBox_eq ha0.ne']
  refine (hunit.inter hall).mono ?_ le_rfl
  push_cast
  linarith

/-- The points of a cropped box have coordinates bounded by `K + 1`. -/
lemma cropBox_bound {σ a K : ℝ} (hσ1 : σ ≤ 1) (ha0 : 0 < a) {z : Label} {b : Coeff}
    (hb : ∀ e, |b e| ≤ K) {c : Coeff} (hc : c ∈ cropBox σ a z b) (e : Fin 5) :
    |c e| ≤ K + 1 := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hb 0)
  rw [mem_cropBox_iff ha0.ne'] at hc
  obtain ⟨⟨⟨h00, h01⟩, ⟨h10, h11⟩⟩, hbox⟩ := hc
  have hrest : ∀ e : Fin 5, uncropScale a e = 1 → uncropOffset a z b e = -b e → |c e| ≤ K + 1 := by
    intro e hs ho
    have h := hbox e
    rw [hs, ho, one_mul] at h
    have := hb e
    rw [abs_le] at this ⊢
    constructor <;> linarith [h.1, h.2]
  fin_cases e
  · show |c 0| ≤ K + 1
    rw [abs_of_nonneg h00]
    linarith
  · show |c 1| ≤ K + 1
    rw [abs_of_nonneg h10]
    linarith
  · exact hrest 2 rfl rfl
  · exact hrest 3 rfl rfl
  · exact hrest 4 rfl rfl

/-- The finite density format of the conditional prior of a scalar crop of a marked prior. -/
theorem conditionalPrior_priorData {N u₀ σ K R p : ℝ} (hN : 0 < N) (hu₀ : N ^ (-u₀) ≤ 1)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) {H : ℕ} (b₀ : Fin H → Coeff) (w : Fin H → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) (hb : ∀ j e, |b₀ j e| ≤ K) (z : Label)
    (hz0 : |N ^ (-u₀) * (z 0 : ℝ)| ≤ K + 2) (hz1 : |N ^ (-u₀) * (z 1 : ℝ)| ≤ K + 2)
    (hp : 0 < p) (hR : 70 * (K + 1) ≤ R) (hHR : (H : ℝ) ≤ R) (hpR : σ⁻¹ ^ 5 ≤ p * R) :
    PriorData R 1 ((ENNReal.ofReal p)⁻¹ • Measure.map (scalarCropLine N u₀ z)
      ((MarkedPrior σ H b₀ w).restrict (scalarCell N u₀ z))) := by
  have ha0 := scale_pos hN u₀
  have hw1' : ∀ j, w j ≤ 1 := fun j => by
    rw [← hw1]
    exact Finset.single_le_sum (fun i _ => hw i) (Finset.mem_univ j)
  refine ⟨H, hHR, fun j => w j * σ⁻¹ ^ 5 * (N ^ (-u₀)) ^ 2 / p, fun j => (j : ℕ),
    fun j => cropBox σ (N ^ (-u₀)) z (b₀ j), fun j => ⟨?_, ?_, ?_, ?_, ?_⟩,
    conditionalPrior_eq hN u₀ z hσ b₀ w hw hp⟩
  · exact div_nonneg (mul_nonneg (mul_nonneg (hw j) (by positivity)) (by positivity)) hp.le
  · rw [div_le_iff₀ hp]
    have hg : (N ^ (-u₀)) ^ 2 ≤ 1 := pow_le_one₀ ha0.le hu₀
    have hs : 0 ≤ σ⁻¹ ^ 5 := by positivity
    calc w j * σ⁻¹ ^ 5 * (N ^ (-u₀)) ^ 2 ≤ 1 * σ⁻¹ ^ 5 * 1 := by gcongr; exact hw1' j
      _ = σ⁻¹ ^ 5 := by ring
      _ ≤ p * R := hpR
      _ = R * p := mul_comm _ _
  · exact (Nat.cast_le.2 j.isLt.le).trans hHR
  · exact (cropBox_format hσ hσ1 ha0 hu₀ hz0 hz1 (hb j)).mono hR le_rfl
  · intro c hc e
    have hK : 0 ≤ K := (abs_nonneg _).trans (hb j 0)
    exact (cropBox_bound hσ1 ha0 (hb j) hc e).trans (by linarith)

end

end Submission.Obl.k4_scalar_conditional_crop_worlds
