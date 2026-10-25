import Submission.Obl.k4_matching_abstract_switching_mixture.Scales

namespace Submission.Obl.k4_matching_abstract_switching_mixture

noncomputable def smallError (m : ℕ) : ℝ := 1 / (2 : ℝ) ^ (m + 10)

noncomputable def sizeConstant (m : ℕ) : ℝ :=
  2 + 8 * ((m : ℝ) + 1) / smallError m ^ 2 + (2 / smallError m) ^ (m + 1)

noncomputable def sizeBound (m : ℕ) (B K : ℝ) : ℝ :=
  sizeConstant m * (B * K) ^ (m + 1)

lemma smallError_pos (m : ℕ) : 0 < smallError m := by
  unfold smallError
  positivity

lemma smallError_le_one (m : ℕ) : smallError m ≤ 1 := by
  unfold smallError
  exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))

lemma smallError_loss (m : ℕ) :
    ((2 : ℝ) ^ (m + 1) - 1) * (4 * smallError m) ≤ 1 / 2 := by
  have hp : 0 < (2 : ℝ) ^ (m + 1) := by positivity
  have he : (2 : ℝ) ^ (m + 10) = 512 * (2 : ℝ) ^ (m + 1) := by
    have hnat : m + 10 = (m + 1) + 9 := by omega
    rw [hnat, pow_add]
    norm_num
    ring
  unfold smallError
  rw [he]
  field_simp
  nlinarith

lemma sizeConstant_pos (m : ℕ) : 0 < sizeConstant m := by
  unfold sizeConstant
  have := smallError_pos m
  positivity

lemma sizeBound_bounds (m : ℕ) {B K : ℝ} (hB : 1 ≤ B) (hK : 2 ≤ K) :
    2 ≤ sizeBound m B K ∧ K ≤ sizeBound m B K ∧
    8 * B * ((m : ℝ) + 1) / smallError m ^ 2 ≤ sizeBound m B K ∧
    (2 * B * K / smallError m) ^ (m + 1) ≤ sizeBound m B K := by
  have he := smallError_pos m
  have hB0 : 0 ≤ B := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hBK1 : 1 ≤ B * K := by nlinarith
  have hpow1 : 1 ≤ (B * K) ^ (m + 1) := one_le_pow₀ hBK1
  have hBKpow : B * K ≤ (B * K) ^ (m + 1) := by
    calc
      B * K = B * K * 1 := by ring
      _ ≤ B * K * (B * K) ^ m :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hBK1) (by positivity)
      _ = (B * K) ^ (m + 1) := by ring
  have hBpow : B ≤ (B * K) ^ (m + 1) := by nlinarith
  have hKpow : K ≤ (B * K) ^ (m + 1) := by nlinarith
  have hsep0 : 0 ≤ 8 * ((m : ℝ) + 1) / smallError m ^ 2 := by positivity
  have hstep0 : 0 ≤ (2 / smallError m) ^ (m + 1) := by positivity
  have hC2 : 2 ≤ sizeConstant m := by unfold sizeConstant; linarith
  have hCsep : 8 * ((m : ℝ) + 1) / smallError m ^ 2 ≤ sizeConstant m := by
    unfold sizeConstant
    linarith
  have hCstep : (2 / smallError m) ^ (m + 1) ≤ sizeConstant m := by
    unfold sizeConstant
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold sizeBound
    nlinarith
  · unfold sizeBound
    nlinarith
  · calc
      8 * B * ((m : ℝ) + 1) / smallError m ^ 2 =
          (8 * ((m : ℝ) + 1) / smallError m ^ 2) * B := by ring
      _ ≤ sizeConstant m * (B * K) ^ (m + 1) :=
        mul_le_mul hCsep hBpow hB0 (sizeConstant_pos m).le
  · calc
      (2 * B * K / smallError m) ^ (m + 1) =
          (2 / smallError m) ^ (m + 1) * (B * K) ^ (m + 1) := by
            rw [← mul_pow]
            congr 1
            ring
      _ ≤ sizeConstant m * (B * K) ^ (m + 1) :=
        mul_le_mul_of_nonneg_right hCstep (by positivity)

lemma sizeBound_time (m : ℕ) {B K : ℝ} (hB : 1 ≤ B) (hK : 2 ≤ K) :
    (sizeBound m B K)⁻¹ ≤ (smallError m ^ 2 / (4 * B * ((m : ℝ) + 1))) / 2 := by
  obtain ⟨hL2, -, hsep, -⟩ := sizeBound_bounds m hB hK
  have hL : 0 < sizeBound m B K := by linarith
  have he := smallError_pos m
  have hB0 : 0 < B := by linarith
  have hd : 0 < 8 * B * ((m : ℝ) + 1) := by positivity
  have hmul : 8 * B * ((m : ℝ) + 1) ≤ sizeBound m B K * smallError m ^ 2 :=
    (div_le_iff₀ (by positivity)).mp hsep
  rw [← one_div (sizeBound m B K)]
  apply (div_le_iff₀ hL).mpr
  calc
    1 ≤ (sizeBound m B K * smallError m ^ 2) / (8 * B * ((m : ℝ) + 1)) :=
      (le_div_iff₀ hd).mpr (by simpa using hmul)
    _ = (smallError m ^ 2 / (4 * B * ((m : ℝ) + 1)) / 2) * sizeBound m B K := by
      field_simp
      <;> ring

lemma sizeBound_subpower (m : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    ∃ η : ℝ, 0 < η ∧ ∃ R : ℝ, 2 ≤ R ∧
      ∀ N B K : ℝ, R ≤ N → 1 ≤ B → B ≤ N ^ η → 2 ≤ K → K ≤ N ^ η →
        sizeBound m B K ≤ N ^ κ := by
  obtain ⟨η, hη, R, hR, h⟩ := absorb_polynomial (sizeConstant m)
    (sizeConstant_pos m).le (m + 1) (by omega) κ hκ
  exact ⟨η, hη, R, hR, fun N B K hN hB hBN hK hKN =>
    h N B K hN hB hBN (by linarith) hKN⟩

noncomputable def timeRadius (m : ℕ) (B : ℝ) : ℝ :=
  smallError m ^ 2 / (4 * B * ((m : ℝ) + 1))

lemma timeRadius_pos (m : ℕ) {B : ℝ} (hB : 0 < B) : 0 < timeRadius m B := by
  unfold timeRadius
  have := smallError_pos m
  positivity

lemma mesh_margin (m : ℕ) {B K d : ℝ} (hB : 1 ≤ B) (hK : 2 ≤ K)
    (hd : d ≤ timeRadius m B / 4) :
    (sizeBound m B K)⁻¹ + 2 * d ≤ timeRadius m B := by
  have h := sizeBound_time m hB hK
  change (sizeBound m B K)⁻¹ ≤ timeRadius m B / 2 at h
  linarith

lemma near_budget (m : ℕ) {B d : ℝ} (hB : 0 < B) (hd : d ≤ timeRadius m B) :
    ((m : ℝ) + 1) * (2 * B * (timeRadius m B + d) / smallError m) ≤ smallError m := by
  have he := smallError_pos m
  calc
    ((m : ℝ) + 1) * (2 * B * (timeRadius m B + d) / smallError m) ≤
        ((m : ℝ) + 1) * (2 * B * (timeRadius m B + timeRadius m B) / smallError m) := by
          gcongr
    _ = smallError m := by
      unfold timeRadius
      have hm : (m : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      <;> ring

lemma exists_fine_depth (H H' : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ G : ℕ, H' ≤ G ∧ (2 : ℝ) ^ H / (2 : ℝ) ^ G ≤ r := by
  have hlarge : ∀ᶠ G : ℕ in Filter.atTop, (2 : ℝ) ^ H / r ≤ (2 : ℝ) ^ G :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop _
  obtain ⟨G, hG, hp⟩ := ((Filter.eventually_ge_atTop H').and hlarge).exists
  refine ⟨G, hG, (div_le_iff₀ (by positivity)).mpr ?_⟩
  have h := (div_le_iff₀ hr).mp hp
  nlinarith

end Submission.Obl.k4_matching_abstract_switching_mixture
