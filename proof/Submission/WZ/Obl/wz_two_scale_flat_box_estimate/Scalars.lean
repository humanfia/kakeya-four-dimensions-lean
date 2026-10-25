-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.Scalars.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.Budget
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.Interfaces

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

noncomputable def fineProfile (σ ω ε A δ a b F : ℝ) : ℝ :=
  A * δ ^ ε * (δ / a) ^ ω * F ^ (1 - σ) * δ ^ (2 - σ) * (a * b) ^ (σ / 2)

noncomputable def cellProfile (σ ω ε A δ a b F D : ℝ) : ℝ :=
  fineProfile σ ω ε A δ a b F / (D ^ 24 * (a * b))

lemma fine_scalar_lower {σ ω ε A δ a b F D M : ℝ}
    (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hA : 0 < A) (hδ : 0 < δ)
    (ha : 0 < a) (hb : 0 < b) (hb8 : b ≤ 8) (hF : 0 < F) (hD : 4 ≤ D)
    (hM : 0 < M) (hsize : F ≤ D ^ (6 : ℕ) * M) :
    fineProfile σ ω ε A δ a b F / D ^ 22 ≤
      A * δ ^ ε * (δ / a) ^ ω * D ^ (-1 + 3 / 2 * σ) *
        (D ^ (14 : ℕ)) ^ (-σ) * M ^ (1 - σ) *
        δ ^ (2 - σ) * (a * min b 2) ^ (σ / 2) := by
  have hD1 : 1 ≤ D := by linarith
  have hDpos : 0 < D := by linarith
  have hconv := rpow_negative_loss hD1 (by linarith : -1 ≤ -1 + 3 / 2 * σ)
  have hslab := rpow_nat_negative_loss hD1 hσ (by linarith : σ ≤ 1) 14
  have hnum := rpow_loss hD1 hF hM (by linarith : 0 ≤ 1 - σ)
    (by linarith : 1 - σ ≤ 1) 6 hsize
  have hmid := min_middle_loss hD ha hb hb8 (by linarith : 0 ≤ σ / 2)
    (by linarith : σ / 2 ≤ 1)
  calc
    _ = A * δ ^ ε * (δ / a) ^ ω * (1 / D) * (1 / D ^ 14) *
        (F ^ (1 - σ) / D ^ 6) * δ ^ (2 - σ) * ((a * b) ^ (σ / 2) / D) := by
      unfold fineProfile
      field_simp
      <;> ring
    _ ≤ _ := by gcongr

lemma cellProfile_pos {σ ω ε A δ a b F D : ℝ} (hA : 0 < A) (hδ : 0 < δ)
    (ha : 0 < a) (hb : 0 < b) (hF : 0 < F) (hD : 0 < D) :
    0 < cellProfile σ ω ε A δ a b F D := by
  unfold cellProfile fineProfile
  positivity

lemma cellProfile_le {σ ω ε A δ a b F D t V : ℝ}
    (hA : 0 < A) (hδ : 0 < δ) (ha : 0 < a) (hb : 0 < b) (hF : 0 < F)
    (hD : 432 ≤ D) (ht : 0 ≤ t)
    (hlower : fineProfile σ ω ε A δ a b F / D ^ 22 ≤ V)
    (hupper : (1 / D) * V ≤ t * (432 * a * b)) :
    cellProfile σ ω ε A δ a b F D ≤ t := by
  have hDpos : 0 < D := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hlower (by positivity : 0 ≤ 1 / D)
  have hbound : fineProfile σ ω ε A δ a b F / D ^ 23 ≤ t * (432 * a * b) := by
    convert hscaled.trans hupper using 1 <;> field_simp <;> ring
  have htD : t * (432 * a * b) ≤ t * (D * a * b) := by gcongr
  unfold cellProfile
  apply (div_le_iff₀ (by positivity : 0 < D ^ 24 * (a * b))).mpr
  have hh := (div_le_iff₀ (by positivity : 0 < D ^ 23)).mp (hbound.trans htD)
  convert hh using 1 <;> ring

lemma coarse_scalar_lower {σ ω ε A δ a b c D q : ℝ}
    (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hA : 0 < A) (hδ : 0 < δ)
    (ha : 0 < a) (hb : 0 < b) (hc : 1 ≤ c) (hD : 1 ≤ D) (hq : 0 < q) :
    A * δ ^ ε * b ^ ω * q ^ (1 - σ) * (a * b) ^ (1 - σ / 2) / D ^ 12 ≤
      A * δ ^ ε * b ^ ω * D ^ (-1 + σ / 2) * (D ^ (11 : ℕ)) ^ (-σ) *
        q ^ (1 - σ) * (a * b * c) ^ (1 - σ / 2) := by
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hconv := rpow_negative_loss hD (by linarith : -1 ≤ -1 + σ / 2)
  have hslab := rpow_nat_negative_loss hD hσ (by linarith : σ ≤ 1) 11
  have hbox : (a * b) ^ (1 - σ / 2) ≤ (a * b * c) ^ (1 - σ / 2) := by
    apply Real.rpow_le_rpow (by positivity) _ (by linarith)
    exact le_mul_of_one_le_right (mul_nonneg ha.le hb.le) hc
  calc
    _ = A * δ ^ ε * b ^ ω * (1 / D) * (1 / D ^ 11) *
        q ^ (1 - σ) * (a * b) ^ (1 - σ / 2) := by field_simp <;> ring
    _ ≤ _ := by gcongr

lemma profile_product {σ ω ε A B δ a b F D q : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hδ : 0 < δ) (ha : 0 < a) (hb : 0 < b)
    (hF : 0 < F) (hD : 0 < D) (hq : 0 < q) :
    cellProfile σ ω ε A δ a b F D *
      (B * δ ^ ε * b ^ ω * q ^ (1 - σ) * (a * b) ^ (1 - σ / 2) / D ^ 12) =
    (A * B) * δ ^ (2 * ε) * (δ / a) ^ ω * b ^ ω * (F * q) ^ (1 - σ) *
      δ ^ (2 - σ) / D ^ 36 := by
  unfold cellProfile fineProfile
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity)
    (by simp only [Set.mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow]
  ring

lemma final_profile_lower {σ ω ε t A δ a b D n q F : ℝ}
    (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hA : 0 < A) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (ha : 0 < a) (hb : 0 < b) (hD : 1 ≤ D)
    (hn : 0 < n) (hq : 0 < q) (hF : 0 < F)
    (hsize : n ≤ D ^ (9 : ℕ) * (F * q))
    (herror : δ ^ ε ≤ δ ^ (2 * t) / D ^ 45) :
    bound σ ω ε A δ a b n ≤
      A * δ ^ (2 * t) * (δ / a) ^ ω * b ^ ω * (F * q) ^ (1 - σ) *
        δ ^ (2 - σ) / D ^ 36 := by
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hnum := rpow_loss hD hn (mul_pos hF hq)
    (by linarith : 0 ≤ 1 - σ) (by linarith : 1 - σ ≤ 1) 9 hsize
  have he : bound σ ω ε A δ a b n =
      A * δ ^ ε * (δ / a) ^ ω * b ^ ω * n ^ (1 - σ) * δ ^ (2 - σ) := by
    unfold bound
    apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity)
      (by simp only [Set.mem_Ioi]; positivity)
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow]
    ring
  rw [he]
  calc
    _ ≤ A * (δ ^ (2 * t) / D ^ 45) * (δ / a) ^ ω * b ^ ω *
        n ^ (1 - σ) * δ ^ (2 - σ) := by gcongr
    _ = A * δ ^ (2 * t) * (δ / a) ^ ω * b ^ ω *
        (n ^ (1 - σ) / D ^ 9) * δ ^ (2 - σ) / D ^ 36 := by field_simp <;> ring
    _ ≤ _ := by gcongr

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
