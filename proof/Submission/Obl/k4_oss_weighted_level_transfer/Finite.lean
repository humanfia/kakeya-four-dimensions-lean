import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RealSeparatedCounts
import Submission.Obl.k4_oss_weighted_level_transfer.Mixture

open MeasureTheory Set
open scoped BigOperators NNReal ENNReal

namespace Submission.Obl.k4_oss_weighted_level_transfer

noncomputable def finiteEnergy (δ t : ℝ) (A B : Finset ℝ) : ℝ := by
  classical
  exact ((((A ×ˢ B) ×ˢ (A ×ˢ B)).filter
    (fun q => |q.1.1 + t * q.1.2 - (q.2.1 + t * q.2.2)| ≤ 16 * δ)).card : ℝ)

lemma finiteEnergy_nonneg (δ t : ℝ) (A B : Finset ℝ) : 0 ≤ finiteEnergy δ t A B := by
  unfold finiteEnergy
  positivity

lemma finiteEnergy_sums (δ t : ℝ) (A B : Finset ℝ) :
    finiteEnergy δ t A B = ∑ a ∈ A, ∑ b ∈ B, ∑ a' ∈ A, ∑ b' ∈ B,
      if |a + t * b - (a' + t * b')| ≤ 16 * δ then (1 : ℝ) else 0 := by
  classical
  simp only [finiteEnergy, Finset.card_eq_sum_ones, Finset.sum_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp only [Finset.sum_product]

lemma separated_window_card {δ R c : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R)
    (A : Finset ℝ)
    (hsep : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → δ ≤ dist a a') :
    ((A.filter (fun a => dist a c ≤ R)).card : ℝ) * δ ≤ 2 * R + 2 * δ := by
  classical
  exact WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.real_separated_ball_card
    hδ hR _
    (fun a ha a' ha' hne => hsep a (Finset.mem_filter.mp ha).1
      a' (Finset.mem_filter.mp ha').1 hne)
    (fun a ha => (Finset.mem_filter.mp ha).2)

lemma energy_second_fiber {δ t : ℝ} (hδ : 0 < δ) (ht : 1 / 4 ≤ t)
    (B : Finset ℝ)
    (hsep : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → δ ≤ dist b b') (a b a' : ℝ) :
    ((B.filter (fun b' => |a + t * b - (a' + t * b')| ≤ 16 * δ)).card : ℝ) ≤ 130 := by
  classical
  have htp : 0 < t := by linarith
  let C := B.filter (fun b' => |a + t * b - (a' + t * b')| ≤ 16 * δ)
  have hball (b' : ℝ) (hb' : b' ∈ C) : dist b' ((a - a') / t + b) ≤ 64 * δ := by
    have hh := (Finset.mem_filter.mp hb').2
    have heq : t * (b' - ((a - a') / t + b)) =
        -(a + t * b - (a' + t * b')) := by
      field_simp
      <;> ring
    have hmul : t * |b' - ((a - a') / t + b)| ≤ 16 * δ := by
      calc
        _ = |t * (b' - ((a - a') / t + b))| := by rw [abs_mul, abs_of_pos htp]
        _ ≤ 16 * δ := by rw [heq, abs_neg]; exact hh
    rw [Real.dist_eq]
    nlinarith [mul_nonneg (show 0 ≤ t - 1 / 4 by linarith)
      (abs_nonneg (b' - ((a - a') / t + b)))]
  have hc := WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.real_separated_ball_card
    hδ (by positivity : 0 ≤ 64 * δ) C
    (fun x hx y hy hne => hsep x (Finset.mem_filter.mp hx).1
      y (Finset.mem_filter.mp hy).1 hne) hball
  change (C.card : ℝ) ≤ 130
  nlinarith

lemma energy_first_fiber {δ t : ℝ} (hδ : 0 < δ)
    (A : Finset ℝ)
    (hsep : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → δ ≤ dist a a') (a b b' : ℝ) :
    ((A.filter (fun a' => |a + t * b - (a' + t * b')| ≤ 16 * δ)).card : ℝ) ≤ 130 := by
  classical
  let C := A.filter (fun a' => |a + t * b - (a' + t * b')| ≤ 16 * δ)
  have hball (a' : ℝ) (ha' : a' ∈ C) : dist a' (a + t * (b - b')) ≤ 16 * δ := by
    have hh := (Finset.mem_filter.mp ha').2
    rw [Real.dist_eq, abs_sub_comm]
    convert hh using 1 <;> congr 1 <;> ring
  have hc := WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.real_separated_ball_card
    hδ (by positivity : 0 ≤ 16 * δ) C
    (fun x hx y hy hne => hsep x (Finset.mem_filter.mp hx).1
      y (Finset.mem_filter.mp hy).1 hne) hball
  change (C.card : ℝ) ≤ 130
  nlinarith

lemma finiteEnergy_le_left {δ t : ℝ} (hδ : 0 < δ) (ht : 1 / 4 ≤ t)
    (A B : Finset ℝ)
    (hsepB : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → δ ≤ dist b b') :
    finiteEnergy δ t A B ≤ 130 * (A.card : ℝ) ^ 2 * (B.card : ℝ) := by
  classical
  rw [finiteEnergy_sums]
  calc
    _ ≤ ∑ _a ∈ A, ∑ _b ∈ B, ∑ _a' ∈ A, (130 : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      apply Finset.sum_le_sum
      intro a' ha'
      simpa only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one] using
        energy_second_fiber hδ ht B hsepB a b a'
    _ = _ := by simp; ring

lemma finiteEnergy_le_right {δ t : ℝ} (hδ : 0 < δ)
    (A B : Finset ℝ)
    (hsepA : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → δ ≤ dist a a') :
    finiteEnergy δ t A B ≤ 130 * (A.card : ℝ) * (B.card : ℝ) ^ 2 := by
  classical
  rw [finiteEnergy_sums]
  have hf (a b : ℝ) : (∑ a' ∈ A, ∑ b' ∈ B,
      if |a + t * b - (a' + t * b')| ≤ 16 * δ then (1 : ℝ) else 0) ≤
      ∑ _b' ∈ B, (130 : ℝ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro b' hb'
    simpa only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one] using
      energy_first_fiber hδ A hsepA a b b'
  calc
    _ ≤ ∑ a ∈ A, ∑ b ∈ B, ∑ _b' ∈ B, (130 : ℝ) :=
      Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hf a b))
    _ = _ := by simp; ring

noncomputable def averageEnergy (δ : ℝ) (ν : Measure ℝ) (A B : Finset ℝ) : ℝ :=
  (∫⁻ t, ENNReal.ofReal (finiteEnergy δ t A B) ∂ν).toReal

lemma averageEnergy_nonneg (δ : ℝ) (ν : Measure ℝ) (A B : Finset ℝ) :
    0 ≤ averageEnergy δ ν A B := ENNReal.toReal_nonneg

lemma lintegral_finiteEnergy_le_left {δ : ℝ} (hδ : 0 < δ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν (Icc (1 / 4 : ℝ) 1)ᶜ = 0) (A B : Finset ℝ)
    (hsep : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → δ ≤ dist b b') :
    (∫⁻ t, ENNReal.ofReal (finiteEnergy δ t A B) ∂ν) ≤
      ENNReal.ofReal (130 * (A.card : ℝ) ^ 2 * (B.card : ℝ)) := by
  have hmem : ∀ᵐ t ∂ν, t ∈ Icc (1 / 4 : ℝ) 1 := ae_iff.mpr hν
  calc
    _ ≤ ∫⁻ _t, ENNReal.ofReal (130 * (A.card : ℝ) ^ 2 * (B.card : ℝ)) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [hmem] with t ht
      exact ENNReal.ofReal_le_ofReal (finiteEnergy_le_left hδ ht.1 A B hsep)
    _ = _ := by simp

lemma lintegral_finiteEnergy_le_right {δ : ℝ} (hδ : 0 < δ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (A B : Finset ℝ)
    (hsep : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → δ ≤ dist a a') :
    (∫⁻ t, ENNReal.ofReal (finiteEnergy δ t A B) ∂ν) ≤
      ENNReal.ofReal (130 * (A.card : ℝ) * (B.card : ℝ) ^ 2) := by
  calc
    _ ≤ ∫⁻ _t, ENNReal.ofReal (130 * (A.card : ℝ) * (B.card : ℝ) ^ 2) ∂ν :=
      lintegral_mono (fun t => ENNReal.ofReal_le_ofReal (finiteEnergy_le_right hδ A B hsep))
    _ = _ := by simp

lemma averageEnergy_le_left {δ : ℝ} (hδ : 0 < δ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν (Icc (1 / 4 : ℝ) 1)ᶜ = 0) (A B : Finset ℝ)
    (hsep : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → δ ≤ dist b b') :
    averageEnergy δ ν A B ≤ 130 * (A.card : ℝ) ^ 2 * (B.card : ℝ) :=
  ENNReal.toReal_le_of_le_ofReal (by positivity)
    (lintegral_finiteEnergy_le_left hδ ν hν A B hsep)

lemma averageEnergy_le_right {δ : ℝ} (hδ : 0 < δ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (A B : Finset ℝ)
    (hsep : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → δ ≤ dist a a') :
    averageEnergy δ ν A B ≤ 130 * (A.card : ℝ) * (B.card : ℝ) ^ 2 :=
  ENNReal.toReal_le_of_le_ofReal (by positivity)
    (lintegral_finiteEnergy_le_right hδ ν A B hsep)

lemma lintegral_finiteEnergy_eq {δ : ℝ} (hδ : 0 < δ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (A B : Finset ℝ)
    (hsep : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → δ ≤ dist a a') :
    (∫⁻ t, ENNReal.ofReal (finiteEnergy δ t A B) ∂ν) =
      ENNReal.ofReal (averageEnergy δ ν A B) := by
  symm
  apply ENNReal.ofReal_toReal
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (lintegral_finiteEnergy_le_right hδ ν A B hsep)

end Submission.Obl.k4_oss_weighted_level_transfer
