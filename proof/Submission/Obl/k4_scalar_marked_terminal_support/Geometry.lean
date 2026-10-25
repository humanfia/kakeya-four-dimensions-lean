import Submission.Obl.k4_scalar_marked_terminal_support.Cover
import Submission.Obl.k4_scalar_marked_packet_recovery.MarkedMeasure
import Submission.Obl.k4_scalar_coefficient_clustering.Evaluation
import Submission.Obl.k4_matching_homogeneous_records.Offsets

namespace Submission.Obl.k4_scalar_marked_terminal_support

open Set MeasureTheory
open Submission.Obl.k4_scalar_marked_packet_recovery (timeCell timeCell_subset_unit)
open Submission.Obl.k4_scalar_coefficient_clustering (floor_scaled_error)
open Submission.Obl.k4_matching_homogeneous_records (floor_sub_bound)

noncomputable def evalX (c : Fin 5 → ℝ) (t : ℝ) : ℝ :=
  c 2 + t * c 3 + t ^ 2 * c 4

noncomputable def evalY (c : Fin 5 → ℝ) (t : ℝ) : ℝ := c 0 + t * c 1

lemma same_timeCell_dist {J : ℕ} (hJ : 1 ≤ J) {σ : ℝ} (hJσ : 1 ≤ (J : ℝ) * σ)
    {z : Fin J} {t v : ℝ} (ht : t ∈ timeCell J z) (hv : v ∈ timeCell J z) :
    |t - v| ≤ σ := by
  have hJ0 : 0 < (J : ℝ) := by exact_mod_cast (show 0 < J by omega)
  have hσ : 1 / (J : ℝ) ≤ σ := (div_le_iff₀ hJ0).mpr (by nlinarith)
  have hh : ((z : ℝ) + 1) / (J : ℝ) - (z : ℝ) / (J : ℝ) = 1 / (J : ℝ) := by ring
  exact (abs_le.mpr ⟨by linarith [ht.1, ht.2.le, hv.1, hv.2.le],
    by linarith [ht.1, ht.2.le, hv.1, hv.2.le]⟩ : |t - v| ≤ 1 / (J : ℝ)) |>.trans hσ

lemma rounded_noisy_near {σ δ : ℝ} (hδσ : δ ≤ σ)
    {c b b₀ : Fin 5 → ℝ} (hb : ∀ i, |b i - b₀ i| ≤ δ)
    (hc : ∀ i, c i - b₀ i ∈ Icc 0 σ) :
    ∀ i, |c i - b i| ≤ 2 * σ := by
  intro i
  have hi : |c i - b₀ i| ≤ σ := by
    rw [abs_of_nonneg (hc i).1]
    exact (hc i).2
  calc
    |c i - b i| ≤ |c i - b₀ i| + |b₀ i - b i| := abs_sub_le _ _ _
    _ ≤ σ + δ := by rw [abs_sub_comm (b₀ i)]; exact add_le_add hi (hb i)
    _ ≤ 2 * σ := by linarith

lemma evalY_perturbation {K σ t v : ℝ} (hK : 1 ≤ K) (hσ : 0 ≤ σ)
    {c b : Fin 5 → ℝ} (hb : ∀ i, |b i| ≤ K) (hc : ∀ i, |c i - b i| ≤ 2 * σ)
    (ht : t ∈ Icc (0 : ℝ) 1) (htv : |t - v| ≤ σ) :
    |evalY c t - evalY b v| ≤ 5 * K * σ := by
  have ht' : |t| ≤ 1 := by simpa [abs_of_nonneg ht.1] using ht.2
  have heq : evalY c t - evalY b v =
      (c 0 - b 0) + t * (c 1 - b 1) + (t - v) * b 1 := by unfold evalY; ring
  rw [heq]
  calc
    _ ≤ |c 0 - b 0| + |t * (c 1 - b 1)| + |(t - v) * b 1| := abs_add_three _ _ _
    _ ≤ 2 * σ + 1 * (2 * σ) + σ * K := by
      simp only [abs_mul]
      gcongr <;> first | apply hc | apply hb | assumption
    _ ≤ _ := by nlinarith

lemma evalX_perturbation {K σ t v : ℝ} (hK : 1 ≤ K) (hσ : 0 ≤ σ)
    {c b : Fin 5 → ℝ} (hb : ∀ i, |b i| ≤ K) (hc : ∀ i, |c i - b i| ≤ 2 * σ)
    (ht : t ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) (htv : |t - v| ≤ σ) :
    |evalX c t - evalX b v| ≤ 9 * K * σ := by
  have ht' : |t| ≤ 1 := by simpa [abs_of_nonneg ht.1] using ht.2
  have htsq : |t ^ 2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [ht.1, ht.2]
  have hsum : |t + v| ≤ 2 := by rw [abs_of_nonneg (by linarith [ht.1, hv.1] : 0 ≤ t + v)]; linarith [ht.2, hv.2]
  have hsq : |t ^ 2 - v ^ 2| ≤ 2 * σ := by
    rw [show t ^ 2 - v ^ 2 = (t - v) * (t + v) by ring, abs_mul]
    nlinarith [mul_le_mul htv hsum (abs_nonneg (t + v)) hσ]
  have hnoise : |evalX c t - evalX b t| ≤ 6 * σ := by
    have heq : evalX c t - evalX b t =
        (c 2 - b 2) + t * (c 3 - b 3) + t ^ 2 * (c 4 - b 4) := by unfold evalX; ring
    rw [heq]
    calc
      _ ≤ |c 2 - b 2| + |t * (c 3 - b 3)| + |t ^ 2 * (c 4 - b 4)| := abs_add_three _ _ _
      _ ≤ 2 * σ + 1 * (2 * σ) + 1 * (2 * σ) := by
        simp only [abs_mul]
        gcongr <;> first | apply hc | apply hb | assumption
      _ = _ := by ring
  have htime : |evalX b t - evalX b v| ≤ 3 * K * σ := by
    have heq : evalX b t - evalX b v =
        (t - v) * b 3 + (t ^ 2 - v ^ 2) * b 4 := by unfold evalX; ring
    rw [heq]
    calc
      _ ≤ |(t - v) * b 3| + |(t ^ 2 - v ^ 2) * b 4| := abs_add_le _ _
      _ ≤ σ * K + (2 * σ) * K := by
        simp only [abs_mul]
        gcongr <;> first | apply hc | apply hb | assumption
      _ = _ := by ring
  calc
    _ ≤ |evalX c t - evalX b t| + |evalX b t - evalX b v| := abs_sub_le _ _ _
    _ ≤ 6 * σ + 3 * K * σ := add_le_add hnoise htime
    _ ≤ _ := by nlinarith

lemma observations_near_original {K σ a t v : ℝ} (hK : 1 ≤ K) (hσ : 0 < σ)
    (hσa : σ ≤ a) {c b : Fin 5 → ℝ} (hb : ∀ i, |b i| ≤ K)
    (hc : ∀ i, |c i - b i| ≤ 2 * σ)
    (ht : t ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) (htv : |t - v| ≤ σ) :
    |t - σ * (⌊v / σ⌋ : ℝ)| ≤ 2 * σ ∧
    |evalY c t - σ * (⌊evalY b v / σ⌋ : ℝ)| ≤ 10 * K * σ ∧
    |(⌊evalX c t / a⌋ : ℝ) - (⌊evalX b v / a⌋ : ℝ)| ≤ 10 * K := by
  have ha : 0 < a := hσ.trans_le hσa
  refine ⟨?_, ?_, ?_⟩
  · exact (abs_sub_le t v _).trans ((add_le_add htv (floor_scaled_error hσ v)).trans (by ring_nf; rfl))
  · calc
      _ ≤ |evalY c t - evalY b v| + |evalY b v - σ * (⌊evalY b v / σ⌋ : ℝ)| := abs_sub_le _ _ _
      _ ≤ 5 * K * σ + σ := add_le_add (evalY_perturbation hK hσ.le hb hc ht htv)
        (floor_scaled_error hσ _)
      _ ≤ _ := by nlinarith
  · have hx := evalX_perturbation hK hσ.le hb hc ht hv htv
    have hxdiv : |evalX c t / a - evalX b v / a| ≤ 9 * K := by
      rw [← sub_div, abs_div, abs_of_pos ha]
      apply (div_le_iff₀ ha).mpr
      exact hx.trans (by nlinarith)
    have hfloor := floor_sub_bound (evalX c t / a) (evalX b v / a)
    push_cast at hfloor
    linarith

end Submission.Obl.k4_scalar_marked_terminal_support
