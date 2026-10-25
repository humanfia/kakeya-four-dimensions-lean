import Mathlib
import Submission.Lib.K4WeightedCellEnergy

namespace Submission.Obl.k4_oss_level_finite_gain

theorem normalized_ball_power_bound {δ a θ s u : ℝ}
    (hδ : 0 < δ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hu : 0 < u) (hu1 : u ≤ 1)
    (habsorb : 4 * δ ^ (-3 * a) ≤ δ ^ (-θ)) :
    δ ^ (-a) * (2 * u) ^ s / δ ^ (2 * a) ≤ δ ^ (-θ) * u ^ (s / 2) := by
  have htwo : (2 : ℝ) ^ s ≤ 4 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs1
    norm_num at hh
    linarith
  have huPow : u ^ s ≤ u ^ (s / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hu hu1 (by linarith)
  have he : δ ^ (-a) / δ ^ (2 * a) = δ ^ (-3 * a) := by
    rw [← Real.rpow_sub hδ]
    congr 1
    ring
  calc
    _ = (δ ^ (-a) / δ ^ (2 * a)) * ((2 : ℝ) ^ s * u ^ s) := by
      rw [Real.mul_rpow (by norm_num) hu.le]
      ring
    _ = δ ^ (-3 * a) * ((2 : ℝ) ^ s * u ^ s) := by rw [he]
    _ ≤ δ ^ (-3 * a) * (4 * u ^ (s / 2)) := by gcongr
    _ = (4 * δ ^ (-3 * a)) * u ^ (s / 2) := by ring
    _ ≤ δ ^ (-θ) * u ^ (s / 2) :=
      mul_le_mul_of_nonneg_right habsorb (Real.rpow_nonneg hu.le _)

theorem large_ball_power_bound {δ a θ s u : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 ≤ a) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hu : (1 / 2 : ℝ) ≤ u) (habsorb : 4 * δ ^ (-3 * a) ≤ δ ^ (-θ)) :
    1 ≤ δ ^ (-θ) * u ^ (s / 2) := by
  have hbase : 1 ≤ δ ^ (-3 * a) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hcoef : 4 ≤ δ ^ (-θ) := by linarith
  have huPow : (1 / 2 : ℝ) ≤ u ^ (s / 2) := by
    calc
      (1 / 2 : ℝ) = (1 / 2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (1 / 2 : ℝ) ^ (s / 2) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
      _ ≤ u ^ (s / 2) := Real.rpow_le_rpow (by norm_num) hu (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left huPow (Real.rpow_nonneg hδ.le (-θ))]

/-- A heavy level inherits the uniform finite Frostman cap at all radii. -/
theorem heavy_level_frostman {δ a θ s : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 ≤ a) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (habsorb : 4 * δ ^ (-3 * a) ≤ δ ^ (-θ))
    (F A : Finset ℝ) (p : ℝ → ℝ) (q : ℝ)
    (hAF : A ⊆ F) (hp : ∀ x ∈ F, 0 ≤ p x) (hq : ∀ x ∈ A, q ≤ p x)
    (hmass : δ ^ (2 * a) ≤ q * (A.card : ℝ))
    (hcap : ∀ x u : ℝ, δ ≤ u → u ≤ (1 / 2 : ℝ) →
      ENNReal.ofReal (Finset.sum (F.filter (fun y => dist y x ≤ u)) p) ≤
        ENNReal.ofReal (δ ^ (-a) * (2 * u) ^ s)) :
    ∀ x u : ℝ, δ ≤ u →
      ((A.filter (fun y => dist y x ≤ u)).card : ℝ) ≤
        δ ^ (-θ) * u ^ (s / 2) * (A.card : ℝ) := by
  classical
  intro x u hδu
  have hu : 0 < u := hδ.trans_le hδu
  by_cases huHalf : u ≤ (1 / 2 : ℝ)
  · have hrealcap : Finset.sum (F.filter (fun y => dist y x ≤ u)) p ≤
        δ ^ (-a) * (2 * u) ^ s :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hcap x u hδu huHalf)
    calc
      _ ≤ ((δ ^ (-a) * (2 * u) ^ s) / δ ^ (2 * a)) * (A.card : ℝ) :=
        Submission.Lib.K4WeightedCellEnergy.heavy_subset_count_bound F A
          (fun y => dist y x ≤ u) p hAF (Real.rpow_pos_of_pos hδ _) hp hq hmass hrealcap
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (normalized_ball_power_bound hδ hs hs1 hu (by linarith) habsorb) (Nat.cast_nonneg _)
  · calc
      ((A.filter (fun y => dist y x ≤ u)).card : ℝ) ≤ (A.card : ℝ) := by
        exact_mod_cast Finset.card_filter_le A (fun y => dist y x ≤ u)
      _ = 1 * (A.card : ℝ) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (large_ball_power_bound hδ hδ1 ha hs hs1 (by linarith) habsorb) (Nat.cast_nonneg _)

theorem direction_power_bound {δ a θ s u : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 ≤ a) (hs : 0 ≤ s)
    (hu : 0 < u) (hu1 : u ≤ 1)
    (habsorb : 4 * δ ^ (-3 * a) ≤ δ ^ (-θ)) :
    4 * δ ^ (-a) * u ^ s ≤ δ ^ (-θ) * u ^ (s / 2) := by
  have hδPow : δ ^ (-a) ≤ δ ^ (-3 * a) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have huPow : u ^ s ≤ u ^ (s / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hu hu1 (by linarith)
  calc
    4 * δ ^ (-a) * u ^ s ≤ (4 * δ ^ (-3 * a)) * u ^ (s / 2) := by gcongr
    _ ≤ δ ^ (-θ) * u ^ (s / 2) :=
      mul_le_mul_of_nonneg_right habsorb (Real.rpow_nonneg hu.le _)

end Submission.Obl.k4_oss_level_finite_gain
