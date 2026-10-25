import Mathlib

namespace Submission.Obl.k4_oss_weighted_level_transfer

lemma weighted_cubic {a b X Y E K : ℝ} (hE : E ≤ K * X ^ 2 * Y) :
    a ^ 2 * b ^ 2 * E ≤ K * (a * X) ^ 2 * (b ^ 2 * Y) := by
  calc
    _ ≤ a ^ 2 * b ^ 2 * (K * X ^ 2 * Y) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    _ = _ := by ring

lemma weighted_cubic_mass {a b X Y E K L η Q : ℝ}
    (ha : 0 ≤ a) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hK : 0 ≤ K)
    (hE : E ≤ K * X ^ 2 * Y) (hm : a * X ≤ η)
    (hq : b ^ 2 * Y ≤ L ^ 2 * Q) :
    a ^ 2 * b ^ 2 * E ≤ K * (η ^ 2 * L ^ 2) * Q := by
  have hη : 0 ≤ η := (mul_nonneg ha hX).trans hm
  calc
    _ ≤ K * (a * X) ^ 2 * (b ^ 2 * Y) := weighted_cubic hE
    _ ≤ K * η ^ 2 * (L ^ 2 * Q) := by gcongr
    _ = _ := by ring

lemma weighted_cubic_ratio {a b X Y E K L k Q : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hK : 0 ≤ K) (hk : 0 ≤ k) (hQ : 0 ≤ Q)
    (hE : E ≤ K * X ^ 2 * Y) (hratio : X ≤ k * Y)
    (hm : b * Y ≤ L) (hq : a ^ 2 * X ≤ L ^ 2 * Q) :
    a ^ 2 * b ^ 2 * E ≤ K * (k * L ^ 4) * Q := by
  have hL : 0 ≤ L := (mul_nonneg hb hY).trans hm
  calc
    _ ≤ K * (a * X) ^ 2 * (b ^ 2 * Y) := weighted_cubic hE
    _ = K * (a ^ 2 * X) * b ^ 2 * Y * X := by ring
    _ ≤ K * (a ^ 2 * X) * b ^ 2 * Y * (k * Y) := by gcongr
    _ = K * k * (a ^ 2 * X) * (b * Y) ^ 2 := by ring
    _ ≤ K * k * (L ^ 2 * Q) * L ^ 2 := by gcongr
    _ = _ := by ring

lemma weighted_cubic_large {a b X Y E K L T τ Q : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hK : 0 ≤ K) (hT : 0 < T) (hlarge : T ≤ Y)
    (hE : E ≤ K * X ^ 2 * Y) (hmX : a * X ≤ L) (hmY : b * Y ≤ L)
    (hbudget : L ^ 4 ≤ τ * Q * T) :
    a ^ 2 * b ^ 2 * E ≤ K * τ * Q := by
  have hL : 0 ≤ L := (mul_nonneg ha hX).trans hmX
  have hq : (b ^ 2 * Y) * T ≤ L ^ 2 := by
    calc
      _ ≤ (b ^ 2 * Y) * Y := by gcongr
      _ = (b * Y) ^ 2 := by ring
      _ ≤ _ := pow_le_pow_left₀ (mul_nonneg hb hY) hmY 2
  have hbound : (a ^ 2 * b ^ 2 * E) * T ≤ (K * τ * Q) * T := by
    calc
      _ ≤ (K * (a * X) ^ 2 * (b ^ 2 * Y)) * T :=
        mul_le_mul_of_nonneg_right (weighted_cubic hE) hT.le
      _ = K * (a * X) ^ 2 * ((b ^ 2 * Y) * T) := by ring
      _ ≤ K * L ^ 2 * L ^ 2 := by gcongr
      _ = K * L ^ 4 := by ring
      _ ≤ K * (τ * Q * T) := mul_le_mul_of_nonneg_left hbudget hK
      _ = _ := by ring
  nlinarith

lemma weighted_cubic_gain {a b X Y E K L Q : ℝ}
    (ha : 0 ≤ a) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hE : E ≤ K * X ^ 2 * Y) (hm : a * X ≤ L)
    (hq : b ^ 2 * Y ≤ L ^ 2 * Q) :
    a ^ 2 * b ^ 2 * E ≤ (K * L ^ 4) * Q := by
  calc
    _ ≤ K * (a * X) ^ 2 * (b ^ 2 * Y) := weighted_cubic hE
    _ ≤ K * L ^ 2 * (L ^ 2 * Q) := by gcongr
    _ = _ := by ring

end Submission.Obl.k4_oss_weighted_level_transfer
