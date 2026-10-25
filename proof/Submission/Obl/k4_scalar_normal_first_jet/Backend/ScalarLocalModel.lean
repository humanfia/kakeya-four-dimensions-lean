/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarLocalModel.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarLocalModel.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact scalar quadratic normalization and its recorded error. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

/-- Two actual model errors and one output collision suffice for the
original scalar dot relation. -/
theorem scalar_collision_of_model_error {u φ v v' G G' z z' F F' p e : ℝ}
    (hF : |F - (z + u * G + φ * v)| ≤ e * p)
    (hF' : |F' - (z' + u * G' + φ * v')| ≤ e * p)
    (hcollision : |F - F'| ≤ p) :
    |u * (G - G') + φ * (v - v') - (z' - z)| ≤ (1 + 2 * e) * p := by
  obtain ⟨h₁, h₂⟩ := abs_le.mp hF
  obtain ⟨h₁', h₂'⟩ := abs_le.mp hF'
  obtain ⟨hc₁, hc₂⟩ := abs_le.mp hcollision
  rw [abs_le]
  constructor <;> nlinarith only [h₁, h₂, h₁', h₂', hc₁, hc₂]

/-- The quadratic remainder in the local scalar model is exact. In
particular no derivative or coefficient is silently frozen in the model. -/
theorem quadratic_local_identity (a₀ a₁ a₂ b₀ b₁ t₀ H Fstar base u Fu : ℝ)
    (hH : H ≠ 0) :
    ((a₀ + a₁ * (t₀ + H * u) + a₂ * (t₀ + H * u) ^ 2) -
        Fu * (b₀ + b₁ * (t₀ + H * u)) - base) / H =
      ((a₀ + a₁ * t₀ + a₂ * t₀ ^ 2 - Fstar * (b₀ + b₁ * t₀)) - base) / H +
        u * (a₁ + 2 * a₂ * t₀ - Fstar * b₁) -
        ((Fu - Fstar) / H) * (b₀ + b₁ * t₀) +
        H * (u ^ 2 * a₂ - u * ((Fu - Fstar) / H) * b₁) := by
  field_simp
  ring

/-- At a normalized unit time, the full local-model error has the stated
polynomial coefficient cost. -/
theorem quadratic_local_error {H K u a₂ b₁ φ : ℝ}
    (hH : 0 ≤ H) (hK : 0 ≤ K) (hu : |u| ≤ 1)
    (ha : |a₂| ≤ K) (hb : |b₁| ≤ K) (hφ : |φ| ≤ K) :
    |H * (u ^ 2 * a₂ - u * φ * b₁)| ≤ H * (K + K ^ 2) := by
  rw [abs_mul, abs_of_nonneg hH]
  apply mul_le_mul_of_nonneg_left _ hH
  calc
    |u ^ 2 * a₂ - u * φ * b₁| ≤ |u ^ 2 * a₂| + |u * φ * b₁| := abs_sub _ _
    _ = |u| ^ 2 * |a₂| + |u| * |φ| * |b₁| := by rw [abs_mul, abs_pow, abs_mul, abs_mul]
    _ ≤ K + K ^ 2 := by
      have hu0 := abs_nonneg u
      have ha0 := abs_nonneg a₂
      have hb0 := abs_nonneg b₁
      have hφ0 := abs_nonneg φ
      have h₁ := mul_le_mul_of_nonneg_left ha (sq_nonneg |u|)
      have h₂ := mul_le_mul_of_nonneg_left hφ hu0
      have h₃ := mul_le_mul_of_nonneg_right h₂ hb0
      have h₄ := mul_le_mul_of_nonneg_left hb (mul_nonneg hu0 hK)
      nlinarith [sq_nonneg (|u| - 1), mul_nonneg hK (sub_nonneg.mpr hu)]

/-- The dot-product identity keeps every approximation error at both tested
times. This is the local scalar collision relation used by planar forcing. -/
theorem scalar_collision_dot_error
    (u u₀ φu φ₀ v v' G G' z z' Su Su' S₀ S₀' p δ : ℝ)
    (hu : |Su - (z + u * G - φu * v)| ≤ δ)
    (hu' : |Su' - (z' + u * G' - φu * v')| ≤ δ)
    (h₀ : |S₀ - (z + u₀ * G - φ₀ * v)| ≤ δ)
    (h₀' : |S₀' - (z' + u₀ * G' - φ₀ * v')| ≤ δ)
    (hcollision : |Su - Su'| ≤ p) :
    |((u - u₀) * (G - G') - (φu - φ₀) * (v - v')) - (S₀' - S₀)| ≤ p + 4 * δ := by
  obtain ⟨hu₁, hu₂⟩ := abs_le.mp hu
  obtain ⟨hu'₁, hu'₂⟩ := abs_le.mp hu'
  obtain ⟨h₀₁, h₀₂⟩ := abs_le.mp h₀
  obtain ⟨h₀'₁, h₀'₂⟩ := abs_le.mp h₀'
  obtain ⟨hc₁, hc₂⟩ := abs_le.mp hcollision
  rw [abs_le]
  constructor <;> nlinarith only [hu₁, hu₂, hu'₁, hu'₂, h₀₁, h₀₂, h₀'₁, h₀'₂, hc₁, hc₂]

/-- Freezing all three collision-cell coordinates changes the dot product
only by the explicit bottom-scale error. -/
theorem scalar_collision_dot_quantization
    {u uk u₀ G G' Gj Gj' φu φk φ₀ v v' vj vj' K p : ℝ}
    (hK : 0 ≤ K) (hp : 0 ≤ p) (hu : |u - uk| ≤ p) (huk : |uk - u₀| ≤ 1)
    (hG : |G| ≤ K) (hG' : |G'| ≤ K)
    (hGj : |G - Gj| ≤ K * p) (hGj' : |G' - Gj'| ≤ K * p)
    (hφ : |φu - φk| ≤ K * p) (hφ₀ : |φk - φ₀| ≤ K)
    (hv : |v| ≤ K) (hv' : |v'| ≤ K)
    (hvj : |v - vj| ≤ p) (hvj' : |v' - vj'| ≤ p) :
    |((u - u₀) * (G - G') - (φu - φ₀) * (v - v')) -
      ((uk - u₀) * (Gj - Gj') - (φk - φ₀) * (vj - vj'))| ≤ (6 * K + 2 * K ^ 2) * p := by
  have hGD : |G - G'| ≤ 2 * K := (abs_sub G G').trans (by linarith)
  have hGQ : |(G - Gj) - (G' - Gj')| ≤ 2 * K * p :=
    (abs_sub (G - Gj) (G' - Gj')).trans (by linarith)
  have hvD : |v - v'| ≤ 2 * K := (abs_sub v v').trans (by linarith)
  have hvQ : |(v - vj) - (v' - vj')| ≤ 2 * p :=
    (abs_sub (v - vj) (v' - vj')).trans (by linarith)
  have h₁ : |(u - uk) * (G - G')| ≤ p * (2 * K) := by
    rw [abs_mul]
    exact mul_le_mul hu hGD (abs_nonneg _) hp
  have h₂ : |(uk - u₀) * ((G - Gj) - (G' - Gj'))| ≤ 2 * K * p := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul huk hGQ (abs_nonneg _) zero_le_one
  have h₃ : |(φu - φk) * (v - v')| ≤ (K * p) * (2 * K) := by
    rw [abs_mul]
    exact mul_le_mul hφ hvD (abs_nonneg _) (mul_nonneg hK hp)
  have h₄ : |(φk - φ₀) * ((v - vj) - (v' - vj'))| ≤ K * (2 * p) := by
    rw [abs_mul]
    exact mul_le_mul hφ₀ hvQ (abs_nonneg _) hK
  have he : ((u - u₀) * (G - G') - (φu - φ₀) * (v - v')) -
      ((uk - u₀) * (Gj - Gj') - (φk - φ₀) * (vj - vj')) =
      (u - uk) * (G - G') + (uk - u₀) * ((G - Gj) - (G' - Gj')) -
        (φu - φk) * (v - v') - (φk - φ₀) * ((v - vj) - (v' - vj')) := by ring
  rw [he]
  have ht₁ := abs_sub
    ((u - uk) * (G - G') + (uk - u₀) * ((G - Gj) - (G' - Gj')) - (φu - φk) * (v - v'))
    ((φk - φ₀) * ((v - vj) - (v' - vj')))
  have ht₂ := abs_sub
      ((u - uk) * (G - G') + (uk - u₀) * ((G - Gj) - (G' - Gj')))
      ((φu - φk) * (v - v'))
  have ht₃ := abs_add_le ((u - uk) * (G - G')) ((uk - u₀) * ((G - Gj) - (G' - Gj')))
  nlinarith only [ht₁, ht₂, ht₃, h₁, h₂, h₃, h₄]

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
