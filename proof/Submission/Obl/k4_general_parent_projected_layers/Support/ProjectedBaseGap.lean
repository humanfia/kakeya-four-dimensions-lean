/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/ProjectedBaseGap.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.ProjectedCellCap
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! A projected cell and a fixed original major group control all base coordinates. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open Set

noncomputable section

theorem movingBox_pair_gap {time radius : ℝ} {center velocity width : Fin 2 → ℝ}
    {p p' : Fin 3 → ℝ} (hp : p ∈ movingBox time radius center velocity width)
    (hp' : p' ∈ movingBox time radius center velocity width) :
    |p 0 - p' 0| ≤ 2 * radius ∧ ∀ i : Fin 2,
      |(p i.succ - p 0 * velocity i) - (p' i.succ - p' 0 * velocity i)| ≤ 2 * width i := by
  constructor
  · calc
      _ = |(p 0 - time) + -(p' 0 - time)| := by congr 1; ring
      _ ≤ |p 0 - time| + |-(p' 0 - time)| := abs_add_le _ _
      _ ≤ radius + radius := add_le_add hp.1 (by simpa only [abs_neg] using hp'.1)
      _ = _ := by ring
  · intro i
    calc
      _ = |(p i.succ - (center i + p 0 * velocity i)) +
          -(p' i.succ - (center i + p' 0 * velocity i))| := by congr 1; ring
      _ ≤ |p i.succ - (center i + p 0 * velocity i)| +
          |-(p' i.succ - (center i + p' 0 * velocity i))| := abs_add_le _ _
      _ ≤ width i + width i := add_le_add (hp.2 i) (by simpa only [abs_neg] using hp'.2 i)
      _ = _ := by ring

theorem projectedCell_base_gap {sigma g chi K y₀ y₁ z₀ z₁ t t' : ℝ}
    (hs : 0 < sigma) (hg : 0 < g) (hc : 0 ≤ chi) (hK : 0 ≤ K)
    (hy₁ : |y₁| ≤ K) (hz₁ : |z₁| ≤ K)
    (b b' : Fin 6 → ℝ) (q : Fin 2 → ℤ)
    (ht : t ∈ Icc (0 : ℝ) 1) (ht' : t' ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ majorGroup chi z₀ z₁) (hb' : b' ∈ majorGroup chi z₀ z₁)
    (hq : projectedCell sigma g y₀ y₁ b t = q)
    (hq' : projectedCell sigma g y₀ y₁ b' t' = q) :
    |t - t'| ≤ 2 * sigma ∧
      |basePoint b t 1 - basePoint b' t' 1| ≤ 4 * chi + 2 * K * sigma ∧
      |basePoint b t 2 - basePoint b' t' 2| ≤ 2 * g * sigma + 2 * K * sigma := by
  have h := movingBox_pair_gap
    (projectedCell_mem_movingBox hs hg hc b q ht hb hq)
    (projectedCell_mem_movingBox hs hg hc b' q ht' hb' hq')
  have htime : |t - t'| ≤ 2 * sigma := h.1
  refine ⟨htime, ?_, ?_⟩
  · have hmajor : |(basePoint b t 1 - t * z₁) -
        (basePoint b' t' 1 - t' * z₁)| ≤ 4 * chi := by
      have hm := h.2 0
      change |(basePoint b t 1 - t * z₁) - (basePoint b' t' 1 - t' * z₁)| ≤ 2 * (2 * chi) at hm
      linarith
    calc
      _ = |((basePoint b t 1 - t * z₁) - (basePoint b' t' 1 - t' * z₁)) +
          (t - t') * z₁| := by congr 1; ring
      _ ≤ |(basePoint b t 1 - t * z₁) - (basePoint b' t' 1 - t' * z₁)| +
          |t - t'| * |z₁| := by
        simpa only [abs_mul] using
          (abs_add_le ((basePoint b t 1 - t * z₁) - (basePoint b' t' 1 - t' * z₁)) ((t - t') * z₁))
      _ ≤ 4 * chi + (2 * sigma) * K := add_le_add hmajor
        (mul_le_mul htime hz₁ (abs_nonneg _) (by positivity))
      _ = _ := by ring
  · have htrans : |(basePoint b t 2 - t * y₁) -
        (basePoint b' t' 2 - t' * y₁)| ≤ 2 * g * sigma := by
      have hm := h.2 1
      change |(basePoint b t 2 - t * y₁) - (basePoint b' t' 2 - t' * y₁)| ≤ 2 * (g * sigma) at hm
      linarith
    calc
      _ = |((basePoint b t 2 - t * y₁) - (basePoint b' t' 2 - t' * y₁)) +
          (t - t') * y₁| := by congr 1; ring
      _ ≤ |(basePoint b t 2 - t * y₁) - (basePoint b' t' 2 - t' * y₁)| +
          |t - t'| * |y₁| := by
        simpa only [abs_mul] using
          (abs_add_le ((basePoint b t 2 - t * y₁) - (basePoint b' t' 2 - t' * y₁)) ((t - t') * y₁))
      _ ≤ 2 * g * sigma + (2 * sigma) * K := add_le_add htrans
        (mul_le_mul htime hy₁ (abs_nonneg _) (by positivity))
      _ = _ := by ring

def tiltedTransverse (c₃ c₄ : ℝ) (p : Fin 3 → ℝ) : ℝ := p 2 - c₃ * p 0 - c₄ * p 1

theorem tiltedTransverse_gap {K sigma chi g c₃ c₄ : ℝ} {p p' : Fin 3 → ℝ}
    (hK : 1 ≤ K) (hs : 0 ≤ sigma) (hc : 0 ≤ chi) (hg : g ≤ 1)
    (hc₃ : |c₃| ≤ K) (hc₄ : |c₄| ≤ K)
    (ht : |p 0 - p' 0| ≤ 2 * sigma)
    (hz : |p 1 - p' 1| ≤ 4 * chi + 2 * K * sigma)
    (hy : |p 2 - p' 2| ≤ 2 * g * sigma + 2 * K * sigma) :
    |tiltedTransverse c₃ c₄ p - tiltedTransverse c₃ c₄ p'| ≤ 8 * K ^ 2 * (sigma + chi) := by
  have hK0 : 0 ≤ K := (zero_le_one : (0 : ℝ) ≤ 1).trans hK
  have hKsq : K ≤ K ^ 2 := by nlinarith
  have hgK : g ≤ K ^ 2 := hg.trans (hK.trans hKsq)
  calc
    _ = |(p 2 - p' 2) + (-c₃ * (p 0 - p' 0)) + (-c₄ * (p 1 - p' 1))| := by
      unfold tiltedTransverse
      congr 1
      ring
    _ ≤ |p 2 - p' 2| + |-c₃ * (p 0 - p' 0)| + |-c₄ * (p 1 - p' 1)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (2 * g * sigma + 2 * K * sigma) + K * (2 * sigma) +
        K * (4 * chi + 2 * K * sigma) := by
      simp only [abs_mul, abs_neg]
      exact add_le_add (add_le_add hy
        (mul_le_mul hc₃ ht (abs_nonneg _) hK0))
        (mul_le_mul hc₄ hz (abs_nonneg _) hK0)
    _ ≤ (2 * K ^ 2 * sigma + 2 * K ^ 2 * sigma) + K ^ 2 * (2 * sigma) +
        (4 * K ^ 2 * chi + 2 * K ^ 2 * sigma) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hgK) hs,
        mul_nonneg (sub_nonneg.mpr hKsq) hs,
        mul_nonneg (sub_nonneg.mpr hKsq) hc]
    _ ≤ _ := by nlinarith [mul_nonneg (pow_nonneg hK0 2) hc]

end

end Submission.Obl.k4_general_parent_projected_layers
