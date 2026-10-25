/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file RoundedHereditary.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.ParameterRefinement
import Submission.Obl.k4_scalar_graph_residual_discovery.SpatialCaps

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice

noncomputable section

/-- Hereditary lists on the original preparation mesh control arbitrary
larger fine/coarse widths. Only the coarse rounding ratio enters, with
two possible containing cells per fine coordinate. -/
theorem hereditary_list_at_rounded_widths {X : Type*} {n : ℕ}
    (Z : X → Fin n → ℝ) (E : Set X) {β δ p R A B : ℝ}
    (hβ : 0 < β) (hδ : 0 < δ) (hp : 0 < p) (hR : 0 < R)
    (hβp : β ≤ p) (hA : 0 ≤ A) (hRδ : R ≤ A * δ)
    (F : (Fin n → ℤ) → Finset (Fin n → ℤ))
    (hcard : ∀ q, ((F q).card : ℝ) ≤ B)
    (hmem : ∀ z ∈ E, cell β (Z z) ∈ F (cell δ (Z z))) (q : Fin n → ℤ) :
    ∃ L : Finset (Fin n → ℤ), (L.card : ℝ) ≤ ((2 : ℝ) ^ n * (A + 2) ^ n) * B ∧
      ∀ z ∈ E, cell R (Z z) = q → cell p (Z z) ∈ L := by
  classical
  have hB : 0 ≤ B := (Nat.cast_nonneg (F 0).card).trans (hcard 0)
  let lower (e : Fin n) := (q e : ℝ) * R
  let Q := cubeIndices δ R lower
  have hQcard : (Q.card : ℝ) ≤ (A + 2) ^ n := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (card_cubeIndices hδ hR.le lower)
    have hc : (Q.card : ℝ) ≤ (R / δ + 2) ^ n := by
      simpa only [ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity : 0 ≤ (R / δ + 2) ^ n)] using hh
    exact hc.trans (pow_le_pow_left₀ (by positivity) (by
      have hh := (div_le_iff₀ hδ).mpr hRδ
      linarith) n)
  have hQmem (z : X) (hz : cell R (Z z) = q) : cell δ (Z z) ∈ Q := by
    apply cell_mem_cubeIndices hδ lower (Z z)
    intro e
    have hh := Int.floor_eq_iff.mp (congrFun hz e)
    constructor
    · exact (le_div_iff₀ hR).mp hh.1
    · have hhi := (div_lt_iff₀ hR).mp hh.2
      dsimp only [lower]
      linarith
  let coarse (b : Fin n → ℤ) := coarseGridList p β b
  have hinner (v : Fin n → ℤ) : (((F v).biUnion coarse).card : ℝ) ≤ (2 : ℝ) ^ n * B := by
    calc
      _ ≤ ∑ a ∈ F v, ((coarse a).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le (s := F v) (t := coarse)
      _ = ((F v).card : ℝ) * (2 : ℝ) ^ n := by
        simp only [coarse, card_coarseGridList, Nat.cast_pow, Nat.cast_ofNat,
          Finset.sum_const, nsmul_eq_mul]
      _ ≤ B * (2 : ℝ) ^ n := mul_le_mul_of_nonneg_right (hcard v) (by positivity)
      _ = _ := mul_comm _ _
  let L := Q.biUnion (fun v => (F v).biUnion coarse)
  refine ⟨L, ?_, ?_⟩
  · calc
      (L.card : ℝ) ≤ ∑ v ∈ Q, (((F v).biUnion coarse).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le (s := Q) (t := fun v => (F v).biUnion coarse)
      _ ≤ ∑ _v ∈ Q, (2 : ℝ) ^ n * B := Finset.sum_le_sum (fun v _ => hinner v)
      _ = (Q.card : ℝ) * ((2 : ℝ) ^ n * B) := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (A + 2) ^ n * ((2 : ℝ) ^ n * B) := mul_le_mul_of_nonneg_right hQcard (by positivity)
      _ = _ := by ring
  · intro z hz hq
    exact Finset.mem_biUnion.mpr ⟨cell δ (Z z), hQmem z hq,
      Finset.mem_biUnion.mpr ⟨cell β (Z z), hmem z hz,
        cell_mem_coarseGridList hβ hβp (Z z)⟩⟩

/-- On the exact selected relative grid the mesh loss is H, not the
all-scale interpolation factor Q. Combined with the 64 assigned-cell
factor, the hereditary constant is a fixed polynomial in the original H. -/
theorem rounded_assigned_hereditary_constant {H β δ ρ r R d : ℝ}
    (hH : 1 ≤ H) (hβ : 0 < β) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hr : 0 < r) (hR : 0 < R) (hd : 0 ≤ d) (hd₁ : d ≤ 1)
    (hδle : δ ≤ ρ * R) (hβge : ρ * r ≤ H * β) :
    ((2 : ℝ) ^ 3 * (H + 2) ^ 3) * (64 * H * (δ / β) ^ (2 + d)) ≤
      13824 * H ^ 7 * (R / r) ^ (2 + d) := by
  have hH₀ : 0 < H := by linarith
  have hratio : δ / β ≤ H * (R / r) := by
    apply (div_le_iff₀ hβ).mpr
    have hh := mul_le_mul_of_nonneg_right hβge (div_nonneg hR.le hr.le)
    have heq : (ρ * r) * (R / r) = ρ * R := by field_simp
    rw [heq] at hh
    exact hδle.trans (by nlinarith only [hh])
  have hpower : (δ / β) ^ (2 + d) ≤ H ^ 3 * (R / r) ^ (2 + d) := by
    calc
      _ ≤ (H * (R / r)) ^ (2 + d) := Real.rpow_le_rpow (by positivity) hratio (by linarith)
      _ = H ^ (2 + d) * (R / r) ^ (2 + d) := Real.mul_rpow hH₀.le (by positivity)
      _ ≤ H ^ (3 : ℝ) * (R / r) ^ (2 + d) := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hH (by linarith)) (by positivity)
      _ = _ := by norm_num
  have hcoarse : (H + 2) ^ 3 ≤ 27 * H ^ 3 := by nlinarith [sq_nonneg (H - 1)]
  calc
    _ ≤ ((2 : ℝ) ^ 3 * (27 * H ^ 3)) * (64 * H * (H ^ 3 * (R / r) ^ (2 + d))) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcoarse (by norm_num))
        (mul_le_mul_of_nonneg_left hpower (by positivity)) (by positivity) (by positivity)
    _ = _ := by ring

end

end Submission.Obl.k4_scalar_graph_residual_discovery
