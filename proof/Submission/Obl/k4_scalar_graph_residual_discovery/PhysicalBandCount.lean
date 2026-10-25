/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file PhysicalBandCount.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.NormalCellLists
import Submission.Obl.k4_scalar_graph_residual_discovery.StripCount

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice

noncomputable section

theorem fine_cell_cover_in_normal_band {X : Type*} (Z : X → Fin 3 → ℝ) (E : Set X)
    (row : Fin 2 → ℝ) {p r ρ A W B : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r ≤ ρ)
    (hW : 0 ≤ W) (hA : W + |row 0| + |row 1| ≤ A)
    (q : Fin 3 → ℤ) (a : ℝ)
    (hEcell : ∀ z ∈ E, cell ρ (Z z) = q)
    (hEband : ∀ z ∈ E, normalCoordinate row (Z z) ∈ Icc a (a + W * r))
    (F : (Fin 3 → ℤ) → Finset (Fin 3 → ℤ))
    (hcard : ∀ v, ((F v).card : ℝ) ≤ B)
    (hmem : ∀ z ∈ E, cell p (Z z) ∈ F (cell r (Z z))) :
    ∃ L : Finset (Fin 3 → ℤ), (L.card : ℝ) ≤ 18 * (A + 1) * (ρ / r) ^ 2 * B ∧
      ∀ z ∈ E, cell p (Z z) ∈ L := by
  classical
  obtain ⟨Q, hQcard, hQmem⟩ := normal_band_cell_cover_quadratic row hr hρ hrρ hW hA q a
  let L := Q.biUnion F
  have hB : 0 ≤ B := (Nat.cast_nonneg (F 0).card).trans (hcard 0)
  refine ⟨L, ?_, ?_⟩
  · calc
      (L.card : ℝ) ≤ ∑ v ∈ Q, ((F v).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le (s := Q) (t := F)
      _ ≤ ∑ _v ∈ Q, B := Finset.sum_le_sum (fun v _ => hcard v)
      _ = (Q.card : ℝ) * B := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hQcard hB
  · intro z hz
    exact Finset.mem_biUnion.mpr ⟨cell r (Z z), hQmem (Z z) (hEcell z hz) (hEband z hz), hmem z hz⟩

def normalStripPhysicalCells {X : Type*} (Z : X → Fin 3 → ℝ) (E : Set X)
    (row : Fin 2 → ℝ) (p : ℝ) (j : ℤ) : Set (Fin 3 → ℤ) :=
  {c | ∃ z ∈ E, cell p (Z z) = c ∧ ⌊normalCoordinate row (Z z) / p⌋ = j}

/-- The concrete normal geometry and hereditary support counts provide
the overlap and support inputs to the scalar strip-counting kernel. -/
theorem scalar_strip_count_from_normal_band {X : Type*}
    (Z : X → Fin 3 → ℝ) (E : Set X) (row : Fin 2 → ℝ)
    {p r ρ A W B K d : ℝ} (hp : 0 < p) (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r ≤ ρ)
    (hK : 0 < K) (hW : 1 ≤ W) (hA : W + |row 0| + |row 1| ≤ A)
    (q : Fin 3 → ℤ) (a : ℝ)
    (hEcell : ∀ z ∈ E, cell ρ (Z z) = q)
    (hEband : ∀ z ∈ E, normalCoordinate row (Z z) ∈ Icc a (a + W * r))
    (F : (Fin 3 → ℤ) → Finset (Fin 3 → ℤ))
    (hcard : ∀ v, ((F v).card : ℝ) ≤ B)
    (hmem : ∀ z ∈ E, cell p (Z z) ∈ F (cell r (Z z)))
    (hbudget : 18 * (A + 1) * B ≤ K * (r / p) ^ ((2 : ℝ) + d))
    (hoverlap : 2 * A + 2 ≤ K) (strips : Finset ℤ)
    (hfill : ∀ j ∈ strips, (ρ / p) ^ 2 / K ≤
      ((normalStripPhysicalCells Z E row p j).ncard : ℝ)) :
    (strips.card : ℝ) ≤ K ^ 3 * (r / p) ^ d := by
  classical
  obtain ⟨L, hLcard, hLmem⟩ := fine_cell_cover_in_normal_band Z E row hr hρ hrρ
    (by linarith : 0 ≤ W) hA q a hEcell hEband F hcard hmem
  let meets : ℤ → (Fin 3 → ℤ) → Prop := fun j c => c ∈ normalStripPhysicalCells Z E row p j
  have hA' : 1 + |row 0| + |row 1| ≤ A := by linarith
  apply scalar_strip_count strips L meets hK hp hr hρ
  · intro j hj
    have heq : (Finset.bipartiteAbove meets L j : Set (Fin 3 → ℤ)) =
        normalStripPhysicalCells Z E row p j := by
      ext c
      constructor
      · intro hc
        exact ((Finset.mem_bipartiteAbove meets).mp hc).2
      · rintro hc
        obtain ⟨z, hz, hzc, hzj⟩ := hc
        exact (Finset.mem_bipartiteAbove meets).mpr
          ⟨by simpa only [hzc] using hLmem z hz, ⟨z, hz, hzc, hzj⟩⟩
    have hncard := congrArg Set.ncard heq
    simp only [Set.ncard_coe_finset] at hncard
    simpa only [hncard] using hfill j hj
  · intro c _
    obtain ⟨J, hJcard, hJmem⟩ := normal_bin_list_in_cell row hp hA' c
    have hsub : Finset.bipartiteBelow meets strips c ⊆ J := by
      intro j hj
      obtain ⟨z, hz, hzc, hzj⟩ := ((Finset.mem_bipartiteBelow meets).mp hj).2
      simpa only [hzj] using hJmem (Z z) hzc
    have hc : ((Finset.bipartiteBelow meets strips c).card : ℝ) ≤ (J.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact hc.trans (hJcard.trans hoverlap)
  · have h := mul_le_mul_of_nonneg_right hbudget (sq_nonneg (ρ / r))
    exact hLcard.trans (by nlinarith only [h])

end

end Submission.Obl.k4_scalar_graph_residual_discovery
