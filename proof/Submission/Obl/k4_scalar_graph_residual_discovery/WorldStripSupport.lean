/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file WorldStripSupport.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.PhysicalBandCount
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldSpatialCells
import Submission.Obl.k4_scalar_graph_residual_discovery.ScalarSupportLists

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory Metric
open Submission.Lib.K4CommonLocalChoice

noncomputable section

def assignedPosition (b : ℝ) (z : ScalarIncidence) : Fin 3 → ℝ :=
  leftCorner b (cell b (scalarPosition z))

def assignedCell (ρ b : ℝ) (z : ScalarIncidence) : Fin 3 → ℤ :=
  cell ρ (assignedPosition b z)

def assignedNormalBin (ρ b r : ℝ) (row : Fin 2 → ℝ) (z : ScalarIncidence) : ℤ :=
  ⌊normalCoordinate row (assignedPosition b z) / (ρ * r)⌋

/-- Whole GLOBAL strip filling and hereditary physical support give the
local scalar cover in any later coefficient world. Filling retains points
from every coefficient world; only the scalar witnesses use `E`. -/
theorem scalar_local_cover_of_global_strip_filling
    {ρ b r R δ A B K d t a : ℝ} (hρ : 0 < ρ) (hb : 0 < b) (hbρ : b ≤ ρ)
    (hr : 0 < r) (hrR : r ≤ R) (hR₁ : R ≤ 1) (hK : 0 < K) (ht : |t| ≤ 1)
    (q : Fin 5 → ℤ) (E Eall : Set ScalarIncidence) (hsub : E ⊆ Eall) (F : ℝ → ℝ)
    (row : (Fin 3 → ℤ) → Fin 2 → ℝ)
    (hworld : ∀ z ∈ E, cell ρ z.1.2 = q)
    (hfinite : ((fun z => cell b (scalarPosition z)) '' E).Finite)
    (hrow : ∀ z ∈ E, |row (assignedCell ρ b z) 1 - F z.2| ≤ δ)
    (hprecision : ∀ v, 2 * δ + (1 + |row v 0| + |row v 1|) * b / ρ ≤ r)
    (hA : ∀ v, 5 + |row v 0| + |row v 1| ≤ A)
    (hereditary : (Fin 3 → ℤ) → Finset (Fin 3 → ℤ))
    (hcount : ∀ v, ((hereditary v).card : ℝ) ≤ B)
    (hmem : ∀ z ∈ Eall, cell (ρ * r) (assignedPosition b z) ∈
      hereditary (cell (ρ * R) (assignedPosition b z)))
    (hbudget : 18 * (A + 1) * B ≤ K * (R / r) ^ ((2 : ℝ) + d))
    (hoverlap : 2 * A + 2 ≤ K)
    (hfill : ∀ v j, (∃ z ∈ Eall, assignedCell ρ b z = v ∧ assignedNormalBin ρ b r (row v) z = j) →
      (ρ / (ρ * r)) ^ 2 / K ≤
        ((normalStripPhysicalCells (assignedPosition b) {z ∈ Eall | assignedCell ρ b z = v}
          (row v) (ρ * r) j).ncard : ℝ)) :
    ∃ (m : ℕ) (c : Fin m → ℝ),
      {s | ∃ l : ScalarLine, (l, t) ∈ E ∧ Zoom.scalar ρ q F l t = s} ∩ Icc a (a + R) ⊆
        ⋃ j, closedBall (c j) r ∧
      (m : ℝ) ≤ 10648 * K ^ 3 * (R / r) ^ d := by
  classical
  let S : ScalarIncidence → ℝ := fun z => Zoom.scalar ρ q F z.1 z.2
  let localE := {z : ScalarIncidence | z ∈ E ∧ z.2 = t ∧ S z ∈ Icc a (a + R)}
  let shift (v : Fin 3 → ℤ) := normalCoordinate (row v) (scalarPosition (Zoom.center ρ q, t)) / ρ
  have hnear (z : ScalarIncidence) (hz : z ∈ localE) :
      |S z - (normalCoordinate (row (assignedCell ρ b z)) (assignedPosition b z) / ρ -
        shift (assignedCell ρ b z))| ≤ r := by
    have hh := (Zoom.scalar_near_assigned_normal hρ hb q (row (assignedCell ρ b z)) F
      z.1 z.2 (hworld z hz.1) (by simpa only [hz.2.1] using ht) (hrow z hz.1)).trans
        (hprecision (assignedCell ρ b z))
    simpa only [S, assignedPosition, shift, sub_div, scalarPosition, hz.2.1] using hh
  let J (v : Fin 3 → ℤ) : Set ℤ :=
    {j | ∃ z ∈ localE, assignedCell ρ b z = v ∧ assignedNormalBin ρ b r (row v) z = j}
  have hJ (v : Fin 3 → ℤ) : (J v).Finite := by
    apply (hfinite.image (fun w => ⌊normalCoordinate (row v) (leftCorner b w) / (ρ * r)⌋)).subset
    rintro j ⟨z, hz, _, hj⟩
    exact ⟨cell b (scalarPosition z), ⟨z, hz.1, rfl⟩, hj⟩
  let strips (v : Fin 3 → ℤ) := (hJ v).toFinset
  let bandE (v : Fin 3 → ℤ) :=
    {z : ScalarIncidence | z ∈ Eall ∧ assignedCell ρ b z = v ∧
      assignedNormalBin ρ b r (row v) z ∈ strips v}
  have hband (v : Fin 3 → ℤ) (z : ScalarIncidence) (hz : z ∈ bandE v) :
      normalCoordinate (row v) (assignedPosition b z) ∈
        Icc (ρ * (a + shift v - 2 * r)) (ρ * (a + shift v - 2 * r) + 5 * (ρ * R)) := by
    obtain ⟨z₀, hz₀, hv₀, hj₀⟩ := (hJ v).mem_toFinset.mp hz.2.2
    have hn := hnear z₀ hz₀
    rw [hv₀] at hn
    have hh := whole_strip_band_of_scalar_witness hρ hr hrR hz₀.2.2 hj₀ hn
    simpa only [mul_assoc] using hh
  have hR : 0 < R := hr.trans_le hrR
  have hratio : (ρ * R) / (ρ * r) = R / r := by field_simp
  have hstripcount (v : Fin 3 → ℤ) : ((strips v).card : ℝ) ≤ K ^ 3 * (R / r) ^ d := by
    have hfilled (j : ℤ) (hj : j ∈ strips v) :
        (ρ / (ρ * r)) ^ 2 / K ≤
          ((normalStripPhysicalCells (assignedPosition b) (bandE v) (row v) (ρ * r) j).ncard : ℝ) := by
      have heq : normalStripPhysicalCells (assignedPosition b) (bandE v) (row v) (ρ * r) j =
          normalStripPhysicalCells (assignedPosition b) {z ∈ Eall | assignedCell ρ b z = v}
            (row v) (ρ * r) j := by
        ext w
        constructor
        · rintro ⟨z, hz, hzw, hzj⟩
          exact ⟨z, ⟨hz.1, hz.2.1⟩, hzw, hzj⟩
        · rintro ⟨z, hz, hzw, hzj⟩
          refine ⟨z, ⟨hz.1, hz.2, ?_⟩, hzw, hzj⟩
          change (⌊normalCoordinate (row v) (assignedPosition b z) / (ρ * r)⌋ : ℤ) ∈ strips v
          rw [hzj]
          exact hj
      rw [heq]
      obtain ⟨z₀, hz₀, hv₀, hj₀⟩ := (hJ v).mem_toFinset.mp hj
      exact hfill v j ⟨z₀, hsub hz₀.1, hv₀, hj₀⟩
    have hbudget' : 18 * (A + 1) * B ≤ K * ((ρ * R) / (ρ * r)) ^ ((2 : ℝ) + d) := by
      rw [hratio]
      exact hbudget
    have hh := scalar_strip_count_from_normal_band (assignedPosition b) (bandE v) (row v)
      (mul_pos hρ hr) (mul_pos hρ hR) hρ
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hR₁ hρ.le)
      hK (by norm_num : (1 : ℝ) ≤ 5) (hA v) v (ρ * (a + shift v - 2 * r))
      (fun _ hz => hz.2.1) (hband v) hereditary hcount (fun z hz => hmem z hz.1)
      hbudget' hoverlap (strips v) hfilled
    simpa only [hratio] using hh
  obtain ⟨cells, hcellcount, hcellmem⟩ := Zoom.world_assigned_coarse_cell_list hρ hb hbρ q ht
  have hlocalcells (z : ScalarIncidence) (hz : z ∈ localE) : assignedCell ρ b z ∈ cells := by
    change cell ρ (leftCorner b (cell b (scalarPosition (z.1, z.2)))) ∈ cells
    rw [hz.2.1]
    exact hcellmem z.1 (hworld z hz.1)
  obtain ⟨L, hLcount, hLmem⟩ := scalar_support_bins_of_cell_strip_lists localE S
    (assignedCell ρ b) (fun v z => normalCoordinate (row v) (assignedPosition b z)) shift
    hr cells hlocalcells hnear strips (fun v _ => hstripcount v)
    (fun z hz => (hJ _).mem_toFinset.mpr ⟨z, hz, rfl, rfl⟩)
  have hscalarList : ∀ s ∈ {s | ∃ l : ScalarLine, (l, t) ∈ E ∧ Zoom.scalar ρ q F l t = s} ∩
      Icc a (a + R), ⌊s / r⌋ ∈ L := by
    rintro s ⟨⟨l, hl, hls⟩, hs⟩
    have hh := hLmem (l, t) ⟨hl, rfl, by simpa only [S, hls] using hs⟩
    simpa only [S, hls] using hh
  obtain ⟨m, c, hcover, hm⟩ := scalar_cover_of_bin_list hr L hscalarList
  refine ⟨m, c, hcover, ?_⟩
  rw [hm]
  have hnonneg : 0 ≤ 8 * (K ^ 3 * (R / r) ^ d) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcellcount hnonneg
  exact hLcount.trans (by nlinarith only [hmul])

/-- The same-set specialization, retained for direct applications where
the filling law already lies in the coefficient world. -/
theorem scalar_local_cover_of_strip_filling
    {ρ b r R δ A B K d t a : ℝ} (hρ : 0 < ρ) (hb : 0 < b) (hbρ : b ≤ ρ)
    (hr : 0 < r) (hrR : r ≤ R) (hR₁ : R ≤ 1) (hK : 0 < K) (ht : |t| ≤ 1)
    (q : Fin 5 → ℤ) (E : Set ScalarIncidence) (F : ℝ → ℝ)
    (row : (Fin 3 → ℤ) → Fin 2 → ℝ)
    (hworld : ∀ z ∈ E, cell ρ z.1.2 = q)
    (hfinite : ((fun z => cell b (scalarPosition z)) '' E).Finite)
    (hrow : ∀ z ∈ E, |row (assignedCell ρ b z) 1 - F z.2| ≤ δ)
    (hprecision : ∀ v, 2 * δ + (1 + |row v 0| + |row v 1|) * b / ρ ≤ r)
    (hA : ∀ v, 5 + |row v 0| + |row v 1| ≤ A)
    (hereditary : (Fin 3 → ℤ) → Finset (Fin 3 → ℤ))
    (hcount : ∀ v, ((hereditary v).card : ℝ) ≤ B)
    (hmem : ∀ z ∈ E, cell (ρ * r) (assignedPosition b z) ∈
      hereditary (cell (ρ * R) (assignedPosition b z)))
    (hbudget : 18 * (A + 1) * B ≤ K * (R / r) ^ ((2 : ℝ) + d))
    (hoverlap : 2 * A + 2 ≤ K)
    (hfill : ∀ v j, (∃ z ∈ E, assignedCell ρ b z = v ∧ assignedNormalBin ρ b r (row v) z = j) →
      (ρ / (ρ * r)) ^ 2 / K ≤
        ((normalStripPhysicalCells (assignedPosition b) {z ∈ E | assignedCell ρ b z = v}
          (row v) (ρ * r) j).ncard : ℝ)) :
    ∃ (m : ℕ) (c : Fin m → ℝ),
      {s | ∃ l : ScalarLine, (l, t) ∈ E ∧ Zoom.scalar ρ q F l t = s} ∩ Icc a (a + R) ⊆
        ⋃ j, closedBall (c j) r ∧
      (m : ℝ) ≤ 10648 * K ^ 3 * (R / r) ^ d :=
  scalar_local_cover_of_global_strip_filling hρ hb hbρ hr hrR hR₁ hK ht q E E
    subset_rfl F row hworld hfinite hrow hprecision hA hereditary hcount hmem hbudget hoverlap hfill

end

end Submission.Obl.k4_scalar_graph_residual_discovery
