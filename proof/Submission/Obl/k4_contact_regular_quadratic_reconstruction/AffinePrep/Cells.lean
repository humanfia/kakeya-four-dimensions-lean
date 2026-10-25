import Mathlib
import Submission.Lib.K4QuadraticSheetCore

/-!
# Fine cells of the normalized unit cube

Cells of side `h` indexed by their floor codes, their volume, the volume of a finite union, the
`ℓ¹` diameter of a cell, and the count of the cells meeting the unit cube.
-/

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep

open MeasureTheory Set

noncomputable section

/-- The cell with floor code `q` in the mesh of side `h`. -/
def cellBox (h : ℝ) (q : Fin 3 → ℤ) : Set (Fin 3 → ℝ) := {z | ∀ i, ⌊z i / h⌋ = q i}

/-- The floor code of a point. -/
def cellCode (h : ℝ) (z : Fin 3 → ℝ) : Fin 3 → ℤ := fun i => ⌊z i / h⌋

theorem mem_cellBox_cellCode (h : ℝ) (z : Fin 3 → ℝ) : z ∈ cellBox h (cellCode h z) :=
  fun _ => rfl

theorem cellBox_eq_pi {h : ℝ} (hh : 0 < h) (q : Fin 3 → ℤ) :
    cellBox h q = Set.pi univ (fun i => Ico ((q i : ℝ) * h) (((q i : ℝ) + 1) * h)) := by
  ext z
  simp only [cellBox, mem_ofPred_eq, Set.mem_pi, mem_univ, true_implies, mem_Ico]
  refine forall_congr' fun i => ?_
  rw [Int.floor_eq_iff, le_div_iff₀ hh, div_lt_iff₀ hh]

theorem measurableSet_cellBox {h : ℝ} (hh : 0 < h) (q : Fin 3 → ℤ) :
    MeasurableSet (cellBox h q) := by
  rw [cellBox_eq_pi hh]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem volume_cellBox {h : ℝ} (hh : 0 < h) (q : Fin 3 → ℤ) :
    volume (cellBox h q) = ENNReal.ofReal (h ^ 3) := by
  rw [cellBox_eq_pi hh, Real.volume_pi_Ico, Fin.prod_univ_three]
  have e : ∀ i : Fin 3, ((q i : ℝ) + 1) * h - (q i : ℝ) * h = h := fun i => by ring
  rw [e 0, e 1, e 2, ← ENNReal.ofReal_mul hh.le, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem cellBox_disjoint {h : ℝ} {q q' : Fin 3 → ℤ} (hq : q ≠ q') :
    Disjoint (cellBox h q) (cellBox h q') := by
  rw [Set.disjoint_left]
  intro z hz hz'
  exact hq (funext fun i => (hz i).symm.trans (hz' i))

theorem volume_biUnion_cellBox {h : ℝ} (hh : 0 < h) (S : Finset (Fin 3 → ℤ)) :
    volume (⋃ q ∈ S, cellBox h q) = S.card * ENNReal.ofReal (h ^ 3) := by
  rw [measure_biUnion_finset]
  · simp only [volume_cellBox hh, Finset.sum_const, nsmul_eq_mul]
  · intro q _ q' _ hqq'
    exact cellBox_disjoint hqq'
  · intro q _
    exact measurableSet_cellBox hh q

theorem abs_sub_lt_of_mem_cellBox {h : ℝ} (hh : 0 < h) {q : Fin 3 → ℤ} {x y : Fin 3 → ℝ}
    (hx : x ∈ cellBox h q) (hy : y ∈ cellBox h q) (i : Fin 3) : |x i - y i| < h := by
  rw [cellBox_eq_pi hh] at hx hy
  have hxi := hx i (mem_univ i)
  have hyi := hy i (mem_univ i)
  rw [abs_lt]
  constructor <;> nlinarith [hxi.1, hxi.2, hyi.1, hyi.2]

theorem l1dist_le_of_mem_cellBox {h : ℝ} (hh : 0 < h) {q : Fin 3 → ℤ} {x y : Fin 3 → ℝ}
    (hx : x ∈ cellBox h q) (hy : y ∈ cellBox h q) :
    Submission.Lib.K4QuadraticSheetCore.l1dist x y ≤ 3 * h := by
  unfold Submission.Lib.K4QuadraticSheetCore.l1dist
  have h0 := abs_sub_lt_of_mem_cellBox hh hx hy 0
  have h1 := abs_sub_lt_of_mem_cellBox hh hx hy 1
  have h2 := abs_sub_lt_of_mem_cellBox hh hx hy 2
  linarith

/-- A cell containing a point at distance at least `h` from the boundary lies in the cube. -/
theorem cellBox_subset_cube {h : ℝ} (hh : 0 < h) {q : Fin 3 → ℤ} {x : Fin 3 → ℝ}
    (hx : x ∈ cellBox h q) (hlo : ∀ i, h ≤ x i) (hhi : ∀ i, x i ≤ 1 - h) :
    cellBox h q ⊆ Icc (0 : Fin 3 → ℝ) 1 := by
  intro y hy
  constructor
  · intro i
    have := abs_sub_lt_of_mem_cellBox hh hx hy i
    have := hlo i
    simp only [Pi.zero_apply]
    rw [abs_lt] at *
    linarith
  · intro i
    have := abs_sub_lt_of_mem_cellBox hh hx hy i
    have := hhi i
    simp only [Pi.one_apply]
    rw [abs_lt] at *
    linarith

/-- The codes of the points of the unit cube. -/
def cubeCodes (h : ℝ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (0 : ℤ) ⌊1 / h⌋

theorem cellCode_mem_cubeCodes {h : ℝ} (hh : 0 < h) {z : Fin 3 → ℝ}
    (hz : z ∈ Icc (0 : Fin 3 → ℝ) 1) : cellCode h z ∈ cubeCodes h := by
  rw [cubeCodes, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have h0 : 0 ≤ z i := hz.1 i
  have h1 : z i ≤ 1 := hz.2 i
  constructor
  · exact Int.floor_nonneg.mpr (div_nonneg h0 hh.le)
  · exact Int.floor_le_floor (div_le_div_of_nonneg_right h1 hh.le)

theorem card_cubeCodes {h : ℝ} (hh : 0 < h) :
    ((cubeCodes h).card : ℝ) ≤ (1 / h + 1) ^ 3 := by
  rw [cubeCodes, Fintype.card_piFinset, Fin.prod_univ_three]
  have hc : ((Finset.Icc (0 : ℤ) ⌊1 / h⌋).card : ℝ) ≤ 1 / h + 1 := by
    rw [Int.card_Icc]
    have hf : (0 : ℤ) ≤ ⌊1 / h⌋ + 1 - 0 := by
      have := Int.floor_nonneg.mpr (show (0 : ℝ) ≤ 1 / h by positivity)
      omega
    have hcast : (((⌊1 / h⌋ + 1 - 0).toNat : ℕ) : ℝ) = ((⌊1 / h⌋ + 1 - 0 : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hf
    rw [hcast]
    push_cast
    linarith [Int.floor_le (1 / h)]
  have hc0 : (0 : ℝ) ≤ ((Finset.Icc (0 : ℤ) ⌊1 / h⌋).card : ℝ) := by positivity
  push_cast
  calc _ ≤ (1 / h + 1) * (1 / h + 1) * (1 / h + 1) := by gcongr
    _ = _ := by ring

/-- Mass of a set split into finitely many coded pieces. -/
theorem measure_le_card_mul_of_codes {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (ρ : Measure Ω) (G : Set Ω) (code : Ω → ι) (S : Finset ι) (hS : ∀ p ∈ G, code p ∈ S)
    (cm : ENNReal) (hcm : ∀ q ∈ S, ρ {p | p ∈ G ∧ code p = q} ≤ cm) :
    ρ G ≤ S.card * cm := by
  have hsub : G ⊆ ⋃ q ∈ S, {p | p ∈ G ∧ code p = q} := by
    intro p hp
    exact mem_iUnion₂.mpr ⟨code p, hS p hp, hp, rfl⟩
  calc ρ G ≤ ρ (⋃ q ∈ S, {p | p ∈ G ∧ code p = q}) := measure_mono hsub
    _ ≤ ∑ q ∈ S, ρ {p | p ∈ G ∧ code p = q} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ S, cm := Finset.sum_le_sum hcm
    _ = S.card * cm := by simp

/-- An interval of length one bin meets at most two bins. -/
theorem floor_mem_pair {η w c : ℝ} (hη : 0 < η) (hw : |w - c| ≤ η / 2) :
    ⌊w / η⌋ = ⌊(c - η / 2) / η⌋ ∨ ⌊w / η⌋ = ⌊(c - η / 2) / η⌋ + 1 := by
  have h1 : (c - η / 2) / η ≤ w / η := by
    apply div_le_div_of_nonneg_right _ hη.le
    linarith [(abs_le.mp hw).1]
  have h2 : w / η ≤ (c - η / 2) / η + 1 := by
    rw [div_add_one hη.ne', div_le_div_iff_of_pos_right hη]
    linarith [(abs_le.mp hw).2]
  have hlo := Int.floor_le_floor h1
  have hhi : ⌊w / η⌋ ≤ ⌊(c - η / 2) / η⌋ + 1 := by
    have := Int.floor_le_floor h2
    rwa [Int.floor_add_one] at this
  omega

end

end Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep
