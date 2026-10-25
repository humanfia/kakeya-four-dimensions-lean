-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceStates
import Submission.Obl.k4_finite_affine_parent_sources.PointStates

/-!
# Joint caps of kept states on base-and-signal cells

With state codes of mesh at most the cell sizes, a cell of side `ε` in base and `ε'` in signal
is covered by the codes of its points, and these codes cover only the `81` neighbouring cells.
The kept part of a cell therefore meets a velocity event `b` in mass at most
`(C / δ) β · 81 · M` once every cell carries mass at most `M`.

Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set

noncomputable section

/-- The cell of base corner `q` (side `ε`) and signal bin `j` (width `ε'`). -/
def bsCell {Ω : Type} (base : Ω → EuclideanSpace ℝ (Fin 3)) (signal : Ω → ℝ) (ε ε' : ℝ)
    (q : Fin 3 → ℤ) (j : ℤ) : Set Ω :=
  {x | (∀ i, ⌊base x i / ε⌋ = q i) ∧ ⌊signal x / ε'⌋ = j}

theorem floor_near {x y ε mesh : ℝ} (hε : 0 < ε) (hm : mesh ≤ ε) (hxy : |x - y| < mesh) :
    ⌊x / ε⌋ - 1 ≤ ⌊y / ε⌋ ∧ ⌊y / ε⌋ ≤ ⌊x / ε⌋ + 1 := by
  have h1 := Int.floor_le (x / ε)
  have h2 := Int.lt_floor_add_one (x / ε)
  rw [abs_lt] at hxy
  have hy1 : (⌊x / ε⌋ - 1 : ℝ) ≤ y / ε := by
    rw [le_div_iff₀ hε]
    have : (⌊x / ε⌋ : ℝ) * ε ≤ x := by rw [← le_div_iff₀ hε]; exact h1
    nlinarith
  have hy2 : y / ε < (⌊x / ε⌋ + 2 : ℝ) := by
    rw [div_lt_iff₀ hε]
    have : x < ((⌊x / ε⌋ : ℝ) + 1) * ε := by rw [← div_lt_iff₀ hε]; exact h2
    nlinarith
  constructor
  · have := Int.floor_mono hy1
    have h3 : ⌊((⌊x / ε⌋ - 1 : ℤ) : ℝ)⌋ = ⌊x / ε⌋ - 1 := Int.floor_intCast _
    push_cast at h3
    omega
  · have := Int.floor_le_floor (le_of_lt hy2)
    have h4 : ⌊y / ε⌋ < ⌊x / ε⌋ + 2 := by
      rw [Int.floor_lt]
      push_cast
      exact hy2
    omega

theorem stateCode_close {Ω : Type} (base : Ω → EuclideanSpace ℝ (Fin 3)) (signal : Ω → ℝ)
    {mesh : ℝ} (hmesh : 0 < mesh) {x y : Ω}
    (h : stateCode base signal mesh x = stateCode base signal mesh y) :
    (∀ i : Fin 3, |base x i - base y i| < mesh) ∧ |signal x - signal y| < mesh := by
  have hc (e : Fin 4) : ⌊stateVector base signal x e / mesh⌋ =
      ⌊stateVector base signal y e / mesh⌋ := congrFun h e
  have hclose (e : Fin 4) : |stateVector base signal x e - stateVector base signal y e| < mesh := by
    have hx1 := Int.floor_le (stateVector base signal x e / mesh)
    have hx2 := Int.lt_floor_add_one (stateVector base signal x e / mesh)
    have hy1 := Int.floor_le (stateVector base signal y e / mesh)
    have hy2 := Int.lt_floor_add_one (stateVector base signal y e / mesh)
    rw [hc e] at hx1 hx2
    rw [abs_lt]
    constructor
    · have h1 : stateVector base signal y e / mesh - stateVector base signal x e / mesh < 1 := by
        linarith
      rw [← sub_div, div_lt_one hmesh] at h1
      linarith
    · have h1 : stateVector base signal x e / mesh - stateVector base signal y e / mesh < 1 := by
        linarith
      rw [← sub_div, div_lt_one hmesh] at h1
      exact h1
  refine ⟨fun i => ?_, ?_⟩
  · have := hclose i.castSucc
    fin_cases i <;> simpa [stateVector] using this
  · simpa [stateVector] using hclose 3

/-- The codes of a cell cover only its neighbouring cells. -/
theorem codes_of_cell_subset {Ω : Type} (base : Ω → EuclideanSpace ℝ (Fin 3))
    (signal : Ω → ℝ) {ε ε' mesh : ℝ} (hε : 0 < ε) (hε' : 0 < ε') (hmesh : 0 < mesh)
    (hm : mesh ≤ ε) (hm' : mesh ≤ ε') (q : Fin 3 → ℤ) (j : ℤ) :
    stateCode base signal mesh ⁻¹' (stateCode base signal mesh '' bsCell base signal ε ε' q j) ⊆
      ⋃ (dq : Fin 3 → Fin 3) (dj : Fin 3),
        bsCell base signal ε ε' (fun i => q i + (dq i : ℤ) - 1) (j + (dj : ℤ) - 1) := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hx
  obtain ⟨hb, hs⟩ := stateCode_close base signal hmesh hxy
  simp only [mem_iUnion, bsCell, mem_ofPred_eq]
  obtain ⟨hyq, hyj⟩ := hy
  have hbase (i : Fin 3) := floor_near hε hm (by rw [abs_sub_comm]; exact hb i)
  have hsig := floor_near hε' hm' (by rw [abs_sub_comm]; exact hs)
  refine ⟨fun i => ⟨(⌊base x i / ε⌋ - q i + 1).toNat, ?_⟩, ⟨(⌊signal x / ε'⌋ - j + 1).toNat, ?_⟩,
    fun i => ?_, ?_⟩
  · have := hbase i; rw [hyq i] at this; omega
  · rw [hyj] at hsig; omega
  · have := hbase i; rw [hyq i] at this
    simp only
    omega
  · rw [hyj] at hsig
    simp only
    omega

/-- **Joint cap of the kept part of a cell.** -/
theorem kept_cell_joint {Ω H : Type} [MeasurableSpace Ω] [Fintype H] [MeasurableSpace H]
    [MeasurableSingletonClass H]
    (lam : Measure Ω) (endL : Ω → H) (hend : Measurable endL)
    (base : Ω → EuclideanSpace ℝ (Fin 3)) (signal : Ω → ℝ) {ε ε' mesh : ℝ}
    (hcode : Measurable (stateCode base signal mesh))
    (w : H → ENNReal) {δ : ENNReal} (hδ0 : δ ≠ 0) (hδt : δ ≠ ⊤)
    {C β : ENNReal} {b : Set Ω} (hb : MeasurableSet b)
    (hnum : ∀ h, lam ({x | endL x = h} ∩ b) ≤ C * w h * β)
    (hε : 0 < ε) (hε' : 0 < ε') (hmesh : 0 < mesh)
    (hm : mesh ≤ ε) (hm' : mesh ≤ ε') (M : ENNReal)
    (hcell : ∀ q j, lam (bsCell base signal ε ε' q j) ≤ M) (q : Fin 3 → ℤ) (j : ℤ) :
    lam (keptSet lam endL (stateCode base signal mesh) w δ ∩
        bsCell base signal ε ε' q j ∩ b) ≤ C / δ * β * (81 * M) := by
  classical
  set V := stateCode base signal mesh '' bsCell base signal ε ε' q j
  have hsub : keptSet lam endL (stateCode base signal mesh) w δ ∩
      bsCell base signal ε ε' q j ∩ b ⊆
      keptSet lam endL (stateCode base signal mesh) w δ ∩ stateCode base signal mesh ⁻¹' V ∩ b :=
    fun x hx => ⟨⟨hx.1.1, x, hx.1.2, rfl⟩, hx.2⟩
  refine (measure_mono hsub).trans ?_
  refine (kept_joint_le hend hcode w hδ0 hδt hb hnum V).trans ?_
  gcongr
  calc lam (stateCode base signal mesh ⁻¹' V)
      ≤ lam (⋃ (dq : Fin 3 → Fin 3) (dj : Fin 3),
          bsCell base signal ε ε' (fun i => q i + (dq i : ℤ) - 1) (j + (dj : ℤ) - 1)) :=
        measure_mono (codes_of_cell_subset base signal hε hε' hmesh hm hm' q j)
    _ ≤ ∑ dq : Fin 3 → Fin 3, ∑ dj : Fin 3,
          lam (bsCell base signal ε ε' (fun i => q i + (dq i : ℤ) - 1) (j + (dj : ℤ) - 1)) :=
        (measure_iUnion_fintype_le _ _).trans
          (Finset.sum_le_sum fun dq _ => measure_iUnion_fintype_le _ _)
    _ ≤ ∑ _dq : Fin 3 → Fin 3, ∑ _dj : Fin 3, M :=
        Finset.sum_le_sum fun dq _ => Finset.sum_le_sum fun dj _ => hcell _ _
    _ = 81 * M := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul]
        norm_num
        ring

end

end Submission.Obl.k4_finite_affine_parent_sources
