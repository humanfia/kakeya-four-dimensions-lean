import Mathlib
import Submission.Lib.K4ProjectedGroups.BandCover

/-!
# Caps of a projected group

A projected group (paper Section 8.2) fixes the bins of the major velocity `b 3` and the
major intercept `b 0` at width `χ`, and the bins of the transverse intercept `b 1` and the
transverse velocity `b 4` at width `g`. In the normalized transverse coordinate
`(Y - (y₀ + t y₁) g) / g` a scalar mesh cell of side `σ` is a moving band of the base.
`group_cap` bounds its mass, in one signal bin, by the joint cap of the frozen model at a
finer cell side `h`, times the number of cells meeting the band.

Adapted from: here:o200 (session x0701, Submission/Obl/k4_finite_projected_horizontal_candidates/GroupCaps.lean).
-/

namespace Submission.Lib.K4ProjectedGroups

open MeasureTheory Set
open scoped Classical ENNReal

noncomputable section

/-- The base point `(t, Z, Y)` of an incidence of the line `b` at time `t`. -/
def basePt (b : Fin 6 → ℝ) (t : ℝ) : Fin 3 → ℝ := ![t, b 0 + t * b 3, b 1 + t * b 4]

/-- Membership of a line in the group with key `(v₀, z₀, y₀, y₁)`. -/
def InGroup (χ g : ℝ) (key : Fin 4 → ℤ) (b : Fin 6 → ℝ) : Prop :=
  ⌊b 3 / χ⌋ = key 0 ∧ ⌊b 0 / χ⌋ = key 1 ∧ ⌊b 1 / g⌋ = key 2 ∧ ⌊b 4 / g⌋ = key 3

/-- The normalized transverse coordinate of a line in the group with key `key`. -/
def groupY (g : ℝ) (key : Fin 4 → ℤ) (b : Fin 6 → ℝ) (t : ℝ) : ℝ :=
  (b 1 - key 2 * g) / g + t * ((b 4 - key 3 * g) / g)

theorem floor_bounds {x w : ℝ} {k : ℤ} (hw : 0 < w) (h : ⌊x / w⌋ = k) :
    k * w ≤ x ∧ x ≤ k * w + w := by
  have h1 := Int.floor_le (x / w)
  have h2 := Int.lt_floor_add_one (x / w)
  rw [h] at h1 h2
  constructor
  · rwa [le_div_iff₀ hw] at h1
  · have := (div_lt_iff₀ hw).mp h2
    linarith

/-- An incidence of a group line in a scalar cell lies in a moving band of the base. -/
theorem group_band {χ g σ : ℝ} (hχ : 0 < χ) (hg : 0 < g) (hσ : 0 < σ)
    {key : Fin 4 → ℤ} {b : Fin 6 → ℝ} (hb : InGroup χ g key b) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) {q : Fin 2 → ℤ}
    (hq0 : ⌊t / σ⌋ = q 0) (hq1 : ⌊groupY g key b t / σ⌋ = q 1) :
    (q 0 : ℝ) * σ ≤ basePt b t 0 ∧ basePt b t 0 ≤ (q 0 : ℝ) * σ + σ ∧
      (key 1 : ℝ) * χ + ((key 0 : ℝ) * χ) * basePt b t 0 ≤ basePt b t 1 ∧
      basePt b t 1 ≤ (key 1 : ℝ) * χ + ((key 0 : ℝ) * χ) * basePt b t 0 + 2 * χ ∧
      ((key 2 : ℝ) * g + (q 1 : ℝ) * σ * g) + ((key 3 : ℝ) * g) * basePt b t 0 ≤ basePt b t 2 ∧
      basePt b t 2 ≤ ((key 2 : ℝ) * g + (q 1 : ℝ) * σ * g) + ((key 3 : ℝ) * g) * basePt b t 0 +
        σ * g := by
  obtain ⟨hv, hz, hy0, hy1⟩ := hb
  have ⟨t1, t2⟩ := floor_bounds hσ hq0
  have ⟨v1, v2⟩ := floor_bounds hχ hv
  have ⟨z1, z2⟩ := floor_bounds hχ hz
  have ⟨y1, y2⟩ := floor_bounds hσ hq1
  have ht0 := ht.1
  have ht1 := ht.2
  simp only [basePt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨t1, t2, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · have : (q 1 : ℝ) * σ * g ≤ groupY g key b t * g := by nlinarith
    simp only [groupY] at this
    field_simp at this
    nlinarith
  · have : groupY g key b t * g ≤ (q 1 : ℝ) * σ * g + σ * g := by nlinarith
    simp only [groupY] at this
    field_simp at this
    nlinarith

/-- The number of cap cells of side `h` meeting a scalar cell of a group. -/
def groupCellCount (χ g σ h : ℝ) (key : Fin 4 → ℤ) : ℝ :=
  (2 * (σ / h + 1) + 2) * ((2 * ((2 * χ + |(key 0 : ℝ) * χ| * h) / h + 1) + 2) *
    (2 * ((σ * g + |(key 3 : ℝ) * g| * h) / h + 1) + 2))

/-- The mass of a group in a scalar cell and a signal bin, from cell caps of side `h` in the
same signal bin and the group's velocity bin. -/
theorem group_cap {α : Type*} [MeasurableSpace α] (μ : Measure (α × ℝ))
    (b : α → Fin 6 → ℝ) (sig : α × ℝ → ℝ)
    {χ g σ h sw : ℝ} (hχ : 0 < χ) (hg : 0 < g) (hσ : 0 < σ) (hh : 0 < h)
    (key : Fin 4 → ℤ) (a : ℤ) (c₀ : ℝ≥0∞)
    (hcap : ∀ q : Fin 3 → ℤ, μ {p | cellCode h (basePt (b p.1) p.2) = q ∧
      ⌊sig p / sw⌋ = a ∧ ⌊b p.1 3 / χ⌋ = key 0} ≤ c₀)
    (hsupp : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0) (q : Fin 2 → ℤ) :
    μ {p | InGroup χ g key (b p.1) ∧ ⌊p.2 / σ⌋ = q 0 ∧
        ⌊groupY g key (b p.1) p.2 / σ⌋ = q 1 ∧ ⌊sig p / sw⌋ = a} ≤
      ENNReal.ofReal (groupCellCount χ g σ h key) * c₀ := by
  set E0 := {p : α × ℝ | InGroup χ g key (b p.1) ∧ ⌊p.2 / σ⌋ = q 0 ∧
        ⌊groupY g key (b p.1) p.2 / σ⌋ = q 1 ∧ ⌊sig p / sw⌋ = a} with hE0
  set E := E0 ∩ (univ ×ˢ Icc (0 : ℝ) 1) with hE
  have hsplit : μ E0 ≤ μ E := by
    have : E0 ⊆ E ∪ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ := by
      intro p hp
      by_cases hp' : p ∈ univ ×ˢ Icc (0 : ℝ) 1
      · exact Or.inl ⟨hp, hp'⟩
      · exact Or.inr hp'
    calc μ E0 ≤ μ (E ∪ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ) := measure_mono this
      _ ≤ μ E + μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ := measure_union_le _ _
      _ = μ E := by rw [hsupp, add_zero]
  refine hsplit.trans ?_
  let T : Set (α × ℝ) := {p | ⌊sig p / sw⌋ = a ∧ ⌊b p.1 3 / χ⌋ = key 0}
  have hcapT : ∀ q' : Fin 3 → ℤ, μ {ω | ω ∈ T ∧ cellCode h (basePt (b ω.1) ω.2) = q'} ≤ c₀ := by
    intro q'
    refine le_trans (le_of_eq ?_) (hcap q')
    congr 1
    ext p
    simp only [T, mem_ofPred_eq]
    tauto
  have hET : E ⊆ T := by
    intro p hp
    exact ⟨hp.1.2.2.2, hp.1.1.1⟩
  have hσg : 0 ≤ σ * g := by positivity
  have hb := band_measure_le μ T (fun p => basePt (b p.1) p.2) hh c₀ hcapT
    ((q 0 : ℝ) * σ) σ ((key 1 : ℝ) * χ) ((key 0 : ℝ) * χ) (2 * χ)
    ((key 2 : ℝ) * g + (q 1 : ℝ) * σ * g) ((key 3 : ℝ) * g) (σ * g) hσ.le (by positivity) hσg
    E hET (by
      intro p hp
      exact group_band hχ hg hσ hp.1.1 hp.2.2 hp.1.2.1 hp.1.2.2.1)
  simpa only [groupCellCount] using hb

/-- A simple bound for the cell count once the cap cells are finer than the band. -/
theorem groupCellCount_le {χ g σ h M : ℝ} (hh : 0 < h) (hM : 0 ≤ M)
    (hσ : h ≤ σ) (hχ : h ≤ χ) (hσg : h ≤ σ * g) (key : Fin 4 → ℤ)
    (hv : |(key 0 : ℝ) * χ| ≤ M) (hy : |(key 3 : ℝ) * g| ≤ M) :
    groupCellCount χ g σ h key ≤ 6 * (2 * M + 8) * (2 * M + 6) * (σ * χ * (σ * g)) / h ^ 3 := by
  have h1 : 1 ≤ σ / h := (one_le_div hh).mpr hσ
  have h2 : 1 ≤ χ / h := (one_le_div hh).mpr hχ
  have h3 : 1 ≤ σ * g / h := (one_le_div hh).mpr hσg
  have f1 : 2 * (σ / h + 1) + 2 ≤ 6 * (σ / h) := by linarith
  have f2 : 2 * ((2 * χ + |(key 0 : ℝ) * χ| * h) / h + 1) + 2 ≤ (2 * M + 8) * (χ / h) := by
    have : (2 * χ + |(key 0 : ℝ) * χ| * h) / h = 2 * (χ / h) + |(key 0 : ℝ) * χ| := by
      field_simp
    rw [this]
    nlinarith
  have f3 : 2 * ((σ * g + |(key 3 : ℝ) * g| * h) / h + 1) + 2 ≤ (2 * M + 6) * (σ * g / h) := by
    have : (σ * g + |(key 3 : ℝ) * g| * h) / h = σ * g / h + |(key 3 : ℝ) * g| := by
      field_simp
    rw [this]
    nlinarith
  unfold groupCellCount
  calc (2 * (σ / h + 1) + 2) * ((2 * ((2 * χ + |(key 0 : ℝ) * χ| * h) / h + 1) + 2) *
        (2 * ((σ * g + |(key 3 : ℝ) * g| * h) / h + 1) + 2))
      ≤ (6 * (σ / h)) * (((2 * M + 8) * (χ / h)) * ((2 * M + 6) * (σ * g / h))) := by
        have n3 : 0 ≤ 2 * ((σ * g + |(key 3 : ℝ) * g| * h) / h + 1) + 2 := by
          have : 0 ≤ (σ * g + |(key 3 : ℝ) * g| * h) / h :=
            div_nonneg (by nlinarith [abs_nonneg ((key 3 : ℝ) * g)]) hh.le
          linarith
        have n2 : 0 ≤ (2 * M + 8) * (χ / h) := mul_nonneg (by linarith) (by linarith)
        have n2' : 0 ≤ 2 * ((2 * χ + |(key 0 : ℝ) * χ| * h) / h + 1) + 2 := by
          have : 0 ≤ (2 * χ + |(key 0 : ℝ) * χ| * h) / h :=
            div_nonneg (by nlinarith [abs_nonneg ((key 0 : ℝ) * χ)]) hh.le
          linarith
        apply mul_le_mul f1 (mul_le_mul f2 f3 n3 n2) (mul_nonneg n2' n3) (by linarith)
    _ = 6 * (2 * M + 8) * (2 * M + 6) * (σ * χ * (σ * g)) / h ^ 3 := by
        field_simp

end

end Submission.Lib.K4ProjectedGroups
