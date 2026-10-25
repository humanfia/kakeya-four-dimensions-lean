/-
Adapted from: here:o222, session x0776, commit 0a43f16b.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/ContactSheet.lean.
The contact-renewal helpers are reused under this obligation's namespace.
-/
import Mathlib
import Submission.Obl.k4_row_parent_contact_candidates.ContactCaps

/-!
# Affine-sheet native polynomial of the zoomed contact instance

The zoomed instance's native polynomial is taken to be an affine sheet
`X₃ - (L₀ + L₁ X₀ + L₂ X₁ + L₃ X₂)` (the residual normalization of the paper's
horizontal model). Its scalar caps follow from the hidden caps on a finer
original mesh: on a fine cell the pulled-back sheet varies by less than one
hidden bin (`offset_bin_cap`, `sheet_variation`), so `zoom_sheet_cap` gives the
`h = true` caps (with or without a velocity bin) from the original `h = false`
caps, with no bound on the sheet coefficients beyond the mesh resolution.
-/

namespace Submission.Obl.k4_row_parent_contact_candidates

open scoped Submission.Obl.k4_row_parent_contact_candidates.ZoomInput

open MeasureTheory Set Filter
open scoped ENNReal
open PreparedModel
open Submission.Lib.K4ContactNormalization (point)
open Submission.Lib.K4MovingMeshBoxes (baseMesh)
open Submission.Lib.K4AffineMeshCaps (affineBase affineBase_coordinate_variation meshBox_coordinate_distance)

noncomputable section

/-- **Offset bins.** If an offset `F` varies by at most `η` on every `δ`-cell,
then on a cell each bin of the offset coordinate `h - F` meets at most four bins
of `h`. -/
theorem offset_bin_cap {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (base : Ω → Fin 3 → ℝ) (h : Ω → ℝ) (F : (Fin 3 → ℝ) → ℝ) (extra : Ω → Prop)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hF : ∀ y y', baseMesh δ y = baseMesh δ y' → |F y - F y'| ≤ η) {C : ℝ≥0∞}
    (hcap : ∀ (z : Fin 3 → ℤ) (j : ℤ),
      μ {w | baseMesh δ (base w) = z ∧ ⌊h w / η⌋ = j ∧ extra w} ≤ C)
    (z : Fin 3 → ℤ) (j : ℤ) :
    μ {w | baseMesh δ (base w) = z ∧ ⌊(h w - F (base w)) / η⌋ = j ∧ extra w} ≤ 4 * C := by
  classical
  set c : Fin 3 → ℝ := fun i => δ * z i with hcdef
  have hc : baseMesh δ c = z := by
    funext i
    simp [baseMesh, Submission.Lib.K4MovingMeshBoxes.baseMesh, c, mul_div_cancel_left₀ _ hδ.ne']
  set j₀ : ℤ := ⌊(j : ℝ) + F c / η⌋ with hj₀
  have hsub : {w | baseMesh δ (base w) = z ∧ ⌊(h w - F (base w)) / η⌋ = j ∧ extra w} ⊆
      ⋃ i ∈ Finset.range 4,
        {w | baseMesh δ (base w) = z ∧ ⌊h w / η⌋ = j₀ - 1 + (i : ℤ) ∧ extra w} := by
    rintro w ⟨hw1, hw2, hw3⟩
    have hFv := abs_le.mp (hF (base w) c (hw1.trans hc.symm))
    rw [Int.floor_eq_iff, le_div_iff₀ hη, div_lt_iff₀ hη] at hw2
    obtain ⟨h1, h2⟩ := hw2
    have hu1 := Int.floor_le ((j : ℝ) + F c / η)
    have hu2 := Int.lt_floor_add_one ((j : ℝ) + F c / η)
    rw [← hj₀] at hu1 hu2
    have e1 : ((j : ℝ) + F c / η) * η = j * η + F c := by
      rw [add_mul, div_mul_cancel₀ _ hη.ne']
    have hA : (j₀ : ℝ) * η ≤ j * η + F c := by
      rw [← e1]; exact mul_le_mul_of_nonneg_right hu1 hη.le
    have hB : j * η + F c < ((j₀ : ℝ) + 1) * η := by
      rw [← e1]; exact mul_lt_mul_of_pos_right hu2 hη
    have hfl1 : j₀ - 1 ≤ ⌊h w / η⌋ := by
      rw [Int.le_floor, le_div_iff₀ hη]; push_cast; nlinarith
    have hfl2 : ⌊h w / η⌋ < j₀ + 3 := by
      rw [Int.floor_lt, div_lt_iff₀ hη]; push_cast; nlinarith
    simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_setOf_eq]
    exact ⟨(⌊h w / η⌋ - (j₀ - 1)).toNat, by omega, hw1, by omega, hw3⟩
  calc μ {w | baseMesh δ (base w) = z ∧ ⌊(h w - F (base w)) / η⌋ = j ∧ extra w}
      ≤ μ (⋃ i ∈ Finset.range 4,
          {w | baseMesh δ (base w) = z ∧ ⌊h w / η⌋ = j₀ - 1 + (i : ℤ) ∧ extra w}) :=
        measure_mono hsub
    _ ≤ ∑ i ∈ Finset.range 4,
          μ {w | baseMesh δ (base w) = z ∧ ⌊h w / η⌋ = j₀ - 1 + (i : ℤ) ∧ extra w} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ Finset.range 4, C := Finset.sum_le_sum fun i _ => hcap z _
    _ = 4 * C := by simp

/-- Value of an affine sheet over the base. -/
def sheetVal (L : Fin 4 → ℝ) (y : Fin 3 → ℝ) : ℝ := L 0 + L 1 * y 0 + L 2 * y 1 + L 3 * y 2

/-- The affine-sheet native polynomial `X₃ - (L₀ + L₁ X₀ + L₂ X₁ + L₃ X₂)`. -/
def sheetPoly (L : Fin 4 → ℝ) : MvPolynomial (Fin 4) ℝ :=
  MvPolynomial.X 3 - (MvPolynomial.C (L 0) + MvPolynomial.C (L 1) * MvPolynomial.X 0 +
    MvPolynomial.C (L 2) * MvPolynomial.X 1 + MvPolynomial.C (L 3) * MvPolynomial.X 2)

theorem eval_sheetPoly (L : Fin 4 → ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    MvPolynomial.eval (point b t) (sheetPoly L) = point b t 3 - sheetVal L (Zoom.baseOf b t) := by
  simp [sheetPoly, sheetVal, point, Zoom.baseOf]

theorem pderiv_sheetPoly (L : Fin 4 → ℝ) : MvPolynomial.pderiv 3 (sheetPoly L) = 1 := by
  simp [sheetPoly, MvPolynomial.pderiv_X]

theorem totalDegree_sheetPoly (L : Fin 4 → ℝ) : (sheetPoly L).totalDegree ≤ 2 := by
  unfold sheetPoly
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
  · rw [MvPolynomial.totalDegree_X]; norm_num
  · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
      · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
        · rw [MvPolynomial.totalDegree_C]; norm_num
        · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
          rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]; norm_num
      · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
        rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]; norm_num
    · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]; norm_num

/-- Variation of an affine sheet through an affine chart on one cell. -/
theorem sheet_variation (L : Fin 4 → ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)
    {δ σ₂ : ℝ} (hδ : 0 < δ) (hres : ∀ i, (∑ j, |A i j| * δ) ≤ σ₂) {y y' : Fin 3 → ℝ}
    (hy : baseMesh δ y = baseMesh δ y') :
    |sheetVal L (affineBase A c y) - sheetVal L (affineBase A c y')| ≤
      (|L 1| + |L 2| + |L 3|) * σ₂ := by
  have hd : ∀ j, |y j - y' j| ≤ δ := fun j =>
    meshBox_coordinate_distance hδ (q := baseMesh δ y') hy rfl j
  have hv : ∀ i, |affineBase A c y i - affineBase A c y' i| ≤ σ₂ := fun i =>
    (affineBase_coordinate_variation A c hd i).trans (hres i)
  have e : sheetVal L (affineBase A c y) - sheetVal L (affineBase A c y') =
      L 1 * (affineBase A c y 0 - affineBase A c y' 0) +
        L 2 * (affineBase A c y 1 - affineBase A c y' 1) +
          L 3 * (affineBase A c y 2 - affineBase A c y' 2) := by
    simp only [sheetVal]; ring
  rw [e]
  calc |L 1 * (affineBase A c y 0 - affineBase A c y' 0) +
        L 2 * (affineBase A c y 1 - affineBase A c y' 1) +
          L 3 * (affineBase A c y 2 - affineBase A c y' 2)|
      ≤ |L 1| * |affineBase A c y 0 - affineBase A c y' 0| +
          |L 2| * |affineBase A c y 1 - affineBase A c y' 1| +
            |L 3| * |affineBase A c y 2 - affineBase A c y' 2| := by
        rw [← abs_mul, ← abs_mul, ← abs_mul]
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ |L 1| * σ₂ + |L 2| * σ₂ + |L 3| * σ₂ := by
        gcongr
        · exact hv 0
        · exact hv 1
        · exact hv 2
    _ = _ := by ring

variable {α : Type} [MeasurableSpace α]

namespace ZoomInput

variable {p : Parameters} {a : PreparedModel α} {r : ℝ} (I : ZoomInput p a r)

/-- The zoomed affine sheet, pulled back to original base coordinates and hidden units. -/
def sheetOffset (L : Fin 4 → ℝ) (y : Fin 3 → ℝ) : ℝ :=
  width p I.k r *
    sheetVal L (affineBase (Zoom.baseMat I.Z I.B I.lam) (Zoom.baseVec I.Z I.B I.lam) y)

/-- Zoomed sheet bins are original offset hidden bins. -/
theorem sheet_bin_zoom (hp : p.Valid) (hlam : I.lam ≠ 0) (L : Fin 4 → ℝ) (b : Fin 6 → ℝ)
    (t s' : ℝ) (j : ℤ) :
    ⌊MvPolynomial.eval (point (Zoom.nCoeff I.Z I.B I.lam b) ((t - I.Z.t₀) / I.Z.q))
        (sheetPoly L) / p.N I.k ^ (-s')⌋ = j ↔
      ⌊((point b t) 3 - I.sheetOffset L (Zoom.baseOf b t)) / p.N I.k ^ (-(r + s'))⌋ = j := by
  have hN0 : 0 < p.N I.k := by linarith [hp.1 I.k]
  have hw := width_pos p hp I.k r
  rw [eval_sheetPoly, I.hidden_zoom hp]
  have hb := Zoom.baseOf_nCoeff (B := I.B) (I.Z_ok hp) hlam b t
  simp only [Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.time] at hb
  rw [hb]
  have e : ((point b t) 3 / width p I.k r -
        sheetVal L (affineBase (Zoom.baseMat I.Z I.B I.lam) (Zoom.baseVec I.Z I.B I.lam)
          (Zoom.baseOf b t))) / p.N I.k ^ (-s') =
      ((point b t) 3 - I.sheetOffset L (Zoom.baseOf b t)) / p.N I.k ^ (-(r + s')) := by
    have hw' : width p I.k r = p.N I.k ^ (-r) := rfl
    simp only [sheetOffset]
    rw [show -(r + s') = -r + -s' by ring, Real.rpow_add hN0, ← hw']
    field_simp
  rw [e]

/-- **Zoomed sheet caps** (`h = true` for the affine-sheet native polynomial), with an
extra line event `E` (a velocity bin, or nothing). -/
theorem zoom_sheet_cap (hp : p.Valid) (hcommon : a.Common p) {R : ℝ}
    (hatr : a.AtlasAt p R I.k r) (hats : ∀ j, a.AtlasAt p R I.k (I.depth j))
    (hGm : MeasurableSet I.G) (hr : 0 ≤ r) (hlam : I.lam ≠ 0) {M₁ : ℝ} (hM₁ : 1 ≤ M₁)
    (hlamM : |I.lam⁻¹| ≤ M₁) (hlamM' : |I.lam| ≤ M₁) (hBle : |I.B 0| + |I.B 1| ≤ M₁)
    (L : Fin 4 → ℝ) {r' r'' s' C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hres : (2 * p.K I.k + M₁ + 1) * M₁ * p.N I.k ^ (-r'') ≤
      a.q I.k r * narrow p I.k r * p.N I.k ^ (-r'))
    (hres₂ : (2 * p.K I.k + M₁ + 1) * M₁ * p.N I.k ^ (-r'') * (|L 1| + |L 2| + |L 3| + 1) ≤
      a.q I.k r * narrow p I.k r * p.N I.k ^ (-s'))
    (E : α → Prop) (hE : MeasurableSet {l | E l})
    (horig : ∀ (z : Fin 3 → ℤ) (j : ℤ), a.mu I.k {w | a.cell (p.N I.k) r'' I.k w = z ∧
      ⌊(a.x I.k w.1 w.2) 3 / p.N I.k ^ (-(r + s'))⌋ = j ∧ E w.1} ≤
        ENNReal.ofReal (C₀ * p.N I.k ^ (-3 * r'')))
    (z' : Fin 3 → ℤ) (j : ℤ) :
    zoomLaw (a.mu I.k) I.keep I.Z.t₀ I.Z.q I.W
      {w | baseMesh (p.N I.k ^ (-r'))
          (Zoom.baseOf (Zoom.nCoeff I.Z I.B I.lam (a.b I.k w.1)) w.2) = z' ∧
        ⌊MvPolynomial.eval (point (Zoom.nCoeff I.Z I.B I.lam (a.b I.k w.1)) w.2) (sheetPoly L) /
          p.N I.k ^ (-s')⌋ = j ∧ E w.1} ≤
      ENNReal.ofReal (27 * p.K I.k * M₁ * (4 * C₀) * p.N I.k ^ (p.d * r) *
        p.N I.k ^ (-3 * r')) := by
  have hN0 : 0 < p.N I.k := by linarith [hp.1 I.k]
  have hN1 : 1 ≤ p.N I.k := by linarith [hp.1 I.k]
  have hK1 := hp.2.2.1.1 I.k
  have hb := (hcommon I.k).1
  have hq := q_pos a I.k r
  have hg := narrow_pos p hp I.k r
  have hℓ : 0 < p.ell := hp.2.2.2.2.2.2.2.1
  have hg1 : narrow p I.k r ≤ 1 := by
    unfold narrow
    apply Real.rpow_le_one_of_one_le_of_nonpos hN1
    nlinarith
  have hc := (hatr.2.2.2.2.1 I.Q).2.2.2.1
  have hδ : 0 < p.N I.k ^ (-r'') := Real.rpow_pos_of_pos hN0 _
  have hη : 0 < p.N I.k ^ (-(r + s')) := Real.rpow_pos_of_pos hN0 _
  set Λ := |L 1| + |L 2| + |L 3| with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  set σ₂ := p.N I.k ^ (-s') / (Λ + 1) with hσ₂
  have hres₂' : (2 * p.K I.k + M₁ + 1) * M₁ * p.N I.k ^ (-r'') ≤
      a.q I.k r * narrow p I.k r * σ₂ := by
    rw [hσ₂, mul_div_assoc', le_div_iff₀ (by positivity)]
    exact hres₂
  have hrow := baseMat_resolve (Z := I.Z) (q := a.q I.k r) (g := narrow p I.k r) (B := I.B)
    (lam := I.lam) hq hg hg1 hK1 hM₁ rfl rfl (hc 3) (hc 4) hBle hlamM hδ.le hres₂'
  have hF : ∀ y y', baseMesh (p.N I.k ^ (-r'')) y = baseMesh (p.N I.k ^ (-r'')) y' →
      |I.sheetOffset L y - I.sheetOffset L y'| ≤ p.N I.k ^ (-(r + s')) := by
    intro y y' hy
    have hv := sheet_variation L (Zoom.baseMat I.Z I.B I.lam) (Zoom.baseVec I.Z I.B I.lam) hδ
      hrow hy
    have hw := width_pos p hp I.k r
    simp only [sheetOffset]
    rw [← mul_sub, abs_mul, abs_of_pos hw]
    calc width p I.k r * |sheetVal L (affineBase (Zoom.baseMat I.Z I.B I.lam)
          (Zoom.baseVec I.Z I.B I.lam) y) - sheetVal L (affineBase (Zoom.baseMat I.Z I.B I.lam)
            (Zoom.baseVec I.Z I.B I.lam) y')|
        ≤ width p I.k r * (Λ * σ₂) := mul_le_mul_of_nonneg_left hv hw.le
      _ ≤ width p I.k r * p.N I.k ^ (-s') := by
          apply mul_le_mul_of_nonneg_left _ hw.le
          rw [hσ₂, mul_div_assoc', div_le_iff₀ (by positivity)]
          have : 0 < p.N I.k ^ (-s') := Real.rpow_pos_of_pos hN0 _
          nlinarith
      _ = p.N I.k ^ (-(r + s')) := by
          simp only [width]
          rw [← Real.rpow_add hN0]; ring_nf
  have hmeasE : MeasurableSet {w : α × ℝ | E w.1} := hE.preimage measurable_fst
  refine I.zoom_cap hp hcommon hatr hats hGm hr hlam hM₁ hlamM hlamM' hBle
    (C := 4 * C₀) (by positivity) hres
    (fun w => ⌊((point (a.b I.k w.1) w.2) 3 - I.sheetOffset L (Zoom.baseOf (a.b I.k w.1) w.2)) /
      p.N I.k ^ (-(r + s'))⌋ = j ∧ E w.1)
    (fun w => ⌊MvPolynomial.eval (point (Zoom.nCoeff I.Z I.B I.lam (a.b I.k w.1)) w.2)
      (sheetPoly L) / p.N I.k ^ (-s')⌋ = j ∧ E w.1)
    (fun w => and_congr (I.sheet_bin_zoom hp hlam L (a.b I.k w.1) w.2 s' j) Iff.rfl)
    (((measurableSet_singleton j).preimage (Int.measurable_floor.comp
      ((I.measurable_eval_line hb (sheetPoly L)).div_const _))).inter hmeasE) ?_ z'
  intro z
  have h4 := offset_bin_cap (a.mu I.k) (fun w => Zoom.baseOf (a.b I.k w.1) w.2)
    (fun w => (point (a.b I.k w.1) w.2) 3) (I.sheetOffset L) (fun w => E w.1) hδ hη hF
    (C := ENNReal.ofReal (C₀ * p.N I.k ^ (-3 * r''))) (fun z j => by
      have := horig z j
      simp only [cell_eq_baseMesh] at this
      exact this) z j
  simp only [cell_eq_baseMesh]
  refine h4.trans_eq ?_
  rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

end ZoomInput

end

end Submission.Obl.k4_row_parent_contact_candidates
