/- Adapted from this LOT tree, obligation o243 (k4_contact_affine_residual_candidate_transfer),
   session x0835, branch x0835, commit c4aab87f,
   Submission/Obl/k4_contact_affine_residual_candidate_transfer/ShearedCells.lean.
   Namespace and module paths renamed into o261's Transfer namespace;
   the accepted Data record is the same o238 one (k4_critical_switching_state_preparation). -/
import Submission.Lib.K4MovingMeshBoxes.Geometry
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer.MeshCalibration

/-!
# Centered horizontal boxes and their sheared cells

A true label of the horizontal model has a block of length `h`, a horizontal
extent of order `h` and a transverse extent of order `h ^ 2`, measured after
removing the contact shear at its center `(tc, Zc, Yc)`:

  `Ŷ = (Y - Yc + Zc * (t - tc) - tc * (Z - Zc)) / h ^ 2`.

A cubic cell of side `δh` in these box coordinates is covered by a bounded
multiple of `h ^ (-2)` axis-aligned base cubes of side `h ^ 2 * δh`. Hence the
frozen axis-aligned base caps give cell ceilings in box coordinates, and the
supplied mesh calibration applies to an affine function on a filled box. Its
coefficients in box coordinates are the horizontal derivatives `h * 𝒳 L`,
`h * 𝒵 L` and the transverse derivative `h ^ 2 * ∂_Y L` at the center.
-/

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer

open MeasureTheory Set MvPolynomial
open Submission.Lib.K4MovingMeshBoxes
open Submission.Lib.K4ContactNormalization

noncomputable section

/-- Coordinates of a base point in the centered horizontal box. -/
def boxCoord (tc Zc Yc h : ℝ) (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![(z 0 - tc) / h, (z 1 - Zc) / h,
    (z 2 - Yc + Zc * (z 0 - tc) - tc * (z 1 - Zc)) / h ^ 2]

/-- The base point with given box coordinates. -/
def boxPoint (tc Zc Yc h : ℝ) (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![tc + h * y 0, Zc + h * y 1,
    Yc - Zc * (h * y 0) + tc * (h * y 1) + h ^ 2 * y 2]

theorem boxPoint_boxCoord {tc Zc Yc h : ℝ} (hh : h ≠ 0) (z : Fin 3 → ℝ) :
    boxPoint tc Zc Yc h (boxCoord tc Zc Yc h z) = z := by
  funext i
  fin_cases i <;> simp [boxPoint, boxCoord] <;> field_simp <;> ring

theorem continuous_boxCoord (tc Zc Yc h : ℝ) : Continuous (boxCoord tc Zc Yc h) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [boxCoord] <;> fun_prop

/-- A floor bin locates its point within half a bin of the bin center. -/
theorem abs_sub_center_of_floor {x c : ℝ} {n : ℤ} (hc : 0 < c) (h : ⌊x / c⌋ = n) :
    |x - ((n : ℝ) + 1 / 2) * c| ≤ c / 2 := by
  have h1 := Int.floor_le (x / c)
  have h2 := Int.lt_floor_add_one (x / c)
  rw [h] at h1 h2
  rw [le_div_iff₀ hc] at h1
  rw [div_lt_iff₀ hc] at h2
  rw [abs_le]
  constructor <;> nlinarith

/-- A point lies in its own mesh interval. -/
theorem floor_div_mem_Ico {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    0 ≤ x - (⌊x / δ⌋ : ℝ) * δ ∧ x - (⌊x / δ⌋ : ℝ) * δ < δ := by
  have h1 := Int.floor_le (x / δ)
  have h2 := Int.lt_floor_add_one (x / δ)
  rw [le_div_iff₀ hδ] at h1
  rw [div_lt_iff₀ hδ] at h2
  constructor <;> linarith

/-- A cell of side `δh` in box coordinates meets a bounded multiple of `h ^ (-2)`
base cubes of side `h ^ 2 * δh`. -/
theorem sheared_cell_cover {tc Zc Yc h δh : ℝ} (hh : 0 < h) (hδh : 0 < δh)
    (q : Fin 3 → ℤ) :
    ∃ F : Finset (Fin 3 → ℤ),
      (F.card : ℝ) ≤ (2 / h + 2) ^ 2 * (4 * (|Zc| + |tc|) + 4) ∧
      ∀ z : Fin 3 → ℝ, (fun i => ⌊boxCoord tc Zc Yc h z i / δh⌋) = q →
        baseMesh (h ^ 2 * δh) z ∈ F := by
  classical
  set δ := h ^ 2 * δh with hδdef
  have hδ : 0 < δ := by positivity
  have hrad : 0 ≤ h * δh / 2 := by positivity
  -- the two horizontal coordinates
  obtain ⟨F₀, hF₀, hcov₀⟩ :=
    interval_mesh_cover hδ hrad (tc + h * (((q 0 : ℝ)) + 1 / 2) * δh)
  obtain ⟨F₁, hF₁, hcov₁⟩ :=
    interval_mesh_cover hδ hrad (Zc + h * (((q 1 : ℝ)) + 1 / 2) * δh)
  -- the transverse coordinate, given the two horizontal cubes
  have hrad₂ : 0 ≤ (|Zc| + |tc|) * δ + h ^ 2 * δh / 2 := by positivity
  choose F₂ hF₂ hcov₂ using fun a b : ℤ =>
    interval_mesh_cover hδ hrad₂
      (Yc - Zc * ((a : ℝ) * δ - tc) + tc * ((b : ℝ) * δ - Zc) +
        h ^ 2 * (((q 2 : ℝ)) + 1 / 2) * δh)
  let F : Finset (Fin 3 → ℤ) := (F₀ ×ˢ F₁).biUnion
    (fun ab => (F₂ ab.1 ab.2).image (fun c => ![ab.1, ab.2, c]))
  have hcard₂ (a b : ℤ) : ((F₂ a b).card : ℝ) ≤ 4 * (|Zc| + |tc|) + 4 := by
    refine (hF₂ a b).trans (le_of_eq ?_)
    rw [hδdef]
    field_simp
    ring
  have hcard₀ : (F₀.card : ℝ) ≤ 2 / h + 2 := by
    refine hF₀.trans (le_of_eq ?_)
    rw [hδdef]
    field_simp
    ring
  have hcard₁ : (F₁.card : ℝ) ≤ 2 / h + 2 := by
    refine hF₁.trans (le_of_eq ?_)
    rw [hδdef]
    field_simp
    ring
  refine ⟨F, ?_, ?_⟩
  · have h1 : (F.card : ℝ) ≤ ∑ ab ∈ F₀ ×ˢ F₁, ((F₂ ab.1 ab.2).card : ℝ) := by
      calc
        (F.card : ℝ) ≤ ((∑ ab ∈ F₀ ×ˢ F₁,
            ((F₂ ab.1 ab.2).image (fun c => ![ab.1, ab.2, c])).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ ab ∈ F₀ ×ˢ F₁, ((F₂ ab.1 ab.2).card : ℝ) := by
          push_cast
          exact Finset.sum_le_sum fun ab _ => by exact_mod_cast Finset.card_image_le
    have h2 : ∑ ab ∈ F₀ ×ˢ F₁, ((F₂ ab.1 ab.2).card : ℝ) ≤
        ∑ _ab ∈ F₀ ×ˢ F₁, (4 * (|Zc| + |tc|) + 4) :=
      Finset.sum_le_sum fun ab _ => hcard₂ ab.1 ab.2
    rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul] at h2
    push_cast at h2
    have hpos : (0 : ℝ) ≤ 4 * (|Zc| + |tc|) + 4 := by positivity
    calc
      (F.card : ℝ) ≤ (F₀.card : ℝ) * F₁.card * (4 * (|Zc| + |tc|) + 4) := h1.trans h2
      _ ≤ (2 / h + 2) * (2 / h + 2) * (4 * (|Zc| + |tc|) + 4) := by
        gcongr
      _ = _ := by ring
  · intro z hz
    have h0 : ⌊(z 0 - tc) / h / δh⌋ = q 0 := by
      simpa [boxCoord] using congrFun hz 0
    have h1 : ⌊(z 1 - Zc) / h / δh⌋ = q 1 := by
      simpa [boxCoord] using congrFun hz 1
    have h2 : ⌊(z 2 - Yc + Zc * (z 0 - tc) - tc * (z 1 - Zc)) / h ^ 2 / δh⌋ = q 2 := by
      simpa [boxCoord] using congrFun hz 2
    set a := ⌊z 0 / δ⌋
    set b := ⌊z 1 / δ⌋
    have hz0 : |z 0 - (tc + h * (((q 0 : ℝ)) + 1 / 2) * δh)| ≤ h * δh / 2 := by
      have := abs_sub_center_of_floor hδh h0
      rw [show z 0 - (tc + h * (((q 0 : ℝ)) + 1 / 2) * δh) =
        h * ((z 0 - tc) / h - ((q 0 : ℝ) + 1 / 2) * δh) by field_simp; ring,
        abs_mul, abs_of_pos hh]
      nlinarith
    have hz1 : |z 1 - (Zc + h * (((q 1 : ℝ)) + 1 / 2) * δh)| ≤ h * δh / 2 := by
      have := abs_sub_center_of_floor hδh h1
      rw [show z 1 - (Zc + h * (((q 1 : ℝ)) + 1 / 2) * δh) =
        h * ((z 1 - Zc) / h - ((q 1 : ℝ) + 1 / 2) * δh) by field_simp; ring,
        abs_mul, abs_of_pos hh]
      nlinarith
    have hz2 : |z 2 - Yc + Zc * (z 0 - tc) - tc * (z 1 - Zc) -
        h ^ 2 * (((q 2 : ℝ)) + 1 / 2) * δh| ≤ h ^ 2 * δh / 2 := by
      have := abs_sub_center_of_floor hδh h2
      have hh2 : 0 < h ^ 2 := by positivity
      rw [show z 2 - Yc + Zc * (z 0 - tc) - tc * (z 1 - Zc) -
          h ^ 2 * (((q 2 : ℝ)) + 1 / 2) * δh =
        h ^ 2 * ((z 2 - Yc + Zc * (z 0 - tc) - tc * (z 1 - Zc)) / h ^ 2 -
          ((q 2 : ℝ) + 1 / 2) * δh) by field_simp,
        abs_mul, abs_of_pos hh2]
      nlinarith
    have ha := floor_div_mem_Ico hδ (z 0)
    have hb := floor_div_mem_Ico hδ (z 1)
    have hzc : |z 2 - (Yc - Zc * ((a : ℝ) * δ - tc) + tc * ((b : ℝ) * δ - Zc) +
        h ^ 2 * (((q 2 : ℝ)) + 1 / 2) * δh)| ≤ (|Zc| + |tc|) * δ + h ^ 2 * δh / 2 := by
      have e : z 2 - (Yc - Zc * ((a : ℝ) * δ - tc) + tc * ((b : ℝ) * δ - Zc) +
          h ^ 2 * (((q 2 : ℝ)) + 1 / 2) * δh) =
          (z 2 - Yc + Zc * (z 0 - tc) - tc * (z 1 - Zc) -
            h ^ 2 * (((q 2 : ℝ)) + 1 / 2) * δh) - Zc * (z 0 - a * δ) +
            tc * (z 1 - b * δ) := by ring
      have hA : |Zc * (z 0 - a * δ)| ≤ |Zc| * δ := by
        rw [abs_mul]; gcongr; rw [abs_of_nonneg ha.1]; exact ha.2.le
      have hB : |tc * (z 1 - b * δ)| ≤ |tc| * δ := by
        rw [abs_mul]; gcongr; rw [abs_of_nonneg hb.1]; exact hb.2.le
      rw [e]
      calc
        _ ≤ |z 2 - Yc + Zc * (z 0 - tc) - tc * (z 1 - Zc) -
              h ^ 2 * (((q 2 : ℝ)) + 1 / 2) * δh - Zc * (z 0 - a * δ)| +
              |tc * (z 1 - b * δ)| := abs_add_le _ _
        _ ≤ (|z 2 - Yc + Zc * (z 0 - tc) - tc * (z 1 - Zc) -
              h ^ 2 * (((q 2 : ℝ)) + 1 / 2) * δh| + |Zc * (z 0 - a * δ)|) +
              |tc * (z 1 - b * δ)| := add_le_add (abs_sub _ _) le_rfl
        _ ≤ _ := by linarith
    have hmesh : baseMesh δ z = ![a, b, ⌊z 2 / δ⌋] := by
      funext i
      fin_cases i <;> rfl
    rw [hmesh]
    refine Finset.mem_biUnion.mpr ⟨(a, b), Finset.mem_product.mpr
      ⟨hcov₀ _ hz0, hcov₁ _ hz1⟩, Finset.mem_image.mpr ⟨⌊z 2 / δ⌋, hcov₂ a b _ hzc, rfl⟩⟩

/-- Axis-aligned base caps at side `h ^ 2 * δh` give caps on box cells. -/
theorem sheared_cell_cap {Ω : Type*} [MeasurableSpace Ω] (τ : Measure Ω)
    (base : Ω → Fin 3 → ℝ) {tc Zc Yc h δh C : ℝ} (hh : 0 < h) (hδh : 0 < δh)
    (hC : 0 ≤ C)
    (hcap : ∀ c : Fin 3 → ℤ, τ {p | baseMesh (h ^ 2 * δh) (base p) = c} ≤
      ENNReal.ofReal (C * (h ^ 2 * δh) ^ 3))
    (q : Fin 3 → ℤ) :
    τ {p | (fun i => ⌊boxCoord tc Zc Yc h (base p) i / δh⌋) = q} ≤
      ENNReal.ofReal ((2 / h + 2) ^ 2 * (4 * (|Zc| + |tc|) + 4) *
        (C * (h ^ 2 * δh) ^ 3)) := by
  classical
  obtain ⟨F, hF, hcov⟩ := sheared_cell_cover (tc := tc) (Zc := Zc) (Yc := Yc) hh hδh q
  have hc0 : 0 ≤ C * (h ^ 2 * δh) ^ 3 := by positivity
  calc
    τ {p | (fun i => ⌊boxCoord tc Zc Yc h (base p) i / δh⌋) = q} ≤
        τ (⋃ c ∈ F, {p | baseMesh (h ^ 2 * δh) (base p) = c}) :=
      measure_mono fun p hp => mem_iUnion₂.2 ⟨_, hcov _ hp, rfl⟩
    _ ≤ ∑ c ∈ F, τ {p | baseMesh (h ^ 2 * δh) (base p) = c} :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _c ∈ F, ENNReal.ofReal (C * (h ^ 2 * δh) ^ 3) :=
      Finset.sum_le_sum fun c _ => hcap c
    _ = ENNReal.ofReal ((F.card : ℝ) * (C * (h ^ 2 * δh) ^ 3)) := by
      rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hF hc0)

/-- The cell-ceiling constant of a centered box in box coordinates. -/
def boxBeta (K C h : ℝ) : ℝ := 16 * (8 * K + 4) * C * h ^ 4

theorem boxBeta_pos {K C h : ℝ} (hK : 0 ≤ K) (hC : 0 < C) (hh : 0 < h) :
    0 < boxBeta K C h := by
  unfold boxBeta; positivity

/-- The affine function in box coordinates whose coefficients are the
derivatives of `L` adapted to the centered box. -/
def boxAffine (tc Zc Yc h : ℝ) (L : Fin 4 → ℝ) : MvPolynomial (Fin 3) ℝ :=
  affineBaseThree ![L 0 + L 1 * tc + L 2 * Zc + L 3 * Yc, h * (L 1 - Zc * L 3),
    h * (L 2 + tc * L 3), h ^ 2 * L 3]

theorem eval_boxAffine_boxCoord {tc Zc Yc h : ℝ} (hh : h ≠ 0) (L : Fin 4 → ℝ)
    (z : Fin 3 → ℝ) :
    eval (boxCoord tc Zc Yc h z) (boxAffine tc Zc Yc h L) =
      L 0 + L 1 * z 0 + L 2 * z 1 + L 3 * z 2 := by
  simp [boxAffine, affineBaseThree, boxCoord]
  field_simp
  ring

theorem coeff_affineBaseThree (L : Fin 4 → ℝ) (i : Fin 3) :
    (affineBaseThree L).coeff (Finsupp.single i 1) = L i.succ := by
  have h0 (j : Fin 3) : (0 : Fin 3 →₀ ℕ) ≠ Finsupp.single j 1 := by
    intro h; have := congrArg (fun f => f j) h; simp at this
  fin_cases i <;>
    simp [affineBaseThree, coeff_X', coeff_C, Finsupp.single_eq_single_iff, h0]

theorem coeff_boxAffine (tc Zc Yc h : ℝ) (L : Fin 4 → ℝ) (i : Fin 3) :
    (boxAffine tc Zc Yc h L).coeff (Finsupp.single i 1) =
      ![h * (L 1 - Zc * L 3), h * (L 2 + tc * L 3), h ^ 2 * L 3] i := by
  unfold boxAffine
  rw [coeff_affineBaseThree]
  fin_cases i <;> rfl

/-- The supplied mesh calibration bounds the box-adapted derivatives of an
affine function that is small on a box whose base cells are capped. -/
theorem affine_box_slopes (hcal : MeshCalibration) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (τ : Measure Ω)
      [IsFiniteMeasure τ] (base : Ω → Fin 3 → ℝ), Measurable base →
      ∀ (tc Zc Yc h δh K C m E : ℝ) (L : Fin 4 → ℝ),
      0 < h → h ≤ 1 → 0 < δh → 1 ≤ K → 0 < C → 0 < m → 0 ≤ E →
      |tc| ≤ K → |Zc| ≤ K →
      A₀ * (1 + K) ^ A₀ * (1 + boxBeta K C h / m) ^ (6 : ℕ) * δh ≤ 1 / 2 →
      ENNReal.ofReal m ≤ τ univ →
      (∀ c : Fin 3 → ℤ, τ {p | baseMesh (h ^ 2 * δh) (base p) = c} ≤
        ENNReal.ofReal (C * (h ^ 2 * δh) ^ 3)) →
      (∀ᵐ p ∂τ, (∀ i, |boxCoord tc Zc Yc h (base p) i| ≤ K) ∧
        |L 0 + L 1 * base p 0 + L 2 * base p 1 + L 3 * base p 2| ≤ E) →
      h * |L 1 - Zc * L 3| ≤ A₀ * (1 + K) ^ A₀ * (1 + boxBeta K C h / m) ^ (6 : ℕ) * E ∧
      h * |L 2 + tc * L 3| ≤ A₀ * (1 + K) ^ A₀ * (1 + boxBeta K C h / m) ^ (6 : ℕ) * E ∧
      h ^ 2 * |L 3| ≤ A₀ * (1 + K) ^ A₀ * (1 + boxBeta K C h / m) ^ (6 : ℕ) * E := by
  obtain ⟨A₀, hA₀, hc⟩ := mesh_calibration_on_original_law hcal
  refine ⟨A₀, hA₀, ?_⟩
  intro Ω _ τ _ base hbase tc Zc Yc h δh K C m E L hh hh1 hδh hK hC hm hE htc hZc
    hsmall hmass hcap hgood
  have hbeta := boxBeta_pos (by linarith : (0 : ℝ) ≤ K) hC hh
  have hZ : Measurable (fun p => boxCoord tc Zc Yc h (base p)) :=
    (continuous_boxCoord tc Zc Yc h).measurable.comp hbase
  have hcells : ∀ q : Fin 3 → ℤ,
      τ {p | (fun i : Fin 3 => ⌊boxCoord tc Zc Yc h (base p) i / δh⌋) = q} ≤
        ENNReal.ofReal (boxBeta K C h * δh ^ (3 : ℕ)) := by
    intro q
    refine (sheared_cell_cap τ base hh hδh hC.le hcap q).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have h2 : 2 / h + 2 ≤ 4 / h := by
      rw [div_add' _ _ _ hh.ne', div_le_div_iff_of_pos_right hh]; linarith
    have h22 : (2 / h + 2) ^ 2 ≤ (4 / h) ^ 2 := by
      have : 0 ≤ 2 / h + 2 := by positivity
      gcongr
    have hzt : 4 * (|Zc| + |tc|) + 4 ≤ 8 * K + 4 := by linarith
    calc
      (2 / h + 2) ^ 2 * (4 * (|Zc| + |tc|) + 4) * (C * (h ^ 2 * δh) ^ 3) ≤
          (4 / h) ^ 2 * (8 * K + 4) * (C * (h ^ 2 * δh) ^ 3) := by
        gcongr
      _ = boxBeta K C h * δh ^ (3 : ℕ) := by
        unfold boxBeta
        field_simp
        ring
  have hvals : ∀ᵐ p ∂τ, (∀ i, |boxCoord tc Zc Yc h (base p) i| ≤ K) ∧
      |eval (boxCoord tc Zc Yc h (base p)) (boxAffine tc Zc Yc h L)| ≤ E := by
    filter_upwards [hgood] with p hp
    exact ⟨hp.1, by rw [eval_boxAffine_boxCoord hh.ne']; exact hp.2⟩
  have hdeg : (boxAffine tc Zc Yc h L).totalDegree ≤ 2 :=
    (affineBaseThree_degree _).trans (by norm_num)
  have hcoef := hc Ω τ (fun p => boxCoord tc Zc Yc h (base p)) hZ K (boxBeta K C h) m E δh
    hK hbeta hm hE hδh hsmall hmass hcells (boxAffine tc Zc Yc h L) hdeg hvals
  have e0 := hcoef (Finsupp.single 0 1)
  have e1 := hcoef (Finsupp.single 1 1)
  have e2 := hcoef (Finsupp.single 2 1)
  rw [coeff_boxAffine] at e0 e1 e2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at e0 e1 e2
  rw [abs_mul, abs_of_pos hh] at e0 e1
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < h ^ 2)] at e2
  exact ⟨e0, e1, e2⟩

end

end Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer
