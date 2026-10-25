/- Inlined from LOT tree g-oai-074, obligation o250, session x0879,
commit c77c1a90bc277c8885ed3af05e20668071ee3318, file Submission/Obl/k4_horizontal_wide_interval_return/Native/Keys.lean.
Namespace and imports renamed for o274; earlier provenance retained below. -/
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.PairCompare
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core.SheetGeometry

/-!
# Short comparison domains

A *slot key* of a label at a time slot `[t₀, t₀ + q]` records its velocity bin and intercept bin
(width `χ`) and the slice (width `m`) of its transverse position `Y(t₀) = b₁ + t₀ b₄`.  Inside a
key the label moves along the representative motion
`Z = z₀ χ + t v₀ χ`, `Y = y₀ m + 2 m (y - 1/4) - q τ z₀ χ` (`t = t₀ + q τ`), where
`y = sliceY ∈ [1/4, 3/4)` is its normalized slice coordinate; the transverse velocity of the
representative motion is `-z₀ χ ≈ -b₀ ≈ b₄` (horizontal premise).

Graphs over a key domain are normalized two-variable quadratics in `(τ, y)` (`quadCoeff`).
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native

open MeasureTheory Set Filter
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.MatchGML2D
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.CompareSheets
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- Key of a label at a slot starting at `t₀`. -/
def slotKey (b : α → Fin 6 → ℝ) (χ m t₀ : ℝ) (l : α) : Fin 3 → ℤ :=
  ![⌊b l 3 / χ⌋, ⌊b l 0 / χ⌋, ⌊(b l 1 + t₀ * b l 4) / m⌋]

/-- Normalized slice coordinate of a label, in `[1/4, 3/4)`. -/
def sliceY (b : α → Fin 6 → ℝ) (m t₀ : ℝ) (l : α) : ℝ :=
  Int.fract ((b l 1 + t₀ * b l 4) / m) / 2 + 1 / 4

/-- Representative intercept motion of a key. -/
def domZ (χ : ℝ) (κ : Fin 3 → ℤ) (t : ℝ) : ℝ := (κ 1 : ℝ) * χ + t * ((κ 0 : ℝ) * χ)

/-- Representative transverse position of a key at normalized time `τ` and slice coordinate `y`. -/
def domY (χ m q : ℝ) (κ : Fin 3 → ℤ) (τ y : ℝ) : ℝ :=
  (κ 2 : ℝ) * m + 2 * m * (y - 1 / 4) - q * τ * ((κ 1 : ℝ) * χ)

open scoped Classical in
/-- Coefficients of a function of two variables which is a quadratic (zero otherwise). -/
def quadCoeff (f : ℝ → ℝ → ℝ) : Fin 6 → ℝ :=
  if h : IsQuad2 f then Classical.choose h else 0

theorem quad2_quadCoeff {f : ℝ → ℝ → ℝ} (h : IsQuad2 f) (t y : ℝ) :
    quad2 (quadCoeff f) t y = f t y := by
  unfold quadCoeff
  rw [dif_pos h]
  have := Classical.choose_spec h t y
  rw [this]
  simp [quad2]

theorem isQuad2_affine_both {f : ℝ → ℝ → ℝ} (hf : IsQuad2 f) (t₀ q Y₀ V W : ℝ) :
    IsQuad2 (fun τ y => f (t₀ + q * τ) (Y₀ + V * τ + W * y)) := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨![c 0 + c 1 * t₀ + c 2 * Y₀ + c 3 * t₀ ^ 2 + c 4 * (t₀ * Y₀) + c 5 * Y₀ ^ 2,
    c 1 * q + c 2 * V + 2 * c 3 * t₀ * q + c 4 * (t₀ * V + q * Y₀) + 2 * c 5 * Y₀ * V,
    c 2 * W + c 4 * t₀ * W + 2 * c 5 * Y₀ * W,
    c 3 * q ^ 2 + c 4 * q * V + c 5 * V ^ 2,
    c 4 * q * W + 2 * c 5 * V * W,
    c 5 * W ^ 2], ?_⟩
  intro τ y
  simp only [hc]
  simp only [Matrix.cons_val]
  ring

theorem isQuad2_const_mul' {f : ℝ → ℝ → ℝ} (hf : IsQuad2 f) (a : ℝ) :
    IsQuad2 (fun t y => f t y / a) := by
  have := IsQuad2.const_mul (a⁻¹) hf
  simpa [div_eq_inv_mul] using this

/-- Affine graph of a block: the value of `-F` at `(t, Z, Y, 0)`. -/
def blockGraph (F : MvPolynomial (Fin 4) ℝ) (t Z Y : ℝ) : ℝ :=
  -(MvPolynomial.eval ![t, Z, Y, 0] F)

/-- A block polynomial of horizontal form. -/
def HorizontalForm (F : MvPolynomial (Fin 4) ℝ) (L : Fin 4 → ℝ) : Prop :=
  F = MvPolynomial.X (3 : Fin 4) - (MvPolynomial.C (L 0) + MvPolynomial.C (L 1) *
    MvPolynomial.X (0 : Fin 4) + MvPolynomial.C (L 2) * MvPolynomial.X (1 : Fin 4) +
    MvPolynomial.C (L 3) * MvPolynomial.X (2 : Fin 4))

theorem blockGraph_eq {F : MvPolynomial (Fin 4) ℝ} {L : Fin 4 → ℝ} (hF : HorizontalForm F L)
    (t Z Y : ℝ) : blockGraph F t Z Y = L 0 + L 1 * t + L 2 * Z + L 3 * Y := by
  rw [blockGraph, hF]
  simp

theorem eval_horizontalForm {F : MvPolynomial (Fin 4) ℝ} {L : Fin 4 → ℝ}
    (hF : HorizontalForm F L) (x : Fin 4 → ℝ) :
    MvPolynomial.eval x F = x 3 - blockGraph F (x 0) (x 1) (x 2) := by
  rw [blockGraph_eq hF, hF]
  simp

/-- Normalized graph of a block over a key domain. -/
def blockKeyCoeff (F : MvPolynomial (Fin 4) ℝ) (a χ m q t₀ : ℝ) (κ : Fin 3 → ℤ) : Fin 6 → ℝ :=
  quadCoeff (fun τ y => blockGraph F (t₀ + q * τ) (domZ χ κ (t₀ + q * τ)) (domY χ m q κ τ y) / a)

/-- Normalized graph of a sheet over a key domain. -/
def sheetKeyCoeff (G : MvPolynomial (Fin 2) ℝ) (a χ m q t₀ : ℝ) (κ : Fin 3 → ℤ) : Fin 6 → ℝ :=
  quadCoeff (fun τ y => MvPolynomial.eval ![t₀ + q * τ, domY χ m q κ τ y] G / a)

theorem isQuad2_sheetKey {G : MvPolynomial (Fin 2) ℝ} (hG : G.totalDegree ≤ 2)
    (a χ m q t₀ : ℝ) (κ : Fin 3 → ℤ) :
    IsQuad2 (fun τ y => MvPolynomial.eval ![t₀ + q * τ, domY χ m q κ τ y] G / a) := by
  apply isQuad2_const_mul'
  have h := isQuad2_affine_both (isQuad2_eval G hG) t₀ q ((κ 2 : ℝ) * m - 2 * m * (1 / 4))
    (-(q * ((κ 1 : ℝ) * χ))) (2 * m)
  convert h using 3 with τ y
  unfold domY
  congr 2
  ring

theorem quad2_sheetKeyCoeff {G : MvPolynomial (Fin 2) ℝ} (hG : G.totalDegree ≤ 2)
    (a χ m q t₀ : ℝ) (κ : Fin 3 → ℤ) (τ y : ℝ) :
    quad2 (sheetKeyCoeff G a χ m q t₀ κ) τ y =
      MvPolynomial.eval ![t₀ + q * τ, domY χ m q κ τ y] G / a :=
  quad2_quadCoeff (isQuad2_sheetKey hG a χ m q t₀ κ) τ y

theorem isQuad2_blockKey {F : MvPolynomial (Fin 4) ℝ} {L : Fin 4 → ℝ} (hF : HorizontalForm F L)
    (a χ m q t₀ : ℝ) (κ : Fin 3 → ℤ) :
    IsQuad2 (fun τ y =>
      blockGraph F (t₀ + q * τ) (domZ χ κ (t₀ + q * τ)) (domY χ m q κ τ y) / a) := by
  apply isQuad2_const_mul'
  refine ⟨![L 0 + L 1 * t₀ + L 2 * ((κ 1 : ℝ) * χ + t₀ * ((κ 0 : ℝ) * χ)) +
      L 3 * ((κ 2 : ℝ) * m - m / 2),
    L 1 * q + L 2 * (q * ((κ 0 : ℝ) * χ)) - L 3 * (q * ((κ 1 : ℝ) * χ)),
    L 3 * (2 * m), 0, 0, 0], ?_⟩
  intro τ y
  simp only [blockGraph_eq hF, domZ, domY]
  simp
  ring

theorem quad2_blockKeyCoeff {F : MvPolynomial (Fin 4) ℝ} {L : Fin 4 → ℝ} (hF : HorizontalForm F L)
    (a χ m q t₀ : ℝ) (κ : Fin 3 → ℤ) (τ y : ℝ) :
    quad2 (blockKeyCoeff F a χ m q t₀ κ) τ y =
      blockGraph F (t₀ + q * τ) (domZ χ κ (t₀ + q * τ)) (domY χ m q κ τ y) / a :=
  quad2_quadCoeff (isQuad2_blockKey hF a χ m q t₀ κ) τ y

theorem sliceY_mem (b : α → Fin 6 → ℝ) (m t₀ : ℝ) (l : α) :
    sliceY b m t₀ l ∈ Icc (1 / 4 : ℝ) (3 / 4) := by
  unfold sliceY
  have h0 := Int.fract_nonneg ((b l 1 + t₀ * b l 4) / m)
  have h1 := Int.fract_lt_one ((b l 1 + t₀ * b l 4) / m)
  constructor <;> linarith

theorem measurable_sliceY {b : α → Fin 6 → ℝ} (hb : Measurable b) (m t₀ : ℝ) :
    Measurable (sliceY b m t₀) := by
  unfold sliceY
  have h1 : Measurable fun l => b l 1 := (measurable_pi_apply 1).comp hb
  have h4 : Measurable fun l => b l 4 := (measurable_pi_apply 4).comp hb
  exact ((measurable_fract.comp ((h1.add (h4.const_mul t₀)).div_const m)).div_const 2).add_const _

theorem measurableSet_slotKey {b : α → Fin 6 → ℝ} (hb : Measurable b) (χ m t₀ : ℝ)
    (κ : Fin 3 → ℤ) : MeasurableSet {l | slotKey b χ m t₀ l = κ} := by
  have h0 : Measurable fun l => b l 0 := (measurable_pi_apply 0).comp hb
  have h1 : Measurable fun l => b l 1 := (measurable_pi_apply 1).comp hb
  have h3 : Measurable fun l => b l 3 := (measurable_pi_apply 3).comp hb
  have h4 : Measurable fun l => b l 4 := (measurable_pi_apply 4).comp hb
  have e : {l | slotKey b χ m t₀ l = κ} =
      {l | ⌊b l 3 / χ⌋ = κ 0} ∩ {l | ⌊b l 0 / χ⌋ = κ 1} ∩
        {l | ⌊(b l 1 + t₀ * b l 4) / m⌋ = κ 2} := by
    ext l
    simp only [mem_setOf_eq, mem_inter_iff, slotKey]
    constructor
    · intro h
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have := congrFun h 0; simpa using this
      · have := congrFun h 1; simpa using this
      · have := congrFun h 2; simpa using this
    · rintro ⟨⟨h0, h1⟩, h2⟩
      funext e
      fin_cases e
      · simpa using h0
      · simpa using h1
      · simpa using h2
  rw [e]
  exact ((Int.measurable_floor.comp (h3.div_const χ) (measurableSet_singleton _)).inter
    (Int.measurable_floor.comp (h0.div_const χ) (measurableSet_singleton _))).inter
    (Int.measurable_floor.comp ((h1.add (h4.const_mul t₀)).div_const m)
      (measurableSet_singleton _))

/-- A label of key `κ` sits exactly on the representative transverse motion, up to its
transverse velocity defect. -/
theorem label_Y_eq {b : α → Fin 6 → ℝ} {χ m q t₀ : ℝ} (hm : m ≠ 0) {l : α} {κ : Fin 3 → ℤ}
    (hκ : slotKey b χ m t₀ l = κ) (τ : ℝ) :
    b l 1 + (t₀ + q * τ) * b l 4 =
      domY χ m q κ τ (sliceY b m t₀ l) + q * τ * (b l 4 + (κ 1 : ℝ) * χ) := by
  have h2 : ⌊(b l 1 + t₀ * b l 4) / m⌋ = κ 2 := by
    have := congrFun hκ 2; simpa [slotKey] using this
  unfold domY sliceY
  rw [← Int.self_sub_floor, h2]
  field_simp
  ring

/-- The intercept of a label of key `κ` follows the representative motion within `2 χ`. -/
theorem label_Z_near {b : α → Fin 6 → ℝ} {χ m t₀ : ℝ} (hχ : 0 < χ) {l : α} {κ : Fin 3 → ℤ}
    (hκ : slotKey b χ m t₀ l = κ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |b l 0 + t * b l 3 - domZ χ κ t| ≤ 2 * χ := by
  have h0 : ⌊b l 3 / χ⌋ = κ 0 := by have := congrFun hκ 0; simpa [slotKey] using this
  have h1 : ⌊b l 0 / χ⌋ = κ 1 := by have := congrFun hκ 1; simpa [slotKey] using this
  have hv1 := Int.floor_le (b l 3 / χ)
  have hv2 := Int.lt_floor_add_one (b l 3 / χ)
  have hz1 := Int.floor_le (b l 0 / χ)
  have hz2 := Int.lt_floor_add_one (b l 0 / χ)
  rw [h0] at hv1 hv2
  rw [h1] at hz1 hz2
  rw [le_div_iff₀ hχ] at hv1 hz1
  rw [div_lt_iff₀ hχ] at hv2 hz2
  unfold domZ
  rw [abs_le]
  obtain ⟨ht0, ht1⟩ := ht
  constructor <;> nlinarith

/-- The velocity defect of a key: the label's `b₀` lies in the key's intercept bin. -/
theorem label_b0_near {b : α → Fin 6 → ℝ} {χ m t₀ : ℝ} (hχ : 0 < χ) {l : α} {κ : Fin 3 → ℤ}
    (hκ : slotKey b χ m t₀ l = κ) : |b l 0 - (κ 1 : ℝ) * χ| ≤ χ := by
  have h1 : ⌊b l 0 / χ⌋ = κ 1 := by have := congrFun hκ 1; simpa [slotKey] using this
  have hz1 := Int.floor_le (b l 0 / χ)
  have hz2 := Int.lt_floor_add_one (b l 0 / χ)
  rw [h1] at hz1 hz2
  rw [le_div_iff₀ hχ] at hz1
  rw [div_lt_iff₀ hχ] at hz2
  rw [abs_le]
  constructor <;> linarith

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native
