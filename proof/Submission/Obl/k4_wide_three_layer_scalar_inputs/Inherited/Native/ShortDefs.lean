/- Inlined from LOT tree g-oai-074, obligation o250, session x0879,
commit ecf664378ad8398f225a4f7cddbe679a98231d2a, file Submission/Obl/k4_horizontal_wide_interval_return/Native/ShortDefs.lean.
Namespace/imports renamed; Blocks dependency made explicit. Earlier provenance retained below. -/
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.ShortKey
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.Prune
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.Blocks
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core.LayerCaps

set_option autoImplicit false

/-!
# Slot entries of the model at one index

Slots of the true blocks of depth `s` (start `slotStart`, length `slotLen = 2^-T`), the labels of
the layer-0 pieces (`goodLab`), the key reference weight `keyRef`, and the label sets of block and
piece entries over a slot key.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native

open MeasureTheory Set Filter
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.MatchGML2D
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.CompareSheets
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- Start of a slot of depth `s`. -/
def slotStart (cfg : Data α) (k : ℕ) (s : ℝ) (jj : Fin (2 ^ cfg.T k s)) : ℝ :=
  (jj : ℝ) / (2 : ℝ) ^ cfg.T k s

/-- Length of the slots of depth `s`. -/
def slotLen (cfg : Data α) (k : ℕ) (s : ℝ) : ℝ := ((2 : ℝ) ^ cfg.T k s)⁻¹

theorem slotLen_pos (cfg : Data α) (k : ℕ) (s : ℝ) : 0 < slotLen cfg k s := by
  unfold slotLen; positivity

theorem I_eq_slot (cfg : Data α) (k : ℕ) (s : ℝ) (jj : Fin (2 ^ cfg.T k s)) :
    cfg.I (cfg.T k s) jj = Icc (slotStart cfg k s jj) (slotStart cfg k s jj + slotLen cfg k s) := by
  unfold Data.I slotStart slotLen
  congr 1
  rw [add_div, one_div]

theorem slot_unit (cfg : Data α) (k : ℕ) (s : ℝ) (jj : Fin (2 ^ cfg.T k s)) :
    0 ≤ slotStart cfg k s jj ∧ slotStart cfg k s jj + slotLen cfg k s ≤ 1 := by
  unfold slotStart slotLen
  have hp : (0 : ℝ) < (2 : ℝ) ^ cfg.T k s := by positivity
  constructor
  · positivity
  · have hj : ((jj : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ cfg.T k s := by
      have := jj.2
      have h' : (jj : ℕ) + 1 ≤ 2 ^ cfg.T k s := this
      exact_mod_cast h'
    rw [div_add' _ _ _ hp.ne', div_le_one hp, inv_mul_cancel₀ hp.ne']
    linarith

/-- Labels of the layer-0 pieces. -/
def goodLab {cfg : Data α} {k : ℕ} {ε R χ D : ℝ} {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth) : Set α := ⋃ i, L.C 0 i

theorem measurableSet_goodLab {cfg : Data α} {k : ℕ} {ε R χ D : ℝ} {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth) : MeasurableSet (goodLab L) :=
  MeasurableSet.iUnion fun i => L.meas 0 i

/-- The reference weight of a slot key. -/
def keyRef (cfg : Data α) (k : ℕ) (χ m q a : ℝ) (κ : Fin 3 → ℤ) : ℝ :=
  q * χ * m * a ^ cfg.d * (cfg.π k {w | ⌊w / χ⌋ = κ 0}).toReal

/-- Labels of a block entry. -/
def blockLab (cfg : Data α) (k : ℕ) (s : ℝ) {ε R χ D : ℝ} {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth) (m : ℝ) (i : Fin (cfg.n k s)) (κ : Fin 3 → ℤ) :
    Set α :=
  (cfg.B k s i ∩ goodLab L) ∩ {l | slotKey (cfg.b k) χ m (slotStart cfg k s (cfg.j k s i)) l = κ}

/-- Labels of a piece entry. -/
def pieceLab (cfg : Data α) (k : ℕ) (s : ℝ) {ε R χ D : ℝ} {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth) (m : ℝ) (h : Fin 3) (i : Fin (L.np h))
    (jj : Fin (2 ^ cfg.T k s)) (κ : Fin 3 → ℤ) : Set α :=
  L.C h i ∩ {l | slotKey (cfg.b k) χ m (slotStart cfg k s jj) l = κ}

/-- A coordinate `b e₁ + t b e₂` of a label with all parameters `≤ M`, at a unit time. -/
theorem shortDefs_coord_bound {b : Fin 6 → ℝ} {M X t : ℝ} (hb : ∀ e, |b e| ≤ M)
    (hX : 2 * M ≤ X) (ht : t ∈ Icc (0 : ℝ) 1) (e₁ e₂ : Fin 6) : |b e₁ + t * b e₂| ≤ X := by
  have h1 := hb e₁
  have h2 := hb e₂
  obtain ⟨ht0, ht1⟩ := ht
  have hM : 0 ≤ M := (abs_nonneg _).trans h1
  calc |b e₁ + t * b e₂| ≤ |b e₁| + |t * b e₂| := abs_add_le _ _
    _ = |b e₁| + t * |b e₂| := by rw [abs_mul, abs_of_nonneg ht0]
    _ ≤ M + 1 * M := add_le_add h1 (mul_le_mul ht1 h2 (abs_nonneg _) zero_le_one)
    _ ≤ X := by linarith

/-- Times of a slot, normalized by `τ ∈ [0,1]`, are unit times. -/
theorem shortDefs_slot_time_unit (cfg : Data α) (k : ℕ) (s : ℝ) (jj : Fin (2 ^ cfg.T k s))
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    slotStart cfg k s jj + slotLen cfg k s * τ ∈ Icc (0 : ℝ) 1 := by
  have hq0 := slotLen_pos cfg k s
  obtain ⟨hs0, hs1⟩ := slot_unit cfg k s jj
  obtain ⟨hτ0, hτ1⟩ := hτ
  constructor <;> nlinarith

/-- Times of a slot, normalized by `τ ∈ [0,1]`, lie in the slot. -/
theorem shortDefs_slot_time_mem (cfg : Data α) (k : ℕ) (s : ℝ) (jj : Fin (2 ^ cfg.T k s))
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    slotStart cfg k s jj + slotLen cfg k s * τ ∈ cfg.I (cfg.T k s) jj := by
  have hq0 := slotLen_pos cfg k s
  rw [I_eq_slot]
  obtain ⟨hτ0, hτ1⟩ := hτ
  constructor <;> nlinarith

/-- **Block labels follow the key graph of their block**, for a positive block scale
`a = N^-s`. -/
theorem block_lab_graph_of_pos (cfg : Data α) (k : ℕ) (s : ℝ) {ε R χ D R' : ℝ}
    {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth) (hB : BlocksAt cfg k s R')
    {m ζ Xb : ℝ} (hχ : 0 < χ) (hm : 0 < m) (hK1 : 1 ≤ cfg.K k)
    (hXb : 2 * cfg.N k ^ ε ≤ Xb) (hXb1 : 1 ≤ Xb)
    (hKa : cfg.K k * cfg.N k ^ (-s) ≤ 1) (ha : 0 < cfg.N k ^ (-s))
    (i : Fin (cfg.n k s)) (κ : Fin 3 → ℤ) :
    ∀ l ∈ blockLab cfg k s L m i κ, |cfg.b k l 4 + cfg.b k l 0| ≤ ζ →
      slotKey (cfg.b k) χ m (slotStart cfg k s (cfg.j k s i)) l = κ ∧
      ∀ τ ∈ Icc (0 : ℝ) 1,
        |cfg.b k l 2 + (slotStart cfg k s (cfg.j k s i) + slotLen cfg k s * τ) * cfg.b k l 5| ≤ Xb ∧
        |cfg.b k l 2 + (slotStart cfg k s (cfg.j k s i) + slotLen cfg k s * τ) * cfg.b k l 5 -
          cfg.N k ^ (-s) * quad2 (blockKeyCoeff (cfg.F k s i) (cfg.N k ^ (-s)) χ m
            (slotLen cfg k s) (slotStart cfg k s (cfg.j k s i)) κ) τ
            (sliceY (cfg.b k) m (slotStart cfg k s (cfg.j k s i)) l)| ≤
          cfg.N k ^ (-s) * (cfg.K k + 12 * Xb ^ 2 * (cfg.K k *
            (1 + cfg.N k ^ (-s) / (slotLen cfg k s) ^ 2)) *
            (2 * χ + slotLen cfg k s * (ζ + χ)) / cfg.N k ^ (-s)) := by
  intro l hl hζ
  obtain ⟨⟨hlB, hlG⟩, hκ⟩ := hl
  have hκ' : slotKey (cfg.b k) χ m (slotStart cfg k s (cfg.j k s i)) l = κ := hκ
  refine ⟨hκ', fun τ hτ => ?_⟩
  obtain ⟨i', hli'⟩ := mem_iUnion.mp hlG
  have hb : ∀ e, |cfg.b k l e| ≤ cfg.N k ^ ε := (L.mem_bins hli').2.2.2
  have hq0 : 0 < slotLen cfg k s := slotLen_pos cfg k s
  obtain ⟨hs0, hs1⟩ := slot_unit cfg k s (cfg.j k s i)
  have hq1 : slotLen cfg k s ≤ 1 := by linarith
  have hunit := shortDefs_slot_time_unit cfg k s (cfg.j k s i) hτ
  have hslot := shortDefs_slot_time_mem cfg k s (cfg.j k s i) hτ
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have hstart0 := shortDefs_slot_time_unit cfg k s (cfg.j k s i) h0
  have hstart := shortDefs_slot_time_mem cfg k s (cfg.j k s i) h0
  rw [mul_zero, add_zero] at hstart0 hstart
  refine ⟨shortDefs_coord_bound hb hXb hunit 2 5, ?_⟩
  obtain ⟨Lc, hF, hL3, hL12⟩ := hB.affine i
  have hqe : ((2 : ℝ) ^ cfg.T k s)⁻¹ = slotLen cfg k s := rfl
  rw [hqe] at hL3 hL12
  have hΛ : 1 ≤ 1 + cfg.N k ^ (-s) / slotLen cfg k s ^ 2 := by
    have : 0 ≤ cfg.N k ^ (-s) / slotLen cfg k s ^ 2 := by positivity
    linarith
  have haq : cfg.N k ^ (-s) / slotLen cfg k s ≤ cfg.N k ^ (-s) / slotLen cfg k s ^ 2 :=
    div_le_div_of_nonneg_left ha.le (by positivity) (by nlinarith)
  have hK0 : 0 ≤ cfg.K k := by linarith
  have h12 := hL12 l hlB _ hstart
  have hfit0 := (hB.fit i l hlB _ hstart).1
  rw [eval_horizontalForm hF, blockGraph_eq hF] at hfit0
  have hLb := block_affine_bound (Lc := Lc) (K := cfg.K k)
    (Λ := 1 + cfg.N k ^ (-s) / slotLen cfg k s ^ 2) (a := cfg.N k ^ (-s)) (Xb := Xb)
    (x₁ := cfg.x k l (slotStart cfg k s (cfg.j k s i)) 1)
    (x₂ := cfg.x k l (slotStart cfg k s (cfg.j k s i)) 2)
    (x₃ := cfg.x k l (slotStart cfg k s (cfg.j k s i)) 3)
    (t := slotStart cfg k s (cfg.j k s i))
    hK1 hΛ hXb1 hstart0 hKa hL3
    (h12.trans (mul_le_mul_of_nonneg_left (by linarith) hK0))
    (shortDefs_coord_bound hb hXb hstart0 0 3)
    (shortDefs_coord_bound hb hXb hstart0 1 4)
    (shortDefs_coord_bound hb hXb hstart0 2 5)
    hfit0
  have key := block_label_graph (b := cfg.b k) hχ hm.ne' hq0.le ha hF hLb hκ' hζ hτ hunit
    (hB.fit i l hlB _ hslot).1
  refine key.trans (le_of_eq ?_)
  have e : ∀ x : ℝ, cfg.N k ^ (-s) * (cfg.K k + x / cfg.N k ^ (-s)) =
      cfg.K k * cfg.N k ^ (-s) + x := by
    intro x; rw [mul_add, mul_div_cancel₀ _ ha.ne', mul_comm]
  rw [e]

/-- **Block labels follow the key graph of their block.** -/
theorem block_lab_graph (cfg : Data α) (k : ℕ) (s : ℝ) {ε R χ D R' : ℝ} {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth) (hB : BlocksAt cfg k s R')
    {m ζ Xb : ℝ} (hχ : 0 < χ) (hm : 0 < m) (hK1 : 1 ≤ cfg.K k)
    (hXb : 2 * cfg.N k ^ ε ≤ Xb) (hXb1 : 1 ≤ Xb)
    (hKa : cfg.K k * cfg.N k ^ (-s) ≤ 1) (hN : 0 < cfg.N k)
    (i : Fin (cfg.n k s)) (κ : Fin 3 → ℤ) :
    ∀ l ∈ blockLab cfg k s L m i κ, |cfg.b k l 4 + cfg.b k l 0| ≤ ζ →
      slotKey (cfg.b k) χ m (slotStart cfg k s (cfg.j k s i)) l = κ ∧
      ∀ τ ∈ Icc (0 : ℝ) 1,
        |cfg.b k l 2 + (slotStart cfg k s (cfg.j k s i) + slotLen cfg k s * τ) * cfg.b k l 5| ≤ Xb ∧
        |cfg.b k l 2 + (slotStart cfg k s (cfg.j k s i) + slotLen cfg k s * τ) * cfg.b k l 5 -
          cfg.N k ^ (-s) * quad2 (blockKeyCoeff (cfg.F k s i) (cfg.N k ^ (-s)) χ m
            (slotLen cfg k s) (slotStart cfg k s (cfg.j k s i)) κ) τ
            (sliceY (cfg.b k) m (slotStart cfg k s (cfg.j k s i)) l)| ≤
          cfg.N k ^ (-s) * (cfg.K k + 12 * Xb ^ 2 * (cfg.K k *
            (1 + cfg.N k ^ (-s) / (slotLen cfg k s) ^ 2)) *
            (2 * χ + slotLen cfg k s * (ζ + χ)) / cfg.N k ^ (-s)) :=
  block_lab_graph_of_pos cfg k s L hB hχ hm hK1 hXb hXb1 hKa (Real.rpow_pos_of_pos hN _) i κ

/-- **Piece labels follow the key graph of their sheet.** -/
theorem piece_lab_graph (cfg : Data α) (k : ℕ) (s : ℝ) {ε R χ D : ℝ} {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth)
    {m ζ Xb a : ℝ} (hχ : 0 < χ) (hD : 0 < D) (hm : 0 < m) (ha : 0 < a)
    (hXb : 2 * cfg.N k ^ ε ≤ Xb) (hdrift : ζ + χ ≤ D / 4)
    (hsmall : slotLen cfg k s * (ζ + χ) ≤ 4 * D)
    (h : Fin 3) (i : Fin (L.np h)) (jj : Fin (2 ^ cfg.T k s)) (κ : Fin 3 → ℤ) :
    ∀ l ∈ pieceLab cfg k s L m h i jj κ, |cfg.b k l 4 + cfg.b k l 0| ≤ ζ →
      slotKey (cfg.b k) χ m (slotStart cfg k s jj) l = κ ∧
      ∀ τ ∈ Icc (0 : ℝ) 1,
        |cfg.b k l 2 + (slotStart cfg k s jj + slotLen cfg k s * τ) * cfg.b k l 5| ≤ Xb ∧
        |cfg.b k l 2 + (slotStart cfg k s jj + slotLen cfg k s * τ) * cfg.b k l 5 -
          a * quad2 (sheetKeyCoeff (L.G h i) a χ m (slotLen cfg k s) (slotStart cfg k s jj) κ) τ
            (sliceY (cfg.b k) m (slotStart cfg k s jj) l)| ≤
          a * ((cfg.N k ^ ε * cfg.N k ^ (-depth h) +
            7 * (160 * cfg.N k ^ ε) * (slotLen cfg k s * (ζ + χ)) / (4 * D)) / a) := by
  intro l hl hζ
  obtain ⟨hlC, hκ⟩ := hl
  have hκ' : slotKey (cfg.b k) χ m (slotStart cfg k s jj) l = κ := hκ
  refine ⟨hκ', fun τ hτ => ?_⟩
  have hq0 : 0 < slotLen cfg k s := slotLen_pos cfg k s
  have hunit := shortDefs_slot_time_unit cfg k s jj hτ
  have hb : ∀ e, |cfg.b k l e| ≤ cfg.N k ^ ε := (L.mem_bins hlC).2.2.2
  refine ⟨shortDefs_coord_bound hb hXb hunit 2 5, ?_⟩
  have hH := sheetCoeff_bound (L.degree h i) (L.strip h i)
  have hη : etaFun ((L.qp h i 2 : ℝ) * D) (-((L.qp h i 1 : ℝ) * χ)) D
      (slotStart cfg k s jj + slotLen cfg k s * τ)
      (cfg.b k l 1 + (slotStart cfg k s jj + slotLen cfg k s * τ) * cfg.b k l 4) ∈
        Icc (1 / 4 : ℝ) 1 :=
    L.etaFun_mem (p := (l, slotStart cfg k s jj + slotLen cfg k s * τ)) hlC hχ hD hunit hζ
      hdrift
  have hη1 : |etaFun ((L.qp h i 2 : ℝ) * D) (-((L.qp h i 1 : ℝ) * χ)) D
      (slotStart cfg k s jj + slotLen cfg k s * τ)
      (cfg.b k l 1 + (slotStart cfg k s jj + slotLen cfg k s * τ) * cfg.b k l 4)| ≤ 1 := by
    obtain ⟨hη0, hη1⟩ := hη
    rw [abs_le]; constructor <;> linarith
  have hfit : |(cfg.b k l 2 + (slotStart cfg k s jj + slotLen cfg k s * τ) * cfg.b k l 5) -
      MvPolynomial.eval ![slotStart cfg k s jj + slotLen cfg k s * τ,
        cfg.b k l 1 + (slotStart cfg k s jj + slotLen cfg k s * τ) * cfg.b k l 4] (L.G h i)| ≤
      cfg.N k ^ ε * cfg.N k ^ (-depth h) :=
    L.fit hlC hunit
  have key := sheet_label_graph (b := cfg.b k) hχ hm.ne' hq0.le ha (L.degree h i) hD hH hκ' hζ
    hτ hunit hη1 hsmall hfit
  refine key.trans (le_of_eq ?_)
  rw [mul_div_cancel₀ _ ha.ne']

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native
