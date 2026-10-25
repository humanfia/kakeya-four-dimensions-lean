-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.CellProofs.LinearityCells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.CellProofs.LinearityRich

/-!
# The cell form of sticky Lemma 5.3: hypotheses and alignment on rich blocks

`CellHyp` collects the hypotheses of the cell (lattice) form of sticky Lemma 5.3: cells of
`ρ ℤ³` in `M` layers (`s = M ρ`), a slope `f` (`1`-Lipschitz, `|f| ≤ 4` on `[0, s]`), global
grain values in Assouad-type sets `A k` (one per layer), a `1`-Lipschitz unit plane map `V`
with horizontal part of length at least `κ`, and local grain values in Assouad-type sets
`AL p` for cells within `20 s` of `p`.  `aligned_of_rich` is Step 1: in every block holding at
least `#P / (2 NB)` cells, `|V 0| ≥ κ / 8`.
-/

namespace WangZahlLot.Obl.wz_slab_local_linearity.CellProofs

open Finset Set Metric
open scoped RealInnerProductSpace

noncomputable section

/-- The hypotheses of the cell form of sticky Lemma 5.3. -/
structure CellHyp (ρ : ℝ) (M : ℕ) (α K κ β : ℝ) (f : ℝ → ℝ) (V : Space → Space)
    (P : Finset (ℤ × ℤ × ℤ)) (A : ℤ → Set ℝ) (AL : ℤ × ℤ × ℤ → Set ℝ) : Prop where
  hρ : 0 < ρ
  hM : 0 < M
  hs : (M : ℝ) * ρ ≤ 1
  hK : 0 ≤ K
  hκ : 0 < κ
  hκ1 : κ ≤ 1
  hf_lip : ∀ z z', 0 ≤ z → z ≤ M * ρ → 0 ≤ z' → z' ≤ M * ρ → |f z - f z'| ≤ |z - z'|
  hf4 : ∀ z, 0 ≤ z → z ≤ M * ρ → |f z| ≤ 4
  layer : ∀ q ∈ P, 0 ≤ q.2.2 ∧ q.2.2 < M
  ybound : ∀ q ∈ P, |ρ * q.2.1| ≤ 1
  region : ∀ q ∈ P, |globalValue ρ f q - β| ≤ 6 * (M * ρ)
  Vunit : ∀ q ∈ P, ‖V (cellPos ρ q)‖ = 1
  Vhor : ∀ q ∈ P, κ ^ 2 ≤ V (cellPos ρ q) 0 ^ 2 + V (cellPos ρ q) 1 ^ 2
  Vlip : ∀ q ∈ P, ∀ q' ∈ P, ‖V (cellPos ρ q) - V (cellPos ρ q')‖ ≤ ‖cellPos ρ q - cellPos ρ q'‖
  globAD : ∀ k, Assouad ρ α K (A k)
  globMem : ∀ q ∈ P, globalValue ρ f q ∈ A q.2.2
  locAD : ∀ p ∈ P, Assouad ρ α K (AL p)
  locMem : ∀ p ∈ P, ∀ q ∈ P, ‖cellPos ρ q - cellPos ρ p‖ ≤ 20 * (M * ρ) →
    ⟪V (cellPos ρ p), cellPos ρ q⟫ ∈ AL p

namespace CellHyp

variable {ρ : ℝ} {M : ℕ} {α K κ β : ℝ} {f : ℝ → ℝ} {V : Space → Space}
  {P : Finset (ℤ × ℤ × ℤ)} {A : ℤ → Set ℝ} {AL : ℤ × ℤ × ℤ → Set ℝ}

theorem height_mem (h : CellHyp ρ M α K κ β f V P A AL) {q : ℤ × ℤ × ℤ} (hq : q ∈ P) :
    0 ≤ ρ * q.2.2 ∧ ρ * q.2.2 ≤ M * ρ := by
  have h1 := h.layer q hq
  have hρ := h.hρ
  constructor
  · exact mul_nonneg hρ.le (by exact_mod_cast h1.1)
  · have : (q.2.2 : ℝ) ≤ M := by exact_mod_cast h1.2.le
    nlinarith

/-- Heights of two cells differ by less than `s`. -/
theorem abs_height_sub_lt (h : CellHyp ρ M α K κ β f V P A AL) {q q' : ℤ × ℤ × ℤ} (hq : q ∈ P)
    (hq' : q' ∈ P) : |ρ * q.2.2 - ρ * q'.2.2| < M * ρ := by
  have h1 := h.layer q hq
  have h2 := h.layer q' hq'
  have hρ := h.hρ
  have : |q.2.2 - q'.2.2| < (M : ℤ) := by rw [abs_lt]; constructor <;> omega
  have hR : |((q.2.2 - q'.2.2 : ℤ) : ℝ)| < M := by exact_mod_cast this
  rw [← mul_sub, abs_mul, abs_of_pos hρ]
  push_cast at hR
  nlinarith [abs_nonneg ((q.2.2 : ℝ) - q'.2.2)]

/-- Horizontal displacement between two cells, controlled by their rows. -/
theorem abs_x_sub_le (h : CellHyp ρ M α K κ β f V P A AL) {q q' : ℤ × ℤ × ℤ} (hq : q ∈ P)
    (hq' : q' ∈ P) :
    |ρ * q.1 - ρ * q'.1| ≤ 13 * (M * ρ) + 4 * |ρ * q.2.1 - ρ * q'.2.1| := by
  have hr := h.region q hq
  have hr' := h.region q' hq'
  have hz := h.height_mem hq
  have hz' := h.height_mem hq'
  have hf := h.hf4 _ hz.1 hz.2
  have hl := h.hf_lip _ _ hz.1 hz.2 hz'.1 hz'.2
  have hy' := h.ybound q' hq'
  have hzz := h.abs_height_sub_lt hq hq'
  simp only [globalValue] at hr hr'
  set F := f (ρ * q.2.2)
  set F' := f (ρ * q'.2.2)
  have hsplit : ρ * q.1 - ρ * q'.1 = ((ρ * q.1 + F * (ρ * q.2.1)) - β) -
      ((ρ * q'.1 + F' * (ρ * q'.2.1)) - β) - F * (ρ * q.2.1 - ρ * q'.2.1) -
      (F - F') * (ρ * q'.2.1) := by ring
  rw [hsplit]
  have e1 : |F * (ρ * q.2.1 - ρ * q'.2.1)| ≤ 4 * |ρ * q.2.1 - ρ * q'.2.1| := by
    rw [abs_mul]; gcongr
  have e2 : |(F - F') * (ρ * q'.2.1)| ≤ M * ρ := by
    rw [abs_mul]
    calc |F - F'| * |ρ * q'.2.1| ≤ |ρ * q.2.2 - ρ * q'.2.2| * 1 := by
          gcongr
      _ ≤ M * ρ := by linarith
  calc |((ρ * q.1 + F * (ρ * q.2.1)) - β) - ((ρ * q'.1 + F' * (ρ * q'.2.1)) - β) -
        F * (ρ * q.2.1 - ρ * q'.2.1) - (F - F') * (ρ * q'.2.1)|
      ≤ |(ρ * q.1 + F * (ρ * q.2.1)) - β| + |(ρ * q'.1 + F' * (ρ * q'.2.1)) - β| +
        |F * (ρ * q.2.1 - ρ * q'.2.1)| + |(F - F') * (ρ * q'.2.1)| := by
        calc _ ≤ |((ρ * q.1 + F * (ρ * q.2.1)) - β) - ((ρ * q'.1 + F' * (ρ * q'.2.1)) - β) -
              F * (ρ * q.2.1 - ρ * q'.2.1)| + |(F - F') * (ρ * q'.2.1)| := abs_sub _ _
          _ ≤ (|((ρ * q.1 + F * (ρ * q.2.1)) - β) - ((ρ * q'.1 + F' * (ρ * q'.2.1)) - β)| +
              |F * (ρ * q.2.1 - ρ * q'.2.1)|) + |(F - F') * (ρ * q'.2.1)| := by
              gcongr; exact abs_sub _ _
          _ ≤ ((|(ρ * q.1 + F * (ρ * q.2.1)) - β| + |(ρ * q'.1 + F' * (ρ * q'.2.1)) - β|) +
              |F * (ρ * q.2.1 - ρ * q'.2.1)|) + |(F - F') * (ρ * q'.2.1)| := by
              gcongr; exact abs_sub _ _
          _ = _ := by ring
    _ ≤ 6 * (M * ρ) + 6 * (M * ρ) + 4 * |ρ * q.2.1 - ρ * q'.2.1| + M * ρ := by gcongr
    _ = 13 * (M * ρ) + 4 * |ρ * q.2.1 - ρ * q'.2.1| := by ring

/-- Distance between two cells, controlled by their rows. -/
theorem dist_cell_le (h : CellHyp ρ M α K κ β f V P A AL) {q q' : ℤ × ℤ × ℤ} (hq : q ∈ P)
    (hq' : q' ∈ P) :
    ‖cellPos ρ q - cellPos ρ q'‖ ≤ 14 * (M * ρ) + 5 * |ρ * q.2.1 - ρ * q'.2.1| := by
  have hx := h.abs_x_sub_le hq hq'
  have hz := h.abs_height_sub_lt hq hq'
  calc ‖cellPos ρ q - cellPos ρ q'‖
      ≤ |(cellPos ρ q - cellPos ρ q') 0| + |(cellPos ρ q - cellPos ρ q') 1| +
        |(cellPos ρ q - cellPos ρ q') 2| := norm_le_abs_add_abs_add_abs _
    _ = |ρ * q.1 - ρ * q'.1| + |ρ * q.2.1 - ρ * q'.2.1| + |ρ * q.2.2 - ρ * q'.2.2| := by
        simp [PiLp.sub_apply]
    _ ≤ 14 * (M * ρ) + 5 * |ρ * q.2.1 - ρ * q'.2.1| := by linarith

/-- Two cells of a common block are within `20 s`. -/
theorem dist_cell_le_of_block (h : CellHyp ρ M α K κ β f V P A AL) {q q' : ℤ × ℤ × ℤ}
    (hq : q ∈ P) (hq' : q' ∈ P) (hb : blockOf M q = blockOf M q') :
    ‖cellPos ρ q - cellPos ρ q'‖ ≤ 20 * (M * ρ) := by
  have hd := h.dist_cell_le hq hq'
  have hM : (0 : ℤ) < M := by exact_mod_cast h.hM
  have hrow : |q.2.1 - q'.2.1| < (M : ℤ) := by
    have e1 := Int.mul_ediv_add_emod q.2.1 (M : ℤ)
    have e2 := Int.mul_ediv_add_emod q'.2.1 (M : ℤ)
    have r1 := Int.emod_nonneg q.2.1 hM.ne'
    have r2 := Int.emod_lt_of_pos q.2.1 hM
    have r3 := Int.emod_nonneg q'.2.1 hM.ne'
    have r4 := Int.emod_lt_of_pos q'.2.1 hM
    simp only [blockOf] at hb
    rw [abs_lt]
    constructor
    · nlinarith
    · nlinarith
  have hR : |((q.2.1 - q'.2.1 : ℤ) : ℝ)| < M := by exact_mod_cast hrow
  push_cast at hR
  have hρ := h.hρ
  have : |ρ * q.2.1 - ρ * q'.2.1| ≤ M * ρ := by
    rw [← mul_sub, abs_mul, abs_of_pos hρ]
    nlinarith [abs_nonneg ((q.2.1 : ℝ) - q'.2.1)]
  have hMρ0 : 0 ≤ (M : ℝ) * ρ := by positivity
  linarith

/-- **Step 1 assembled.** At every cell of a block with at least `#P / (2 NB)` cells,
`|V 0| ≥ κ / 8`, provided `#P / (2 NB)` beats the block bound. -/
theorem aligned_of_rich (h : CellHyp ρ M α K κ β f V P A AL) {NB : ℝ}
    (hτ : (3 * (K * ((40 * (M * ρ)) / ρ) ^ α)) * M * (3 * (K * ((12 * (M * ρ)) / ρ) ^ α)) *
      (1 + 16 / κ) < (#P : ℝ) / (2 * NB))
    {q : ℤ × ℤ × ℤ} (hq : q ∈ P)
    (hrich : (#P : ℝ) / (2 * NB) ≤ #{q' ∈ P | blockOf M q' = blockOf M q}) :
    κ / 8 ≤ |V (cellPos ρ q) 0| := by
  classical
  have hρ := h.hρ
  have hMρ : ρ ≤ M * ρ := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast h.hM
    nlinarith
  set B := P.filter fun q' => blockOf M q' = blockOf M q with hBdef
  have hqB : q ∈ B := Finset.mem_filter.mpr ⟨hq, rfl⟩
  have hBP : ∀ q' ∈ B, q' ∈ P ∧ blockOf M q' = blockOf M q := fun q' hq' =>
    Finset.mem_filter.mp hq'
  set W := V (cellPos ρ q)
  have hW : ‖W‖ = 1 := h.Vunit q hq
  apply abs_zero_ge_of_block (Rl := 40 * (M * ρ)) (Rg := 12 * (M * ρ)) (τ := (#P : ℝ) / (2 * NB))
    (xg := fun _ => β - 6 * (M * ρ)) (xl := ⟪V (cellPos ρ q), cellPos ρ q⟫ - 20 * (M * ρ))
    hρ (by linarith) (by linarith) h.hK h.hκ f W (by rw [← hW]; exact abs_apply_le_norm W 0)
    (h.Vhor q hq) B ⟨q, hqB⟩ M (Finset.Ico 0 (M : ℤ)) (by simp)
  · intro q' hq'
    have := h.layer q' (hBP q' hq').1
    exact Finset.mem_Ico.mpr this
  · intro k hk
    rw [Finset.mem_Ico] at hk
    apply h.hf4
    · exact mul_nonneg hρ.le (by exact_mod_cast hk.1)
    · have : (k : ℝ) ≤ M := by exact_mod_cast hk.2.le
      nlinarith
  · exact h.globAD
  · intro q' hq'
    have hq'P := (hBP q' hq').1
    refine ⟨h.globMem q' hq'P, ?_⟩
    have := h.region q' hq'P
    rw [abs_le] at this
    constructor <;> linarith
  · exact h.locAD q hq
  · intro q' hq'
    obtain ⟨hq'P, hb⟩ := hBP q' hq'
    have hd : ‖cellPos ρ q' - cellPos ρ q‖ ≤ 20 * (M * ρ) := h.dist_cell_le_of_block hq'P hq hb
    refine ⟨h.locMem q hq q' hq'P hd, ?_⟩
    have hin : |⟪W, cellPos ρ q'⟫ - ⟪W, cellPos ρ q⟫| ≤ 20 * (M * ρ) := by
      rw [← inner_sub_right]
      calc |⟪W, cellPos ρ q' - cellPos ρ q⟫| ≤ ‖W‖ * ‖cellPos ρ q' - cellPos ρ q‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ 1 * (20 * (M * ρ)) := by rw [hW]; gcongr
        _ = 20 * (M * ρ) := one_mul _
    rw [abs_le] at hin
    constructor <;> linarith
  · exact hrich
  · exact hτ

end CellHyp

end

end WangZahlLot.Obl.wz_slab_local_linearity.CellProofs
