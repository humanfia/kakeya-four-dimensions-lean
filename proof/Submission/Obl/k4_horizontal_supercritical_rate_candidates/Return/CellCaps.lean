import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.Cells
import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Grid

/-!
# Caps over crossing cells

From the model's cube caps: an `x3`-window over an anisotropic cell has mass at most a
constant times `width^d`, and one cube with a direction bin and a narrow hidden window has
mass at most `2 K h^3 w^d π(bin)`.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_horizontal_supercritical_rate_candidates

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- The cube code of a point as a function. -/
theorem cube_eq_of_floors (b : α → Fin 6 → ℝ) (h : ℝ) (p : α × ℝ) :
    cube b h p = ![⌊p.2 / h⌋, ⌊x1 b p.1 p.2 / h⌋, ⌊x2 b p.1 p.2 / h⌋] := by
  funext e; fin_cases e <;> rfl

/-- Cubes of a column cell. -/
def columnCubes (h Hc : ℝ) (ω : ℤ × ℤ × ℤ) : Finset (Fin 3 → ℤ) :=
  (Finset.Icc ⌊(ω.2.2 : ℝ) * Hc / h⌋ ⌊((ω.2.2 : ℝ) + 1) * Hc / h⌋).image
    (fun k => ![ω.1, ω.2.1, k])

theorem mem_columnCubes {b : α → Fin 6 → ℝ} {h Hc : ℝ} (hh : 0 < h) (hHc : 0 < Hc)
    {p : α × ℝ} {ω : ℤ × ℤ × ℤ} (hp : xcell b h Hc p = ω) :
    cube b h p ∈ columnCubes h Hc ω := by
  rw [cube_eq_of_floors]
  unfold xcell at hp
  have h1 : ⌊p.2 / h⌋ = ω.1 := by rw [← hp]
  have h2 : ⌊x1 b p.1 p.2 / h⌋ = ω.2.1 := by rw [← hp]
  have h3 : ⌊x2 b p.1 p.2 / Hc⌋ = ω.2.2 := by rw [← hp]
  refine Finset.mem_image.mpr ⟨⌊x2 b p.1 p.2 / h⌋, Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
  · apply Int.floor_mono
    apply div_le_div_of_nonneg_right _ hh.le
    have := Int.floor_le (x2 b p.1 p.2 / Hc)
    rw [h3] at this
    rwa [le_div_iff₀ hHc] at this
  · apply Int.floor_mono
    apply div_le_div_of_nonneg_right _ hh.le
    have := Int.lt_floor_add_one (x2 b p.1 p.2 / Hc)
    rw [h3] at this
    rw [div_lt_iff₀ hHc] at this
    exact this.le
  · rw [h1, h2]

theorem card_columnCubes {h Hc : ℝ} (hh : 0 < h) (hHc : 0 < Hc) (ω : ℤ × ℤ × ℤ) :
    ((columnCubes h Hc ω).card : ℝ) ≤ Hc / h + 2 := by
  unfold columnCubes
  refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
  rw [Int.card_Icc]
  set lo := ⌊(ω.2.2 : ℝ) * Hc / h⌋
  set hi := ⌊((ω.2.2 : ℝ) + 1) * Hc / h⌋
  have hle : lo ≤ hi := Int.floor_mono (div_le_div_of_nonneg_right (by nlinarith) hh.le)
  have : ((hi + 1 - lo).toNat : ℝ) = (hi : ℝ) + 1 - lo := by
    rw [show (hi + 1 - lo).toNat = ((hi + 1 - lo).toNat : ℤ).toNat from rfl]
    have h0 : 0 ≤ hi + 1 - lo := by omega
    exact_mod_cast Int.toNat_of_nonneg h0
  rw [this]
  have h1 : (hi : ℝ) ≤ ((ω.2.2 : ℝ) + 1) * Hc / h := Int.floor_le _
  have h2 : (ω.2.2 : ℝ) * Hc / h - 1 < (lo : ℝ) := Int.sub_one_lt_floor _
  have h3 : ((ω.2.2 : ℝ) + 1) * Hc / h - (ω.2.2 : ℝ) * Hc / h = Hc / h := by ring
  linarith

/-- A window over one crossing cell, for windows of width at most one. -/
theorem window_cap_cell {μ : Measure (α × ℝ)} {π : Measure ℝ} {b : α → Fin 6 → ℝ}
    {N K d S rlo rhi shi vlo vhi : ℝ} (hcaps : Caps μ π b N K d S rlo rhi shi vlo vhi)
    (hN : 1 < N) {r : ℝ} (hr1 : rlo ≤ r) (hr2 : r ≤ rhi) {Hc : ℝ} (hHc : 0 < Hc)
    (ω : ℤ × ℤ × ℤ) (w W : ℝ) (hW : 0 < W) (hW1 : W ≤ 1) (hWs : -Real.logb N W ≤ shi)
    (m : Measure (α × ℝ)) (hm : m ≤ μ) :
    m ({p | xcell b (N ^ (-r)) Hc p = ω} ∩ {p | x3 b p.1 p.2 ∈ Icc w (w + W)}) ≤
      ENNReal.ofReal ((Hc / N ^ (-r) + 2) * 2 * (K * N ^ (-3 * r - d * (-Real.logb N W)))) := by
  set h := N ^ (-r) with hhdef
  have hh : 0 < h := Real.rpow_pos_of_pos (by linarith) _
  set σ := -Real.logb N W with hσ
  have hσ0 : 0 ≤ σ := by
    rw [hσ, neg_nonneg]; exact Real.logb_nonpos hN hW.le hW1
  have hNσ : N ^ (-σ) = W := by
    rw [hσ, neg_neg, Real.rpow_logb (by linarith) (by linarith) hW]
  set Qs := columnCubes h Hc ω
  set Js : Finset ℤ := {⌊w / W⌋, ⌊w / W⌋ + 1}
  have hsub : {p | xcell b h Hc p = ω} ∩ {p | x3 b p.1 p.2 ∈ Icc w (w + W)} ⊆
      {p | cube b h p ∈ Qs ∧ ⌊x3 b p.1 p.2 / N ^ (-σ)⌋ ∈ Js} := by
    intro p hp
    refine ⟨mem_columnCubes hh hHc hp.1, ?_⟩
    rw [hNσ]
    obtain ⟨hw1, hw2⟩ := hp.2
    have hlo : ⌊w / W⌋ ≤ ⌊x3 b p.1 p.2 / W⌋ := Int.floor_mono (div_le_div_of_nonneg_right hw1 hW.le)
    have hhi : ⌊x3 b p.1 p.2 / W⌋ ≤ ⌊w / W⌋ + 1 := by
      have : x3 b p.1 p.2 / W ≤ w / W + 1 := by
        rw [div_add_one hW.ne', div_le_div_iff_of_pos_right hW]; exact hw2
      exact (Int.floor_mono this).trans (by rw [Int.floor_add_one])
    simp only [Js, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hcap : ∀ z j, μ {p | cube b h p = z ∧ ⌊x3 b p.1 p.2 / N ^ (-σ)⌋ = j} ≤
      ENNReal.ofReal (K * N ^ (-3 * r - d * σ)) :=
    fun z j => hcaps.cap r σ hr1 hr2 hσ0 hWs z j
  have hfin := finite_cell_cap μ (cube b h) (fun p => ⌊x3 b p.1 p.2 / N ^ (-σ)⌋) Qs Js _ hcap
  have hQ : (Qs.card : ℝ≥0∞) ≤ ENNReal.ofReal (Hc / h + 2) := by
    rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal (card_columnCubes hh hHc ω)
  have hJ : (Js.card : ℝ≥0∞) ≤ 2 := by
    have : Js.card ≤ 2 := Finset.card_le_two
    exact_mod_cast this
  calc m ({p | xcell b h Hc p = ω} ∩ {p | x3 b p.1 p.2 ∈ Icc w (w + W)})
      ≤ μ ({p | xcell b h Hc p = ω} ∩ {p | x3 b p.1 p.2 ∈ Icc w (w + W)}) := hm _
    _ ≤ μ {p | cube b h p ∈ Qs ∧ ⌊x3 b p.1 p.2 / N ^ (-σ)⌋ ∈ Js} := measure_mono hsub
    _ ≤ (Qs.card : ℝ≥0∞) * Js.card * ENNReal.ofReal (K * N ^ (-3 * r - d * σ)) := hfin
    _ ≤ ENNReal.ofReal (Hc / h + 2) * 2 * ENNReal.ofReal (K * N ^ (-3 * r - d * σ)) := by
        gcongr
    _ = ENNReal.ofReal ((Hc / h + 2) * 2 * (K * N ^ (-3 * r - d * σ))) := by
        have hA : 0 ≤ Hc / h + 2 := by have := div_pos hHc hh; linarith
        rw [eq_comm, ENNReal.ofReal_mul (p := (Hc / h + 2) * 2) (by linarith),
          ENNReal.ofReal_mul (p := Hc / h + 2) hA]
        norm_num

/-- One cube, a hidden window of one bin width, and one direction bin. -/
theorem cube_dir_cap {μ : Measure (α × ℝ)} {π : Measure ℝ} {b : α → Fin 6 → ℝ}
    {N K d S rlo rhi shi vlo vhi : ℝ} (hcaps : Caps μ π b N K d S rlo rhi shi vlo vhi)
    (hN : 1 < N) {r σ v : ℝ} (hr1 : rlo ≤ r) (hr2 : r ≤ rhi) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ shi)
    (hv1 : vlo ≤ v) (hv2 : v ≤ vhi) (q : Fin 3 → ℤ) (w : ℝ) (v₀ : ℤ)
    (m : Measure (α × ℝ)) (hm : m ≤ μ) :
    m ({p | cube b (N ^ (-r)) p = q} ∩ {p | x3 b p.1 p.2 ∈ Icc w (w + N ^ (-σ))} ∩
        {p | ⌊b p.1 3 / N ^ (-v)⌋ = v₀}) ≤
      2 * ENNReal.ofReal (K * N ^ (-3 * r - d * σ)) * π {u : ℝ | ⌊u / N ^ (-v)⌋ = v₀} := by
  set W := N ^ (-σ) with hWdef
  have hW : 0 < W := Real.rpow_pos_of_pos (by linarith) _
  have hsub : {p | cube b (N ^ (-r)) p = q} ∩ {p | x3 b p.1 p.2 ∈ Icc w (w + W)} ∩
      {p | ⌊b p.1 3 / N ^ (-v)⌋ = v₀} ⊆
      {p | cube b (N ^ (-r)) p = q ∧ ⌊x3 b p.1 p.2 / W⌋ = ⌊w / W⌋ ∧
          ⌊b p.1 3 / N ^ (-v)⌋ = v₀} ∪
      {p | cube b (N ^ (-r)) p = q ∧ ⌊x3 b p.1 p.2 / W⌋ = ⌊w / W⌋ + 1 ∧
          ⌊b p.1 3 / N ^ (-v)⌋ = v₀} := by
    intro p hp
    obtain ⟨⟨hq, hw1, hw2⟩, hv⟩ := hp
    have hlo : ⌊w / W⌋ ≤ ⌊x3 b p.1 p.2 / W⌋ := Int.floor_mono (div_le_div_of_nonneg_right hw1 hW.le)
    have hhi : ⌊x3 b p.1 p.2 / W⌋ ≤ ⌊w / W⌋ + 1 := by
      have : x3 b p.1 p.2 / W ≤ w / W + 1 := by
        rw [div_add_one hW.ne', div_le_div_iff_of_pos_right hW]; exact hw2
      exact (Int.floor_mono this).trans (by rw [Int.floor_add_one])
    rcases (show ⌊x3 b p.1 p.2 / W⌋ = ⌊w / W⌋ ∨ ⌊x3 b p.1 p.2 / W⌋ = ⌊w / W⌋ + 1 by omega)
      with h | h
    · exact Or.inl ⟨hq, h, hv⟩
    · exact Or.inr ⟨hq, h, hv⟩
  calc m _ ≤ μ _ := hm _
    _ ≤ μ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (K * N ^ (-3 * r - d * σ)) * π {u : ℝ | ⌊u / N ^ (-v)⌋ = v₀} +
        ENNReal.ofReal (K * N ^ (-3 * r - d * σ)) * π {u : ℝ | ⌊u / N ^ (-v)⌋ = v₀} :=
        add_le_add (hcaps.jcap r σ v hr1 hr2 hσ0 hσ1 hv1 hv2 q _ v₀)
          (hcaps.jcap r σ v hr1 hr2 hσ0 hσ1 hv1 hv2 q _ v₀)
    _ = _ := by ring

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
