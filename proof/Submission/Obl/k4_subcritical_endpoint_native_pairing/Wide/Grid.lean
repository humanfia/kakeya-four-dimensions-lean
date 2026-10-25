/- Adapted from this LOT tree, obligation o218, session x0764, commit e1e41f8e737fdc1974cfdf32d18bbf69838b3ce8,
   Submission/Obl/k4_horizontal_endpoint_wide_return/Wide/Grid.lean.
   Original source attributions are retained below. -/
/- Adapted from this LOT obligation o218, session x0764, commita3589e1863cabf6b40f6f216f23e52a954177867, Wide/Grid.lean. Its earlier provenance is retained below. -/

import Submission.Obl.k4_fixed_budget_quadratic_recovery.GraphCaps

set_option linter.unusedVariables false

/-!
# Ordinary fine cells meeting a sheared box

`intervalBins`, `rectangularGrid` and their membership/count lemmas are adapted (renamed into
this namespace, otherwise unchanged) from LOT tree g-oai-074, o203
`k4_horizontal_supercritical_rate_candidates`, session x0699, branch x0699, commit 4ae1d60e,
files `Grid.lean` and `RectangularGrid.lean` (which import accepted o177
`k4_fixed_budget_quadratic_recovery.GraphCaps`).  New here: `moving_cell_cap` and
`rectangular_moving_box_cap`, which charge a box whose signal window MOVES with the base point
(a scalar residual bin around a varying offset) to the fine joint caps, with a per-cell bin list.
-/

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing

open Set MeasureTheory
open Submission.Obl.k4_fixed_budget_quadratic_recovery

noncomputable section

def intervalBins (δ c R : ℝ) : Finset ℤ :=
  (Finset.Icc (-⌈R / δ + 1⌉ : ℤ) ⌈R / δ + 1⌉).image (fun k => ⌊c / δ⌋ + k)

theorem mem_intervalBins {δ c R x : ℝ} (hδ : 0 < δ) (hx : |x - c| ≤ R) :
    ⌊x / δ⌋ ∈ intervalBins δ c R := by
  have heq : R / δ * δ = R := by field_simp
  have hm := floor_offset_mem hδ (by simpa only [heq] using hx : |x - c| ≤ R / δ * δ)
  exact Finset.mem_image.mpr ⟨⌊x / δ⌋ - ⌊c / δ⌋, hm, by omega⟩

theorem card_intervalBins {δ R : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R) (c : ℝ) :
    ((intervalBins δ c R).card : ℝ) ≤ 2 * R / δ + 5 := by
  calc
    _ ≤ ((Finset.Icc (-⌈R / δ + 1⌉ : ℤ) ⌈R / δ + 1⌉).card : ℝ) := by
      exact_mod_cast Finset.card_image_le
    _ ≤ 2 * (R / δ) + 5 := card_floor_offsets_le (by positivity)
    _ = _ := by ring

/-- Ordinary cells meeting a sheared box with three independent widths. -/
def rectangularGrid (δ A B C t₀ p r v w τ : ℝ) : Finset (Fin 3 → ℤ) :=
  (intervalBins δ t₀ A).biUnion fun a =>
    (intervalBins δ (p + (a : ℝ) * δ * v) (B + |v| * δ)).biUnion fun b =>
      (intervalBins δ
        (r - (a : ℝ) * δ * w + τ * ((b : ℝ) * δ - (p + (a : ℝ) * δ * v)))
        (C + (|w| + |τ| * (1 + |v|)) * δ)).image fun c => ![a, b, c]

theorem mem_rectangularGrid {δ A B C t₀ p r v w τ t Z Y : ℝ}
    (hδ : 0 < δ) (ht : |t - t₀| ≤ A)
    (hZ : |Z - (p + t * v)| ≤ B)
    (hY : |Y - (r - t * w) - τ * (Z - (p + t * v))| ≤ C) :
    ![⌊t / δ⌋, ⌊Z / δ⌋, ⌊Y / δ⌋] ∈ rectangularGrid δ A B C t₀ p r v w τ := by
  let a := ⌊t / δ⌋
  let b := ⌊Z / δ⌋
  have htcell : |t - (a : ℝ) * δ| ≤ δ := by
    have h₀ := (le_div_iff₀ hδ).mp (Int.floor_le (t / δ))
    have h₁ := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (t / δ))
    rw [abs_le]
    dsimp only [a]
    constructor <;> nlinarith only [h₀, h₁, hδ]
  have hZcell : |Z - (b : ℝ) * δ| ≤ δ := by
    have h₀ := (le_div_iff₀ hδ).mp (Int.floor_le (Z / δ))
    have h₁ := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (Z / δ))
    rw [abs_le]
    dsimp only [b]
    constructor <;> nlinarith only [h₀, h₁, hδ]
  have hZanchor : |Z - (p + (a : ℝ) * δ * v)| ≤ B + |v| * δ := by
    calc
      _ = |(Z - (p + t * v)) + (t - (a : ℝ) * δ) * v| := by congr 1; ring
      _ ≤ |Z - (p + t * v)| + |(t - (a : ℝ) * δ) * v| := abs_add_le _ _
      _ ≤ B + |v| * δ := by
        rw [abs_mul, mul_comm |t - (a : ℝ) * δ|]
        exact add_le_add hZ (mul_le_mul_of_nonneg_left htcell (abs_nonneg _))
  have hYanchor :
      |Y - (r - (a : ℝ) * δ * w + τ * ((b : ℝ) * δ - (p + (a : ℝ) * δ * v)))| ≤
        C + (|w| + |τ| * (1 + |v|)) * δ := by
    have heq :
        Y - (r - (a : ℝ) * δ * w + τ * ((b : ℝ) * δ - (p + (a : ℝ) * δ * v))) =
        (Y - (r - t * w) - τ * (Z - (p + t * v))) -
          (t - (a : ℝ) * δ) * w +
          τ * ((Z - (b : ℝ) * δ) - (t - (a : ℝ) * δ) * v) := by ring
    rw [heq]
    calc
      _ ≤ |Y - (r - t * w) - τ * (Z - (p + t * v))| +
          |(t - (a : ℝ) * δ) * w| +
          |τ| * (|Z - (b : ℝ) * δ| + |(t - (a : ℝ) * δ) * v|) := by
        refine (abs_add_le _ _).trans (add_le_add (abs_sub _ _) ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
      _ ≤ C + δ * |w| + |τ| * (δ + δ * |v|) := by
        simp only [abs_mul]
        gcongr
      _ = _ := by ring
  apply Finset.mem_biUnion.mpr
  refine ⟨a, mem_intervalBins hδ ht, Finset.mem_biUnion.mpr ?_⟩
  refine ⟨b, mem_intervalBins hδ hZanchor, Finset.mem_image.mpr ?_⟩
  exact ⟨⌊Y / δ⌋, mem_intervalBins hδ hYanchor, rfl⟩

/-- Ordinary grid count with the three anisotropic factors kept separate. -/
theorem card_rectangularGrid {δ A B C : ℝ} (hδ : 0 < δ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (t₀ p r v w τ : ℝ) :
    ((rectangularGrid δ A B C t₀ p r v w τ).card : ℝ) ≤
      (2 * A / δ + 5) * (2 * (B + |v| * δ) / δ + 5) *
        (2 * (C + (|w| + |τ| * (1 + |v|)) * δ) / δ + 5) := by
  let BZ := 2 * (B + |v| * δ) / δ + 5
  let BY := 2 * (C + (|w| + |τ| * (1 + |v|)) * δ) / δ + 5
  have hBY : 0 ≤ BY := by dsimp [BY]; positivity
  have hBZ : 0 ≤ BZ := by dsimp [BZ]; positivity
  have hinner (a : ℤ) :
      (((intervalBins δ (p + (a : ℝ) * δ * v) (B + |v| * δ)).biUnion fun b =>
        (intervalBins δ
          (r - (a : ℝ) * δ * w + τ * ((b : ℝ) * δ - (p + (a : ℝ) * δ * v)))
          (C + (|w| + |τ| * (1 + |v|)) * δ)).image
          fun c => ![a, b, c]).card : ℝ) ≤ BZ * BY := by
    calc
      _ ≤ ∑ b ∈ intervalBins δ (p + (a : ℝ) * δ * v) (B + |v| * δ),
          (((intervalBins δ
            (r - (a : ℝ) * δ * w + τ * ((b : ℝ) * δ - (p + (a : ℝ) * δ * v)))
            (C + (|w| + |τ| * (1 + |v|)) * δ)).image
            fun c => ![a, b, c]).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ intervalBins δ (p + (a : ℝ) * δ * v) (B + |v| * δ), BY := by
        apply Finset.sum_le_sum
        intro b _
        exact (Nat.cast_le.mpr Finset.card_image_le).trans (card_intervalBins hδ (by positivity) _)
      _ = ((intervalBins δ (p + (a : ℝ) * δ * v) (B + |v| * δ)).card : ℝ) * BY := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ BZ * BY := mul_le_mul_of_nonneg_right (card_intervalBins hδ (by positivity) _) hBY
  calc
    _ ≤ ∑ a ∈ intervalBins δ t₀ A,
        (((intervalBins δ (p + (a : ℝ) * δ * v) (B + |v| * δ)).biUnion fun b =>
          (intervalBins δ
            (r - (a : ℝ) * δ * w + τ * ((b : ℝ) * δ - (p + (a : ℝ) * δ * v)))
            (C + (|w| + |τ| * (1 + |v|)) * δ)).image
            fun c => ![a, b, c]).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ intervalBins δ t₀ A, BZ * BY := Finset.sum_le_sum (fun a _ => hinner a)
    _ = ((intervalBins δ t₀ A).card : ℝ) * (BZ * BY) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * A / δ + 5) * (BZ * BY) :=
      mul_le_mul_of_nonneg_right (card_intervalBins hδ hA _) (mul_nonneg hBZ hBY)
    _ = _ := by ring

/-- The independent time, horizontal, and transverse widths are all retained
in the count. This is used with widths `σ`, `D`, and `D * σ` in scalar charts. -/
theorem card_rectangularGrid_volume {δ A B C H : ℝ} (hδ : 0 < δ)
    (hA : δ ≤ A) (hB : δ ≤ B) (hC : δ ≤ C) (hH : 1 ≤ H)
    (t₀ p r v w τ : ℝ) (hw : |w| ≤ H) (hv : |v| ≤ H) (hτ : |τ| ≤ H) :
    ((rectangularGrid δ A B C t₀ p r v w τ).card : ℝ) ≤
      819 * H ^ 3 * A * B * C / δ ^ 3 := by
  have hH₀ : 0 ≤ H := zero_le_one.trans hH
  have hA₀ : 0 ≤ A := hδ.le.trans hA
  have hB₀ : 0 ≤ B := hδ.le.trans hB
  have hC₀ : 0 ≤ C := hδ.le.trans hC
  have hHsq : H ≤ H ^ 2 := by nlinarith only [hH]
  have hA₁ : 1 ≤ A / δ := (le_div_iff₀ hδ).mpr (by simpa using hA)
  have hB₁ : 1 ≤ B / δ := (le_div_iff₀ hδ).mpr (by simpa using hB)
  have hC₁ : 1 ≤ C / δ := (le_div_iff₀ hδ).mpr (by simpa using hC)
  have hHB : H ≤ H * (B / δ) := le_mul_of_one_le_right hH₀ hB₁
  have hHB₁ : 1 ≤ H * (B / δ) := hH.trans hHB
  have hB' : B / δ ≤ H * (B / δ) := le_mul_of_one_le_left (by positivity) hH
  have hH₂C : H ^ 2 ≤ H ^ 2 * (C / δ) :=
    le_mul_of_one_le_right (sq_nonneg H) hC₁
  have hH₂C₁ : 1 ≤ H ^ 2 * (C / δ) := (hH.trans hHsq).trans hH₂C
  have hC' : C / δ ≤ H ^ 2 * (C / δ) :=
    le_mul_of_one_le_left (by positivity) (hH.trans hHsq)
  have hT : |w| + |τ| * (1 + |v|) ≤ 3 * H ^ 2 := by
    calc
      _ ≤ H + H * (1 + H) := by gcongr
      _ ≤ _ := by nlinarith only [hHsq]
  have h₁ : 2 * A / δ + 5 ≤ 7 * A / δ := by
    calc
      _ = 2 * (A / δ) + 5 := by ring
      _ ≤ 7 * (A / δ) := by linarith only [hA₁]
      _ = _ := by ring
  have h₂ : 2 * (B + |v| * δ) / δ + 5 ≤ 9 * H * B / δ := by
    have heq : 2 * (B + |v| * δ) / δ + 5 = 2 * (B / δ) + 2 * |v| + 5 := by
      field_simp
    rw [heq]
    rw [show 9 * H * B / δ = 9 * (H * (B / δ)) by ring]
    linarith only [hHB, hHB₁, hB', hv]
  have h₃ : 2 * (C + (|w| + |τ| * (1 + |v|)) * δ) / δ + 5 ≤
      13 * H ^ 2 * C / δ := by
    have heq : 2 * (C + (|w| + |τ| * (1 + |v|)) * δ) / δ + 5 =
        2 * (C / δ) + 2 * (|w| + |τ| * (1 + |v|)) + 5 := by
      field_simp
    rw [heq]
    rw [show 13 * H ^ 2 * C / δ = 13 * (H ^ 2 * (C / δ)) by ring]
    linarith only [hC', hH₂C, hH₂C₁, hT]
  calc
    _ ≤ (2 * A / δ + 5) * (2 * (B + |v| * δ) / δ + 5) *
        (2 * (C + (|w| + |τ| * (1 + |v|)) * δ) / δ + 5) :=
      card_rectangularGrid hδ (hδ.le.trans hA) (hδ.le.trans hB) (hδ.le.trans hC) t₀ p r v w τ
    _ ≤ (7 * A / δ) * (9 * H * B / δ) * (13 * H ^ 2 * C / δ) := by
      gcongr
    _ = _ := by ring

/-- Charge a set to fine joint caps when its points lie in finitely many base cells and, in
each base cell, in a cell-dependent finite list of signal bins. -/
theorem moving_cell_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (code : Ω → Fin 3 → ℤ) (signal : Ω → ℤ)
    (Q : Finset (Fin 3 → ℤ)) (J : (Fin 3 → ℤ) → Finset ℤ) (m : ℕ)
    (hJ : ∀ c ∈ Q, (J c).card ≤ m) (E : Set Ω)
    (hE : ∀ z ∈ E, code z ∈ Q ∧ signal z ∈ J (code z)) (L : ENNReal)
    (hcap : ∀ c j, μ {p | code p = c ∧ signal p = j} ≤ L) :
    μ E ≤ (Q.card : ENNReal) * m * L := by
  have hsub : E ⊆ ⋃ c ∈ Q, ⋃ j ∈ J c, {p | code p = c ∧ signal p = j} := by
    intro p hp
    obtain ⟨hc, hj⟩ := hE p hp
    exact mem_biUnion hc (mem_biUnion hj ⟨rfl, rfl⟩)
  calc
    _ ≤ μ (⋃ c ∈ Q, ⋃ j ∈ J c, {p | code p = c ∧ signal p = j}) := measure_mono hsub
    _ ≤ ∑ c ∈ Q, μ (⋃ j ∈ J c, {p | code p = c ∧ signal p = j}) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ c ∈ Q, ∑ j ∈ J c, μ {p | code p = c ∧ signal p = j} :=
      Finset.sum_le_sum (fun _ _ => measure_biUnion_finset_le _ _)
    _ ≤ ∑ c ∈ Q, (m : ENNReal) * L := by
      apply Finset.sum_le_sum
      intro c hc
      calc ∑ j ∈ J c, μ {p | code p = c ∧ signal p = j}
          ≤ ∑ _j ∈ J c, L := Finset.sum_le_sum (fun j _ => hcap c j)
        _ = (J c).card * L := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ m * L := mul_le_mul' (by exact_mod_cast hJ c hc) le_rfl
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- The unit signal bins met by a window `[o, o + W]`. -/
def windowBins (o W : ℝ) : Finset ℤ := Finset.Icc ⌊o⌋ ⌊o + W⌋

theorem mem_windowBins {o W f : ℝ} (h0 : o ≤ f) (h1 : f ≤ o + W) : ⌊f⌋ ∈ windowBins o W :=
  Finset.mem_Icc.mpr ⟨Int.floor_mono h0, Int.floor_mono h1⟩

theorem card_windowBins {o W : ℝ} (hW : 0 ≤ W) : ((windowBins o W).card : ℝ) ≤ W + 2 := by
  unfold windowBins
  rw [Int.card_Icc]
  have h1 := Int.floor_le (o + W)
  have h2 := Int.lt_floor_add_one o
  have hle : ⌊o⌋ ≤ ⌊o + W⌋ + 1 := by
    have := Int.floor_mono (show o ≤ o + W by linarith)
    omega
  have hnn : (0 : ℤ) ≤ ⌊o + W⌋ + 1 - ⌊o⌋ := by omega
  have hcast : (((⌊o + W⌋ + 1 - ⌊o⌋).toNat : ℕ) : ℝ) = ((⌊o + W⌋ + 1 - ⌊o⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnn
  rw [hcast]
  push_cast
  linarith

end

end Submission.Obl.k4_subcritical_endpoint_native_pairing

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing

open Set MeasureTheory

/-- **Moving slab cap.** A set whose base points lie in a sheared box and whose signal lies in a
window `[o, o + w]` moving with the base point is charged to the fine joint caps
(base cells of side `δ`, signal bins of width `w`), provided the offset `o` moves by at most
`θ ≤ w` from a point of the set to any point of its base cell.  The fine mesh cancels. -/
theorem moving_slab_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (x : Ω → Fin 3 → ℝ) (X : Ω → ℝ) (o : (Fin 3 → ℝ) → ℝ) (E : Set Ω)
    {δ w θ A B C H V : ℝ} (hδ : 0 < δ) (hw : 0 < w) (hθ : 0 ≤ θ) (hθw : θ ≤ w)
    (hA : δ ≤ A) (hB : δ ≤ B) (hC : δ ≤ C) (hH : 1 ≤ H) (hV : 0 ≤ V)
    (t₀ p r v w' τ : ℝ) (hw' : |w'| ≤ H) (hv : |v| ≤ H) (hτ : |τ| ≤ H)
    (ho : ∀ z ∈ E, ∀ y' : Fin 3 → ℝ, (∀ i, |x z i - y' i| ≤ δ) → |o (x z) - o y'| ≤ θ)
    (hE : ∀ z ∈ E, |x z 0 - t₀| ≤ A ∧ |x z 1 - (p + x z 0 * v)| ≤ B ∧
      |x z 2 - (r - x z 0 * w') - τ * (x z 1 - (p + x z 0 * v))| ≤ C ∧
      o (x z) ≤ X z ∧ X z ≤ o (x z) + w)
    (weight : ENNReal)
    (hcap : ∀ c j, μ {z | (fun i => ⌊x z i / δ⌋) = c ∧ ⌊X z / w⌋ = j} ≤
      ENNReal.ofReal (V * δ ^ 3) * weight) :
    μ E ≤ ENNReal.ofReal (4095 * H ^ 3 * A * B * C * V) * weight := by
  have hA₀ : 0 ≤ A := hδ.le.trans hA
  have hB₀ : 0 ≤ B := hδ.le.trans hB
  have hC₀ : 0 ≤ C := hδ.le.trans hC
  have hH₀ : 0 ≤ H := zero_le_one.trans hH
  let corner : (Fin 3 → ℤ) → Fin 3 → ℝ := fun c i => (c i : ℝ) * δ
  let Q := rectangularGrid δ A B C t₀ p r v w' τ
  let J : (Fin 3 → ℤ) → Finset ℤ := fun c => windowBins ((o (corner c) - θ) / w) (1 + 2 * θ / w)
  have hJ : ∀ c ∈ Q, (J c).card ≤ 5 := by
    intro c _
    have h := card_windowBins (o := (o (corner c) - θ) / w)
      (show (0 : ℝ) ≤ 1 + 2 * θ / w by positivity)
    have h2 : 2 * θ / w ≤ 2 := by rw [div_le_iff₀ hw]; linarith
    have : ((J c).card : ℝ) ≤ 5 := by
      calc ((J c).card : ℝ) ≤ 1 + 2 * θ / w + 2 := h
        _ ≤ 5 := by linarith
    exact_mod_cast this
  have hsub : ∀ z ∈ E, (fun i => ⌊x z i / δ⌋) ∈ Q ∧
      ⌊X z / w⌋ ∈ J (fun i => ⌊x z i / δ⌋) := by
    intro z hz
    obtain ⟨ht, hZ, hY, hlo, hhi⟩ := hE z hz
    constructor
    · have hx : (fun i => ⌊x z i / δ⌋) = ![⌊x z 0 / δ⌋, ⌊x z 1 / δ⌋, ⌊x z 2 / δ⌋] := by
        ext i
        fin_cases i <;> rfl
      rw [hx]
      exact mem_rectangularGrid hδ ht hZ hY
    · have hcell : ∀ i, |x z i - corner (fun i => ⌊x z i / δ⌋) i| ≤ δ := by
        intro i
        have h₀ := (le_div_iff₀ hδ).mp (Int.floor_le (x z i / δ))
        have h₁ := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (x z i / δ))
        rw [abs_le]
        simp only [corner]
        constructor <;> nlinarith
      have hoc := ho z hz _ hcell
      rw [abs_le] at hoc
      apply mem_windowBins
      · rw [div_le_div_iff_of_pos_right hw]; linarith
      · have : (o (corner fun i => ⌊x z i / δ⌋) - θ) / w + (1 + 2 * θ / w) =
            (o (corner fun i => ⌊x z i / δ⌋) + θ + w) / w := by field_simp; ring
        rw [this, div_le_div_iff_of_pos_right hw]; linarith
  have hQ : (Q.card : ENNReal) ≤ ENNReal.ofReal (819 * H ^ 3 * A * B * C / δ ^ 3) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal
      (card_rectangularGrid_volume hδ hA hB hC hH t₀ p r v w' τ hw' hv hτ)
  calc μ E ≤ (Q.card : ENNReal) * (5 : ℕ) * (ENNReal.ofReal (V * δ ^ 3) * weight) :=
        moving_cell_cap μ (fun z i => ⌊x z i / δ⌋) (fun z => ⌊X z / w⌋) Q J 5 hJ E hsub _ hcap
    _ ≤ ENNReal.ofReal (819 * H ^ 3 * A * B * C / δ ^ 3) * (5 : ℕ) *
          (ENNReal.ofReal (V * δ ^ 3) * weight) := by gcongr
    _ = ENNReal.ofReal (4095 * H ^ 3 * A * B * C * V) * weight := by
        rw [← mul_assoc, show ((5 : ℕ) : ENNReal) = ENNReal.ofReal 5 by simp,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp
        ring

end Submission.Obl.k4_subcritical_endpoint_native_pairing
