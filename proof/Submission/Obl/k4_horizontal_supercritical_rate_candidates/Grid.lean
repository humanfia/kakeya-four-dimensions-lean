import Submission.Obl.k4_fixed_budget_quadratic_recovery.GraphCaps

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates

open Set
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

/-- Fine ordinary cells meeting a moving horizontal box. The last range is
chosen separately over each time and first-position cell. -/
def horizontalGrid (δ q t₀ p r v τ H : ℝ) : Finset (Fin 3 → ℤ) :=
  (intervalBins δ t₀ q).biUnion fun a =>
    (intervalBins δ (p + (a : ℝ) * δ * v) (H * q + |v| * δ)).biUnion fun b =>
      (intervalBins δ
        (r - (a : ℝ) * δ * p + τ * ((b : ℝ) * δ - (p + (a : ℝ) * δ * v)))
        (H * q ^ 2 + (|p| + |τ| * (1 + |v|)) * δ)).image fun c => ![a, b, c]

theorem mem_horizontalGrid {δ q t₀ p r v τ H t Z Y : ℝ}
    (hδ : 0 < δ) (ht : |t - t₀| ≤ q)
    (hZ : |Z - (p + t * v)| ≤ H * q)
    (hY : |Y - (r - t * p) - τ * (Z - (p + t * v))| ≤ H * q ^ 2) :
    ![⌊t / δ⌋, ⌊Z / δ⌋, ⌊Y / δ⌋] ∈ horizontalGrid δ q t₀ p r v τ H := by
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
  have hZanchor : |Z - (p + (a : ℝ) * δ * v)| ≤ H * q + |v| * δ := by
    calc
      _ = |(Z - (p + t * v)) + (t - (a : ℝ) * δ) * v| := by congr 1; ring
      _ ≤ |Z - (p + t * v)| + |(t - (a : ℝ) * δ) * v| := abs_add_le _ _
      _ ≤ H * q + |v| * δ := by
        rw [abs_mul, mul_comm |t - (a : ℝ) * δ|]
        exact add_le_add hZ (mul_le_mul_of_nonneg_left htcell (abs_nonneg _))
  have hYanchor :
      |Y - (r - (a : ℝ) * δ * p + τ * ((b : ℝ) * δ - (p + (a : ℝ) * δ * v)))| ≤
        H * q ^ 2 + (|p| + |τ| * (1 + |v|)) * δ := by
    have heq :
        Y - (r - (a : ℝ) * δ * p + τ * ((b : ℝ) * δ - (p + (a : ℝ) * δ * v))) =
        (Y - (r - t * p) - τ * (Z - (p + t * v))) -
          (t - (a : ℝ) * δ) * p +
          τ * ((Z - (b : ℝ) * δ) - (t - (a : ℝ) * δ) * v) := by ring
    rw [heq]
    calc
      _ ≤ |Y - (r - t * p) - τ * (Z - (p + t * v))| +
          |(t - (a : ℝ) * δ) * p| +
          |τ| * (|Z - (b : ℝ) * δ| + |(t - (a : ℝ) * δ) * v|) := by
        refine (abs_add_le _ _).trans (add_le_add (abs_sub _ _) ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
      _ ≤ H * q ^ 2 + δ * |p| + |τ| * (δ + δ * |v|) := by
        simp only [abs_mul]
        gcongr
      _ = _ := by ring
  apply Finset.mem_biUnion.mpr
  refine ⟨a, mem_intervalBins hδ ht, Finset.mem_biUnion.mpr ?_⟩
  refine ⟨b, mem_intervalBins hδ hZanchor, Finset.mem_image.mpr ?_⟩
  exact ⟨⌊Y / δ⌋, mem_intervalBins hδ hYanchor, rfl⟩

/-- Ordinary grid count with the three anisotropic factors kept separate. -/
theorem card_horizontalGrid {δ q H : ℝ} (hδ : 0 < δ) (hq : 0 ≤ q) (hH : 0 ≤ H)
    (t₀ p r v τ : ℝ) :
    ((horizontalGrid δ q t₀ p r v τ H).card : ℝ) ≤
      (2 * q / δ + 5) * (2 * (H * q + |v| * δ) / δ + 5) *
        (2 * (H * q ^ 2 + (|p| + |τ| * (1 + |v|)) * δ) / δ + 5) := by
  let BZ := 2 * (H * q + |v| * δ) / δ + 5
  let BY := 2 * (H * q ^ 2 + (|p| + |τ| * (1 + |v|)) * δ) / δ + 5
  have hBY : 0 ≤ BY := by dsimp [BY]; positivity
  have hBZ : 0 ≤ BZ := by dsimp [BZ]; positivity
  have hinner (a : ℤ) :
      (((intervalBins δ (p + (a : ℝ) * δ * v) (H * q + |v| * δ)).biUnion fun b =>
        (intervalBins δ
          (r - (a : ℝ) * δ * p + τ * ((b : ℝ) * δ - (p + (a : ℝ) * δ * v)))
          (H * q ^ 2 + (|p| + |τ| * (1 + |v|)) * δ)).image
          fun c => ![a, b, c]).card : ℝ) ≤ BZ * BY := by
    calc
      _ ≤ ∑ b ∈ intervalBins δ (p + (a : ℝ) * δ * v) (H * q + |v| * δ),
          (((intervalBins δ
            (r - (a : ℝ) * δ * p + τ * ((b : ℝ) * δ - (p + (a : ℝ) * δ * v)))
            (H * q ^ 2 + (|p| + |τ| * (1 + |v|)) * δ)).image
            fun c => ![a, b, c]).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ intervalBins δ (p + (a : ℝ) * δ * v) (H * q + |v| * δ), BY := by
        apply Finset.sum_le_sum
        intro b _
        exact (Nat.cast_le.mpr Finset.card_image_le).trans (card_intervalBins hδ (by positivity) _)
      _ = ((intervalBins δ (p + (a : ℝ) * δ * v) (H * q + |v| * δ)).card : ℝ) * BY := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ BZ * BY := mul_le_mul_of_nonneg_right (card_intervalBins hδ (by positivity) _) hBY
  calc
    _ ≤ ∑ a ∈ intervalBins δ t₀ q,
        (((intervalBins δ (p + (a : ℝ) * δ * v) (H * q + |v| * δ)).biUnion fun b =>
          (intervalBins δ
            (r - (a : ℝ) * δ * p + τ * ((b : ℝ) * δ - (p + (a : ℝ) * δ * v)))
            (H * q ^ 2 + (|p| + |τ| * (1 + |v|)) * δ)).image
            fun c => ![a, b, c]).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ intervalBins δ t₀ q, BZ * BY := Finset.sum_le_sum (fun a _ => hinner a)
    _ = ((intervalBins δ t₀ q).card : ℝ) * (BZ * BY) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * q / δ + 5) * (BZ * BY) :=
      mul_le_mul_of_nonneg_right (card_intervalBins hδ hq _) (mul_nonneg hBZ hBY)
    _ = _ := by ring

theorem card_horizontalGrid_power {δ q H : ℝ} (hδ : 0 < δ) (hq : 0 < q)
    (hq1 : q ≤ 1) (hδq : δ ≤ q ^ 2) (hH : 1 ≤ H)
    (t₀ p r v τ : ℝ) (hp : |p| ≤ H) (hv : |v| ≤ H) (hτ : |τ| ≤ H) :
    ((horizontalGrid δ q t₀ p r v τ H).card : ℝ) ≤ 819 * H ^ 3 * q ^ 4 / δ ^ 3 := by
  have hH₀ : 0 ≤ H := zero_le_one.trans hH
  have hHsq : H ≤ H ^ 2 := by nlinarith only [hH]
  have hδq' : δ ≤ q := hδq.trans (by nlinarith only [hq, hq1])
  have hQ : 1 ≤ q / δ := (le_div_iff₀ hδ).mpr (by simpa using hδq')
  have hQ₂ : 1 ≤ q ^ 2 / δ := (le_div_iff₀ hδ).mpr (by simpa using hδq)
  have hHQ : H ≤ H * (q / δ) := by nlinarith only [mul_le_mul_of_nonneg_left hQ hH₀]
  have hHQ₁ : 1 ≤ H * (q / δ) := hH.trans hHQ
  have hH₂Q₂ : H ^ 2 ≤ H ^ 2 * (q ^ 2 / δ) := by
    nlinarith only [mul_le_mul_of_nonneg_left hQ₂ (sq_nonneg H)]
  have hH₂Q₂₁ : 1 ≤ H ^ 2 * (q ^ 2 / δ) := (hH.trans hHsq).trans hH₂Q₂
  have hHQ₂ : H * (q ^ 2 / δ) ≤ H ^ 2 * (q ^ 2 / δ) :=
    mul_le_mul_of_nonneg_right hHsq (by positivity)
  have hT : |p| + |τ| * (1 + |v|) ≤ 3 * H ^ 2 := by
    calc
      _ ≤ H + H * (1 + H) := by gcongr
      _ ≤ _ := by nlinarith only [hHsq]
  have h₁ : 2 * q / δ + 5 ≤ 7 * q / δ := by
    calc
      _ = 2 * (q / δ) + 5 := by ring
      _ ≤ 7 * (q / δ) := by linarith only [hQ]
      _ = _ := by ring
  have h₂ : 2 * (H * q + |v| * δ) / δ + 5 ≤ 9 * H * q / δ := by
    have heq : 2 * (H * q + |v| * δ) / δ + 5 = 2 * H * (q / δ) + 2 * |v| + 5 := by
      field_simp
    rw [heq]
    rw [show 9 * H * q / δ = 9 * (H * (q / δ)) by ring]
    linarith only [hHQ, hHQ₁, hv]
  have h₃ : 2 * (H * q ^ 2 + (|p| + |τ| * (1 + |v|)) * δ) / δ + 5 ≤
      13 * H ^ 2 * q ^ 2 / δ := by
    have heq : 2 * (H * q ^ 2 + (|p| + |τ| * (1 + |v|)) * δ) / δ + 5 =
        2 * H * (q ^ 2 / δ) + 2 * (|p| + |τ| * (1 + |v|)) + 5 := by
      field_simp
    rw [heq]
    rw [show 13 * H ^ 2 * q ^ 2 / δ = 13 * (H ^ 2 * (q ^ 2 / δ)) by ring]
    linarith only [hHQ₂, hH₂Q₂, hH₂Q₂₁, hT]
  calc
    _ ≤ (2 * q / δ + 5) * (2 * (H * q + |v| * δ) / δ + 5) *
        (2 * (H * q ^ 2 + (|p| + |τ| * (1 + |v|)) * δ) / δ + 5) :=
      card_horizontalGrid hδ hq.le hH₀ t₀ p r v τ
    _ ≤ (7 * q / δ) * (9 * H * q / δ) * (13 * H ^ 2 * q ^ 2 / δ) := by
      gcongr
    _ = _ := by ring

open MeasureTheory

/-- Sum the original cell caps over a finite base/hidden-bin rectangle. -/
theorem finite_cell_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (code : Ω → Fin 3 → ℤ) (signal : Ω → ℤ)
    (Q : Finset (Fin 3 → ℤ)) (J : Finset ℤ) (L : ENNReal)
    (hcap : ∀ z j, μ {p | code p = z ∧ signal p = j} ≤ L) :
    μ {p | code p ∈ Q ∧ signal p ∈ J} ≤ (Q.card : ENNReal) * J.card * L := by
  have hsub : {p | code p ∈ Q ∧ signal p ∈ J} ⊆
      ⋃ z ∈ Q, ⋃ j ∈ J, {p | code p = z ∧ signal p = j} := by
    intro p hp
    exact mem_biUnion hp.1 (mem_biUnion hp.2 ⟨rfl, rfl⟩)
  calc
    _ ≤ μ (⋃ z ∈ Q, ⋃ j ∈ J, {p | code p = z ∧ signal p = j}) := measure_mono hsub
    _ ≤ ∑ z ∈ Q, μ (⋃ j ∈ J, {p | code p = z ∧ signal p = j}) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ z ∈ Q, ∑ j ∈ J, μ {p | code p = z ∧ signal p = j} :=
      Finset.sum_le_sum (fun _ _ => measure_biUnion_finset_le _ _)
    _ ≤ ∑ _z ∈ Q, ∑ _j ∈ J, L :=
      Finset.sum_le_sum (fun z _ => Finset.sum_le_sum (fun j _ => hcap z j))
    _ = _ := by simp [mul_assoc]

/-- A moving horizontal box is charged to the original fine base-cell caps.
The constant `L` may already include the unchanged external palette weight. -/
theorem horizontal_box_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (x : Ω → Fin 3 → ℝ) (f : Ω → ℝ) (E : Set Ω)
    {δ q H X : ℝ} (hδ : 0 < δ) (hq : 0 < q) (hq1 : q ≤ 1) (hδq : δ ≤ q ^ 2)
    (hH : 1 ≤ H) (hX : 0 ≤ X) (t₀ p r v τ : ℝ)
    (hp : |p| ≤ H) (hv : |v| ≤ H) (hτ : |τ| ≤ H)
    (hE : ∀ z ∈ E, |x z 0 - t₀| ≤ q ∧ |x z 1 - (p + x z 0 * v)| ≤ H * q ∧
      |x z 2 - (r - x z 0 * p) - τ * (x z 1 - (p + x z 0 * v))| ≤ H * q ^ 2 ∧ |f z| ≤ X)
    (L : ENNReal) (hcap : ∀ c j, μ {z | (fun i => ⌊x z i / δ⌋) = c ∧ ⌊f z⌋ = j} ≤ L) :
    μ E ≤ ENNReal.ofReal (819 * H ^ 3 * q ^ 4 / δ ^ 3 * (2 * X + 5)) * L := by
  let Q := horizontalGrid δ q t₀ p r v τ H
  let J := intervalBins 1 0 X
  have hsub : E ⊆ {z | (fun i => ⌊x z i / δ⌋) ∈ Q ∧ ⌊f z⌋ ∈ J} := by
    intro z hz
    obtain ⟨ht, hZ, hY, hf⟩ := hE z hz
    constructor
    · have hx : (fun i => ⌊x z i / δ⌋) = ![⌊x z 0 / δ⌋, ⌊x z 1 / δ⌋, ⌊x z 2 / δ⌋] := by
        ext i
        fin_cases i <;> rfl
      rw [hx]
      exact mem_horizontalGrid hδ ht hZ hY
    · simpa [J] using (mem_intervalBins (by norm_num : (0 : ℝ) < 1) (by simpa using hf))
  have hQ : (Q.card : ENNReal) ≤ ENNReal.ofReal (819 * H ^ 3 * q ^ 4 / δ ^ 3) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (card_horizontalGrid_power hδ hq hq1 hδq hH t₀ p r v τ hp hv hτ)
  have hJ : (J.card : ENNReal) ≤ ENNReal.ofReal (2 * X + 5) := by
    rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    simpa [J] using card_intervalBins (by norm_num : (0 : ℝ) < 1) hX 0
  calc
    _ ≤ μ {z | (fun i => ⌊x z i / δ⌋) ∈ Q ∧ ⌊f z⌋ ∈ J} := measure_mono hsub
    _ ≤ (Q.card : ENNReal) * J.card * L := finite_cell_cap μ _ _ Q J L hcap
    _ ≤ ENNReal.ofReal (819 * H ^ 3 * q ^ 4 / δ ^ 3) * ENNReal.ofReal (2 * X + 5) * L :=
      mul_le_mul' (mul_le_mul' hQ hJ) le_rfl
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]

/-- The fine spatial mesh cancels exactly. The palette factor is left intact. -/
theorem horizontal_box_joint_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (x : Ω → Fin 3 → ℝ) (f : Ω → ℝ) (E : Set Ω)
    {δ q H X C : ℝ} (hδ : 0 < δ) (hq : 0 < q) (hq1 : q ≤ 1) (hδq : δ ≤ q ^ 2)
    (hH : 1 ≤ H) (hX : 0 ≤ X) (_hC : 0 ≤ C) (t₀ p r v τ : ℝ)
    (hp : |p| ≤ H) (hv : |v| ≤ H) (hτ : |τ| ≤ H)
    (hE : ∀ z ∈ E, |x z 0 - t₀| ≤ q ∧ |x z 1 - (p + x z 0 * v)| ≤ H * q ∧
      |x z 2 - (r - x z 0 * p) - τ * (x z 1 - (p + x z 0 * v))| ≤ H * q ^ 2 ∧ |f z| ≤ X)
    (w : ENNReal) (hcap : ∀ c j, μ {z | (fun i => ⌊x z i / δ⌋) = c ∧ ⌊f z⌋ = j} ≤
      ENNReal.ofReal (C * δ ^ 3) * w) :
    μ E ≤ ENNReal.ofReal (819 * H ^ 3 * q ^ 4 * (2 * X + 5) * C) * w := by
  calc
    _ ≤ ENNReal.ofReal (819 * H ^ 3 * q ^ 4 / δ ^ 3 * (2 * X + 5)) *
        (ENNReal.ofReal (C * δ ^ 3) * w) :=
      horizontal_box_cap μ x f E hδ hq hq1 hδq hH hX t₀ p r v τ hp hv hτ hE _ hcap
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      field_simp

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates
