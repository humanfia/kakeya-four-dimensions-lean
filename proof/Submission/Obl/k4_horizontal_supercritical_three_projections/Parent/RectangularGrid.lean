/-
Adapted from this LOT tree o203, session x0699, commit 4341160d,
Submission/Obl/k4_horizontal_supercritical_rate_candidates/RectangularGrid.lean (namespace
Submission.Obl.k4_horizontal_supercritical_rate_candidates renamed to
Submission.Obl.k4_horizontal_supercritical_three_projections.Parent).
-/
import Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.Grid

namespace Submission.Obl.k4_horizontal_supercritical_three_projections.Parent

open Set MeasureTheory
noncomputable section

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

/-- A moving sheared box is charged to the original fine base-cell caps.
The constant `L` may already include the unchanged external palette weight. -/
theorem rectangular_box_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (x : Ω → Fin 3 → ℝ) (f : Ω → ℝ) (E : Set Ω)
    {δ A B C H X : ℝ} (hδ : 0 < δ) (hA : δ ≤ A) (hB : δ ≤ B) (hC : δ ≤ C)
    (hH : 1 ≤ H) (hX : 0 ≤ X) (t₀ p r v w τ : ℝ)
    (hw : |w| ≤ H) (hv : |v| ≤ H) (hτ : |τ| ≤ H)
    (hE : ∀ z ∈ E, |x z 0 - t₀| ≤ A ∧ |x z 1 - (p + x z 0 * v)| ≤ B ∧
      |x z 2 - (r - x z 0 * w) - τ * (x z 1 - (p + x z 0 * v))| ≤ C ∧ |f z| ≤ X)
    (L : ENNReal) (hcap : ∀ c j, μ {z | (fun i => ⌊x z i / δ⌋) = c ∧ ⌊f z⌋ = j} ≤ L) :
    μ E ≤ ENNReal.ofReal (819 * H ^ 3 * A * B * C / δ ^ 3 * (2 * X + 5)) * L := by
  have hH₀ : 0 ≤ H := zero_le_one.trans hH
  have hA₀ : 0 ≤ A := hδ.le.trans hA
  have hB₀ : 0 ≤ B := hδ.le.trans hB
  have hC₀ : 0 ≤ C := hδ.le.trans hC
  let Q := rectangularGrid δ A B C t₀ p r v w τ
  let J := intervalBins 1 0 X
  have hsub : E ⊆ {z | (fun i => ⌊x z i / δ⌋) ∈ Q ∧ ⌊f z⌋ ∈ J} := by
    intro z hz
    obtain ⟨ht, hZ, hY, hf⟩ := hE z hz
    constructor
    · have hx : (fun i => ⌊x z i / δ⌋) = ![⌊x z 0 / δ⌋, ⌊x z 1 / δ⌋, ⌊x z 2 / δ⌋] := by
        ext i
        fin_cases i <;> rfl
      rw [hx]
      exact mem_rectangularGrid hδ ht hZ hY
    · simpa [J] using (mem_intervalBins (by norm_num : (0 : ℝ) < 1) (by simpa using hf))
  have hQ : (Q.card : ENNReal) ≤ ENNReal.ofReal (819 * H ^ 3 * A * B * C / δ ^ 3) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (card_rectangularGrid_volume hδ hA hB hC hH t₀ p r v w τ hw hv hτ)
  have hJ : (J.card : ENNReal) ≤ ENNReal.ofReal (2 * X + 5) := by
    rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    simpa [J] using card_intervalBins (by norm_num : (0 : ℝ) < 1) hX 0
  calc
    _ ≤ μ {z | (fun i => ⌊x z i / δ⌋) ∈ Q ∧ ⌊f z⌋ ∈ J} := measure_mono hsub
    _ ≤ (Q.card : ENNReal) * J.card * L := finite_cell_cap μ _ _ Q J L hcap
    _ ≤ ENNReal.ofReal (819 * H ^ 3 * A * B * C / δ ^ 3) * ENNReal.ofReal (2 * X + 5) * L :=
      mul_le_mul' (mul_le_mul' hQ hJ) le_rfl
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]

/-- Summing joint caps cancels the fine mesh, retaining the product of the
three independent widths and the original palette weight. -/
theorem rectangular_box_joint_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (x : Ω → Fin 3 → ℝ) (f : Ω → ℝ) (E : Set Ω)
    {δ A B C H X V : ℝ} (hδ : 0 < δ) (hA : δ ≤ A) (hB : δ ≤ B) (hC : δ ≤ C)
    (hH : 1 ≤ H) (hX : 0 ≤ X) (t₀ p r v w τ : ℝ)
    (hw : |w| ≤ H) (hv : |v| ≤ H) (hτ : |τ| ≤ H)
    (hE : ∀ z ∈ E, |x z 0 - t₀| ≤ A ∧ |x z 1 - (p + x z 0 * v)| ≤ B ∧
      |x z 2 - (r - x z 0 * w) - τ * (x z 1 - (p + x z 0 * v))| ≤ C ∧ |f z| ≤ X)
    (weight : ENNReal) (hcap : ∀ c j, μ {z | (fun i => ⌊x z i / δ⌋) = c ∧ ⌊f z⌋ = j} ≤
      ENNReal.ofReal (V * δ ^ 3) * weight) :
    μ E ≤ ENNReal.ofReal (819 * H ^ 3 * A * B * C * (2 * X + 5) * V) * weight := by
  have hH₀ : 0 ≤ H := zero_le_one.trans hH
  have hA₀ : 0 ≤ A := hδ.le.trans hA
  have hB₀ : 0 ≤ B := hδ.le.trans hB
  have hC₀ : 0 ≤ C := hδ.le.trans hC
  calc
    _ ≤ ENNReal.ofReal (819 * H ^ 3 * A * B * C / δ ^ 3 * (2 * X + 5)) *
        (ENNReal.ofReal (V * δ ^ 3) * weight) :=
      rectangular_box_cap μ x f E hδ hA hB hC hH hX t₀ p r v w τ hw hv hτ hE _ hcap
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      field_simp

end

end Submission.Obl.k4_horizontal_supercritical_three_projections.Parent
