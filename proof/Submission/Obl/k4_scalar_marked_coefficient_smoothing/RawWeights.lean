import Submission.Obl.k4_scalar_marked_coefficient_smoothing.RawGeometry

/-!
# The pointwise tag-weight bounds

`weight_sum_le_pure`: the weights of the tags whose window (hidden `ρ`-bin `i`) contains a base
point sum to at most `J K₁ · 3 (2L + 11)(6L + 19) · Q`, `L = ⌈K⌉₊`, when every original
`(σ, σ, ρ)`-cell has mass at most `Q`.

`weight_sum_le_ang`: with a noisy slope bin `k` of width `ρu ≥ σ`, at most
`J K₁ · 15 (2L + 11)(6L + 19) · Q`, when every original `(σ, σ, a)`-cell with a slope bin of
width `ρu` has mass at most `Q`.
-/

namespace Submission.Obl.k4_scalar_marked_coefficient_smoothing.Raw

open MeasureTheory Set
open scoped ENNReal

/-- The original cells met by the tags of a pure window. -/
def pureCells (a0 a1 i : ℤ) (L : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  Finset.Icc (a0 - ((1 : ℕ) : ℤ)) (a0 + ((1 : ℕ) : ℤ)) ×ˢ
    (Finset.Icc (a1 - ((L + 5 : ℕ) : ℤ)) (a1 + ((L + 5 : ℕ) : ℤ)) ×ˢ
      Finset.Icc (i - ((3 * L + 9 : ℕ) : ℤ)) (i + ((3 * L + 9 : ℕ) : ℤ)))

theorem card_pureCells (a0 a1 i : ℤ) (L : ℕ) :
    (pureCells a0 a1 i L).card = 3 * ((2 * (L + 5) + 1) * (2 * (3 * L + 9) + 1)) := by
  simp only [pureCells, Finset.card_product, card_Icc_sym]

/-- The original cell `c` at scales `(σ, σ, ρ)`. -/
def pureCellSet {α : Type*} (b : α → Coeff) (σ ρ : ℝ) (c : ℤ × ℤ × ℤ) : Set (α × ℝ) :=
  {p | meshCode b σ p = ![c.1, c.2.1] ∧ ⌊curveX b p.1 p.2 / ρ⌋ = c.2.2}

theorem weight_sum_le_pure {α : Type*} [MeasurableSpace α] {μ : Measure (α × ℝ)}
    {b : α → Coeff} {H J : ℕ} {tag : α → Fin H} (htag : Measurable tag) {b₀ : Fin H → Coeff}
    {w : Fin H → ℝ} {mark : Fin H → Fin J → Bool} {K K₁ σ δ ρ : ℝ} (hK : 1 ≤ K) (hK₁ : 0 < K₁)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hδσ : δ ≤ σ) (hσρ : σ ≤ ρ) (hJσ : 1 ≤ (J : ℝ) * σ)
    (hb : ∀ l e, |b l e| ≤ K) (hround : ∀ l e, |b l e - b₀ (tag l) e| ≤ δ)
    (hmark : ∀ j z, mark j z = true →
      ENNReal.ofReal (w j / ((J : ℝ) * K₁)) ≤ μ {p | tag p.1 = j ∧ p.2 ∈ timeCell J z})
    {Q : ℝ≥0∞} (hcell : ∀ (q : Fin 2 → ℤ) (i' : ℤ),
      μ {p | meshCode b σ p = q ∧ ⌊curveX b p.1 p.2 / ρ⌋ = i'} ≤ Q)
    (i : ℤ) (Ksl : Set ℝ) (q : ℝ × ℝ) :
    ∑ j, (tagWindow σ ρ b₀ mark j i Ksl).indicator (fun _ => ENNReal.ofReal (w j)) q ≤
      ENNReal.ofReal ((J : ℝ) * K₁) *
        ((3 * ((2 * (⌈K⌉₊ + 5) + 1) * (2 * (3 * ⌈K⌉₊ + 9) + 1)) : ℕ) : ℝ≥0∞) * Q := by
  have hJ : (0 : ℝ) < J := by
    by_contra h
    rw [not_lt] at h
    have : (J : ℝ) * σ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hσ.le
    linarith
  rw [← card_pureCells ⌊q.1 / σ⌋ ⌊q.2 / σ⌋ i ⌈K⌉₊]
  refine weight_sum_le_of_cover htag (mul_pos hJ hK₁) hmark (fun j hj => hj.1) _
    (pureCellSet b σ ρ) (fun c _ => hcell _ _) ?_
  intro j hj z htz p hpj hpz
  obtain ⟨h1, h2, h3⟩ := cover_pure hK hσ hσ1 hδσ hσρ hJσ hb hround hj htz hpj hpz
  refine ⟨(⌊p.2 / σ⌋, ⌊curveY b p.1 p.2 / σ⌋, ⌊curveX b p.1 p.2 / ρ⌋), ?_, rfl, rfl⟩
  simp only [pureCells, Finset.mem_product]
  exact ⟨h1, h2, h3⟩

/-- The original cells met by the tags of an angular window. -/
def angCells (a0 a1 i k : ℤ) (L : ℕ) : Finset (ℤ × ℤ × ℤ × ℤ) :=
  Finset.Icc (a0 - ((1 : ℕ) : ℤ)) (a0 + ((1 : ℕ) : ℤ)) ×ˢ
    (Finset.Icc (a1 - ((L + 5 : ℕ) : ℤ)) (a1 + ((L + 5 : ℕ) : ℤ)) ×ˢ
      (Finset.Icc (i - ((3 * L + 9 : ℕ) : ℤ)) (i + ((3 * L + 9 : ℕ) : ℤ)) ×ˢ
        Finset.Icc (k - ((2 : ℕ) : ℤ)) (k + ((2 : ℕ) : ℤ))))

theorem card_angCells (a0 a1 i k : ℤ) (L : ℕ) :
    (angCells a0 a1 i k L).card =
      3 * ((2 * (L + 5) + 1) * ((2 * (3 * L + 9) + 1) * (2 * 2 + 1))) := by
  simp only [angCells, Finset.card_product, card_Icc_sym]

/-- The original angular cell `c` at scales `(σ, σ, a)` with slope bin of width `ρu`. -/
def angCellSet {α : Type*} (b : α → Coeff) (σ a ρu : ℝ) (c : ℤ × ℤ × ℤ × ℤ) : Set (α × ℝ) :=
  {p | meshCode b σ p = ![c.1, c.2.1] ∧ ⌊curveX b p.1 p.2 / a⌋ = c.2.2.1 ∧
    ⌊b p.1 1 / ρu⌋ = c.2.2.2}

/-- The original slope of a tag whose noisy slope reaches bin `k` lies within two bins. -/
theorem slope_floor_mem {bl β : ℝ} {σ δ ρu : ℝ} {k : ℤ} (hσρu : σ ≤ ρu) (hρu : 0 < ρu)
    (hδσ : δ ≤ σ) (hr : |bl - β| ≤ δ) (hv : ∃ v ∈ Icc 0 σ, β + v ∈ {v : ℝ | ⌊v / ρu⌋ = k}) :
    ⌊bl / ρu⌋ ∈ Finset.Icc (k - ((2 : ℕ) : ℤ)) (k + ((2 : ℕ) : ℤ)) := by
  obtain ⟨v, ⟨hv0, hvσ⟩, hvk⟩ := hv
  simp only [mem_ofPred_eq] at hvk
  have hf1 := Int.floor_le ((β + v) / ρu)
  have hf2 := Int.lt_floor_add_one ((β + v) / ρu)
  rw [hvk, le_div_iff₀ hρu] at hf1
  rw [hvk, div_lt_iff₀ hρu] at hf2
  rw [abs_le] at hr
  rw [Finset.mem_Icc]
  push_cast
  constructor
  · rw [Int.le_floor, le_div_iff₀ hρu]
    push_cast
    nlinarith
  · rw [← Int.lt_add_one_iff, Int.floor_lt, div_lt_iff₀ hρu]
    push_cast
    nlinarith

theorem weight_sum_le_ang {α : Type*} [MeasurableSpace α] {μ : Measure (α × ℝ)}
    {b : α → Coeff} {H J : ℕ} {tag : α → Fin H} (htag : Measurable tag) {b₀ : Fin H → Coeff}
    {w : Fin H → ℝ} {mark : Fin H → Fin J → Bool} {K K₁ σ δ a ρu : ℝ} (hK : 1 ≤ K)
    (hK₁ : 0 < K₁) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hδσ : δ ≤ σ) (hσa : σ ≤ a) (hσρu : σ ≤ ρu)
    (hJσ : 1 ≤ (J : ℝ) * σ)
    (hb : ∀ l e, |b l e| ≤ K) (hround : ∀ l e, |b l e - b₀ (tag l) e| ≤ δ)
    (hmark : ∀ j z, mark j z = true →
      ENNReal.ofReal (w j / ((J : ℝ) * K₁)) ≤ μ {p | tag p.1 = j ∧ p.2 ∈ timeCell J z})
    {Q : ℝ≥0∞} (hcell : ∀ (q : Fin 2 → ℤ) (i' k' : ℤ),
      μ {p | meshCode b σ p = q ∧ ⌊curveX b p.1 p.2 / a⌋ = i' ∧ ⌊b p.1 1 / ρu⌋ = k'} ≤ Q)
    (i k : ℤ) (q : ℝ × ℝ) :
    ∑ j, (tagWindow σ a b₀ mark j i {v | ⌊v / ρu⌋ = k}).indicator
        (fun _ => ENNReal.ofReal (w j)) q ≤
      ENNReal.ofReal ((J : ℝ) * K₁) *
        ((3 * ((2 * (⌈K⌉₊ + 5) + 1) * ((2 * (3 * ⌈K⌉₊ + 9) + 1) * (2 * 2 + 1))) : ℕ) :
          ℝ≥0∞) * Q := by
  have hJ : (0 : ℝ) < J := by
    by_contra h
    rw [not_lt] at h
    have : (J : ℝ) * σ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hσ.le
    linarith
  have hρu : 0 < ρu := hσ.trans_le hσρu
  rw [← card_angCells ⌊q.1 / σ⌋ ⌊q.2 / σ⌋ i k ⌈K⌉₊]
  refine weight_sum_le_of_cover htag (mul_pos hJ hK₁) hmark (fun j hj => hj.1) _
    (angCellSet b σ a ρu) (fun c _ => hcell _ _ _) ?_
  intro j hj z htz p hpj hpz
  obtain ⟨h1, h2, h3⟩ := cover_pure hK hσ hσ1 hδσ hσa hJσ hb hround hj htz hpj hpz
  have h4 : ⌊b p.1 1 / ρu⌋ ∈ Finset.Icc (k - ((2 : ℕ) : ℤ)) (k + ((2 : ℕ) : ℤ)) := by
    have hr : |b p.1 1 - b₀ j 1| ≤ δ := by rw [← hpj]; exact hround p.1 1
    exact slope_floor_mem hσρu hρu hδσ hr hj.2.2.2.2.2
  refine ⟨(⌊p.2 / σ⌋, ⌊curveY b p.1 p.2 / σ⌋, ⌊curveX b p.1 p.2 / a⌋, ⌊b p.1 1 / ρu⌋), ?_,
    rfl, rfl, rfl⟩
  simp only [angCells, Finset.mem_product]
  exact ⟨h1, h2, h3, h4⟩

end Submission.Obl.k4_scalar_marked_coefficient_smoothing.Raw
