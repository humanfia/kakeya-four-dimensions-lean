import Submission.Obl.k4_scalar_marked_coefficient_smoothing.RawCeiling

/-!
# Tag weights near a base point

A tag whose window contains a base point `(t, y)` was marked at the time cell of `t`, so its
weight is at most `J K₁` times the original active mass of that tag in that cell.  Every
original trajectory of the tag lies, in that cell, within `O(K σ)` of the noisy base point and
of the hidden bin, so all this original mass sits in `O(K²)` original mesh cells, whose masses
are capped by the original law.

The trace estimates are those of `original_near` of x0215's
`Submission/Lib/K4ScalarMeshSmoothing.lean` (o062, branch x0215), redone with the constants
needed here.
-/

namespace Submission.Obl.k4_scalar_marked_coefficient_smoothing.Raw

open MeasureTheory Set
open scoped ENNReal

/-! ### Elementary trace estimates -/

theorem abs_coeff_le_of_round {b β : Coeff} {K δ : ℝ} (hb : ∀ e, |b e| ≤ K)
    (hround : ∀ e, |b e - β e| ≤ δ) (e : Fin 5) : |β e| ≤ K + δ := by
  have h1 := hb e
  have h2 := hround e
  calc |β e| = |b e - (b e - β e)| := by ring_nf
    _ ≤ |b e| + |b e - β e| := abs_sub _ _
    _ ≤ K + δ := add_le_add h1 h2

/-- The base trace of an original trajectory at `t'` is within `(K + 3) σ` of the rounded
trace at `t`. -/
theorem traceY_close {b β : Coeff} {K σ δ t t' : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hδσ : δ ≤ σ)
    (hb : ∀ e, |b e| ≤ K) (hround : ∀ e, |b e - β e| ≤ δ)
    (ht0' : 0 ≤ t') (ht1' : t' ≤ 1) (htt : |t' - t| ≤ σ) :
    |(b 0 + t' * b 1) - (β 0 + t * β 1)| ≤ (K + 3) * σ := by
  have hβ1 := abs_coeff_le_of_round hb hround 1
  have h0 := hround 0
  have h1 := hround 1
  have hδ : 0 ≤ δ := (abs_nonneg _).trans h0
  have e : (b 0 + t' * b 1) - (β 0 + t * β 1) =
      (b 0 - β 0) + t' * (b 1 - β 1) + (t' - t) * β 1 := by ring
  rw [e]
  have hA : |t' * (b 1 - β 1)| ≤ δ := by
    rw [abs_mul, abs_of_nonneg ht0']
    calc t' * |b 1 - β 1| ≤ 1 * δ := mul_le_mul ht1' h1 (abs_nonneg _) zero_le_one
      _ = δ := one_mul δ
  have hB : |(t' - t) * β 1| ≤ σ * (K + δ) := by
    rw [abs_mul]; exact mul_le_mul htt hβ1 (abs_nonneg _) hσ
  have hσδ : σ * δ ≤ σ * 1 := mul_le_mul_of_nonneg_left (hδσ.trans hσ1) hσ
  calc |(b 0 - β 0) + t' * (b 1 - β 1) + (t' - t) * β 1|
      ≤ |b 0 - β 0| + |t' * (b 1 - β 1)| + |(t' - t) * β 1| := abs_add_three _ _ _
    _ ≤ δ + δ + σ * (K + δ) := add_le_add (add_le_add h0 hA) hB
    _ ≤ (K + 3) * σ := by nlinarith

/-- The hidden trace of an original trajectory at `t'` is within `(3K + 6) σ` of the rounded
trace at `t`. -/
theorem traceX_close {b β : Coeff} {K σ δ t t' : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hδσ : δ ≤ σ)
    (hb : ∀ e, |b e| ≤ K) (hround : ∀ e, |b e - β e| ≤ δ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ht0' : 0 ≤ t') (ht1' : t' ≤ 1) (htt : |t' - t| ≤ σ) :
    |(b 2 + t' * b 3 + t' ^ 2 * b 4) - (β 2 + t * β 3 + t ^ 2 * β 4)| ≤ (3 * K + 6) * σ := by
  have hβ3 := abs_coeff_le_of_round hb hround 3
  have hβ4 := abs_coeff_le_of_round hb hround 4
  have h2 := hround 2
  have h3 := hround 3
  have h4 := hround 4
  have hδ : 0 ≤ δ := (abs_nonneg _).trans h2
  have e : (b 2 + t' * b 3 + t' ^ 2 * b 4) - (β 2 + t * β 3 + t ^ 2 * β 4) =
      ((b 2 - β 2) + t' * (b 3 - β 3)) + (t' ^ 2 * (b 4 - β 4) + (t' - t) * β 3) +
        (t' - t) * ((t' + t) * β 4) := by ring
  rw [e]
  have hA : |t' * (b 3 - β 3)| ≤ δ := by
    rw [abs_mul, abs_of_nonneg ht0']
    calc t' * |b 3 - β 3| ≤ 1 * δ := mul_le_mul ht1' h3 (abs_nonneg _) zero_le_one
      _ = δ := one_mul δ
  have hB : |t' ^ 2 * (b 4 - β 4)| ≤ δ := by
    have ht2 : t' ^ 2 ≤ 1 := by nlinarith
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc t' ^ 2 * |b 4 - β 4| ≤ 1 * δ := mul_le_mul ht2 h4 (abs_nonneg _) zero_le_one
      _ = δ := one_mul δ
  have hC : |(t' - t) * β 3| ≤ σ * (K + δ) := by
    rw [abs_mul]; exact mul_le_mul htt hβ3 (abs_nonneg _) hσ
  have hD : |(t' - t) * ((t' + t) * β 4)| ≤ σ * (2 * (K + δ)) := by
    have hsum : |t' + t| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    rw [abs_mul, abs_mul]
    refine mul_le_mul htt ?_ (by positivity) hσ
    exact mul_le_mul hsum hβ4 (abs_nonneg _) zero_le_two
  have hσδ : σ * δ ≤ σ * 1 := mul_le_mul_of_nonneg_left (hδσ.trans hσ1) hσ
  calc |((b 2 - β 2) + t' * (b 3 - β 3)) + (t' ^ 2 * (b 4 - β 4) + (t' - t) * β 3) +
        (t' - t) * ((t' + t) * β 4)|
      ≤ (|b 2 - β 2| + |t' * (b 3 - β 3)|) + (|t' ^ 2 * (b 4 - β 4)| + |(t' - t) * β 3|) +
          |(t' - t) * ((t' + t) * β 4)| := by
        refine (abs_add_three _ _ _).trans ?_
        gcongr
        · exact abs_add_le _ _
        · exact abs_add_le _ _
    _ ≤ (δ + δ) + (δ + σ * (K + δ)) + σ * (2 * (K + δ)) := by gcongr
    _ ≤ (3 * K + 6) * σ := by nlinarith

/-- A real within `R` of `b` has its floor within `R` of `⌊b⌋`. -/
theorem floor_mem_Icc_of_abs_sub_le {a b : ℝ} {R : ℤ} (h : |a - b| ≤ R) :
    ⌊a⌋ ∈ Finset.Icc (⌊b⌋ - R) (⌊b⌋ + R) := by
  rw [abs_le] at h
  rw [Finset.mem_Icc]
  constructor
  · rw [← Int.floor_sub_intCast]; exact Int.floor_mono (by linarith)
  · rw [← Int.floor_add_intCast]; exact Int.floor_mono (by linarith)

theorem card_Icc_sym (c : ℤ) (R : ℕ) : (Finset.Icc (c - R) (c + R)).card = 2 * R + 1 := by
  rw [Int.card_Icc]; omega

/-! ### Summing tag weights over a cover by original cells -/

/-- If every original incidence of a selected tag in the time cell of `t` lies in one of the
cells `cellSet c`, `c ∈ Cells`, each of `μ`-mass at most `Q`, then the selected weights sum to
at most `J K₁ |Cells| Q`. -/
theorem weight_sum_le_of_cover {α : Type*} [MeasurableSpace α] {μ : Measure (α × ℝ)}
    {H J : ℕ} {tag : α → Fin H} (htag : Measurable tag) {w : Fin H → ℝ}
    {mark : Fin H → Fin J → Bool} {K₁ : ℝ} (hJK : 0 < (J : ℝ) * K₁)
    (hmark : ∀ j z, mark j z = true →
      ENNReal.ofReal (w j / ((J : ℝ) * K₁)) ≤ μ {p | tag p.1 = j ∧ p.2 ∈ timeCell J z})
    {T : Fin H → Set (ℝ × ℝ)} {q : ℝ × ℝ} (hT : ∀ j, q ∈ T j → q.1 ∈ markTimes mark j)
    {X : Type*} (Cells : Finset X) (cellSet : X → Set (α × ℝ)) {Q : ℝ≥0∞}
    (hQ : ∀ c ∈ Cells, μ (cellSet c) ≤ Q)
    (hcover : ∀ j, q ∈ T j → ∀ z : Fin J, q.1 ∈ timeCell J z → ∀ p : α × ℝ, tag p.1 = j →
      p.2 ∈ timeCell J z → ∃ c ∈ Cells, p ∈ cellSet c) :
    ∑ j, (T j).indicator (fun _ => ENNReal.ofReal (w j)) q ≤
      ENNReal.ofReal ((J : ℝ) * K₁) * Cells.card * Q := by
  classical
  have hz : ∀ j, ∃ z : Fin J, q ∈ T j → mark j z = true ∧ q.1 ∈ timeCell J z := by
    intro j
    by_cases hj : q ∈ T j
    · obtain ⟨z, hz1, hz2⟩ := hT j hj
      exact ⟨z, fun _ => ⟨hz1, hz2⟩⟩
    · have hJ : 0 < J := by
        rcases Nat.eq_zero_or_pos J with h | h
        · simp [h] at hJK
        · exact h
      exact ⟨⟨0, hJ⟩, fun h => absurd h hj⟩
  choose zf hzf using hz
  set Sel := Finset.univ.filter (fun j => q ∈ T j) with hSel
  set E : Fin H → Set (α × ℝ) := fun j => {p | tag p.1 = j ∧ p.2 ∈ timeCell J (zf j)} with hE
  have hEm : ∀ j, MeasurableSet (E j) := fun j =>
    ((measurableSet_singleton j).preimage (htag.comp measurable_fst)).inter
      ((measurableSet_timeCell J (zf j)).preimage measurable_snd)
  have h1 : ∑ j, (T j).indicator (fun _ => ENNReal.ofReal (w j)) q =
      ∑ j ∈ Sel, ENNReal.ofReal (w j) := by
    rw [hSel, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Set.indicator_apply]
  have h2 : ∀ j ∈ Sel, ENNReal.ofReal (w j) ≤ ENNReal.ofReal ((J : ℝ) * K₁) * μ (E j) := by
    intro j hj
    have hj' : q ∈ T j := (Finset.mem_filter.mp hj).2
    have hm := hmark j (zf j) (hzf j hj').1
    have hne : (J : ℝ) * K₁ ≠ 0 := hJK.ne'
    calc ENNReal.ofReal (w j) = ENNReal.ofReal ((J : ℝ) * K₁ * (w j / ((J : ℝ) * K₁))) := by
          rw [mul_div_cancel₀ _ hne]
      _ = ENNReal.ofReal ((J : ℝ) * K₁) * ENNReal.ofReal (w j / ((J : ℝ) * K₁)) :=
          ENNReal.ofReal_mul hJK.le
      _ ≤ ENNReal.ofReal ((J : ℝ) * K₁) * μ (E j) := by gcongr
  have hdisj : (Sel : Set (Fin H)).PairwiseDisjoint E := by
    intro j _ j' _ hjj'
    refine Set.disjoint_left.mpr ?_
    rintro p ⟨hp1, -⟩ ⟨hp2, -⟩
    exact hjj' (hp1.symm.trans hp2)
  have h3 : ∑ j ∈ Sel, μ (E j) = μ (⋃ j ∈ Sel, E j) :=
    (measure_biUnion_finset hdisj (fun j _ => hEm j)).symm
  have h4 : (⋃ j ∈ Sel, E j) ⊆ ⋃ c ∈ Cells, cellSet c := by
    intro p hp
    simp only [mem_iUnion] at hp ⊢
    obtain ⟨j, hj, hpj, hpz⟩ := hp
    have hj' : q ∈ T j := (Finset.mem_filter.mp hj).2
    obtain ⟨c, hc, hpc⟩ := hcover j hj' (zf j) (hzf j hj').2 p hpj hpz
    exact ⟨c, hc, hpc⟩
  have h5 : μ (⋃ c ∈ Cells, cellSet c) ≤ Cells.card * Q := by
    calc μ (⋃ c ∈ Cells, cellSet c) ≤ ∑ c ∈ Cells, μ (cellSet c) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _c ∈ Cells, Q := Finset.sum_le_sum hQ
      _ = Cells.card * Q := by rw [Finset.sum_const, nsmul_eq_mul]
  calc ∑ j, (T j).indicator (fun _ => ENNReal.ofReal (w j)) q
      = ∑ j ∈ Sel, ENNReal.ofReal (w j) := h1
    _ ≤ ∑ j ∈ Sel, ENNReal.ofReal ((J : ℝ) * K₁) * μ (E j) := Finset.sum_le_sum h2
    _ = ENNReal.ofReal ((J : ℝ) * K₁) * μ (⋃ j ∈ Sel, E j) := by rw [← Finset.mul_sum, h3]
    _ ≤ ENNReal.ofReal ((J : ℝ) * K₁) * (Cells.card * Q) := by
        gcongr
        exact (measure_mono h4).trans h5
    _ = ENNReal.ofReal ((J : ℝ) * K₁) * Cells.card * Q := by ring

/-! ### The covers -/

/-- The common geometric setting: an original trajectory `p` of tag `j`, in the same marked
time cell as a base point `q` of the window of `j`. -/
theorem cover_pure {α : Type*} {b : α → Coeff} {H J : ℕ} {tag : α → Fin H}
    {b₀ : Fin H → Coeff} {mark : Fin H → Fin J → Bool} {K σ δ ρ : ℝ} (hK : 1 ≤ K)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hδσ : δ ≤ σ) (hσρ : σ ≤ ρ) (hJσ : 1 ≤ (J : ℝ) * σ)
    (hb : ∀ l e, |b l e| ≤ K) (hround : ∀ l e, |b l e - b₀ (tag l) e| ≤ δ)
    {j : Fin H} {i : ℤ} {Ksl : Set ℝ} {q : ℝ × ℝ} (hq : q ∈ tagWindow σ ρ b₀ mark j i Ksl)
    {z : Fin J} (htz : q.1 ∈ timeCell J z) {p : α × ℝ} (hpj : tag p.1 = j)
    (hpz : p.2 ∈ timeCell J z) :
    ⌊p.2 / σ⌋ ∈ Finset.Icc (⌊q.1 / σ⌋ - ((1 : ℕ) : ℤ)) (⌊q.1 / σ⌋ + ((1 : ℕ) : ℤ)) ∧
    ⌊curveY b p.1 p.2 / σ⌋ ∈
      Finset.Icc (⌊q.2 / σ⌋ - ((⌈K⌉₊ + 5 : ℕ) : ℤ)) (⌊q.2 / σ⌋ + ((⌈K⌉₊ + 5 : ℕ) : ℤ)) ∧
    ⌊curveX b p.1 p.2 / ρ⌋ ∈
      Finset.Icc (i - ((3 * ⌈K⌉₊ + 9 : ℕ) : ℤ)) (i + ((3 * ⌈K⌉₊ + 9 : ℕ) : ℤ)) := by
  have hρ : 0 < ρ := hσ.trans_le hσρ
  have hJ : (0 : ℝ) < J := by exact_mod_cast (Nat.zero_lt_of_lt z.isLt)
  have hJinv : 1 / (J : ℝ) ≤ σ := by
    rw [div_le_iff₀ hJ]; linarith
  have htt : |p.2 - q.1| ≤ σ := (abs_sub_lt_of_mem_timeCell hpz htz).le.trans hJinv
  have ht := timeCell_subset z htz
  have ht' := timeCell_subset z hpz
  have hbl : ∀ e, |b p.1 e| ≤ K := hb p.1
  have hrl : ∀ e, |b p.1 e - b₀ j e| ≤ δ := by rw [← hpj]; exact hround p.1
  obtain ⟨-, hx1, hx2, hy1, hy2, -⟩ := hq
  have hKc : K ≤ (⌈K⌉₊ : ℝ) := Nat.le_ceil K
  refine ⟨?_, ?_, ?_⟩
  · apply floor_mem_Icc_of_abs_sub_le
    rw [← sub_div, abs_div, abs_of_pos hσ, div_le_iff₀ hσ]
    push_cast; linarith
  · apply floor_mem_Icc_of_abs_sub_le
    have hY := traceY_close hσ.le hσ1 hδσ hbl hrl ht'.1 ht'.2.le htt
    have hY' : |curveY b p.1 p.2 - q.2| ≤ (K + 5) * σ := by
      have e : curveY b p.1 p.2 - q.2 =
          ((b p.1 0 + p.2 * b p.1 1) - (b₀ j 0 + q.1 * b₀ j 1)) +
            (curveY b₀ j q.1 - q.2) := by simp only [curveY]; ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      have : |curveY b₀ j q.1 - q.2| ≤ 2 * σ := by
        rw [abs_le]; constructor <;> linarith
      linarith
    rw [← sub_div, abs_div, abs_of_pos hσ, div_le_iff₀ hσ]
    push_cast
    nlinarith
  · have hX := traceX_close hσ.le hσ1 hδσ hbl hrl ht.1 ht.2.le ht'.1 ht'.2.le htt
    have hXe : curveX b p.1 p.2 = b p.1 2 + p.2 * b p.1 3 + p.2 ^ 2 * b p.1 4 := rfl
    have hX0 : curveX b₀ j q.1 = b₀ j 2 + q.1 * b₀ j 3 + q.1 ^ 2 * b₀ j 4 := rfl
    rw [← hXe, ← hX0, abs_le] at hX
    have hKσ : (3 * K + 6) * σ ≤ (3 * K + 6) * ρ := mul_le_mul_of_nonneg_left hσρ (by linarith)
    have h3σ : 3 * σ ≤ 3 * ρ := by linarith
    rw [Finset.mem_Icc]
    push_cast
    constructor
    · rw [Int.le_floor]
      push_cast
      rw [le_div_iff₀ hρ]
      nlinarith
    · rw [← Int.lt_add_one_iff, Int.floor_lt]
      push_cast
      rw [div_lt_iff₀ hρ]
      nlinarith

end Submission.Obl.k4_scalar_marked_coefficient_smoothing.Raw
