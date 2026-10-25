-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.ContactGridCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactGrid

noncomputable section

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set MeasureTheory
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- The physical patch belonging to a quantized contact cell. -/
def contactPatch (f₀ : ℝ → ℝ) (δ s ℓ w : ℝ) (t : ℤ × ℤ × ℤ) : Set (ℝ × ℝ) :=
  shearRect f₀ (w + t.1 * ℓ) ℓ (t.2.1 * δ) (t.2.2 * s) (150 * δ)

/-- A cell has a witness from each color and a tagged contact in the slope band. -/
def ContactCellWitness {n : ℕ} (A B : Finset (Fin n)) (g : Fin n → ℝ → ℝ)
    (f₀ : ℝ → ℝ) (δ lower s ℓ w a b : ℝ) (t : ℤ × ℤ × ℤ) : Prop :=
  ∃ i ∈ A, ∃ j ∈ B, ∃ x ∈ Icc a b,
    |x - (w + t.1 * ℓ)| ≤ ℓ ∧ NearContact (2 * δ) s (g i) (g j) x ∧
    lower ≤ |deriv (g i) x - deriv (g j) x| ∧
    JetCell (g i) f₀ δ s ℓ w 42 t ∧ JetCell (g j) f₀ δ s ℓ w 42 t

private theorem exists_scaled_round (x : ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ k : ℤ, |x - k * h| ≤ h / 2 := by
  refine ⟨round (x / h), ?_⟩
  have hround := abs_sub_round (x / h)
  have heq : x - round (x / h) * h = (x / h - round (x / h)) * h := by field_simp
  rw [heq, abs_mul, abs_of_pos hh]
  have hm := mul_le_mul_of_nonneg_right hround hh.le
  linarith

/-- Round the jet of one curve; any near-contacting curve occupies the same
enlarged value/slope cell. -/
theorem exists_common_jetCell {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i j i₀ : Fin n) {δ s ℓ w D x : ℝ} (k : ℤ)
    (hδ : 0 < δ) (hs : 0 < s) (hℓ : 0 ≤ ℓ) (hD : 0 ≤ D)
    (hdist : dist (q i) (q j) ≤ 2 * D)
    (hx : x ∈ Icc (-1 : ℝ) 1) (hw : w + k * ℓ ∈ Icc (-1 : ℝ) 1)
    (hnear : |x - (w + k * ℓ)| ≤ ℓ)
    (hlin : s * ℓ ≤ δ) (hcurv : D * ℓ ≤ s)
    (hc : NearContact (2 * δ) s (g i) (g j) x) :
    ∃ l m : ℤ, JetCell (g i) (g i₀) δ s ℓ w 42 (k, l, m) ∧
      JetCell (g j) (g i₀) δ s ℓ w 42 (k, l, m) := by
  let y := w + k * ℓ
  have hyx : |y - x| ≤ ℓ := by simpa only [abs_sub_comm] using hnear
  have hv := value_difference_near_contact hg hjet i j hw hx hc.2
  have hv' : |(g i y - g j y) - (g i x - g j x)| ≤ 39 * δ := by
    have hmul : (s + 19 * dist (q i) (q j) * |y - x|) * |y - x| ≤
        (s + 38 * D * ℓ) * ℓ := by
      apply mul_le_mul _ hyx (abs_nonneg _) (by positivity)
      apply add_le_add le_rfl
      exact mul_le_mul (by linarith) hyx (abs_nonneg _) (by positivity)
    have hcoef : s + 38 * D * ℓ ≤ 39 * s := by linarith
    have hbound := mul_le_mul_of_nonneg_right hcoef hℓ
    have hbound' : (s + 38 * D * ℓ) * ℓ ≤ 39 * δ := by nlinarith [hlin]
    exact hv.trans (hmul.trans hbound')
  have hval : |g i y - g j y| ≤ 41 * δ := by
    have ht := abs_sub_le (g i y - g j y) (g i x - g j x) 0
    simp only [sub_zero] at ht
    linarith [hc.1]
  have hsl := hjet.slope_difference_lipschitz hg i j hw hx
  have hsl' : |(deriv (g i) y - deriv (g j) y) -
      (deriv (g i) x - deriv (g j) x)| ≤ 38 * s := by
    have hm : 19 * dist (q i) (q j) * |y - x| ≤ 38 * D * ℓ :=
      mul_le_mul (by linarith) hyx (abs_nonneg _) (by positivity)
    exact hsl.trans (hm.trans (by linarith))
  have hslope : |deriv (g i) y - deriv (g j) y| ≤ 39 * s := by
    have ht := abs_sub_le (deriv (g i) y - deriv (g j) y)
      (deriv (g i) x - deriv (g j) x) 0
    simp only [sub_zero] at ht
    linarith [hc.2]
  obtain ⟨l, hl⟩ := exists_scaled_round (g i y - g i₀ y) hδ
  obtain ⟨m, hm⟩ := exists_scaled_round (deriv (g i) y - deriv (g i₀) y) hs
  refine ⟨l, m, ⟨?_, ?_⟩, ?_, ?_⟩
  · change |g i y - g i₀ y - l * δ| ≤ 42 * δ
    linarith
  · change |deriv (g i) y - deriv (g i₀) y - m * s| ≤ 42 * s
    linarith
  · change |g j y - g i₀ y - l * δ| ≤ 42 * δ
    have ht := abs_sub_le (g j y - g i₀ y - l * δ) (g i y - g i₀ y - l * δ) 0
    have heq : (g j y - g i₀ y - l * δ) - (g i y - g i₀ y - l * δ) =
        -(g i y - g j y) := by ring
    rw [heq, abs_neg] at ht
    simp only [sub_zero] at ht
    linarith
  · change |deriv (g j) y - deriv (g i₀) y - m * s| ≤ 42 * s
    have ht := abs_sub_le (deriv (g j) y - deriv (g i₀) y - m * s)
      (deriv (g i) y - deriv (g i₀) y - m * s) 0
    have heq : (deriv (g j) y - deriv (g i₀) y - m * s) -
        (deriv (g i) y - deriv (g i₀) y - m * s) =
        -(deriv (g i) y - deriv (g j) y) := by ring
    rw [heq, abs_neg] at ht
    simp only [sub_zero] at ht
    linarith

/-- The cell of a curve covers its strip throughout the cell's time window. -/
theorem mem_contactPatch_of_jetCell {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i i₀ : Fin n) {δ s ℓ w D : ℝ} (t : ℤ × ℤ × ℤ)
    (hδ : 0 ≤ δ) (hs : 0 ≤ s) (hℓ : 0 ≤ ℓ) (hD : 0 ≤ D)
    (hdist : dist (q i) (q i₀) ≤ 2 * D)
    (hw : w + t.1 * ℓ ∈ Icc (-1 : ℝ) 1)
    (hlin : s * ℓ ≤ δ) (hquad : D * ℓ ^ 2 ≤ δ)
    (hcell : JetCell (g i) (g i₀) δ s ℓ w 42 t) {p : ℝ × ℝ}
    (hp : p ∈ strip δ (g i)) (htime : |p.2 - (w + t.1 * ℓ)| ≤ ℓ) :
    p ∈ contactPatch (g i₀) δ s ℓ w t := by
  refine ⟨htime, ?_⟩
  have hf := jetCell_follows hg hjet i i₀ 42 t hδ hs hℓ hD hdist hw hlin hquad
    hcell p.2 hp.1 htime
  have ht := abs_sub_le
    (p.1 - g i₀ p.2 - (t.2.1 * δ + t.2.2 * s * (p.2 - (w + t.1 * ℓ))))
    (g i p.2 - g i₀ p.2 - (t.2.1 * δ + t.2.2 * s * (p.2 - (w + t.1 * ℓ)))) 0
  have heq : (p.1 - g i₀ p.2 - (t.2.1 * δ + t.2.2 * s * (p.2 - (w + t.1 * ℓ)))) -
      (g i p.2 - g i₀ p.2 - (t.2.1 * δ + t.2.2 * s * (p.2 - (w + t.1 * ℓ)))) =
      p.1 - g i p.2 := by ring
  rw [heq] at ht
  simp only [sub_zero] at ht
  change |p.1 - g i₀ p.2 - (t.2.1 * δ + t.2.2 * s * (p.2 - (w + t.1 * ℓ)))| ≤ 150 * δ
  norm_num at hf
  linarith [hp.2]

private def gridIndexWindow (x h : ℝ) (C : ℕ) : Finset ℤ :=
  Finset.Icc ⌈x / h - C⌉ ⌊x / h + C⌋

private theorem mem_gridIndexWindow {x h : ℝ} (hh : 0 < h) (C : ℕ) {j : ℤ}
    (hj : |x - j * h| ≤ C * h) : j ∈ gridIndexWindow x h C := by
  have hab := abs_le.mp hj
  have hlo : x / h - C ≤ j := by
    have hdiv : x / h ≤ j + C := (div_le_iff₀ hh).mpr (by nlinarith)
    linarith
  have hhi : (j : ℝ) ≤ x / h + C := by
    have hdiv : (j : ℝ) - C ≤ x / h := (le_div_iff₀ hh).mpr (by nlinarith)
    linarith
  exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr hlo, Int.le_floor.mpr hhi⟩

private def curveTimeCells (f f₀ : ℝ → ℝ) (δ s ℓ w : ℝ) (C : ℕ) (k : ℤ) :
    Finset (ℤ × ℤ × ℤ) :=
  ((gridIndexWindow (f (w + k * ℓ) - f₀ (w + k * ℓ)) δ C) ×ˢ
    (gridIndexWindow (deriv f (w + k * ℓ) - deriv f₀ (w + k * ℓ)) s C)).image
      (fun lm => (k, lm.1, lm.2))

private theorem mem_curveTimeCells {f f₀ : ℝ → ℝ} {δ s ℓ w : ℝ}
    (hδ : 0 < δ) (hs : 0 < s) (C : ℕ) {t : ℤ × ℤ × ℤ}
    (ht : JetCell f f₀ δ s ℓ w C t) : t ∈ curveTimeCells f f₀ δ s ℓ w C t.1 := by
  apply Finset.mem_image.mpr
  exact ⟨t.2, Finset.mem_product.mpr
    ⟨mem_gridIndexWindow hδ C ht.1, mem_gridIndexWindow hs C ht.2⟩, rfl⟩

/-- The portion of a strip union in one slope band has a finite grid cover.
Each cell retains actual curve-pair and contact-time witnesses. -/
theorem exists_contactCell_cover {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (A B : Finset (Fin n)) (i₀ : Fin n) (T : Finset ℤ)
    {δ lower s ℓ w D a b : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    (hℓ : 0 < ℓ) (hD : 0 ≤ D)
    (href : ∀ i ∈ A, dist (q i) (q i₀) ≤ 2 * D)
    (hcross : ∀ i ∈ A, ∀ j ∈ B, dist (q i) (q j) ≤ 2 * D)
    (hinterval : Icc a b ⊆ Icc (-1 : ℝ) 1)
    (hT : ∀ k ∈ T, w + k * ℓ ∈ Icc (-1 : ℝ) 1)
    (hcover : ∀ x ∈ Icc a b, ∃ k ∈ T, |x - (w + k * ℓ)| ≤ ℓ)
    (hlin : s * ℓ ≤ δ) (hcurv : D * ℓ ≤ s)
    (E : Set (ℝ × ℝ))
    (hE : ∀ p ∈ E, p.2 ∈ Icc a b ∧ ∃ i ∈ A, ∃ j ∈ B,
      |p.1 - g i p.2| ≤ δ ∧ |p.1 - g j p.2| ≤ δ ∧
      lower ≤ |deriv (g i) p.2 - deriv (g j) p.2| ∧
      |deriv (g i) p.2 - deriv (g j) p.2| ≤ s) :
    ∃ S : Finset (ℤ × ℤ × ℤ),
      (∀ t ∈ S, t.1 ∈ T ∧ ContactCellWitness A B g (g i₀) δ lower s ℓ w a b t) ∧
      E ⊆ ⋃ t ∈ S, contactPatch (g i₀) δ s ℓ w t ∧
      volume E ≤ ENNReal.ofReal (600 * δ * ℓ * S.card) := by
  classical
  let S₀ := A.biUnion (fun i => T.biUnion (fun k => curveTimeCells (g i) (g i₀) δ s ℓ w 42 k))
  let S := S₀.filter (fun t => t.1 ∈ T ∧ ContactCellWitness A B g (g i₀) δ lower s ℓ w a b t)
  have hquad : D * ℓ ^ 2 ≤ δ := by
    have hh := mul_le_mul_of_nonneg_right hcurv hℓ.le
    nlinarith [hlin]
  have hS : ∀ t ∈ S, t.1 ∈ T ∧ ContactCellWitness A B g (g i₀) δ lower s ℓ w a b t :=
    fun _ ht => (Finset.mem_filter.mp ht).2
  have hsub : E ⊆ ⋃ t ∈ S, contactPatch (g i₀) δ s ℓ w t := by
    intro p hp
    obtain ⟨hpI, i, hi, j, hj, hpi, hpj, hlo, hhi⟩ := hE p hp
    obtain ⟨k, hk, hpk⟩ := hcover p.2 hpI
    have hc : NearContact (2 * δ) s (g i) (g j) p.2 := by
      refine ⟨?_, hhi⟩
      have ht := abs_sub_le (g i p.2) p.1 (g j p.2)
      rw [abs_sub_comm (g i p.2) p.1] at ht
      linarith
    obtain ⟨l, m, hci, hcj⟩ := exists_common_jetCell hg hjet i j i₀ k hδ hs hℓ.le hD
      (hcross i hi j hj) (hinterval hpI) (hT k hk) hpk hlin hcurv hc
    have hmem : (k, l, m) ∈ S := by
      change (k, l, m) ∈ S₀.filter _
      rw [Finset.mem_filter]
      constructor
      · have hmemcell : (k, l, m) ∈ curveTimeCells (g i) (g i₀) δ s ℓ w 42 k :=
          @mem_curveTimeCells (g i) (g i₀) δ s ℓ w hδ hs 42 (k, l, m) hci
        have hmemtime : (k, l, m) ∈ T.biUnion
            (fun k => curveTimeCells (g i) (g i₀) δ s ℓ w 42 k) :=
          Finset.mem_biUnion.mpr ⟨k, hk, hmemcell⟩
        exact Finset.mem_biUnion.mpr ⟨i, hi, hmemtime⟩
      · exact ⟨hk, i, hi, j, hj, p.2, hpI, hpk, hc, hlo, hci, hcj⟩
    exact mem_iUnion₂.mpr ⟨(k, l, m), hmem,
      mem_contactPatch_of_jetCell hg hjet i i₀ (k, l, m) hδ.le hs.le hℓ.le hD
        (href i hi) (hT k hk) hlin hquad hci ⟨hinterval hpI, hpi⟩ hpk⟩
  refine ⟨S, hS, hsub, ?_⟩
  calc
    volume E ≤ volume (⋃ t ∈ S, contactPatch (g i₀) δ s ℓ w t) := measure_mono hsub
    _ ≤ ∑ t ∈ S, volume (contactPatch (g i₀) δ s ℓ w t) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _t ∈ S, ENNReal.ofReal (600 * δ * ℓ) := by
      apply Finset.sum_le_sum
      intro t ht
      have hv := volume_shearRect_le (hg i₀).continuous (w + t.1 * ℓ) ℓ
        (t.2.1 * δ) (t.2.2 * s) (150 * δ) (by positivity)
      convert hv using 1 <;> congr 1 <;> ring
    _ = ENNReal.ofReal (600 * δ * ℓ * S.card) := by
      rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      ring

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
