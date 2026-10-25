import Submission.Obl.k4_general_wide_layer_offset_comparison.Table.GoodData
import Submission.Obl.k4_general_wide_layer_offset_comparison.StoredOffsetCounts
import Submission.Obl.k4_general_wide_layer_offset_comparison.TrueFiberIncidences

/-!
# Geometric facts and counts for the compared table

On the pointwise good set, every realized entry has a bounded canonical
offset, every stored projected witness on the entry's short code lies in the
whole true fiber, and the fine offsets and reverse coarse labels are counted
by stored original witnesses under the original native band caps.
-/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial
open scoped ENNReal

noncomputable section

namespace Parent
namespace GoodTableData

variable {α : Type} [MeasurableSpace α] {p : Parent α} {k : ℕ} {r u v m H₀ Hf : ℝ}
  (t : p.GoodTableData k r u v m H₀ Hf)

theorem depth_succ (c : Fin 2) :
    (![r, r + u, r + v] : Fin 3 → ℝ) c.succ = r + (![u, v] : Fin 2 → ℝ) c := by
  fin_cases c <;> rfl

/-- The major bins of a labelled point are the label's tag. -/
theorem tag_eq {a : Fin 3} {i : Fin (t.layers a).count} {l : α}
    (hl : l ∈ (t.layers a).C i) :
    (![⌊p.b k l 3 / p.N k ^ (-m)⌋, ⌊p.b k l 0 / p.N k ^ (-m)⌋] : Fin 2 → ℤ) =
      (t.layers a).tag i := by
  have h := t.label_tags hl
  funext e
  fin_cases e
  · exact h.1
  · exact h.2

theorem tag_eq_of_mem {a b : Fin 3} {i : Fin (t.layers a).count} {j : Fin (t.layers b).count}
    {l : α} (hi : l ∈ (t.layers a).C i) (hj : l ∈ (t.layers b).C j) :
    (t.layers a).tag i = (t.layers b).tag j :=
  (t.tag_eq hi).symm.trans (t.tag_eq hj)

theorem shortComparisonCode_eq {a : Fin 3} {i : Fin (t.layers a).count} {ω : α × ℝ}
    (hl : ω.1 ∈ (t.layers a).C i) :
    p.shortComparisonCode k r m ω = ((t.layers a).tag i, p.shortDomainCode k r ω) := by
  have h := t.tag_eq hl
  simp only [shortComparisonCode, comparisonCode, shortDomainCode]
  rw [h]

/-- The original fit of a projected label at any unit-time point. -/
theorem fit_at {a : Fin 3} {i : Fin (t.layers a).count} {ω : α × ℝ}
    (hl : ω.1 ∈ (t.layers a).C i) (ht : ω.2 ∈ Icc (0 : ℝ) 1) :
    |eval (p.x k ω.1 ω.2) (p.P k) - eval ![ω.2, (p.x k ω.1 ω.2) 2] ((t.layers a).G i)| ≤
      H₀ * p.N k ^ (-(![r, r + u, r + v] : Fin 3 → ℝ) a) :=
  ((((t.layer_valid a).2.2.2.2.2.1 i).2.2.2.1 ω.1 hl).2.2 ω.2 ht).2

/-- A good incidence lies in the whole true fiber of its true label. -/
theorem point_mem_fiber {ω : α × ℝ} {Q : Fin (p.n k r)}
    (hQ : ω.1 ∈ p.B k r Q) (hQt : ω.2 ∈ block (p.T k r) (p.j k r Q))
    {i : Fin (t.layers 0).count} (hi : ω.1 ∈ (t.layers 0).C i)
    (hHf : 2 ≤ Hf) (hKHf : p.K k ≤ Hf) :
    ![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2] ∈
      p.trueFiberBox k r m Hf Q ((t.layers 0).tag i) := by
  have htag := t.label_tags hi
  exact AtDepth.base_mem_trueFiberBox p t.atDepth (N_pos t) hHf hKHf Q _ hQ htag.2 htag.1 hQt

include t in
theorem fine_scale_le (c : Fin 2) (hgain : 0 ≤ (![u, v] : Fin 2 → ℝ) c) :
    p.N k ^ (-r - (![u, v] : Fin 2 → ℝ) c) ≤ p.N k ^ (-r) :=
  Real.rpow_le_rpow_of_exponent_le t.N_one.le (by linarith)

/-- A realized entry has a canonical offset of coarse size. -/
theorem offset_abs_le (c : Fin 2) {ω : α × ℝ} (hω : ω ∈ t.good) {Q : Fin (p.n k r)}
    {i : Fin (t.layers 0).count} {j : Fin (t.layers c.succ).count}
    (hQ : ω.1 ∈ p.B k r Q) (hQt : ω.2 ∈ block (p.T k r) (p.j k r Q))
    (hi : ω.1 ∈ (t.layers 0).C i) (hj : ω.1 ∈ (t.layers c.succ).C j)
    (hHf : 2 ≤ Hf) (hKHf : p.K k ≤ Hf) (hH₀ : 1 ≤ H₀)
    (hgain : 0 ≤ (![u, v] : Fin 2 → ℝ) c) :
    |p.canonicalOffset k r m (t.layers 0) (t.layers c.succ) Q i j| ≤
      3 * H₀ * p.N k ^ (-r) := by
  have hz := t.point_mem_fiber hQ hQt hi hHf hKHf
  have hoff := t.good_offset ω hω c Q i j hQ hQt hi hj _ hz
  have ht : ω.2 ∈ Icc (0 : ℝ) 1 := (t.good_base ω hω).1
  have hfj := t.fit_at hj ht
  have hfi := t.fit_at hi ht
  rw [depth_succ, show -(r + (![u, v] : Fin 2 → ℝ) c) = -r - (![u, v] : Fin 2 → ℝ) c by ring]
    at hfj
  have hfj' : |eval (p.x k ω.1 ω.2) (p.P k) - eval ![ω.2, (p.x k ω.1 ω.2) 2]
      ((t.layers c.succ).G j)| ≤ H₀ * p.N k ^ (-r - (![u, v] : Fin 2 → ℝ) c) := hfj
  have hfi' : |eval (p.x k ω.1 ω.2) (p.P k) - eval ![ω.2, (p.x k ω.1 ω.2) 2]
      ((t.layers 0).G i)| ≤ H₀ * p.N k ^ (-r) := by
    simpa using hfi
  have hac := t.fine_scale_le c hgain
  have hNr : 0 ≤ p.N k ^ (-r) := (Real.rpow_pos_of_pos (N_pos t) _).le
  have hoff' : |eval ![ω.2, (p.x k ω.1 ω.2) 2] ((t.layers c.succ).G j) -
      eval ![ω.2, (p.x k ω.1 ω.2) 2] ((t.layers 0).G i) -
      p.canonicalOffset k r m (t.layers 0) (t.layers c.succ) Q i j| ≤
      p.N k ^ (-r - (![u, v] : Fin 2 → ℝ) c) := hoff
  set G₁ := eval ![ω.2, (p.x k ω.1 ω.2) 2] ((t.layers c.succ).G j)
  set G₀ := eval ![ω.2, (p.x k ω.1 ω.2) 2] ((t.layers 0).G i)
  set X := eval (p.x k ω.1 ω.2) (p.P k)
  set o := p.canonicalOffset k r m (t.layers 0) (t.layers c.succ) Q i j
  have h1 : |o| ≤ |G₁ - G₀ - o| + |X - G₁| + |X - G₀| := by
    have := abs_add_three (-(G₁ - G₀ - o)) (-(X - G₁)) (X - G₀)
    rw [abs_neg, abs_neg] at this
    calc |o| = |-(G₁ - G₀ - o) + -(X - G₁) + (X - G₀)| := by congr 1; ring
      _ ≤ _ := this
  calc
    |o| ≤ |G₁ - G₀ - o| + |X - G₁| + |X - G₀| := h1
    _ ≤ p.N k ^ (-r - (![u, v] : Fin 2 → ℝ) c) +
        H₀ * p.N k ^ (-r - (![u, v] : Fin 2 → ℝ) c) + H₀ * p.N k ^ (-r) :=
      add_le_add (add_le_add hoff' hfj') hfi'
    _ ≤ H₀ * p.N k ^ (-r) + H₀ * p.N k ^ (-r) + H₀ * p.N k ^ (-r) := by
      gcongr
      · exact hac.trans (le_mul_of_one_le_left hNr hH₀)
    _ = 3 * H₀ * p.N k ^ (-r) := by ring

/-- Every stored projected witness on the short code of a good incidence
lies in the whole true fiber of that incidence. -/
theorem witness_mem_fiber {ω : α × ℝ} (hω : ω ∈ t.good) {Q : Fin (p.n k r)}
    (hQ : ω.1 ∈ p.B k r Q) (hQt : ω.2 ∈ block (p.T k r) (p.j k r Q))
    {i : Fin (t.layers 0).count} (hi : ω.1 ∈ (t.layers 0).C i)
    {a : Fin 3} {l : Fin (t.layers a).count} (hl : ω.1 ∈ (t.layers a).C l)
    {ω' : α × ℝ} (hω' : ω' ∈ p.witnessSet k r (t.layers a) l (p.shortDomainCode k r ω))
    (hHf : 10 * p.K k ≤ Hf) :
    ![ω'.2, (p.x k ω'.1 ω'.2) 1, (p.x k ω'.1 ω'.2) 2] ∈
      p.trueFiberBox k r m Hf Q ((t.layers 0).tag i) := by
  obtain ⟨hbase', hl', hD'⟩ := hω'
  apply AtDepth.short_code_in_trueFiberBox p t.atDepth (N_pos t) t.K_one hHf t.chi_width Q
    ((t.layers 0).tag i) (p.shortDomainCode k r ω) ?_ (t.good_base ω hω) hQ ?_ hbase' ?_
  · have h := t.good_time ω hω Q hQt
    simpa only [shortDomainCode, domainCode, movingDomainCode] using h
  · exact t.shortComparisonCode_eq hi
  · rw [t.shortComparisonCode_eq hl', hD', t.tag_eq_of_mem hi hl]

theorem witnessSet_measurable (a : Fin 3) (l : Fin (t.layers a).count) (D : ℤ × ℤ × ℤ) :
    MeasurableSet (p.witnessSet k r (t.layers a) l D) := by
  have hb := Basic.measurableSet_baseGood p t.basic k
  have hC : MeasurableSet ((t.layers a).C l) := (t.layer_valid a).2.2.2.1 l
  have hD : MeasurableSet {ω : α × ℝ | p.shortDomainCode k r ω = D} :=
    (p.measurable_shortDomainCode t.basic k r) (measurableSet_singleton _)
  have h : p.witnessSet k r (t.layers a) l D =
      p.baseGood k ∩ (Prod.fst ⁻¹' (t.layers a).C l) ∩
        {ω : α × ℝ | p.shortDomainCode k r ω = D} := by
    ext ω
    simp only [witnessSet, mem_setOf_eq, mem_inter_iff, mem_preimage, and_assoc]
  rw [h]
  exact (hb.inter (measurable_fst hC)).inter hD

/-- Fine offsets with respect to one true label and one coarse label are
locally sparse: stored original fine witnesses on the short codes of the
true label sit in one native band, and their floors pay for each label. -/
theorem fine_offset_count (c : Fin 2) (Q : Fin (p.n k r)) (i : Fin (t.layers 0).count)
    (S : Finset (Fin (t.layers c.succ).count))
    (hS : ∀ j ∈ S, ∃ ω ∈ t.good, ω.1 ∈ p.B k r Q ∧ ω.2 ∈ block (p.T k r) (p.j k r Q) ∧
      ω.1 ∈ (t.layers 0).C i ∧ ω.1 ∈ (t.layers c.succ).C j)
    (hHf : 10 * p.K k ≤ Hf) (hH₀ : 1 ≤ H₀)
    (x δ' : ℝ) (hδ' : p.N k ^ (-r - (![u, v] : Fin 2 → ℝ) c) ≤ δ') :
    ((S.filter (fun j =>
        |p.canonicalOffset k r m (t.layers 0) (t.layers c.succ) Q i j - x| ≤ δ')).card : ℝ) ≤
      ((4 * p.K k + 5) * (6 * p.K k + 5) * (16800 * p.K k ^ 2)) * t.δ⁻¹ *
        (2 * H₀ + 1) ^ p.d * (δ' / p.N k ^ (-r - (![u, v] : Fin 2 → ℝ) c)) ^ p.d := by
  classical
  have hrhs : 0 ≤ ((4 * p.K k + 5) * (6 * p.K k + 5) * (16800 * p.K k ^ 2)) * t.δ⁻¹ *
      (2 * H₀ + 1) ^ p.d * (δ' / p.N k ^ (-r - (![u, v] : Fin 2 → ℝ) c)) ^ p.d := by
    have := K_nonneg t
    have := t.δ_pos
    have hNp := N_pos t
    have hδ'0 : 0 ≤ δ' := (Real.rpow_pos_of_pos hNp _).le.trans hδ'
    have : 0 ≤ 2 * H₀ + 1 := by linarith
    positivity
  rcases S.eq_empty_or_nonempty with hSe | ⟨j₀, hj₀⟩
  · simpa [hSe] using hrhs
  obtain ⟨ω₀, hω₀, -⟩ := hS j₀ hj₀
  have : Nonempty (α × ℝ) := ⟨ω₀⟩
  choose! ω hωgood hωQ hωt hωi hωj using hS
  set q := (2 : ℝ) ^ (-(p.T k r : ℤ)) with hq_def
  set g := p.N k ^ (-p.ℓ * r) with hg_def
  set χ := p.N k ^ (-m) with hχ_def
  set a := p.N k ^ (-r - (![u, v] : Fin 2 → ℝ) c) with ha_def
  set tg := (t.layers 0).tag i with htg_def
  have hN := N_pos t
  have hq : 0 < q := by rw [hq_def]; positivity
  have hg : 0 < g := by rw [hg_def]; positivity
  have hχ : 0 < χ := by rw [hχ_def]; positivity
  have ha : 0 < a := by rw [ha_def]; positivity
  have hK0 := K_nonneg t
  let Dof : Fin (t.layers c.succ).count → ℤ × ℤ × ℤ := fun j => p.shortDomainCode k r (ω j)
  let SD := S.image Dof
  let U : Set (α × ℝ) := {ω' | ω' ∈ p.baseGood k ∧ ∃ D ∈ SD,
    p.shortComparisonCode k r m ω' = (tg, D)}
  let E : Fin (t.layers c.succ).count → Set (α × ℝ) := fun j =>
    p.witnessSet k r (t.layers c.succ) j (Dof j)
  let J := q * χ * (q * g)
  let w := p.π k {w : ℝ | ⌊w / χ⌋ = tg 0}
  -- tags along the anchors
  have htagj (j : Fin (t.layers c.succ).count) (hj : j ∈ S) : (t.layers c.succ).tag j = tg :=
    (t.tag_eq_of_mem (hωi j hj) (hωj j hj)).symm
  have hfloor0 (j : Fin (t.layers c.succ).count) (hj : j ∈ S) :
      ⌊p.b k (ω j).1 3 / χ⌋ = tg 0 := (t.label_tags (hωi j hj)).1
  -- the domain menu is the true menu
  have hSD : SD ⊆ p.trueDomains k r m Q tg := by
    intro D hD
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hD
    exact t.domain_mem_trueDomains c (e := (Q, i, j, Dof j)) (hωgood j hj)
      ⟨hωQ j hj, hωt j hj, hωi j hj, hωj j hj, rfl⟩
  have hSDcard : (SD.card : ℝ) ≤ (4 * p.K k + 5) * (6 * p.K k + 5) :=
    (Nat.cast_le.mpr (Finset.card_le_card hSD)).trans
      (p.card_trueDomains_le k r m Q tg hK0)
  -- the palette weight
  have hw : w ≠ 0 := by
    have hpos := t.good_palette (ω j₀) (hωgood j₀ hj₀)
    rw [hfloor0 j₀ hj₀] at hpos
    exact hpos.ne'
  have hwtop : w ≠ ⊤ := by
    have := (t.basic k).2.2.1
    exact measure_ne_top _ _
  have hJ : 0 < J := by positivity
  have hK' : 0 < (4 * p.K k + 5) * (6 * p.K k + 5) * (16800 * p.K k ^ 2) := by
    have := t.K_one
    positivity
  have hsmax : p.N k ^ (-t.smax) ≤ a :=
    Real.rpow_le_rpow_of_exponent_le t.N_one.le (by linarith [t.smax_fine c])
  have hcap : ∀ x Δ : ℝ, a ≤ Δ →
      t.wit {ω' | ω' ∈ U ∧ |eval (p.x k ω'.1 ω'.2) (p.P k) -
        eval ![ω'.2, (p.x k ω'.1 ω'.2) 2] ((t.layers 0).G i) - x| ≤ Δ} ≤
      ENNReal.ofReal (((4 * p.K k + 5) * (6 * p.K k + 5) * (16800 * p.K k ^ 2)) * J *
        Δ ^ p.d) * w := by
    intro x Δ haΔ
    have hsub : {ω' | ω' ∈ U ∧ |eval (p.x k ω'.1 ω'.2) (p.P k) -
        eval ![ω'.2, (p.x k ω'.1 ω'.2) 2] ((t.layers 0).G i) - x| ≤ Δ} ⊆
        ⋃ D ∈ SD, p.comparisonBand k m q g (q * g) tg D ((t.layers 0).G i + C x) Δ := by
      rintro ω' ⟨⟨hb', D, hD, hcode⟩, hband⟩
      refine mem_iUnion₂.mpr ⟨D, hD, hb', hcode, ?_⟩
      simpa only [eval_add, eval_C, sub_sub] using hband
    have hdeg := ((t.layer_valid 0).2.2.2.2.2.1 i).2.1
    calc
      _ ≤ t.wit (⋃ D ∈ SD,
          p.comparisonBand k m q g (q * g) tg D ((t.layers 0).G i + C x) Δ) := measure_mono hsub
      _ ≤ ∑ D ∈ SD, t.wit
          (p.comparisonBand k m q g (q * g) tg D ((t.layers 0).G i + C x) Δ) :=
        measure_biUnion_finset_le SD _
      _ ≤ ∑ _D ∈ SD, ENNReal.ofReal
          (16800 * p.K k ^ 2 * χ * q * (q * g) * Δ ^ p.d) * w := by
        apply Finset.sum_le_sum
        intro D hD
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hD
        have hcapj := t.band_cap (ω j) (hωgood j hj) ((t.layers 0).G i) x Δ hdeg
          (t.coefficient_bound 0 i) (hsmax.trans haΔ)
        rw [t.tag_eq (hωi j hj), (t.label_tags (hωi j hj)).1] at hcapj
        exact hcapj
      _ = (SD.card : ℝ≥0∞) * (ENNReal.ofReal
          (16800 * p.K k ^ 2 * χ * q * (q * g) * Δ ^ p.d) * w) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal ((4 * p.K k + 5) * (6 * p.K k + 5)) * (ENNReal.ofReal
          (16800 * p.K k ^ 2 * χ * q * (q * g) * Δ ^ p.d) * w) := by
        refine mul_le_mul' ?_ le_rfl
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal hSDcard
      _ = _ := by
        have hΔ : 0 ≤ Δ := ha.le.trans haΔ
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        dsimp only [J]
        ring
  have hE : ∀ j ∈ S, MeasurableSet (E j) ∧ E j ⊆ U := by
    intro j hj
    refine ⟨t.witnessSet_measurable c.succ j (Dof j), ?_⟩
    rintro ω' ⟨hb', hl', hD'⟩
    refine ⟨hb', Dof j, Finset.mem_image_of_mem Dof hj, ?_⟩
    rw [t.shortComparisonCode_eq hl', hD', htagj j hj]
  have hdisj : (S : Set (Fin (t.layers c.succ).count)).PairwiseDisjoint E := by
    intro j _ j' _ hne
    apply Set.disjoint_left.mpr
    rintro ω' ⟨-, hl, -⟩ ⟨-, hl', -⟩
    exact hne (t.label_unique hl hl')
  have hfloor : ∀ j ∈ S, ENNReal.ofReal (J * a ^ p.d / t.δ⁻¹) * w ≤ t.wit (E j) := by
    intro j hj
    have h := t.good_witness (ω j) (hωgood j hj) c.succ j (hωj j hj)
    rw [htagj j hj, depth_succ, show -(r + (![u, v] : Fin 2 → ℝ) c) =
      -r - (![u, v] : Fin 2 → ℝ) c by ring] at h
    have heq : J * a ^ p.d / t.δ⁻¹ =
        t.δ * (q * χ * (q * g) * (p.N k ^ (-r - (![u, v] : Fin 2 → ℝ) c)) ^ p.d) := by
      dsimp only [J]
      rw [div_inv_eq_mul]
      ring
    rw [heq]
    exact h
  have hfit : ∀ j ∈ S, ∀ ω' ∈ E j, |eval (p.x k ω'.1 ω'.2) (p.P k) -
      eval ![ω'.2, (p.x k ω'.1 ω'.2) 2] ((t.layers c.succ).G j)| ≤ H₀ * a := by
    intro j hj ω' hω'
    have h := t.fit_at hω'.2.1 hω'.1.1
    rwa [depth_succ, show -(r + (![u, v] : Fin 2 → ℝ) c) =
      -r - (![u, v] : Fin 2 → ℝ) c by ring] at h
  have hcompare : ∀ j ∈ S, ∀ ω' ∈ E j,
      |eval ![ω'.2, (p.x k ω'.1 ω'.2) 2] ((t.layers c.succ).G j) -
        eval ![ω'.2, (p.x k ω'.1 ω'.2) 2] ((t.layers 0).G i) -
        p.canonicalOffset k r m (t.layers 0) (t.layers c.succ) Q i j| ≤ H₀ * a := by
    intro j hj ω' hω'
    have hz := t.witness_mem_fiber (hωgood j hj) (hωQ j hj) (hωt j hj) (hωi j hj)
      (hωj j hj) hω' hHf
    have h := t.good_offset (ω j) (hωgood j hj) c Q i j (hωQ j hj) (hωt j hj) (hωi j hj)
      (hωj j hj) _ hz
    exact h.trans (le_mul_of_one_le_left ha.le hH₀)
  exact stored_offset_local_count t.wit U E S
    (fun ω' => eval (p.x k ω'.1 ω'.2) (p.P k))
    (fun ω' => eval ![ω'.2, (p.x k ω'.1 ω'.2) 2] ((t.layers 0).G i))
    (fun j ω' => eval ![ω'.2, (p.x k ω'.1 ω'.2) 2] ((t.layers c.succ).G j))
    (fun j => p.canonicalOffset k r m (t.layers 0) (t.layers c.succ) Q i j)
    ha hJ hK' (inv_pos.mpr t.δ_pos) hH₀ w hw hwtop hcap hE hdisj hfloor hfit hcompare x δ' hδ'

/-- Coarse labels paired with one fine label on one short code are few:
their stored original coarse witnesses on that code all lie in one native
band around the fine polynomial, by the whole-fiber offsets. -/
theorem reverse_coarse_count (c : Fin 2) {ω₀ : α × ℝ} (hω₀ : ω₀ ∈ t.good)
    (j : Fin (t.layers c.succ).count) (hj₀ : ω₀.1 ∈ (t.layers c.succ).C j)
    (I : Finset (Fin (t.layers 0).count))
    (hI : ∀ i ∈ I, ∃ ω ∈ t.good, ∃ Q : Fin (p.n k r), ω.1 ∈ p.B k r Q ∧
      ω.2 ∈ block (p.T k r) (p.j k r Q) ∧ ω.1 ∈ (t.layers 0).C i ∧
      ω.1 ∈ (t.layers c.succ).C j ∧ p.shortDomainCode k r ω = p.shortDomainCode k r ω₀)
    (hHf : 10 * p.K k ≤ Hf) (hH₀ : 1 ≤ H₀) (hgain : 0 ≤ (![u, v] : Fin 2 → ℝ) c) :
    (I.card : ℝ) ≤ 16800 * p.K k ^ 2 * (5 * H₀) ^ p.d / t.δ := by
  classical
  have hK1 := t.K_one
  have hrhs : 0 ≤ 16800 * p.K k ^ 2 * (5 * H₀) ^ p.d / t.δ := by
    have := t.δ_pos
    have : 0 ≤ 5 * H₀ := by linarith
    positivity
  rcases I.eq_empty_or_nonempty with hIe | ⟨i₀, hi₀⟩
  · simpa [hIe] using hrhs
  obtain ⟨ω₁, hω₁, Q₁, -⟩ := hI i₀ hi₀
  have : Nonempty (α × ℝ) := ⟨ω₁⟩
  have : Nonempty (Fin (p.n k r)) := ⟨Q₁⟩
  choose! ω hωgood Q hωQ hωt hωi hωj hωD using hI
  set q := (2 : ℝ) ^ (-(p.T k r : ℤ)) with hq_def
  set g := p.N k ^ (-p.ℓ * r) with hg_def
  set χ := p.N k ^ (-m) with hχ_def
  set ar := p.N k ^ (-r) with har_def
  have hN := N_pos t
  have hq : 0 < q := by rw [hq_def]; positivity
  have hg : 0 < g := by rw [hg_def]; positivity
  have hχ : 0 < χ := by rw [hχ_def]; positivity
  have har : 0 < ar := by rw [har_def]; positivity
  have hHf2 : 2 ≤ Hf := by linarith
  have hKHf : p.K k ≤ Hf := by linarith
  set D₀ := p.shortDomainCode k r ω₀ with hD₀_def
  set tg₀ : Fin 2 → ℤ := ![⌊p.b k ω₀.1 3 / χ⌋, ⌊p.b k ω₀.1 0 / χ⌋] with htg₀_def
  have htg₀ : tg₀ = (t.layers c.succ).tag j := t.tag_eq hj₀
  have htagi (i : Fin (t.layers 0).count) (hi : i ∈ I) : (t.layers 0).tag i = tg₀ :=
    (t.tag_eq_of_mem (hωi i hi) (hωj i hi)).trans htg₀.symm
  let Δ := 5 * H₀ * ar
  let J := q * χ * (q * g)
  let U := p.comparisonBand k m q g (q * g) tg₀ D₀ ((t.layers c.succ).G j + C 0) Δ
  let E : Fin (t.layers 0).count → Set (α × ℝ) := fun i => p.witnessSet k r (t.layers 0) i D₀
  let w := p.π k {w : ℝ | ⌊w / χ⌋ = ⌊p.b k ω₀.1 3 / χ⌋}
  have hw : w ≠ 0 := (t.good_palette ω₀ hω₀).ne'
  have hwtop : w ≠ ⊤ := by
    have := (t.basic k).2.2.1
    exact measure_ne_top _ _
  have hJ : 0 < J := by positivity
  have hΔ : 0 < Δ := by positivity
  have hsmax : p.N k ^ (-t.smax) ≤ Δ := by
    have h1 : p.N k ^ (-t.smax) ≤ ar :=
      Real.rpow_le_rpow_of_exponent_le t.N_one.le (by linarith [t.smax_fine c])
    have h2 : ar ≤ Δ := by
      dsimp only [Δ]
      nlinarith
    exact h1.trans h2
  have hcap : t.wit U ≤ ENNReal.ofReal (16800 * p.K k ^ 2 * J * Δ ^ p.d) * w := by
    have h := t.band_cap ω₀ hω₀ ((t.layers c.succ).G j) 0 Δ
      ((t.layer_valid c.succ).2.2.2.2.2.1 j).2.1 (t.coefficient_bound c.succ j) hsmax
    refine h.trans (le_of_eq ?_)
    congr 2
    dsimp only [J]
    ring
  have hfit_fine : ∀ i ∈ I, ∀ ω' ∈ E i,
      |eval (p.x k ω'.1 ω'.2) (p.P k) - eval ![ω'.2, (p.x k ω'.1 ω'.2) 2]
        ((t.layers c.succ).G j + C 0)| ≤ Δ := by
    intro i hi ω' hω'
    have hω'' : ω' ∈ p.witnessSet k r (t.layers 0) i (p.shortDomainCode k r (ω i)) := by
      rw [hωD i hi]
      exact hω'
    have hz := t.witness_mem_fiber (hωgood i hi) (hωQ i hi) (hωt i hi) (hωi i hi) (hωi i hi)
      hω'' hHf
    have hoff := t.good_offset (ω i) (hωgood i hi) c (Q i) i j (hωQ i hi) (hωt i hi)
      (hωi i hi) (hωj i hi) _ hz
    have hoff' : |eval ![ω'.2, (p.x k ω'.1 ω'.2) 2] ((t.layers c.succ).G j) -
        eval ![ω'.2, (p.x k ω'.1 ω'.2) 2] ((t.layers 0).G i) -
        p.canonicalOffset k r m (t.layers 0) (t.layers c.succ) (Q i) i j| ≤
        p.N k ^ (-r - (![u, v] : Fin 2 → ℝ) c) := hoff
    have hob := t.offset_abs_le c (hωgood i hi) (hωQ i hi) (hωt i hi) (hωi i hi) (hωj i hi)
      hHf2 hKHf hH₀ hgain
    have hfi := t.fit_at hω'.2.1 hω'.1.1
    have hfi' : |eval (p.x k ω'.1 ω'.2) (p.P k) - eval ![ω'.2, (p.x k ω'.1 ω'.2) 2]
        ((t.layers 0).G i)| ≤ H₀ * ar := by simpa using hfi
    have hac := t.fine_scale_le c hgain
    rw [eval_add, eval_C, add_zero]
    set X := eval (p.x k ω'.1 ω'.2) (p.P k)
    set G₁ := eval ![ω'.2, (p.x k ω'.1 ω'.2) 2] ((t.layers c.succ).G j)
    set G₀ := eval ![ω'.2, (p.x k ω'.1 ω'.2) 2] ((t.layers 0).G i)
    set o := p.canonicalOffset k r m (t.layers 0) (t.layers c.succ) (Q i) i j
    calc
      |X - G₁| = |(X - G₀) - (G₁ - G₀ - o) - o| := by congr 1; ring
      _ ≤ |X - G₀| + |G₁ - G₀ - o| + |o| := by
        have h1 := abs_sub (X - G₀ - (G₁ - G₀ - o)) o
        have h2 := abs_sub (X - G₀) (G₁ - G₀ - o)
        linarith
      _ ≤ H₀ * ar + ar + 3 * H₀ * ar := by
        have := hoff'.trans hac
        linarith
      _ ≤ Δ := by
        dsimp only [Δ]
        nlinarith
  have hE : ∀ i ∈ I, MeasurableSet (E i) ∧ E i ⊆ U := by
    intro i hi
    refine ⟨t.witnessSet_measurable 0 i D₀, ?_⟩
    intro ω' hω'
    refine ⟨hω'.1, ?_, hfit_fine i hi ω' hω'⟩
    have h := t.shortComparisonCode_eq hω'.2.1
    rw [hω'.2.2, htagi i hi] at h
    exact h
  have hdisj : (I : Set (Fin (t.layers 0).count)).PairwiseDisjoint E := by
    intro i _ i' _ hne
    apply Set.disjoint_left.mpr
    rintro ω' ⟨-, hl, -⟩ ⟨-, hl', -⟩
    exact hne (t.label_unique hl hl')
  have hfloor : ∀ i ∈ I, ENNReal.ofReal (t.δ * (J * ar ^ p.d)) * w ≤ t.wit (E i) := by
    intro i hi
    have h := t.good_witness (ω i) (hωgood i hi) 0 i (hωi i hi)
    have htag0 : (t.layers 0).tag i 0 = ⌊p.b k ω₀.1 3 / χ⌋ := by
      rw [htagi i hi]
      rfl
    rw [htag0, hωD i hi] at h
    have heq : t.δ * (J * ar ^ p.d) =
        t.δ * (q * χ * (q * g) * (p.N k ^ (-(![r, r + u, r + v] : Fin 3 → ℝ) 0)) ^ p.d) := by
      simp only [Matrix.cons_val_zero]
      rfl
    rw [heq]
    exact h
  have hδJ : 0 < t.δ * (J * ar ^ p.d) := by
    have := t.δ_pos
    positivity
  have hC : 0 < 16800 * p.K k ^ 2 * J * Δ ^ p.d := by positivity
  have hcount := card_le_from_original_witnesses t.wit U E I hδJ hC w hw hwtop hcap hE hdisj
    hfloor
  refine hcount.trans (le_of_eq ?_)
  have hΔeq : Δ ^ p.d = (5 * H₀) ^ p.d * ar ^ p.d := by
    dsimp only [Δ]
    rw [Real.mul_rpow (by linarith) har.le]
  rw [hΔeq]
  have hδ := t.δ_pos
  have harp : 0 < ar ^ p.d := Real.rpow_pos_of_pos har _
  field_simp

end GoodTableData
end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
