-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Common.FiberLists; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254 (k4_general_parent_wide_layer_candidates), session x0900. -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Common.Hyps

/-!
# Fiber lists of transverse coefficients

For a key `(⌊b / χ⌋, ⌊v / χ⌋)` of the normalized major intercept `b` and velocity `v` at the
coarse tag mesh `χ = N^(-m)`, the fiber list collects, over the at most three major tags
compatible with the key and the recorded coarse choices of the block for each of them, the
virtual-line coefficients `lineCoeff` of the label's projected quadratic at the key's corner,
keeping only bounded entries. It has at most `3 H^4` entries, and for almost every incidence
of a consensus law it contains an entry matching the incidence's transverse pair up to
`E + 32 H^4 χ / N^(-ℓ r)`.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set MvPolynomial
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] {p : Parent α}

/-- The major intercept `b₀` of the virtual line with normalized intercept `bb` and velocity
`vv`. -/
def fiberAnchor (p : Parent α) (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (bb vv : ℝ) : ℝ :=
  p.blockLen k r * bb - p.blockStart k r Q * (vv - p.c k r Q 1) + p.c k r Q 0

open Classical in
/-- The fiber list of a key `(⌊b / χ⌋, ⌊v / χ⌋)`. -/
def fiberList {k : ℕ} {r u v m H : ℝ} (s : p.ComparedSample k r u v m H)
    (Q : Fin (p.n k r)) (χ bound : ℝ) (key : ℤ × ℤ) : Finset (Fin 3 → ℝ) :=
  ((Finset.Icc (⌊p.fiberAnchor k r Q ((key.1 : ℝ) * χ) ((key.2 : ℝ) * χ) / χ⌋ - 1)
      (⌊p.fiberAnchor k r Q ((key.1 : ℝ) * χ) ((key.2 : ℝ) * χ) / χ⌋ + 1)).biUnion
    (fun t1 => (s.coarseChoices Q ![key.2, t1]).image
      (fun i => p.lineCoeff k r Q ((s.layers 0).G i) ((key.1 : ℝ) * χ) ((key.2 : ℝ) * χ)))).filter
    (fun a => ∀ i, |a i| ≤ bound)

theorem card_fiberList_le {k : ℕ} {r u v m H : ℝ} (s : p.ComparedSample k r u v m H)
    (Q : Fin (p.n k r)) (χ bound : ℝ) (key : ℤ × ℤ) :
    ((p.fiberList s Q χ bound key).card : ℝ) ≤ 3 * H ^ 4 := by
  classical
  unfold fiberList
  set A := ⌊p.fiberAnchor k r Q ((key.1 : ℝ) * χ) ((key.2 : ℝ) * χ) / χ⌋
  have hIcc : (Finset.Icc (A - 1) (A + 1)).card = 3 := by
    rw [Int.card_Icc]
    omega
  calc _ ≤ (((Finset.Icc (A - 1) (A + 1)).biUnion
        (fun t1 => (s.coarseChoices Q ![key.2, t1]).image
          (fun i => p.lineCoeff k r Q ((s.layers 0).G i) ((key.1 : ℝ) * χ)
            ((key.2 : ℝ) * χ)))).card : ℝ) := by
        exact_mod_cast Finset.card_filter_le _ _
    _ ≤ ∑ t1 ∈ Finset.Icc (A - 1) (A + 1), (((s.coarseChoices Q ![key.2, t1]).image
          (fun i => p.lineCoeff k r Q ((s.layers 0).G i) ((key.1 : ℝ) * χ)
            ((key.2 : ℝ) * χ))).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ t1 ∈ Finset.Icc (A - 1) (A + 1), ((s.coarseChoices Q ![key.2, t1]).card : ℝ) := by
        apply Finset.sum_le_sum
        intro t1 _
        exact_mod_cast Finset.card_image_le
    _ ≤ ∑ _t1 ∈ Finset.Icc (A - 1) (A + 1), H ^ 4 :=
        Finset.sum_le_sum (fun t1 _ => s.coarse_card Q _)
    _ = 3 * H ^ 4 := by
        rw [Finset.sum_const, hIcc, nsmul_eq_mul]
        norm_num

theorem fiberList_bound {k : ℕ} {r u v m H : ℝ} (s : p.ComparedSample k r u v m H)
    (Q : Fin (p.n k r)) (χ bound : ℝ) (key : ℤ × ℤ) :
    ∀ a ∈ p.fiberList s Q χ bound key, ∀ i, |a i| ≤ bound := by
  classical
  intro a ha
  unfold fiberList at ha
  exact (Finset.mem_filter.mp ha).2

theorem mem_fiberList {k : ℕ} {r u v m H : ℝ} (s : p.ComparedSample k r u v m H)
    (Q : Fin (p.n k r)) (χ bound : ℝ) (key : ℤ × ℤ) {i : Fin (s.layers 0).count}
    (hi : i ∈ s.coarseChoices Q ((s.layers 0).tag i))
    (h0 : (s.layers 0).tag i 0 = key.2)
    (h1 : (s.layers 0).tag i 1 ∈
      Finset.Icc (⌊p.fiberAnchor k r Q ((key.1 : ℝ) * χ) ((key.2 : ℝ) * χ) / χ⌋ - 1)
        (⌊p.fiberAnchor k r Q ((key.1 : ℝ) * χ) ((key.2 : ℝ) * χ) / χ⌋ + 1))
    (hb : ∀ j, |p.lineCoeff k r Q ((s.layers 0).G i) ((key.1 : ℝ) * χ) ((key.2 : ℝ) * χ) j| ≤
      bound) :
    p.lineCoeff k r Q ((s.layers 0).G i) ((key.1 : ℝ) * χ) ((key.2 : ℝ) * χ) ∈
      p.fiberList s Q χ bound key := by
  classical
  unfold fiberList
  rw [Finset.mem_filter]
  refine ⟨?_, hb⟩
  rw [Finset.mem_biUnion]
  refine ⟨(s.layers 0).tag i 1, h1, ?_⟩
  rw [Finset.mem_image]
  refine ⟨i, ?_, rfl⟩
  have htag : (s.layers 0).tag i = ![key.2, (s.layers 0).tag i 1] := by
    funext j
    fin_cases j
    · exact h0
    · rfl
  rw [← htag]
  exact hi

end Parent

namespace FieldCommon

/-- The major tag of an actual line is within one of the major tag of its key's corner. -/
theorem tag_window {q t₀ χ braw b3 c0 c1 : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ht0 : 0 ≤ t₀)
    (ht1 : t₀ ≤ 1) (hχ : 0 < χ) :
    ⌊(q * braw - t₀ * (b3 - c1) + c0) / χ⌋ ∈
      Finset.Icc (⌊(q * ((⌊braw / χ⌋ : ℝ) * χ) - t₀ * ((⌊b3 / χ⌋ : ℝ) * χ - c1) + c0) / χ⌋ - 1)
        (⌊(q * ((⌊braw / χ⌋ : ℝ) * χ) - t₀ * ((⌊b3 / χ⌋ : ℝ) * χ - c1) + c0) / χ⌋ + 1) := by
  set bb := (⌊braw / χ⌋ : ℝ) * χ with hbb
  set vv := (⌊b3 / χ⌋ : ℝ) * χ with hvv
  have hcb := floor_cell hχ (rfl : ⌊braw / χ⌋ = ⌊braw / χ⌋)
  have hcv := floor_cell hχ (rfl : ⌊b3 / χ⌋ = ⌊b3 / χ⌋)
  set x := q * braw - t₀ * (b3 - c1) + c0 with hx
  set y := q * bb - t₀ * (vv - c1) + c0 with hy
  have hxy : x - y = q * (braw - bb) - t₀ * (b3 - vv) := by rw [hx, hy]; ring
  have hb1 : 0 ≤ braw - bb := by rw [hbb]; linarith [hcb.1]
  have hb2 : braw - bb ≤ χ := by rw [hbb]; linarith [hcb.2]
  have hv1 : 0 ≤ b3 - vv := by rw [hvv]; linarith [hcv.1]
  have hv2 : b3 - vv ≤ χ := by rw [hvv]; linarith [hcv.2]
  have hlo' : y - χ ≤ x := by
    have : t₀ * (b3 - vv) ≤ 1 * χ := mul_le_mul ht1 hv2 hv1 zero_le_one
    have : 0 ≤ q * (braw - bb) := mul_nonneg hq0 hb1
    linarith
  have hhi' : x ≤ y + χ := by
    have : q * (braw - bb) ≤ 1 * χ := mul_le_mul hq1 hb2 hb1 zero_le_one
    have : 0 ≤ t₀ * (b3 - vv) := mul_nonneg ht0 hv1
    linarith
  have hlo : y / χ - 1 ≤ x / χ := by
    have : y / χ - 1 = (y - χ) / χ := by field_simp
    rw [this]
    exact div_le_div_of_nonneg_right hlo' hχ.le
  have hhi : x / χ ≤ y / χ + 1 := by
    have : y / χ + 1 = (y + χ) / χ := by field_simp
    rw [this]
    exact div_le_div_of_nonneg_right hhi' hχ.le
  rw [Finset.mem_Icc]
  constructor
  · have := Int.floor_le_floor hlo
    rw [Int.floor_sub_one] at this
    exact this
  · have := Int.floor_le_floor hhi
    rw [Int.floor_add_one] at this
    exact this

/-- The difference factor of two virtual lines. -/
theorem slope_factor_bound {q g β H dd c4 : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (hg0 : 0 < g)
    (hβ : 0 < β) (hgβ : g ≤ H * β) (hH : 1 ≤ H) (hdd : |dd| ≤ 16 * H / β ^ 2)
    (hc4 : |c4| ≤ H) : |q * g * dd * c4 * q| ≤ 16 * H ^ 4 / g := by
  have hH0 : 0 ≤ H := by linarith
  have hβ2 : 0 < β ^ 2 := by positivity
  have hgg : g * g ≤ H ^ 2 * β ^ 2 := by
    have := mul_le_mul hgβ hgβ hg0.le (by positivity)
    nlinarith
  have hgβ2 : g / β ^ 2 ≤ H ^ 2 / g := by
    rw [div_le_div_iff₀ hβ2 hg0]
    nlinarith
  have hq2 : q ^ 2 ≤ 1 := by nlinarith
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hq0, abs_of_pos hg0]
  calc q * g * |dd| * |c4| * q ≤ q * g * (16 * H / β ^ 2) * H * q := by gcongr
    _ = (16 * H ^ 2) * q ^ 2 * (g / β ^ 2) := by ring
    _ ≤ (16 * H ^ 2) * 1 * (H ^ 2 / g) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hq2 (by positivity)) hgβ2
          (div_nonneg hg0.le hβ2.le) (by positivity)
    _ = 16 * H ^ 4 / g := by ring

/-- Bounds of a list entry from bounds of the actual line and closeness. -/
theorem entry_bounds {H A0 A1 B0 B1 D : ℝ} (hH : 1 ≤ H) (hA0 : |A0| ≤ 48 * H ^ 4)
    (hA1 : |A1| ≤ 48 * H ^ 4) (h0 : |A0 - B0| ≤ 1) (h1 : |A1 - B1| ≤ 1)
    (hD : |D| ≤ 8 * H ^ 3) :
    |B0| ≤ 98 * H ^ 4 ∧ |B1 - B0| ≤ 98 * H ^ 4 ∧ |D| ≤ 98 * H ^ 4 := by
  have hH4 : 1 ≤ H ^ 4 := one_le_pow₀ hH
  have hH34 : H ^ 3 ≤ H ^ 4 := pow_le_pow_right₀ hH (by norm_num)
  rw [abs_le] at hA0 hA1 h0 h1 hD
  refine ⟨?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> linarith

end FieldCommon

namespace Parent

variable {α : Type} [MeasurableSpace α] {p : Parent α}

theorem common_b0_eq (p : Parent α) (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (l : α) :
    p.b k l 0 = p.blockLen k r * p.majorIntercept k r Q l -
      p.blockStart k r Q * (p.b k l 3 - p.c k r Q 1) + p.c k r Q 0 := by
  have hq := (p.common_blockLen_pos k r).ne'
  unfold majorIntercept
  field_simp
  ring

/-- **Fiber agreement.** For almost every incidence of a submeasure of a consensus law, the
fiber list of its key contains an entry matching its transported native center. -/
theorem blockLaw_fiber_agree (h : p.Valid) {R : ℝ} {k : ℕ} {r u v m H : ℝ}
    (hat : p.AtDepth k r R) (a : ParentGeometry p k r) (hKH : p.K k ≤ H)
    {s : p.ComparedSample k r u v m H} {βb w mv E C : ℝ} (c : p.ConsensusLaw k s βb w mv E C)
    {law : Measure (α × ℝ)} (hlaw : law ≤ c.law) {bound tol : ℝ}
    (hbound : 98 * H ^ 4 ≤ bound)
    (hvar : 32 * H ^ 4 * p.N k ^ (-m) / p.N k ^ (-p.ℓ * r) ≤ 1)
    (htol : E + 32 * H ^ 4 * p.N k ^ (-m) / p.N k ^ (-p.ℓ * r) ≤ tol) :
    ∀ᵐ x ∂p.blockLaw k r c.block law,
      ∃ a' ∈ p.fiberList s c.block (p.N k ^ (-m)) bound
          (⌊p.normB k r c.block x.1 / p.N k ^ (-m)⌋, ⌊p.normV k x.1 / p.N k ^ (-m)⌋),
        |p.normF k r c.block (p.N k ^ (-βb)) (p.N k ^ (-w)) c.center x 0 - a' 0 -
            a' 1 * x.2| ≤ tol ∧
        |p.normF k r c.block (p.N k ^ (-βb)) (p.N k ^ (-w)) c.center x 1 - a' 2| ≤ tol := by
  have hN : 0 < p.N k := by linarith [h.scale k]
  have hχ0 : 0 < p.N k ^ (-m) := Real.rpow_pos_of_pos hN _
  have hg0 : 0 < p.N k ^ (-p.ℓ * r) := Real.rpow_pos_of_pos hN _
  have hH1 : 1 ≤ H := by linarith [s.loss_one]
  have hq := p.common_blockLen_pos k r
  have hq1 := p.common_blockLen_le_one k r
  have ht₀ := p.common_blockStart_mem k r c.block
  have ht₀1 := p.common_block_subset_unit k r c.block ht₀
  have ht₁ := p.common_blockEnd_mem k r c.block
  apply ae_blockLaw
  filter_upwards [ae_mono hlaw (c.ae_facts h hat), ae_mono hlaw c.agree] with ω hfacts hagree
  obtain ⟨hB, hI, hb3, hcoarse⟩ := hfacts
  obtain ⟨i, hCi, hagr⟩ := hagree
  have hA : ω.1 ∈ p.A k r c.block := (hat.2.2.1 c.block).2.2 hB
  rw [p.normF_blockEquiv, p.blockEquiv_apply]
  simp only
  rw [hat.normB_eq c.block hA, normV_eq hb3]
  obtain ⟨hβ, hgβ, hdeg, ⟨cc, hc, -, hrep2⟩, hl⟩ := s.label_data i
  obtain ⟨htag0, htag1, -⟩ := hl ω.1 hCi
  -- the difference of the actual line and the key's corner line
  have hσ := FieldCommon.slope_factor_bound hq hq1 hg0 hβ hgβ hH1
    (FieldCommon.second_derivative_bound hβ hc hrep2 ![0, 0])
    ((a.coefficient_bound c.block 4).trans hKH)
  have hcb := FieldCommon.floor_cell hχ0
    (rfl : ⌊p.majorIntercept k r c.block ω.1 / p.N k ^ (-m)⌋ =
      ⌊p.majorIntercept k r c.block ω.1 / p.N k ^ (-m)⌋)
  have hcv := FieldCommon.floor_cell hχ0
    (rfl : ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋ = ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋)
  have hdiff : ∀ τ ∈ Icc (0 : ℝ) 1,
      |p.lineB k r c.block ((s.layers 0).G i) (p.majorIntercept k r c.block ω.1) (p.b k ω.1 3) τ -
        p.lineB k r c.block ((s.layers 0).G i)
          ((⌊p.majorIntercept k r c.block ω.1 / p.N k ^ (-m)⌋ : ℝ) * p.N k ^ (-m))
          ((⌊p.b k ω.1 3 / p.N k ^ (-m)⌋ : ℝ) * p.N k ^ (-m)) τ| ≤
        32 * H ^ 4 * p.N k ^ (-m) / p.N k ^ (-p.ℓ * r) := by
    intro τ hτ
    rw [p.lineB_sub k r c.block hdeg, abs_mul]
    have hτ' : |τ| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hτ.1, hτ.2]
    have hdb : |p.majorIntercept k r c.block ω.1 -
        (⌊p.majorIntercept k r c.block ω.1 / p.N k ^ (-m)⌋ : ℝ) * p.N k ^ (-m)| ≤
        p.N k ^ (-m) := by
      rw [abs_le]
      constructor <;> linarith [hcb.1, hcb.2]
    have hdv : |p.b k ω.1 3 - (⌊p.b k ω.1 3 / p.N k ^ (-m)⌋ : ℝ) * p.N k ^ (-m)| ≤
        p.N k ^ (-m) := by
      rw [abs_le]
      constructor <;> linarith [hcv.1, hcv.2]
    have hsum : |p.majorIntercept k r c.block ω.1 -
        (⌊p.majorIntercept k r c.block ω.1 / p.N k ^ (-m)⌋ : ℝ) * p.N k ^ (-m) +
        τ * (p.b k ω.1 3 - (⌊p.b k ω.1 3 / p.N k ^ (-m)⌋ : ℝ) * p.N k ^ (-m))| ≤
        2 * p.N k ^ (-m) := by
      calc _ ≤ _ := abs_add_le _ _
        _ = _ := by rw [abs_mul]
        _ ≤ p.N k ^ (-m) + 1 * p.N k ^ (-m) := add_le_add hdb (mul_le_mul hτ' hdv
            (abs_nonneg _) zero_le_one)
        _ = 2 * p.N k ^ (-m) := by ring
    calc _ ≤ 16 * H ^ 4 / p.N k ^ (-p.ℓ * r) * (2 * p.N k ^ (-m)) :=
          mul_le_mul hσ hsum (abs_nonneg _) (by positivity)
      _ = 32 * H ^ 4 * p.N k ^ (-m) / p.N k ^ (-p.ℓ * r) := by ring
  -- the actual line at the block's end points
  have hT : ∀ t ∈ Parent.block (p.T k r) (p.j k r c.block),
      |p.lineB k r c.block ((s.layers 0).G i) (p.majorIntercept k r c.block ω.1)
        (p.b k ω.1 3) (p.tauN k r c.block (ω.1, t))| ≤ 48 * H ^ 4 := by
    intro t ht
    have h1 := (s.transPair_bound h a hKH (Q := c.block) (i := i) (ω := (ω.1, t)) hA ht hCi).1
    rw [p.transPair_zero_eq_lineB] at h1
    exact h1
  have hτ0 : p.tauN k r c.block (ω.1, p.blockStart k r c.block) = 0 := by
    unfold tauN
    simp
  have hτ1 : p.tauN k r c.block (ω.1, p.blockStart k r c.block + p.blockLen k r) = 1 := by
    unfold tauN
    simp only [add_sub_cancel_left]
    exact div_self hq.ne'
  have hT0 := hT _ ht₀
  have hT1 := hT _ ht₁
  rw [hτ0] at hT0
  rw [hτ1] at hT1
  have hD : |transD ((s.layers 0).G i) (p.blockWidth k r)| ≤ 8 * H ^ 3 := by
    have h1 := (s.transPair_bound h a hKH (Q := c.block) (i := i) (ω := ω) hA hI hCi).2
    rwa [p.transPair_one_eq] at h1
  have hd0 := (hdiff 0 ⟨le_rfl, zero_le_one⟩).trans hvar
  have hd1 := (hdiff 1 ⟨zero_le_one, le_rfl⟩).trans hvar
  obtain ⟨hB0, hB1, hBD⟩ := FieldCommon.entry_bounds hH1 hT0 hT1 hd0 hd1 hD
  have hbd : ∀ j, |p.lineCoeff k r c.block ((s.layers 0).G i)
      ((⌊p.majorIntercept k r c.block ω.1 / p.N k ^ (-m)⌋ : ℝ) * p.N k ^ (-m))
      ((⌊p.b k ω.1 3 / p.N k ^ (-m)⌋ : ℝ) * p.N k ^ (-m)) j| ≤ bound := by
    intro j
    fin_cases j
    · exact hB0.trans hbound
    · exact hB1.trans hbound
    · exact hBD.trans hbound
  -- membership of the entry in the fiber list
  have hwin := FieldCommon.tag_window (c0 := p.c k r c.block 0) (c1 := p.c k r c.block 1)
    (braw := p.majorIntercept k r c.block ω.1) (b3 := p.b k ω.1 3) hq.le hq1 ht₀1.1 ht₀1.2 hχ0
  rw [← p.common_b0_eq k r c.block ω.1, htag1] at hwin
  have hmem := p.mem_fiberList s c.block (p.N k ^ (-m)) bound
    (⌊p.majorIntercept k r c.block ω.1 / p.N k ^ (-m)⌋, ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋)
    (hcoarse i hCi) htag0.symm hwin hbd
  refine ⟨_, hmem, ?_, ?_⟩
  · -- the affine first coefficient
    have hτ := p.common_tauN_mem_unit k r c.block hI
    have haff := p.lineB_affine k r c.block hdeg
      ((⌊p.majorIntercept k r c.block ω.1 / p.N k ^ (-m)⌋ : ℝ) * p.N k ^ (-m))
      ((⌊p.b k ω.1 3 / p.N k ^ (-m)⌋ : ℝ) * p.N k ^ (-m)) (p.tauN k r c.block ω)
    have hagr0 := hagr 0
    rw [p.transPair_zero_eq_lineB] at hagr0
    have hdτ := hdiff _ hτ
    simp only [lineCoeff, Matrix.cons_val_zero, Matrix.cons_val_one]
    set L := p.lineB k r c.block ((s.layers 0).G i)
      ((⌊p.majorIntercept k r c.block ω.1 / p.N k ^ (-m)⌋ : ℝ) * p.N k ^ (-m))
      ((⌊p.b k ω.1 3 / p.N k ^ (-m)⌋ : ℝ) * p.N k ^ (-m)) with hL
    have he : c.center (p.nativeState k r c.block (p.N k ^ (-βb)) (p.N k ^ (-w)) ω) 0 - L 0 -
        (L 1 - L 0) * p.tauN k r c.block ω =
        c.center (p.nativeState k r c.block (p.N k ^ (-βb)) (p.N k ^ (-w)) ω) 0 -
          L (p.tauN k r c.block ω) := by
      rw [haff]
      ring
    rw [he]
    rw [abs_sub_comm] at hagr0
    calc _ ≤ _ := abs_sub_le _ _ _
      _ ≤ E + 32 * H ^ 4 * p.N k ^ (-m) / p.N k ^ (-p.ℓ * r) := add_le_add hagr0 hdτ
      _ ≤ tol := htol
  · -- the constant second coefficient
    have hagr1 := hagr 1
    rw [p.transPair_one_eq] at hagr1
    have hlc2 : p.lineCoeff k r c.block ((s.layers 0).G i)
        ((⌊p.majorIntercept k r c.block ω.1 / p.N k ^ (-m)⌋ : ℝ) * p.N k ^ (-m))
        ((⌊p.b k ω.1 3 / p.N k ^ (-m)⌋ : ℝ) * p.N k ^ (-m)) 2 =
        transD ((s.layers 0).G i) (p.blockWidth k r) := rfl
    rw [hlc2, abs_sub_comm]
    have : 0 ≤ 32 * H ^ 4 * p.N k ^ (-m) / p.N k ^ (-p.ℓ * r) := by positivity
    linarith

/-- The transported native center is bounded on almost every incidence. -/
theorem blockLaw_normF_bound (h : p.Valid) {R : ℝ} {k : ℕ} {r u v m H : ℝ}
    (hat : p.AtDepth k r R) (a : ParentGeometry p k r) (hKH : p.K k ≤ H)
    {s : p.ComparedSample k r u v m H} {βb w mv E C : ℝ} (c : p.ConsensusLaw k s βb w mv E C)
    {law : Measure (α × ℝ)} (hlaw : law ≤ c.law) {bound : ℝ}
    (hbound : 48 * H ^ 4 + E ≤ bound) :
    ∀ᵐ x ∂p.blockLaw k r c.block law, ∀ i,
      |p.normF k r c.block (p.N k ^ (-βb)) (p.N k ^ (-w)) c.center x i| ≤ bound := by
  have hH1 : 1 ≤ H := by linarith [s.loss_one]
  apply ae_blockLaw
  filter_upwards [ae_mono hlaw (c.ae_facts h hat), ae_mono hlaw c.agree] with ω hfacts hagree
  obtain ⟨hB, hI, -, -⟩ := hfacts
  obtain ⟨i, hCi, hagr⟩ := hagree
  have hA : ω.1 ∈ p.A k r c.block := (hat.2.2.1 c.block).2.2 hB
  rw [p.normF_blockEquiv]
  obtain ⟨hT0, hT1⟩ := s.transPair_bound h a hKH (Q := c.block) (i := i) hA hI hCi
  have hH4 : 8 * H ^ 3 ≤ 48 * H ^ 4 := by
    have : H ^ 3 ≤ H ^ 4 := pow_le_pow_right₀ hH1 (by norm_num)
    have : 0 ≤ H ^ 4 := by positivity
    linarith
  intro e
  have he := hagr e
  have hTe : |p.transPair k r c.block ((s.layers 0).G i) ω e| ≤ 48 * H ^ 4 := by
    fin_cases e
    · exact hT0
    · exact hT1.trans hH4
  calc _ = |p.transPair k r c.block ((s.layers 0).G i) ω e -
          (p.transPair k r c.block ((s.layers 0).G i) ω e -
            c.center (p.nativeState k r c.block (p.N k ^ (-βb)) (p.N k ^ (-w)) ω) e)| := by
        ring_nf
    _ ≤ |p.transPair k r c.block ((s.layers 0).G i) ω e| +
          |p.transPair k r c.block ((s.layers 0).G i) ω e -
            c.center (p.nativeState k r c.block (p.N k ^ (-βb)) (p.N k ^ (-w)) ω) e| :=
        abs_sub _ _
    _ ≤ 48 * H ^ 4 + E := add_le_add hTe he
    _ ≤ bound := hbound

end Parent

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
