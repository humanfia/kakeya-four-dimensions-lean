-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Common.Hyps; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254 (k4_general_parent_wide_layer_candidates), session x0900. -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Common.Normal
import Submission.Obl.k4_general_compared_layers_velocity_lists.Confine.Loss

/-!
# The hypotheses of the common affine field on one consensus law

On a submeasure of a consensus law (`ConsensusLaw`) of one original block:

* almost every incidence lies in the block, has an unclipped velocity, and its coarse label is
  one of the recorded coarse choices of the block (`ConsensusLaw.ae_facts`);
* the transverse coefficient pair of a coarse label is bounded by `48 H^4` on the block
  (`ComparedSample.transPair_bound`);
* normalized base cells inherit an original cell bound (`blockLaw_cell_le`);
* the normalized law inherits conditional palette domination at every coarser state built
  from the native state (`blockLaw_state_domination`);
* palette bin caps give a Frostman ball bound (`FieldCommon.frostman_of_palette`);
* fiber lists of virtual-line coefficients over the recorded coarse choices
  (`fiberList`) are short and bounded, and contain, for almost every incidence, an entry
  matching its transverse pair (`blockLaw_fiber_agree`).
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set MvPolynomial
open scoped ENNReal

noncomputable section

namespace FieldCommon

theorem measure_eq_of_inter_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {S A B : Set Ω} (hS : μ Sᶜ = 0) (h : A ∩ S = B ∩ S) : μ A = μ B := by
  rw [← measure_inter_conull (s := A) hS, h, measure_inter_conull hS]

theorem floor_div_eq_iff_mem_Ico {x δ : ℝ} (hδ : 0 < δ) (j : ℤ) :
    ⌊x / δ⌋ = j ↔ x ∈ Ico ((j : ℝ) * δ) (((j : ℝ) + 1) * δ) := by
  rw [Int.floor_eq_iff, le_div_iff₀ hδ, div_lt_iff₀ hδ]
  rfl

/-- **Frostman ball bound from palette bin caps.** -/
theorem frostman_of_palette {π : Measure ℝ} [IsProbabilityMeasure π]
    {N K S η vMin vMax δ : ℝ} (hN : 1 < N) (hS1 : S ≤ 1)
    (hpal : ∀ v : ℝ, vMin ≤ v → v ≤ vMax → ∀ a : ℤ,
      π {w : ℝ | ⌊w / N ^ (-v)⌋ = a} ≤ ENNReal.ofReal (K * N ^ (-S * v)))
    (hδ : N ^ (-vMax) ≤ δ) (hvη : vMin ≤ η) (h3K : 3 * K ≤ N ^ η) :
    ∀ x r : ℝ, δ ≤ r → r ≤ 1 → π (Icc (x - r) (x + r)) ≤ ENNReal.ofReal (N ^ η * r ^ S) := by
  intro x r hδr hr1
  have hN0 : 0 < N := by linarith
  have hr0 : 0 < r := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) (hδ.trans hδr)
  have hS0 : 0 ≤ r ^ S := Real.rpow_nonneg hr0.le _
  by_cases hsmall : r ≤ N ^ (-vMin)
  · set v := -Real.logb N r with hv
    have hNv : N ^ (-v) = r := by
      rw [hv, neg_neg, Real.rpow_logb hN0 hN.ne' hr0]
    have hv1 : vMin ≤ v := by
      rw [hv, le_neg]
      exact (Real.logb_le_iff_le_rpow hN hr0).mpr hsmall
    have hv2 : v ≤ vMax := by
      rw [hv, neg_le]
      exact (Real.le_logb_iff_rpow_le hN hr0).mpr (hδ.trans hδr)
    have hbin := hpal v hv1 hv2
    rw [hNv] at hbin
    set a := ⌊x / r⌋ with ha
    have hcover : Icc (x - r) (x + r) ⊆
        ⋃ b ∈ ({a - 1, a, a + 1} : Finset ℤ), {w : ℝ | ⌊w / r⌋ = b} := by
      intro w hw
      have h1 : x / r - 1 ≤ w / r := by
        have : x / r - 1 = (x - r) / r := by field_simp
        rw [this]
        exact div_le_div_of_nonneg_right hw.1 hr0.le
      have h2 : w / r ≤ x / r + 1 := by
        have : x / r + 1 = (x + r) / r := by field_simp
        rw [this]
        exact div_le_div_of_nonneg_right hw.2 hr0.le
      have hlo : a - 1 ≤ ⌊w / r⌋ := by
        have := Int.floor_le_floor h1
        rw [Int.floor_sub_one] at this
        exact this
      have hhi : ⌊w / r⌋ ≤ a + 1 := by
        have := Int.floor_le_floor h2
        rw [Int.floor_add_one] at this
        exact this
      apply mem_iUnion₂.mpr
      refine ⟨⌊w / r⌋, ?_, rfl⟩
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hpow : N ^ (-S * v) = r ^ S := by
      rw [← hNv, ← Real.rpow_mul hN0.le]
      congr 1
      ring
    have hcard : (({a - 1, a, a + 1} : Finset ℤ).card : ℝ≥0∞) ≤ 3 := by
      exact_mod_cast Finset.card_le_three
    calc π (Icc (x - r) (x + r)) ≤
          π (⋃ b ∈ ({a - 1, a, a + 1} : Finset ℤ), {w : ℝ | ⌊w / r⌋ = b}) := measure_mono hcover
      _ ≤ ∑ b ∈ ({a - 1, a, a + 1} : Finset ℤ), π {w : ℝ | ⌊w / r⌋ = b} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _b ∈ ({a - 1, a, a + 1} : Finset ℤ), ENNReal.ofReal (K * N ^ (-S * v)) :=
          Finset.sum_le_sum (fun b _ => hbin b)
      _ = (({a - 1, a, a + 1} : Finset ℤ).card : ℝ≥0∞) * ENNReal.ofReal (K * N ^ (-S * v)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 3 * ENNReal.ofReal (K * N ^ (-S * v)) := mul_le_mul' hcard le_rfl
      _ = ENNReal.ofReal (3 * K * r ^ S) := by
          rw [hpow, mul_assoc, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
          simp only [ENNReal.ofReal_ofNat]
      _ ≤ ENNReal.ofReal (N ^ η * r ^ S) := by
          apply ENNReal.ofReal_le_ofReal
          exact mul_le_mul_of_nonneg_right h3K hS0
  · replace hsmall := not_le.mp hsmall
    have h1 : N ^ (-η) ≤ r :=
      (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith : -η ≤ -vMin)).trans hsmall.le
    have h2 : r ≤ r ^ S := Real.self_le_rpow_of_le_one hr0.le hr1 hS1
    have h3 : N ^ η * N ^ (-η) = 1 := by
      rw [← Real.rpow_add hN0]
      simp
    have hone : 1 ≤ N ^ η * r ^ S := by
      calc (1 : ℝ) = N ^ η * N ^ (-η) := h3.symm
        _ ≤ N ^ η * r ^ S :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (Real.rpow_nonneg hN0.le _)
    calc π (Icc (x - r) (x + r)) ≤ π univ := measure_mono (subset_univ _)
      _ = ENNReal.ofReal 1 := by rw [measure_univ, ENNReal.ofReal_one]
      _ ≤ ENNReal.ofReal (N ^ η * r ^ S) := ENNReal.ofReal_le_ofReal hone

end FieldCommon

namespace Parent

variable {α : Type} [MeasurableSpace α] {p : Parent α}

/-- Almost every incidence of a consensus law lies in its block, has a bounded velocity,
and its coarse label is a recorded coarse choice of the block. -/
theorem ConsensusLaw.ae_facts (h : p.Valid) {k : ℕ} {r u v m H : ℝ}
    {s : p.ComparedSample k r u v m H} {βb w mv E C : ℝ} (c : p.ConsensusLaw k s βb w mv E C)
    {R : ℝ} (hat : p.AtDepth k r R) :
    ∀ᵐ ω ∂c.law, ω.1 ∈ p.B k r c.block ∧ ω.2 ∈ Parent.block (p.T k r) (p.j k r c.block) ∧
      |p.b k ω.1 3| ≤ p.K k ∧
      ∀ i, ω.1 ∈ (s.layers 0).C i → i ∈ s.coarseChoices c.block ((s.layers 0).tag i) := by
  have hle : c.law ≤ p.μ k := c.le_law.trans (s.le_rho.trans (h.basic k).2.2.2.2.1)
  have hdyμ : ∀ᵐ ω ∂p.μ k, ω.2 ∉ dyadicTimes (p.T k r) := by
    rw [ae_iff]
    simpa only [not_not] using h.dyadic_null k (p.T k r)
  have hdy : ∀ᵐ ω ∂c.law, ω.2 ∉ dyadicTimes (p.T k r) := ae_mono hle hdyμ
  have hcov : ∀ᵐ ω ∂c.law, ∃ e, ω ∈ s.event 0 e := ae_mono c.le_law (s.event_cover 0)
  filter_upwards [c.support, hdy, hcov] with ω hsupp hD hev
  obtain ⟨hB, hI, hgood⟩ := hsupp
  refine ⟨hB, hI, ?_, ?_⟩
  · have hg := hgood.2
    have h0 := abs_nonneg (p.b k ω.1 0)
    have h1 := abs_nonneg (p.b k ω.1 1)
    have h4 := abs_nonneg (p.b k ω.1 4)
    linarith
  · intro i hi
    obtain ⟨e, he⟩ := hev
    obtain ⟨-, hBe, hIe, hCe, -, -⟩ := s.event_data 0 e ω he
    have hBA : ∀ Q, p.B k r Q ⊆ p.A k r Q := fun Q => (hat.2.2.1 Q).2.2
    have hpar : s.parent 0 e = c.block :=
      block_eq_of_mem hat.2.2.2.1 (hBA _ hBe) (hBA _ hB) hIe hI hD
    obtain ⟨-, -, -, -, hdisj, -, -⟩ := s.layer_valid 0
    have hcoarse : s.coarse 0 e = i := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisj _ _ hne) hCe hi
    have hmem := s.coarse_mem 0 e
    rw [hpar, hcoarse] at hmem
    exact hmem

/-- The data of a coarse label: positive adapted width, bounded adapted derivatives, degree,
and the trajectory tube. -/
theorem ComparedSample.label_data {k : ℕ} {r u v m H : ℝ}
    (s : p.ComparedSample k r u v m H) (i : Fin (s.layers 0).count) :
    0 < (s.layers 0).β ∧ p.N k ^ (-p.ℓ * r) ≤ H * (s.layers 0).β ∧
      ((s.layers 0).G i).totalDegree ≤ 2 ∧
      (∃ cc : Fin 6 → ℝ, (∀ j, |cc j| ≤ 8 * H) ∧
        (∀ t Y, (s.layers 0).β * eval ![t, Y] (pderiv 1 ((s.layers 0).G i)) =
          cc 2 + cc 4 * t + 2 * cc 5 * ((Y - (s.layers 0).u i - t * (s.layers 0).v i) /
            (s.layers 0).β)) ∧
        (∀ x, (s.layers 0).β ^ 2 * eval x (pderiv 1 (pderiv 1 ((s.layers 0).G i))) =
          2 * cc 5)) ∧
      (∀ l ∈ (s.layers 0).C i,
        ⌊p.b k l 3 / p.N k ^ (-m)⌋ = (s.layers 0).tag i 0 ∧
        ⌊p.b k l 0 / p.N k ^ (-m)⌋ = (s.layers 0).tag i 1 ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          |p.x k l t 2 - (s.layers 0).u i - t * (s.layers 0).v i| ≤ H * (s.layers 0).β) := by
  obtain ⟨hβ, hβlo, -, -, -, hlab, -⟩ := s.layer_valid 0
  obtain ⟨-, hdeg, hbound, hl, -⟩ := hlab i
  have hH : 0 < H := by linarith [s.loss_one]
  refine ⟨hβ, ?_, hdeg, FieldCommon.adapted_derivs _ hdeg hβ hbound, ?_⟩
  · have h1 : p.N k ^ (-p.ℓ * r) / H ≤ (s.layers 0).β := by simpa using hβlo
    rw [div_le_iff₀ hH] at h1
    linarith
  · intro l hlC
    obtain ⟨h0, h1, h2⟩ := hl l hlC
    exact ⟨h0, h1, fun t ht => (h2 t ht).1⟩

/-- The transverse coefficient pair of a coarse label is bounded on the block. -/
theorem ComparedSample.transPair_bound (h : p.Valid) {k : ℕ} {r u v m H : ℝ}
    (s : p.ComparedSample k r u v m H) (a : ParentGeometry p k r) (hKH : p.K k ≤ H)
    {Q : Fin (p.n k r)} {i : Fin (s.layers 0).count} {ω : α × ℝ}
    (hA : ω.1 ∈ p.A k r Q) (ht : ω.2 ∈ block (p.T k r) (p.j k r Q))
    (hC : ω.1 ∈ (s.layers 0).C i) :
    |p.transPair k r Q ((s.layers 0).G i) ω 0| ≤ 48 * H ^ 4 ∧
      |p.transPair k r Q ((s.layers 0).G i) ω 1| ≤ 8 * H ^ 3 := by
  obtain ⟨hβ, hgβ, -, ⟨cc, hc, hrep1, hrep2⟩, hl⟩ := s.label_data i
  have hH1 : 1 ≤ H := by linarith [s.loss_one]
  have hN : 0 < p.N k := by linarith [h.scale k]
  have hK : 1 ≤ p.K k := h.subpower.1 k
  have hg : 0 < p.N k ^ (-p.ℓ * r) := Real.rpow_pos_of_pos hN _
  have hq := p.common_blockLen_pos k r
  have hq1 := p.common_blockLen_le_one k r
  have hw0 : 0 ≤ p.blockWidth k r := by unfold blockWidth; positivity
  have hwg : p.blockWidth k r ≤ p.N k ^ (-p.ℓ * r) := by
    unfold blockWidth
    calc p.blockLen k r * p.N k ^ (-p.ℓ * r) ≤ 1 * p.N k ^ (-p.ℓ * r) := by gcongr
      _ = _ := one_mul _
  have hwβ : p.blockWidth k r ≤ H * (s.layers 0).β := hwg.trans hgβ
  have ht01 := p.common_block_subset_unit k r Q ht
  have hlab := (hl ω.1 hC).2.2 ω.2 ht01
  have htr := a.transverse Q ω.1 hA ω.2 ht
  constructor
  · simp only [transPair, Matrix.cons_val_zero, transB]
    apply FieldCommon.transverse_slope_bound hH1 hβ hc (hrep1 _ _) hw0 hwβ
    · rw [abs_le]
      constructor <;> linarith [ht01.1, ht01.2]
    · have hwK : p.K k * ((2 : ℝ) ^ p.T k r)⁻¹ * p.N k ^ (-p.ℓ * r) ≤
          H * (H * (s.layers 0).β) := by
        have : p.K k * ((2 : ℝ) ^ p.T k r)⁻¹ * p.N k ^ (-p.ℓ * r) =
            p.K k * p.blockWidth k r := by
          unfold blockWidth blockLen
          ring
        rw [this]
        exact mul_le_mul hKH hwβ hw0 (by linarith)
      have hβH : H * (s.layers 0).β ≤ H * (H * (s.layers 0).β) := by
        have : 0 ≤ H * (s.layers 0).β := by positivity
        nlinarith
      unfold tiltY
      have he : p.c k r Q 2 + p.c k r Q 3 * ω.2 + p.c k r Q 4 * p.x k ω.1 ω.2 1 -
          (s.layers 0).u i - ω.2 * (s.layers 0).v i =
          (p.x k ω.1 ω.2 2 - (s.layers 0).u i - ω.2 * (s.layers 0).v i) -
            (p.x k ω.1 ω.2 2 - p.c k r Q 2 - ω.2 * p.c k r Q 3 -
              p.c k r Q 4 * p.x k ω.1 ω.2 1) := by ring
      rw [he]
      calc _ ≤ |p.x k ω.1 ω.2 2 - (s.layers 0).u i - ω.2 * (s.layers 0).v i| +
            |p.x k ω.1 ω.2 2 - p.c k r Q 2 - ω.2 * p.c k r Q 3 -
              p.c k r Q 4 * p.x k ω.1 ω.2 1| := abs_sub _ _
        _ ≤ H * (H * (s.layers 0).β) + H * (H * (s.layers 0).β) :=
            add_le_add (hlab.trans hβH) (htr.trans hwK)
        _ = 2 * H ^ 2 * (s.layers 0).β := by ring
  · simp only [transPair, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact FieldCommon.transverse_curvature_bound hH1 hβ hc hrep2 hw0 hwβ

/-- Normalized base cells inherit an original cell bound. -/
theorem blockLaw_cell_le {R : ℝ} {k : ℕ} {r : ℝ} (h : p.Valid) (hat : p.AtDepth k r R)
    {Q : Fin (p.n k r)} (hA0 : p.ν k (p.A k r Q) ≠ 0) {law : Measure (α × ℝ)}
    (hsupp : ∀ᵐ ω ∂law, ω ∈ p.blockSupport k r Q) {δ X : ℝ}
    (hcell : ∀ q0 q1 : ℤ,
      law {ω | ⌊p.tauN k r Q ω / δ⌋ = q0 ∧ ⌊p.zetaN k r Q ω / δ⌋ = q1} ≤
        ENNReal.ofReal X * p.blockWeight k r Q)
    (qq : Fin 2 → ℤ) :
    p.blockLaw k r Q law {x | (fun i => ⌊(![x.2, p.normB k r Q x.1 + x.2 *
        (p.normV k x.1 - p.c k r Q 1)] : Fin 2 → ℝ) i / δ⌋) = qq} ≤ ENNReal.ofReal X := by
  rw [blockLaw_apply]
  have hS : law (p.blockSupport k r Q)ᶜ = 0 := ae_iff.mp hsupp
  have hsub : (p.blockEquiv k r Q ⁻¹' {x | (fun i => ⌊(![x.2, p.normB k r Q x.1 + x.2 *
        (p.normV k x.1 - p.c k r Q 1)] : Fin 2 → ℝ) i / δ⌋) = qq}) ∩ p.blockSupport k r Q ⊆
      {ω | ⌊p.tauN k r Q ω / δ⌋ = qq 0 ∧ ⌊p.zetaN k r Q ω / δ⌋ = qq 1} := by
    intro ω hω
    obtain ⟨hω, hS⟩ := hω
    obtain ⟨h1, h2, -⟩ := hat.normalized_coords Q hS
    have h0' := congrFun hω 0
    have h1' := congrFun hω 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0' h1'
    rw [h1] at h0'
    rw [h2] at h1'
    exact ⟨h0', h1'⟩
  have hbw0 := blockWeight_ne_zero hA0
  have hbwt := blockWeight_ne_top h k r Q
  calc (p.blockWeight k r Q)⁻¹ * law (p.blockEquiv k r Q ⁻¹' _) =
        (p.blockWeight k r Q)⁻¹ * law (p.blockEquiv k r Q ⁻¹' {x | (fun i =>
          ⌊(![x.2, p.normB k r Q x.1 + x.2 * (p.normV k x.1 - p.c k r Q 1)] : Fin 2 → ℝ) i /
            δ⌋) = qq} ∩ p.blockSupport k r Q) := by rw [measure_inter_conull hS]
    _ ≤ (p.blockWeight k r Q)⁻¹ *
          law {ω | ⌊p.tauN k r Q ω / δ⌋ = qq 0 ∧ ⌊p.zetaN k r Q ω / δ⌋ = qq 1} := by
        gcongr
    _ ≤ (p.blockWeight k r Q)⁻¹ * (ENNReal.ofReal X * p.blockWeight k r Q) := by
        gcongr
        exact hcell _ _
    _ = ENNReal.ofReal X := by
        rw [mul_comm (ENNReal.ofReal X), ← mul_assoc, ENNReal.inv_mul_cancel hbw0 hbwt, one_mul]

/-- The coarse state of the common field, as a function of the native state. -/
def coarseState (e : ℝ) (center : (Fin 4 → ℤ) → Fin 2 → ℝ) (σ : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![σ 0, σ 1, ⌊center σ 0 / e⌋, ⌊center σ 1 / e⌋]

/-- The normalized law inherits conditional palette domination at the coarse states. -/
theorem blockLaw_state_domination {R : ℝ} {k : ℕ} {r : ℝ} (hat : p.AtDepth k r R)
    (hb : Measurable (p.b k)) {Q : Fin (p.n k r)} {law : Measure (α × ℝ)}
    (hsupp : ∀ᵐ ω ∂law, ω ∈ p.blockSupport k r Q) {δ δs e : ℝ} (hδ : 0 < δ)
    (center : (Fin 4 → ℤ) → Fin 2 → ℝ) (Cd : ℝ≥0∞)
    (hdom : ∀ (σ : Fin 4 → ℤ) (j : ℤ),
      law {ω | p.nativeState k r Q δ δs ω = σ ∧ ⌊p.b k ω.1 3 / δ⌋ = j} ≤
        Cd * law {ω | p.nativeState k r Q δ δs ω = σ} * p.π k {x | ⌊x / δ⌋ = j})
    (qq : Fin 4 → ℤ) (j : ℤ) :
    p.blockLaw k r Q law {x |
        ![⌊(![x.2, p.normB k r Q x.1 + x.2 * (p.normV k x.1 - p.c k r Q 1)] : Fin 2 → ℝ) 0 / δ⌋,
          ⌊(![x.2, p.normB k r Q x.1 + x.2 * (p.normV k x.1 - p.c k r Q 1)] : Fin 2 → ℝ) 1 / δ⌋,
          ⌊p.normF k r Q δ δs center x 0 / e⌋, ⌊p.normF k r Q δ δs center x 1 / e⌋] = qq ∧
        ⌊p.normV k x.1 / δ⌋ = j} ≤
      Cd * p.blockLaw k r Q law {x |
        ![⌊(![x.2, p.normB k r Q x.1 + x.2 * (p.normV k x.1 - p.c k r Q 1)] : Fin 2 → ℝ) 0 / δ⌋,
          ⌊(![x.2, p.normB k r Q x.1 + x.2 * (p.normV k x.1 - p.c k r Q 1)] : Fin 2 → ℝ) 1 / δ⌋,
          ⌊p.normF k r Q δ δs center x 0 / e⌋, ⌊p.normF k r Q δ δs center x 1 / e⌋] = qq} *
        p.π k (Ico ((j : ℝ) * δ) (((j : ℝ) + 1) * δ)) := by
  set M := p.blockEquiv k r Q with hM
  set ns := p.nativeState k r Q δ δs with hns
  have hS : law (p.blockSupport k r Q)ᶜ = 0 := ae_iff.mp hsupp
  have hstate : ∀ ω ∈ p.blockSupport k r Q,
      ![⌊(![(M ω).2, p.normB k r Q (M ω).1 + (M ω).2 * (p.normV k (M ω).1 - p.c k r Q 1)] :
          Fin 2 → ℝ) 0 / δ⌋,
        ⌊(![(M ω).2, p.normB k r Q (M ω).1 + (M ω).2 * (p.normV k (M ω).1 - p.c k r Q 1)] :
          Fin 2 → ℝ) 1 / δ⌋,
        ⌊p.normF k r Q δ δs center (M ω) 0 / e⌋, ⌊p.normF k r Q δ δs center (M ω) 1 / e⌋] =
        coarseState e center (ns ω) := by
    intro ω hω
    obtain ⟨h1, h2, -⟩ := hat.normalized_coords Q hω
    rw [hM, p.normF_blockEquiv]
    rw [← hM] at h1 h2 ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h2, h1]
    rfl
  have hctrl : ∀ ω ∈ p.blockSupport k r Q, ⌊p.normV k (M ω).1 / δ⌋ = ⌊p.b k ω.1 3 / δ⌋ := by
    intro ω hω
    rw [(hat.normalized_coords Q hω).2.2]
  have hA : M ⁻¹' {x |
        ![⌊(![x.2, p.normB k r Q x.1 + x.2 * (p.normV k x.1 - p.c k r Q 1)] : Fin 2 → ℝ) 0 / δ⌋,
          ⌊(![x.2, p.normB k r Q x.1 + x.2 * (p.normV k x.1 - p.c k r Q 1)] : Fin 2 → ℝ) 1 / δ⌋,
          ⌊p.normF k r Q δ δs center x 0 / e⌋, ⌊p.normF k r Q δ δs center x 1 / e⌋] = qq ∧
        ⌊p.normV k x.1 / δ⌋ = j} ∩ p.blockSupport k r Q =
      {ω | coarseState e center (ns ω) = qq ∧ ⌊p.b k ω.1 3 / δ⌋ = j} ∩
        p.blockSupport k r Q := by
    ext ω
    constructor
    · rintro ⟨hω, hS⟩
      refine ⟨?_, hS⟩
      simp only [mem_preimage, mem_ofPred_eq] at hω
      rw [hstate ω hS, hctrl ω hS] at hω
      exact hω
    · rintro ⟨hω, hS⟩
      refine ⟨?_, hS⟩
      simp only [mem_preimage, mem_ofPred_eq]
      rw [hstate ω hS, hctrl ω hS]
      exact hω
  have hB : M ⁻¹' {x |
        ![⌊(![x.2, p.normB k r Q x.1 + x.2 * (p.normV k x.1 - p.c k r Q 1)] : Fin 2 → ℝ) 0 / δ⌋,
          ⌊(![x.2, p.normB k r Q x.1 + x.2 * (p.normV k x.1 - p.c k r Q 1)] : Fin 2 → ℝ) 1 / δ⌋,
          ⌊p.normF k r Q δ δs center x 0 / e⌋, ⌊p.normF k r Q δ δs center x 1 / e⌋] = qq} ∩
        p.blockSupport k r Q =
      {ω | coarseState e center (ns ω) = qq} ∩ p.blockSupport k r Q := by
    ext ω
    constructor
    · rintro ⟨hω, hS⟩
      refine ⟨?_, hS⟩
      simp only [mem_preimage, mem_ofPred_eq] at hω
      rw [hstate ω hS] at hω
      exact hω
    · rintro ⟨hω, hS⟩
      refine ⟨?_, hS⟩
      simp only [mem_preimage, mem_ofPred_eq]
      rw [hstate ω hS]
      exact hω
  have hdom' := FieldCommon.refine_domination law (p.measurable_nativeState hb r Q δ δs)
    (ctrl := fun ω => ⌊p.b k ω.1 3 / δ⌋) (fun j => p.π k {x | ⌊x / δ⌋ = j}) Cd hdom
    (coarseState e center) qq j
  have hπ : p.π k {x | ⌊x / δ⌋ = j} = p.π k (Ico ((j : ℝ) * δ) (((j : ℝ) + 1) * δ)) := by
    congr 1
    ext x
    exact FieldCommon.floor_div_eq_iff_mem_Ico hδ j
  rw [blockLaw_apply, blockLaw_apply, FieldCommon.measure_eq_of_inter_eq hS hA,
    FieldCommon.measure_eq_of_inter_eq hS hB, ← hπ]
  calc (p.blockWeight k r Q)⁻¹ *
        law {ω | coarseState e center (ns ω) = qq ∧ ⌊p.b k ω.1 3 / δ⌋ = j} ≤
      (p.blockWeight k r Q)⁻¹ * (Cd * law {ω | coarseState e center (ns ω) = qq} *
        p.π k {x | ⌊x / δ⌋ = j}) := by gcongr
    _ = Cd * ((p.blockWeight k r Q)⁻¹ * law {ω | coarseState e center (ns ω) = qq}) *
        p.π k {x | ⌊x / δ⌋ = j} := by ring

end Parent

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
