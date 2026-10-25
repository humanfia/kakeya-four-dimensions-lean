-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Common.Normal; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254 (k4_general_parent_wide_layer_candidates), session x0900. -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Common.Measures
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Common.CellCap

/-!
# The normalized line-time law of one original block

For an original block `Q` at depth `r` with start `t₀` and length `q`:

* `blockEquiv`: `(l, t) ↦ (l, (t - t₀) / q)`, a measurable equivalence;
* `blockPrior`: the trajectory prior restricted to `A_Q` and normalized (a probability);
* `blockLaw law`: the pushforward of an original submeasure, divided by the reference weight
  `q ν(A_Q)` of the block;
* `normB`, `normV`: the normalized major intercept and the velocity `b₃`, clipped at `K` (they
  are unclipped on the block and on almost every trajectory);
* `normF`: a function of the native fine state, transported to normalized time.

An original submeasure of `μ` carried by `A_Q × ℝ` gives a normalized law dominated by `K`
times the normalized prior times Lebesgue measure; a law carried by the block's time interval
gives a normalized law carried by unit time.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- The time normalization of an original block. -/
def blockEquiv (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) : (α × ℝ) ≃ᵐ (α × ℝ) :=
  FieldCommon.timeEquiv α (p.blockStart k r Q) (p.blockLen k r) (p.common_blockLen_pos k r).ne'

theorem blockEquiv_apply (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (ω : α × ℝ) :
    p.blockEquiv k r Q ω = (ω.1, p.tauN k r Q ω) := rfl

theorem blockEquiv_symm_apply (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (x : α × ℝ) :
    (p.blockEquiv k r Q).symm x = (x.1, p.blockStart k r Q + p.blockLen k r * x.2) := rfl

/-- The normalized trajectory prior of an original block. -/
def blockPrior (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) : Measure α :=
  (p.ν k (p.A k r Q))⁻¹ • (p.ν k).restrict (p.A k r Q)

/-- The normalized line-time law of an original submeasure carried by a block. -/
def blockLaw (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (law : Measure (α × ℝ)) :
    Measure (α × ℝ) :=
  (p.blockWeight k r Q)⁻¹ • law.map (p.blockEquiv k r Q)

/-- Clipping to `[-M, M]`. -/
def clip (M x : ℝ) : ℝ := max (-M) (min M x)

theorem abs_clip_le {M : ℝ} (hM : 0 ≤ M) (x : ℝ) : |clip M x| ≤ M := by
  unfold clip
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem clip_of_abs_le {M x : ℝ} (h : |x| ≤ M) : clip M x = x := by
  unfold clip
  rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

theorem measurable_clip (M : ℝ) : Measurable (clip M) := by
  unfold clip
  fun_prop

/-- The clipped normalized major intercept. -/
def normB (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (l : α) : ℝ :=
  clip (p.K k) (p.majorIntercept k r Q l)

/-- The clipped velocity. -/
def normV (k : ℕ) (l : α) : ℝ := clip (p.K k) (p.b k l 3)

/-- A function of the native fine state, transported to normalized time. -/
def normF (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (δb δs : ℝ)
    (center : (Fin 4 → ℤ) → Fin 2 → ℝ) (x : α × ℝ) : Fin 2 → ℝ :=
  center (p.nativeState k r Q δb δs ((p.blockEquiv k r Q).symm x))

theorem normF_blockEquiv (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (δb δs : ℝ)
    (center : (Fin 4 → ℤ) → Fin 2 → ℝ) (ω : α × ℝ) :
    p.normF k r Q δb δs center (p.blockEquiv k r Q ω) =
      center (p.nativeState k r Q δb δs ω) := by
  unfold normF
  rw [MeasurableEquiv.symm_apply_apply]

variable {p}

theorem measurable_normB {k : ℕ} (hb : Measurable (p.b k)) (r : ℝ) (Q : Fin (p.n k r)) :
    Measurable (p.normB k r Q) := by
  unfold normB majorIntercept
  exact (measurable_clip _).comp (by fun_prop)

theorem measurable_normV {k : ℕ} (hb : Measurable (p.b k)) : Measurable (p.normV k) := by
  unfold normV
  exact (measurable_clip _).comp (by fun_prop)

theorem measurable_normF {k : ℕ} (hb : Measurable (p.b k)) (r : ℝ) (Q : Fin (p.n k r)) (δb δs : ℝ)
    (center : (Fin 4 → ℤ) → Fin 2 → ℝ) : Measurable (p.normF k r Q δb δs center) := by
  unfold normF
  exact (measurable_of_countable center).comp
    ((p.measurable_nativeState hb r Q δb δs).comp (p.blockEquiv k r Q).symm.measurable)

theorem abs_normB_le (h : p.Valid) (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (l : α) :
    |p.normB k r Q l| ≤ p.K k :=
  abs_clip_le (by linarith [h.subpower.1 k]) _

theorem abs_normV_le (h : p.Valid) (k : ℕ) (l : α) : |p.normV k l| ≤ p.K k :=
  abs_clip_le (by linarith [h.subpower.1 k]) _

theorem normV_eq {k : ℕ} {l : α} (hl : |p.b k l 3| ≤ p.K k) : p.normV k l = p.b k l 3 :=
  clip_of_abs_le hl

/-- The block start lies in the block, and so does the block end. -/
theorem common_blockStart_mem (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) :
    p.blockStart k r Q ∈ block (p.T k r) (p.j k r Q) := by
  change p.blockStart k r Q ∈ Icc (((p.j k r Q : ℕ) : ℝ) / 2 ^ p.T k r)
    ((((p.j k r Q : ℕ) : ℝ) + 1) / 2 ^ p.T k r)
  unfold blockStart
  constructor
  · exact le_rfl
  · apply div_le_div_of_nonneg_right (by linarith) (by positivity)

theorem common_blockEnd_mem (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) :
    p.blockStart k r Q + p.blockLen k r ∈ block (p.T k r) (p.j k r Q) := by
  change p.blockStart k r Q + p.blockLen k r ∈ Icc (((p.j k r Q : ℕ) : ℝ) / 2 ^ p.T k r)
    ((((p.j k r Q : ℕ) : ℝ) + 1) / 2 ^ p.T k r)
  unfold blockStart blockLen
  have h2 : (0 : ℝ) < 2 ^ p.T k r := by positivity
  constructor
  · have : 0 ≤ ((2 : ℝ) ^ p.T k r)⁻¹ := by positivity
    linarith
  · rw [div_add' _ _ _ h2.ne', inv_mul_cancel₀ h2.ne']

theorem common_block_subset_unit (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) :
    block (p.T k r) (p.j k r Q) ⊆ Icc (0 : ℝ) 1 := by
  intro t ht
  change t ∈ Icc (((p.j k r Q : ℕ) : ℝ) / 2 ^ p.T k r)
    ((((p.j k r Q : ℕ) : ℝ) + 1) / 2 ^ p.T k r) at ht
  have h2 : (0 : ℝ) < 2 ^ p.T k r := by positivity
  have hj : ((p.j k r Q : ℕ) : ℝ) + 1 ≤ 2 ^ p.T k r := by
    have := (p.j k r Q).isLt
    exact_mod_cast this
  constructor
  · exact le_trans (by positivity) ht.1
  · exact ht.2.trans ((div_le_one h2).mpr hj)

/-- The block time of a time of the block lies in `[0, 1]`. -/
theorem common_tauN_mem_unit (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) {ω : α × ℝ}
    (hω : ω.2 ∈ block (p.T k r) (p.j k r Q)) : p.tauN k r Q ω ∈ Icc (0 : ℝ) 1 := by
  change ω.2 ∈ Icc (((p.j k r Q : ℕ) : ℝ) / 2 ^ p.T k r)
    ((((p.j k r Q : ℕ) : ℝ) + 1) / 2 ^ p.T k r) at hω
  unfold tauN blockStart blockLen
  have h2 : (0 : ℝ) < 2 ^ p.T k r := by positivity
  rw [div_inv_eq_mul]
  constructor
  · apply mul_nonneg _ h2.le
    linarith [hω.1]
  · have h := hω.2
    rw [add_div] at h
    have h' : ω.2 - ((p.j k r Q : ℕ) : ℝ) / 2 ^ p.T k r ≤ 1 / 2 ^ p.T k r := by linarith
    calc (ω.2 - ((p.j k r Q : ℕ) : ℝ) / 2 ^ p.T k r) * 2 ^ p.T k r ≤
          1 / 2 ^ p.T k r * 2 ^ p.T k r := mul_le_mul_of_nonneg_right h' h2.le
      _ = 1 := by field_simp

/-- On the block, the normalized major intercept is bounded by `K`, hence unclipped. -/
theorem AtDepth.normB_eq {R : ℝ} {k : ℕ} {r : ℝ} (hat : p.AtDepth k r R) (Q : Fin (p.n k r))
    {l : α} (hl : l ∈ p.A k r Q) : p.normB k r Q l = p.majorIntercept k r Q l := by
  apply clip_of_abs_le
  have hmaj := ((hat.2.2.2.2.1 Q).2.2.2.2.2.1 l hl (p.blockStart k r Q)
    (p.common_blockStart_mem k r Q)).1
  have hq := p.common_blockLen_pos k r
  have hq' : ((2 : ℝ) ^ (-(p.T k r : ℤ))) = p.blockLen k r := by
    unfold blockLen
    rw [zpow_neg, zpow_natCast]
  rw [hq'] at hmaj
  unfold majorIntercept
  rw [abs_div, abs_of_pos hq, div_le_iff₀ hq]
  have he : p.b k l 0 + p.blockStart k r Q * (p.b k l 3 - p.c k r Q 1) - p.c k r Q 0 =
      p.x k l (p.blockStart k r Q) 1 - p.c k r Q 0 - p.blockStart k r Q * p.c k r Q 1 := by
    simp only [Submission.Obl.k4_critical_intercept_concentration.Data.x,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    ring
  rw [he]
  exact hmaj

/-- The incidences of a block with unclipped velocity. -/
def blockSupport (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) : Set (α × ℝ) :=
  {ω | ω.1 ∈ p.A k r Q ∧ |p.b k ω.1 3| ≤ p.K k}

/-- On the block support, the normalized coordinates are the native block coordinates. -/
theorem AtDepth.normalized_coords {R : ℝ} {k : ℕ} {r : ℝ} (hat : p.AtDepth k r R)
    (Q : Fin (p.n k r)) {ω : α × ℝ} (hω : ω ∈ p.blockSupport k r Q) :
    (p.blockEquiv k r Q ω).2 = p.tauN k r Q ω ∧
      p.normB k r Q (p.blockEquiv k r Q ω).1 + (p.blockEquiv k r Q ω).2 *
        (p.normV k (p.blockEquiv k r Q ω).1 - p.c k r Q 1) = p.zetaN k r Q ω ∧
      p.normV k (p.blockEquiv k r Q ω).1 = p.b k ω.1 3 := by
  rw [p.blockEquiv_apply]
  refine ⟨rfl, ?_, normV_eq hω.2⟩
  simp only
  rw [hat.normB_eq Q hω.1, normV_eq hω.2, p.common_zetaN_eq]

/-! ### The normalized prior and law -/

theorem blockPrior_isProbability (h : p.Valid) {k : ℕ} {r : ℝ} {Q : Fin (p.n k r)}
    (hA0 : p.ν k (p.A k r Q) ≠ 0) : IsProbabilityMeasure (p.blockPrior k r Q) := by
  have : IsProbabilityMeasure (p.ν k) := (h.basic k).2.1
  constructor
  unfold blockPrior
  rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
    ENNReal.inv_mul_cancel hA0 (measure_ne_top _ _)]

theorem blockWeight_ne_top (h : p.Valid) (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) :
    p.blockWeight k r Q ≠ ⊤ := by
  have : IsProbabilityMeasure (p.ν k) := (h.basic k).2.1
  unfold blockWeight
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

theorem blockWeight_ne_zero {k : ℕ} {r : ℝ} {Q : Fin (p.n k r)}
    (hA0 : p.ν k (p.A k r Q) ≠ 0) : p.blockWeight k r Q ≠ 0 := by
  unfold blockWeight
  exact mul_ne_zero (ENNReal.ofReal_pos.mpr (p.common_blockLen_pos k r)).ne' hA0

theorem blockLaw_apply (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (law : Measure (α × ℝ))
    (X : Set (α × ℝ)) :
    p.blockLaw k r Q law X = (p.blockWeight k r Q)⁻¹ * law (p.blockEquiv k r Q ⁻¹' X) :=
  FieldCommon.scaled_map_apply law _ _ X

theorem ae_blockLaw {k : ℕ} {r : ℝ} {Q : Fin (p.n k r)} {law : Measure (α × ℝ)}
    {P : α × ℝ → Prop} (hP : ∀ᵐ ω ∂law, P (p.blockEquiv k r Q ω)) :
    ∀ᵐ x ∂p.blockLaw k r Q law, P x :=
  FieldCommon.ae_scaled_map _ _ hP

/-- **Domination of the normalized law** by `K` times the normalized prior times Lebesgue
measure. -/
theorem blockLaw_le (h : p.Valid) {k : ℕ} {r : ℝ} {Q : Fin (p.n k r)}
    {law : Measure (α × ℝ)} (hle : law ≤ p.μ k)
    (hsupp : ∀ᵐ ω ∂law, ω.1 ∈ p.A k r Q) :
    p.blockLaw k r Q law ≤
      ENNReal.ofReal (p.K k) • ((p.blockPrior k r Q).prod volume) := by
  have : IsProbabilityMeasure (p.ν k) := (h.basic k).2.1
  have hq := p.common_blockLen_pos k r
  set M := p.blockEquiv k r Q with hM
  set S : Set (α × ℝ) := p.A k r Q ×ˢ (univ : Set ℝ) with hSdef
  have hS : law Sᶜ = 0 := by
    have h0 := ae_iff.mp hsupp
    have he : Sᶜ = {ω : α × ℝ | ¬ ω.1 ∈ p.A k r Q} := by
      ext ω
      simp [hSdef]
    rw [he]
    exact h0
  have hprod : ((p.ν k).prod volume).restrict S = ((p.ν k).restrict (p.A k r Q)).prod volume := by
    rw [hSdef, ← Measure.prod_restrict, Measure.restrict_univ]
  have hbw : (p.blockWeight k r Q)⁻¹ =
      (ENNReal.ofReal (p.blockLen k r))⁻¹ * (p.ν k (p.A k r Q))⁻¹ := by
    unfold blockWeight
    exact ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.mpr hq).ne')
      (Or.inl ENNReal.ofReal_ne_top)
  have hq0 : ENNReal.ofReal (p.blockLen k r) ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
  rw [Measure.le_iff]
  intro X hX
  have hMX : MeasurableSet (M ⁻¹' X) := M.measurable hX
  calc p.blockLaw k r Q law X = (p.blockWeight k r Q)⁻¹ * law (M ⁻¹' X) :=
        p.blockLaw_apply k r Q law X
    _ = (p.blockWeight k r Q)⁻¹ * law (M ⁻¹' X ∩ S) := by rw [measure_inter_conull hS]
    _ ≤ (p.blockWeight k r Q)⁻¹ * p.μ k (M ⁻¹' X ∩ S) := by gcongr
    _ ≤ (p.blockWeight k r Q)⁻¹ *
          (ENNReal.ofReal (p.K k) * ((p.ν k).prod volume) (M ⁻¹' X ∩ S)) := by
        gcongr
        have h1 := (h.basic k).2.2.2.1 (M ⁻¹' X ∩ S)
        rw [Measure.smul_apply, smul_eq_mul] at h1
        exact h1
    _ = (p.blockWeight k r Q)⁻¹ * (ENNReal.ofReal (p.K k) *
          (((p.ν k).restrict (p.A k r Q)).prod volume) (M ⁻¹' X)) := by
        rw [← hprod, Measure.restrict_apply hMX]
    _ = (p.blockWeight k r Q)⁻¹ * (ENNReal.ofReal (p.K k) *
          (ENNReal.ofReal (p.blockLen k r) *
            (((p.ν k).restrict (p.A k r Q)).prod volume) X)) := by
        rw [← MeasurableEquiv.map_apply, hM, blockEquiv,
          FieldCommon.map_prod_timeEquiv _ hq, Measure.smul_apply, smul_eq_mul]
    _ = ((ENNReal.ofReal (p.blockLen k r))⁻¹ * ENNReal.ofReal (p.blockLen k r)) *
          (ENNReal.ofReal (p.K k) * ((p.ν k (p.A k r Q))⁻¹ *
            (((p.ν k).restrict (p.A k r Q)).prod volume) X)) := by
        rw [hbw]
        ring
    _ = (ENNReal.ofReal (p.K k) • ((p.blockPrior k r Q).prod volume)) X := by
        rw [ENNReal.inv_mul_cancel hq0 ENNReal.ofReal_ne_top, one_mul, Measure.smul_apply,
          smul_eq_mul, blockPrior, Measure.prod_smul_left, Measure.smul_apply, smul_eq_mul]

/-- A law carried by the block's time interval has its normalized law carried by unit
time. -/
theorem blockLaw_time_support {k : ℕ} {r : ℝ} {Q : Fin (p.n k r)} {law : Measure (α × ℝ)}
    (hsupp : ∀ᵐ ω ∂law, ω.2 ∈ block (p.T k r) (p.j k r Q)) :
    p.blockLaw k r Q law (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 := by
  have hae : ∀ᵐ x ∂p.blockLaw k r Q law, x ∈ (univ : Set α) ×ˢ Icc (0 : ℝ) 1 := by
    apply ae_blockLaw
    filter_upwards [hsupp] with ω hω
    exact ⟨mem_univ _, p.common_tauN_mem_unit k r Q hω⟩
  have h0 := ae_iff.mp hae
  have he : ((univ : Set α) ×ˢ Icc (0 : ℝ) 1)ᶜ =
      {x : α × ℝ | ¬ x ∈ (univ : Set α) ×ˢ Icc (0 : ℝ) 1} := rfl
  rw [he]
  exact h0

theorem blockLaw_univ (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (law : Measure (α × ℝ)) :
    p.blockLaw k r Q law univ = (p.blockWeight k r Q)⁻¹ * law univ := by
  rw [blockLaw_apply, preimage_univ]

end Parent

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
