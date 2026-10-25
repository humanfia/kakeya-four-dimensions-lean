-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Common.Ready; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254 (k4_general_parent_wide_layer_candidates), session x0900. -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Common.AtScale

/-!
# A field-ready law from a consensus law, at one fixed `k`

`Parent.fieldReady_at`: at one fixed `k`, given the two native-signal groups of the consensus
law's block, original fine caps, and explicit numerical hypotheses, the frozen statement of
o273 at the scale `N = N_k` (`CommonFieldAt`) applied to the normalized law of the consensus
law restricted to its half-states on the groups produces a field-ready law.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] {p : Parent α}

theorem smul_measure_mono {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {c d : ℝ≥0∞}
    (hcd : c ≤ d) : c • μ ≤ d • μ :=
  IsOrderedSMul.smul_le_smul_right c d hcd μ

set_option maxHeartbeats 1000000 in
/-- **A field-ready law at one fixed `k`.** -/
theorem fieldReady_at (h : p.Valid) {k : ℕ} {r u v m H R : ℝ}
    (hat : p.AtDepth k r R) (hKH : p.K k ≤ H)
    (s : p.ComparedSample k r u v m H)
    {C₀ A θ ε₁ η' η : ℝ} (hm : 0 ≤ m) (hmA : m ≤ A) (hθ : 0 < θ) (hε₁ : 0 < ε₁)
    (c : p.ConsensusLaw k s (C₀ * (A + θ)) (r + u) (C₀ * (A + θ)) (p.N k ^ (-θ))
      (p.N k ^ η))
    (hO : CommonFieldAt p.S C₀ A θ (ε₁ / 2) η' (p.N k) α)
    {E : Fin 2 → Set (α × ℝ)} (hEm : ∀ e, MeasurableSet (E e))
    (hEsub : ∀ e, E e ⊆ p.B k r c.block ×ˢ Parent.block (p.T k r) (p.j k r c.block))
    {Lf : ℝ}
    (hEloss : p.μ k ((p.B k r c.block ×ˢ Parent.block (p.T k r) (p.j k r c.block)) \
        ⋃ e, E e) ≤
      p.μ k (p.B k r c.block ×ˢ Parent.block (p.T k r) (p.j k r c.block)) * ENNReal.ofReal Lf)
    {δU Mf s' vMin vMax : ℝ} (hδU : 0 < δU) (hs'r : s' ≤ r) (hs'0 : 0 ≤ s')
    (hosc : ∀ e, ∀ z ∈ E e, ∀ z' ∈ E e,
      (∀ c' : Fin 3, |p.base k z.1 z.2 c' - p.base k z'.1 z'.2 c'| ≤
        (p.K k + 1) ^ 2 * p.blockLen k r * p.N k ^ (-(C₀ * (A + θ))) +
          p.blockWidth k r * δU) →
      |p.signal k z.1 z.2 - p.signal k z'.1 z'.2| ≤ p.N k ^ (-s'))
    (hfc : FineCaps p k Mf r vMin vMax)
    (hfine1 : (p.K k + p.K k ^ 2) * p.N k ^ (-Mf) ≤
      p.blockLen k r * p.N k ^ (-(C₀ * (A + θ))))
    (hfine2 : (p.K k + p.K k ^ 2) * p.N k ^ (-Mf) ≤ p.blockWidth k r * δU)
    (hshear : p.K k * p.blockLen k r * p.N k ^ (-(C₀ * (A + θ))) ≤ p.blockWidth k r * δU)
    (hδUK : δU ≤ p.K k)
    (hvη : vMin ≤ η') (hvδ : p.N k ^ (-vMax) ≤ p.N k ^ (-(C₀ * (A + θ))))
    (n1 : 98 * H ^ 4 + 1 ≤ p.N k ^ η')
    (n2 : 2 * p.N k ^ η ≤ p.N k ^ η')
    (n3 : 24 * p.K k * H * Lf ≤ 1)
    (n4 : 32 * H ^ 4 * p.N k ^ (-m) / p.N k ^ (-p.ℓ * r) ≤ p.N k ^ (-θ))
    (n5 : 1 + p.N k ^ (ε₁ / 2) ≤ p.N k ^ ε₁)
    (n6 : 67200 * p.K k ^ 3 * p.N k ^ (r - s') ≤ p.N k ^ η') :
    Nonempty (p.FieldReady k s (p.N k ^ (-θ)) ε₁) := by
  have hN2 : 2 ≤ p.N k := h.scale k
  have hN : 0 < p.N k := by linarith
  have hN1 : 1 ≤ p.N k := by linarith
  have hN1' : 1 < p.N k := by linarith
  have hK : 1 ≤ p.K k := h.subpower.1 k
  have hH1 : 1 ≤ H := by linarith [s.loss_one]
  have hH0 : 0 < H := by linarith
  have hH4 : 1 ≤ H ^ 4 := one_le_pow₀ hH1
  have hHH4 : H ≤ H ^ 4 := by
    calc H = H ^ 1 := (pow_one H).symm
      _ ≤ H ^ 4 := pow_le_pow_right₀ hH1 (by norm_num)
  have hδ0 : 0 < p.N k ^ (-(C₀ * (A + θ))) := Real.rpow_pos_of_pos hN _
  have he0 : 0 < p.N k ^ (-θ) := Real.rpow_pos_of_pos hN _
  have he1 : p.N k ^ (-θ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hNη : 0 < p.N k ^ η' := Real.rpow_pos_of_pos hN _
  have hNη2 : 2 ≤ p.N k ^ η' := by nlinarith
  have hcK : ∀ e, |p.c k r c.block e| ≤ p.K k := (hat.commonParentGeometry).coefficient_bound c.block
  have a := hat.commonParentGeometry
  have hb := (h.basic k).1
  have : IsProbabilityMeasure (p.π k) := (h.basic k).2.2.1
  have hBm : MeasurableSet (p.B k r c.block) := (hat.2.2.1 c.block).2.1
  have hBA : p.B k r c.block ⊆ p.A k r c.block := (hat.2.2.1 c.block).2.2
  have hA0 : p.ν k (p.A k r c.block) ≠ 0 := by
    intro h0
    have hpl := a.prior_lower c.block
    rw [h0, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hpl
    have : 0 < (p.N k ^ (-r)) ^ p.d * (((2 : ℝ) ^ p.T k r)⁻¹) ^ 2 * p.N k ^ (-p.ℓ * r) /
        p.K k := by
      have : 0 < (p.N k ^ (-r)) ^ p.d := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hN _) _
      have : 0 < p.N k ^ (-p.ℓ * r) := Real.rpow_pos_of_pos hN _
      have : 0 < p.K k := by linarith
      positivity
    linarith
  have hbw0 := blockWeight_ne_zero hA0
  have hbwt := blockWeight_ne_top h k r c.block
  -- the half-states of the groups
  obtain ⟨Keep, hKm, hKG, hmass, hdom⟩ := c.keep_groups h (MeasurableSet.iUnion hEm) hBm hBA
    hEloss n3 hH0
  have := c.finite
  set law₁ := c.law.restrict Keep with hlaw₁
  have hlaw₁c : law₁ ≤ c.law := Measure.restrict_le_self
  have hlaw₁μ : law₁ ≤ p.μ k :=
    hlaw₁c.trans (c.le_law.trans (s.le_rho.trans (h.basic k).2.2.2.2.1))
  have hfacts : ∀ᵐ ω ∂law₁, ω.1 ∈ p.B k r c.block ∧
      ω.2 ∈ Parent.block (p.T k r) (p.j k r c.block) ∧ |p.b k ω.1 3| ≤ p.K k ∧
      ∀ i, ω.1 ∈ (s.layers 0).C i → i ∈ s.coarseChoices c.block ((s.layers 0).tag i) :=
    ae_mono hlaw₁c (c.ae_facts h hat)
  have hsuppS : ∀ᵐ ω ∂law₁, ω ∈ p.blockSupport k r c.block :=
    Filter.Eventually.mono hfacts (fun ω hω => ⟨hBA hω.1, hω.2.2.1⟩)
  have hsuppA : ∀ᵐ ω ∂law₁, ω.1 ∈ p.A k r c.block :=
    Filter.Eventually.mono hfacts (fun ω hω => hBA hω.1)
  have hsuppT : ∀ᵐ ω ∂law₁, ω.2 ∈ Parent.block (p.T k r) (p.j k r c.block) :=
    Filter.Eventually.mono hfacts (fun ω hω => hω.2.1)
  -- the hypotheses of o273
  have hχA : p.N k ^ (-A) ≤ p.N k ^ (-m) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hχ1 : p.N k ^ (-m) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hbv : ∀ l, |p.normB k r c.block l| + |p.normV k l| + |p.c k r c.block 1| ≤ p.N k ^ η' := by
    intro l
    have h1 := abs_normB_le h k r c.block l
    have h2 := abs_normV_le h k l
    have h3 := hcK 1
    nlinarith
  have hdomle : p.blockLaw k r c.block law₁ ≤
      ENNReal.ofReal (p.N k ^ η') • ((p.blockPrior k r c.block).prod volume) := by
    refine (blockLaw_le h hlaw₁μ hsuppA).trans (smul_measure_mono _ ?_)
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  have hsupp1 := blockLaw_time_support hsuppT
  have hmass' : ENNReal.ofReal (p.N k ^ (-η')) ≤ p.blockLaw k r c.block law₁ univ := by
    rw [blockLaw_univ, hlaw₁, Measure.restrict_apply_univ]
    have h8 : p.N k ^ (-η') ≤ 1 / (8 * H) := by
      rw [Real.rpow_neg hN.le, le_div_iff₀ (by positivity), inv_mul_eq_div,
        div_le_one hNη]
      nlinarith
    calc ENNReal.ofReal (p.N k ^ (-η')) ≤ ENNReal.ofReal (1 / (8 * H)) :=
          ENNReal.ofReal_le_ofReal h8
      _ = (p.blockWeight k r c.block)⁻¹ *
            (ENNReal.ofReal (1 / (8 * H)) * p.blockWeight k r c.block) := by
          rw [mul_comm (ENNReal.ofReal _), ← mul_assoc, ENNReal.inv_mul_cancel hbw0 hbwt,
            one_mul]
      _ ≤ (p.blockWeight k r c.block)⁻¹ * c.law Keep := by gcongr
  have hfbound := blockLaw_normF_bound h hat a hKH c hlaw₁c
    (bound := p.N k ^ η') (by nlinarith)
  have hcell : ∀ q0 q1 : ℤ, law₁ {ω | ⌊p.tauN k r c.block ω / p.N k ^ (-(C₀ * (A + θ)))⌋ = q0 ∧
      ⌊p.zetaN k r c.block ω / p.N k ^ (-(C₀ * (A + θ)))⌋ = q1} ≤
      ENNReal.ofReal (p.N k ^ η' * (p.N k ^ (-(C₀ * (A + θ)))) ^ 2) *
        p.blockWeight k r c.block := by
    intro q0 q1
    rw [hlaw₁, Measure.restrict_apply' hKm]
    have hcap : ∀ (q : Fin 3 → ℤ) (j : ℤ),
        p.μ k {ω | (fun i => ⌊p.finePoint k ω i / p.N k ^ (-Mf)⌋) = q ∧
          ⌊p.signal k ω.1 ω.2 / p.N k ^ (-s')⌋ = j} ≤
          ENNReal.ofReal (p.K k * (p.N k ^ (-s')) ^ p.d * (p.N k ^ (-Mf)) ^ 3) := by
      intro q j
      calc p.μ k {ω | (fun i => ⌊p.finePoint k ω i / p.N k ^ (-Mf)⌋) = q ∧
            ⌊p.signal k ω.1 ω.2 / p.N k ^ (-s')⌋ = j} ≤
          ENNReal.ofReal (p.K k * (p.N k ^ (-Mf)) ^ 3 * (p.N k ^ (-s')) ^ p.d) :=
            hfc.pure s' hs'0 hs'r q j
        _ = ENNReal.ofReal (p.K k * (p.N k ^ (-s')) ^ p.d * (p.N k ^ (-Mf)) ^ 3) := by
            congr 1
            ring
    have hcc := group_cell_cap_weight h a c.block hEsub hδ0 hδU (Real.rpow_pos_of_pos hN _)
      hs'r hosc hcap hfine1 hfine2 hshear hδUK q0 q1
    calc c.law ({ω | ⌊p.tauN k r c.block ω / p.N k ^ (-(C₀ * (A + θ)))⌋ = q0 ∧
          ⌊p.zetaN k r c.block ω / p.N k ^ (-(C₀ * (A + θ)))⌋ = q1} ∩ Keep) ≤
        c.law ({ω | ⌊p.tauN k r c.block ω / p.N k ^ (-(C₀ * (A + θ)))⌋ = q0 ∧
          ⌊p.zetaN k r c.block ω / p.N k ^ (-(C₀ * (A + θ)))⌋ = q1} ∩ ⋃ e, E e) :=
          measure_mono (inter_subset_inter_right _ hKG)
      _ ≤ p.μ k ({ω | ⌊p.tauN k r c.block ω / p.N k ^ (-(C₀ * (A + θ)))⌋ = q0 ∧
          ⌊p.zetaN k r c.block ω / p.N k ^ (-(C₀ * (A + θ)))⌋ = q1} ∩ ⋃ e, E e) :=
          (c.le_law.trans (s.le_rho.trans (h.basic k).2.2.2.2.1)) _
      _ ≤ ENNReal.ofReal (67200 * p.K k ^ 3 * p.N k ^ (r - s') *
            (p.N k ^ (-(C₀ * (A + θ)))) ^ 2) * p.blockWeight k r c.block := hcc
      _ ≤ ENNReal.ofReal (p.N k ^ η' * (p.N k ^ (-(C₀ * (A + θ)))) ^ 2) *
            p.blockWeight k r c.block := by
          gcongr
  have hcellN := blockLaw_cell_le h hat hA0 hsuppS hcell
  have hfrost := FieldCommon.frostman_of_palette (π := p.π k) hN1' h.palette_le_one
    hfc.palette hvδ hvη (by nlinarith)
  have hdom' : ∀ (σ : Fin 4 → ℤ) (j : ℤ),
      law₁ {ω | p.nativeState k r c.block (p.N k ^ (-(C₀ * (A + θ)))) (p.N k ^ (-(r + u))) ω =
          σ ∧ ⌊p.b k ω.1 3 / p.N k ^ (-(C₀ * (A + θ)))⌋ = j} ≤
        (2 * ENNReal.ofReal (p.N k ^ η)) *
          law₁ {ω | p.nativeState k r c.block (p.N k ^ (-(C₀ * (A + θ))))
            (p.N k ^ (-(r + u))) ω = σ} *
          p.π k {x | ⌊x / p.N k ^ (-(C₀ * (A + θ)))⌋ = j} := hdom
  have hCd : 2 * ENNReal.ofReal (p.N k ^ η) ≤ ENNReal.ofReal (p.N k ^ η') := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal n2
  have hstate : ∀ (qq : Fin 4 → ℤ) (j : ℤ),
      p.blockLaw k r c.block law₁ {x |
        ![⌊(![x.2, p.normB k r c.block x.1 + x.2 * (p.normV k x.1 - p.c k r c.block 1)] :
            Fin 2 → ℝ) 0 / p.N k ^ (-(C₀ * (A + θ)))⌋,
          ⌊(![x.2, p.normB k r c.block x.1 + x.2 * (p.normV k x.1 - p.c k r c.block 1)] :
            Fin 2 → ℝ) 1 / p.N k ^ (-(C₀ * (A + θ)))⌋,
          ⌊p.normF k r c.block (p.N k ^ (-(C₀ * (A + θ)))) (p.N k ^ (-(r + u))) c.center x 0 /
            p.N k ^ (-θ)⌋,
          ⌊p.normF k r c.block (p.N k ^ (-(C₀ * (A + θ)))) (p.N k ^ (-(r + u))) c.center x 1 /
            p.N k ^ (-θ)⌋] = qq ∧
        ⌊p.normV k x.1 / p.N k ^ (-(C₀ * (A + θ)))⌋ = j} ≤
      ENNReal.ofReal (p.N k ^ η') * p.blockLaw k r c.block law₁ {x |
        ![⌊(![x.2, p.normB k r c.block x.1 + x.2 * (p.normV k x.1 - p.c k r c.block 1)] :
            Fin 2 → ℝ) 0 / p.N k ^ (-(C₀ * (A + θ)))⌋,
          ⌊(![x.2, p.normB k r c.block x.1 + x.2 * (p.normV k x.1 - p.c k r c.block 1)] :
            Fin 2 → ℝ) 1 / p.N k ^ (-(C₀ * (A + θ)))⌋,
          ⌊p.normF k r c.block (p.N k ^ (-(C₀ * (A + θ)))) (p.N k ^ (-(r + u))) c.center x 0 /
            p.N k ^ (-θ)⌋,
          ⌊p.normF k r c.block (p.N k ^ (-(C₀ * (A + θ)))) (p.N k ^ (-(r + u))) c.center x 1 /
            p.N k ^ (-θ)⌋] = qq} *
        p.π k (Ico ((j : ℝ) * p.N k ^ (-(C₀ * (A + θ))))
          (((j : ℝ) + 1) * p.N k ^ (-(C₀ * (A + θ))))) := by
    intro qq j
    refine (blockLaw_state_domination hat hb hsuppS hδ0 c.center _ hdom' qq j).trans ?_
    gcongr
  have hcard : ∀ key, ((p.fiberList s c.block (p.N k ^ (-m)) (p.N k ^ η') key).card : ℝ) ≤
      p.N k ^ η' := by
    intro key
    refine (card_fiberList_le s c.block _ _ key).trans ?_
    nlinarith
  have hlistb := fiberList_bound s c.block (p.N k ^ (-m)) (p.N k ^ η')
  have hagree := blockLaw_fiber_agree h hat a hKH c hlaw₁c (bound := p.N k ^ η')
    (tol := p.N k ^ η' * p.N k ^ (-θ)) (by nlinarith) (n4.trans he1) (by nlinarith)
  -- apply o273
  obtain ⟨Cc, hCb, hCm⟩ := hO (p.blockPrior k r c.block) (p.blockLaw k r c.block law₁) (p.π k)
    (p.normB k r c.block) (p.normV k) (p.c k r c.block 1) (p.N k ^ (-m)) (p.N k ^ (-m))
    (p.normF k r c.block (p.N k ^ (-(C₀ * (A + θ)))) (p.N k ^ (-(r + u))) c.center)
    (p.fiberList s c.block (p.N k ^ (-m)) (p.N k ^ η'))
    (measurable_normB hb r c.block) (measurable_normV hb) (measurable_normF hb r c.block _ _ _)
    (blockPrior_isProbability h hA0) (h.basic k).2.2.1 hχA hχ1 hχA hχ1 hbv hdomle hsupp1
    hmass' hfbound hcellN hfrost hstate hcard hlistb hagree
  -- the field-ready law
  have hfM : ∀ ω, p.normF k r c.block (p.N k ^ (-(C₀ * (A + θ)))) (p.N k ^ (-(r + u))) c.center
      (p.blockEquiv k r c.block ω) =
      c.center (p.nativeState k r c.block (p.N k ^ (-(C₀ * (A + θ)))) (p.N k ^ (-(r + u))) ω) :=
    fun ω => p.normF_blockEquiv k r c.block _ _ c.center ω
  have hfm := measurable_normF hb r c.block (p.N k ^ (-(C₀ * (A + θ)))) (p.N k ^ (-(r + u)))
    c.center
  have hf0 : Measurable (fun x : α × ℝ => p.normF k r c.block (p.N k ^ (-(C₀ * (A + θ))))
      (p.N k ^ (-(r + u))) c.center x 0) := (measurable_pi_apply 0).comp hfm
  have hf1 : Measurable (fun x : α × ℝ => p.normF k r c.block (p.N k ^ (-(C₀ * (A + θ))))
      (p.N k ^ (-(r + u))) c.center x 1) := (measurable_pi_apply 1).comp hfm
  have hBmeas : Measurable (fun x : α × ℝ => p.normB k r c.block x.1) :=
    (measurable_normB hb r c.block).comp measurable_fst
  have hVmeas : Measurable (fun x : α × ℝ => p.normV k x.1) :=
    (measurable_normV hb).comp measurable_fst
  set Good : Set (α × ℝ) := {x |
    |p.normF k r c.block (p.N k ^ (-(C₀ * (A + θ)))) (p.N k ^ (-(r + u))) c.center x 0 - Cc 0 -
        Cc 1 * x.2 - Cc 2 * (p.normB k r c.block x.1 + x.2 * (p.normV k x.1 - p.c k r c.block 1))| ≤
      p.N k ^ (ε₁ / 2) * p.N k ^ (-θ) ∧
    |p.normF k r c.block (p.N k ^ (-(C₀ * (A + θ)))) (p.N k ^ (-(r + u))) c.center x 1 - Cc 3| ≤
      p.N k ^ (ε₁ / 2) * p.N k ^ (-θ)} with hGood
  have hCm' : ENNReal.ofReal (p.N k ^ (-(ε₁ / 2))) ≤ p.blockLaw k r c.block law₁ Good := hCm
  have hGm : MeasurableSet Good := by
    have hF0 : Measurable (fun x : α × ℝ =>
        |p.normF k r c.block (p.N k ^ (-(C₀ * (A + θ)))) (p.N k ^ (-(r + u))) c.center x 0 -
          Cc 0 - Cc 1 * x.2 - Cc 2 * (p.normB k r c.block x.1 + x.2 *
            (p.normV k x.1 - p.c k r c.block 1))|) :=
      (((hf0.sub measurable_const).sub (measurable_const.mul measurable_snd)).sub
        (measurable_const.mul (hBmeas.add (measurable_snd.mul
          (hVmeas.sub measurable_const))))).abs
    have hF1 : Measurable (fun x : α × ℝ =>
        |p.normF k r c.block (p.N k ^ (-(C₀ * (A + θ)))) (p.N k ^ (-(r + u))) c.center x 1 -
          Cc 3|) := (hf1.sub measurable_const).abs
    exact (measurableSet_le hF0 measurable_const).inter (measurableSet_le hF1 measurable_const)
  have hMGm : MeasurableSet (p.blockEquiv k r c.block ⁻¹' Good) :=
    (p.blockEquiv k r c.block).measurable hGm
  refine ⟨{ block := c.block
            law := law₁.restrict (p.blockEquiv k r c.block ⁻¹' Good)
            le_law := Measure.restrict_le_self.trans (hlaw₁c.trans c.le_law)
            finite := inferInstance
            support := ae_restrict_of_ae (ae_mono hlaw₁c c.support)
            mass_lower := ?_
            C := Cc
            C_bound := ?_
            field := ?_ }⟩
  · -- the mass floor
    rw [Measure.restrict_apply_univ]
    rw [blockLaw_apply] at hCm'
    have hle : p.N k ^ (-ε₁) ≤ p.N k ^ (-(ε₁ / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    calc ENNReal.ofReal (p.N k ^ (-ε₁)) * p.blockWeight k r c.block ≤
          ENNReal.ofReal (p.N k ^ (-(ε₁ / 2))) * p.blockWeight k r c.block := by
          gcongr
      _ ≤ ((p.blockWeight k r c.block)⁻¹ * law₁ (p.blockEquiv k r c.block ⁻¹' Good)) *
            p.blockWeight k r c.block := by gcongr
      _ = law₁ (p.blockEquiv k r c.block ⁻¹' Good) := by
          rw [mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel hbw0 hbwt, one_mul]
  · -- the coefficient bound
    intro i
    exact (hCb i).trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  · -- the common field
    have hε : 0 ≤ p.N k ^ (ε₁ / 2) := (Real.rpow_pos_of_pos hN _).le
    filter_upwards [ae_restrict_mem hMGm, ae_restrict_of_ae (ae_mono hlaw₁c c.agree),
      ae_restrict_of_ae hsuppS] with ω hωG hagr hS
    obtain ⟨i, hCi, hag⟩ := hagr
    obtain ⟨hG0, hG1⟩ := hωG
    obtain ⟨h1, h2, -⟩ := hat.normalized_coords c.block hS
    rw [hfM] at hG0 hG1
    rw [h2, h1] at hG0
    refine ⟨i, hCi, ?_, ?_⟩
    · have hag0 := hag 0
      calc |p.transPair k r c.block ((s.layers 0).G i) ω 0 -
            (Cc 0 + Cc 1 * p.tauN k r c.block ω + Cc 2 * p.zetaN k r c.block ω)| ≤
          |p.transPair k r c.block ((s.layers 0).G i) ω 0 -
              c.center (p.nativeState k r c.block (p.N k ^ (-(C₀ * (A + θ))))
                (p.N k ^ (-(r + u))) ω) 0| +
            |c.center (p.nativeState k r c.block (p.N k ^ (-(C₀ * (A + θ))))
                (p.N k ^ (-(r + u))) ω) 0 - Cc 0 - Cc 1 * p.tauN k r c.block ω -
              Cc 2 * p.zetaN k r c.block ω| := by
            have he : p.transPair k r c.block ((s.layers 0).G i) ω 0 -
                (Cc 0 + Cc 1 * p.tauN k r c.block ω + Cc 2 * p.zetaN k r c.block ω) =
                (p.transPair k r c.block ((s.layers 0).G i) ω 0 -
                  c.center (p.nativeState k r c.block (p.N k ^ (-(C₀ * (A + θ))))
                    (p.N k ^ (-(r + u))) ω) 0) +
                (c.center (p.nativeState k r c.block (p.N k ^ (-(C₀ * (A + θ))))
                    (p.N k ^ (-(r + u))) ω) 0 - Cc 0 - Cc 1 * p.tauN k r c.block ω -
                  Cc 2 * p.zetaN k r c.block ω) := by ring
            rw [he]
            exact abs_add_le _ _
        _ ≤ p.N k ^ (-θ) + p.N k ^ (ε₁ / 2) * p.N k ^ (-θ) := add_le_add hag0 hG0
        _ = (1 + p.N k ^ (ε₁ / 2)) * p.N k ^ (-θ) := by ring
        _ ≤ p.N k ^ ε₁ * p.N k ^ (-θ) := by gcongr
    · have hag1 := hag 1
      calc |p.transPair k r c.block ((s.layers 0).G i) ω 1 - Cc 3| ≤
          |p.transPair k r c.block ((s.layers 0).G i) ω 1 -
              c.center (p.nativeState k r c.block (p.N k ^ (-(C₀ * (A + θ))))
                (p.N k ^ (-(r + u))) ω) 1| +
            |c.center (p.nativeState k r c.block (p.N k ^ (-(C₀ * (A + θ))))
                (p.N k ^ (-(r + u))) ω) 1 - Cc 3| := abs_sub_le _ _ _
        _ ≤ p.N k ^ (-θ) + p.N k ^ (ε₁ / 2) * p.N k ^ (-θ) := add_le_add hag1 hG1
        _ = (1 + p.N k ^ (ε₁ / 2)) * p.N k ^ (-θ) := by ring
        _ ≤ p.N k ^ ε₁ * p.N k ^ (-θ) := by gcongr

end Parent

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
