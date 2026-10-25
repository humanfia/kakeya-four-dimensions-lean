import Submission.Obl.k4_scalar_candidate_original_return.Core.ListedMass
import Submission.Obl.k4_scalar_candidate_original_return.Core.Eventual
import Submission.Obl.k4_scalar_candidate_original_return.EncodingMain

/-!
# Candidate conversion

The globalized coverage of one positive scenario on one layer (`frequent_positive_layer`), the
per-plank comparison (`listed_mass`, `label_fit`, ...) and the original encoding
(`original_encoding`) give frequent recovered original charts, which the guard excludes.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Filter Set MvPolynomial

/-- The fixed depth and coefficient exponent of the listed families. -/
noncomputable def CmpParams.Rlist (π : CmpParams) : ℝ :=
  (π.σ.R : ℝ) + 2 / π.σ.s₀ + 2 * π.σ.s₀ + 2 * π.σ.c₀ + 2

namespace PreparedData

variable {a : PreparedData} (ha : a.Valid)
include ha

/-- One stage of a fixed positive scenario gives the analytical listed family. -/
theorem listedAt_of_stage (π : CmpParams) (k : ℕ) (s : ℝ)
    (hs : |s - π.σ.s₀| ≤ π.θ * π.σ.c₀ / 4 ∧ |s - π.σ.s₀| ≤ π.σ.s₀ / 2)
    (hpar : 0 < π.σ.s₀ ∧ 0 < π.σ.c₀ ∧ 0 < π.θ ∧ π.θ ≤ π.εm / 16 ∧ 0 < π.εm ∧ π.εm ≤ 1 / 2)
    (hP : ∀ i, a.PlankHyp π k (a.nd k s) i s)
    (hM : MatchAt (a.tangent k ^ π.σ.c₀) π.εm a.rd)
    {C : ℝ} (hC : 1 ≤ C)
    (hcov : ENNReal.ofReal ((C * a.H k ^ 2)⁻¹) ≤ a.layerCoverageMass π.θ π.σ k (a.nd k s))
    (hCN : 4000 * C ≤ a.tangent k ^ (π.θ * π.σ.c₀)) :
    a.tangentData.ListedAt π.Rlist (π.εm * π.σ.c₀ / 4) (max 729 (2 * C)) 2 k := by
  classical
  obtain ⟨hs₀, hc₀, hθ, hθε, hεm, hεm1⟩ := hpar
  have hd0 : 0 ≤ a.rd := ha.tangent_input.2.2.2.1
  have hd1 : a.rd < 1 := ha.tangent_input.2.2.2.2.1
  have hN : 2 ≤ a.tangent k := ha.tangent_input.1 k
  have hN1 : 1 ≤ a.tangent k := by linarith
  have hNpos : 0 < a.tangent k := by linarith
  have hH : 2 ≤ a.H k := (ha.bounds k).2.2.1
  have hs_lo : π.σ.s₀ / 2 ≤ s := by
    have h1 := neg_abs_le (s - π.σ.s₀)
    linarith [hs.2]
  have hs_hi : s ≤ 3 * π.σ.s₀ / 2 := by
    have h1 := le_abs_self (s - π.σ.s₀)
    linarith [hs.2]
  have hR1 : (1 : ℝ) ≤ π.Rlist := by
    unfold CmpParams.Rlist
    have : (0 : ℝ) ≤ (π.σ.R : ℝ) := Nat.cast_nonneg _
    have : 0 < 2 / π.σ.s₀ := by positivity
    linarith
  have hRpos : 0 < π.Rlist := by linarith
  -- the scale exponents of counts lie below `Rlist`
  have hcountexp : kap0 π + (a.rd * π.σ.c₀ + π.θ * π.σ.c₀) ≤ π.Rlist := by
    unfold CmpParams.Rlist kap0
    have : (0 : ℝ) ≤ (π.σ.R : ℝ) := Nat.cast_nonneg _
    have : 0 < 2 / π.σ.s₀ := by positivity
    have h1 : a.rd * π.σ.c₀ ≤ π.σ.c₀ := by nlinarith
    have hθ1 : π.θ ≤ 1 / 32 := by linarith
    have h2 : π.θ * π.σ.c₀ ≤ π.σ.c₀ / 32 := by nlinarith
    nlinarith
  set ℓ := a.nd k s with hℓ
  have hNR : ∀ x : ℝ, x ≤ π.Rlist → a.tangent k ^ x ≤ a.tangent k ^ π.Rlist :=
    fun x hx => Real.rpow_le_rpow_of_exponent_le hN1 hx
  -- a per-plank count bound
  have hcount : ∀ i : Fin (a.ls k ℓ).n, (a.ncand π k ℓ i : ℝ) ≤ a.tangent k ^ π.Rlist := by
    intro i
    have h1 := ncand_le ha π k ℓ i s (hP i)
    have hK := (hP i).K_small
    have hpowpos : 0 ≤ a.tangent k ^ (a.rd * π.σ.c₀ + π.θ * π.σ.c₀) :=
      Real.rpow_nonneg hNpos.le _
    calc (a.ncand π k ℓ i : ℝ) ≤ a.rK k * a.tangent k ^ (a.rd * π.σ.c₀ + π.θ * π.σ.c₀) := h1
      _ ≤ a.tangent k ^ (kap0 π) * a.tangent k ^ (a.rd * π.σ.c₀ + π.θ * π.σ.c₀) :=
          mul_le_mul_of_nonneg_right hK hpowpos
      _ = a.tangent k ^ (kap0 π + (a.rd * π.σ.c₀ + π.θ * π.σ.c₀)) :=
          (Real.rpow_add hNpos _ _).symm
      _ ≤ a.tangent k ^ π.Rlist := hNR _ hcountexp
  have hcoef : ∀ i (h : Fin (a.ncand π k ℓ i)), (a.cand π k ℓ i h).totalDegree ≤ 2 ∧
      ∀ b, |(a.cand π k ℓ i h).coeff b| ≤ a.tangent k ^ π.Rlist := by
    intro i h
    refine ⟨cand_totalDegree ha π k ℓ i h, fun b => (cand_coeff ha π k ℓ i h b).trans ?_⟩
    apply hNR
    unfold CmpParams.Rlist
    have : 0 < 2 / π.σ.s₀ := by positivity
    linarith
  refine ⟨s, ?_, ?_, fun i => a.ncand π k ℓ i, fun i h => a.cand π k ℓ i h,
    a.fitTol π.θ π.σ k, a.nNew π k ℓ, a.parentOf π k ℓ, a.binOf π k ℓ, a.Qof π k ℓ,
    a.listsOf π k ℓ, ?_⟩
  · -- Rlist⁻¹ ≤ s
    have h2 : 2 / π.σ.s₀ ≤ π.Rlist := by
      unfold CmpParams.Rlist
      have : (0 : ℝ) ≤ (π.σ.R : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hinv : π.Rlist⁻¹ ≤ (2 / π.σ.s₀)⁻¹ := inv_anti₀ (by positivity) h2
    rw [inv_div] at hinv
    linarith
  · unfold CmpParams.Rlist
    have : (0 : ℝ) ≤ (π.σ.R : ℝ) := Nat.cast_nonneg _
    have : 0 < 2 / π.σ.s₀ := by positivity
    linarith
  intro q A
  have hasg : ∀ i h, TangentData.assignment q s (a.fitTol π.θ π.σ k)
      (fun i => a.ncand π k ℓ i) (fun i h => a.cand π k ℓ i h) i h = a.asg π k ℓ i h :=
    fun i h => assignment_eq_asg ha π k ℓ s i h
  have hAeq : ∀ j, A j = {l | ∃ i h, a.binOf π k ℓ i h = j ∧ l ∈ a.asg π k ℓ i h} := by
    intro j
    ext l
    simp only [A, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, h, hj, hl⟩
      exact ⟨i, h, hj, by rwa [hasg i h] at hl⟩
    · rintro ⟨i, h, hj, hl⟩
      exact ⟨i, h, hj, by rwa [hasg i h]⟩
  refine ⟨hcount, ?_, ?_, ?_, fun i h => parentOf_binOf ha π k ℓ i h, hcoef,
    fun j => hcoef _ _, ?_, ?_, fun g j => listsOf_measurable ha π k ℓ g j, ?_⟩
  · -- number of new labels
    have h1 := nNew_le ha π k ℓ s hP
    by_cases hn : (a.ls k ℓ).n = 0
    · have hzero : a.nNew π k ℓ = 0 := by
        unfold nNew
        rw [Fintype.card_sigma]
        apply Finset.sum_eq_zero
        intro i _
        exact absurd i.isLt (by omega)
      change (a.nNew π k ℓ : ℝ) ≤ ((a.ls k ℓ).n : ℝ) * a.tangent k ^ π.Rlist
      rw [hzero, Nat.cast_zero]
      exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hNpos.le _)
    · have i0 : Fin (a.ls k ℓ).n := ⟨0, Nat.pos_of_ne_zero hn⟩
      have hK := (hP i0).K_small
      have hpowpos : 0 ≤ a.tangent k ^ (a.rd * π.σ.c₀ + π.θ * π.σ.c₀) :=
        Real.rpow_nonneg hNpos.le _
      have hb : a.rK k * a.tangent k ^ (a.rd * π.σ.c₀ + π.θ * π.σ.c₀) ≤
          a.tangent k ^ π.Rlist := by
        calc a.rK k * a.tangent k ^ (a.rd * π.σ.c₀ + π.θ * π.σ.c₀)
            ≤ a.tangent k ^ (kap0 π) * a.tangent k ^ (a.rd * π.σ.c₀ + π.θ * π.σ.c₀) :=
              mul_le_mul_of_nonneg_right hK hpowpos
          _ = a.tangent k ^ (kap0 π + (a.rd * π.σ.c₀ + π.θ * π.σ.c₀)) :=
              (Real.rpow_add hNpos _ _).symm
          _ ≤ a.tangent k ^ π.Rlist := hNR _ hcountexp
      change (a.nNew π k ℓ : ℝ) ≤ ((a.ls k ℓ).n : ℝ) * a.tangent k ^ π.Rlist
      exact h1.trans (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))
  · exact Real.rpow_nonneg hNpos.le _
  · change a.tangent k ^ (π.θ * π.σ.c₀ - π.σ.s₀ - π.σ.c₀) ≤ a.tangent k ^ π.Rlist
    apply hNR
    have : π.θ * π.σ.c₀ ≤ π.σ.c₀ := by nlinarith
    linarith
  · intro j l hl t ht
    rw [hAeq j] at hl
    exact label_fit ha π k ℓ s hP j l hl t ht
  · intro g z
    have h1 := listsOf_card ha π k ℓ g z
    have hH1 : a.H k ≤ a.H k ^ 2 := by nlinarith
    have hmax : (729 : ℝ) ≤ max 729 (2 * C) := le_max_left _ _
    change ((a.listsOf π k ℓ g z).card : ℝ) ≤ max 729 (2 * C) * a.H k ^ 2
    nlinarith
  · have hmass := listed_mass ha π k s hP hM hC hcov hCN
    have hle : ENNReal.ofReal ((max 729 (2 * C) * a.H k ^ 2)⁻¹) ≤
        ENNReal.ofReal ((2 * C * a.H k ^ 2)⁻¹) := by
      apply ENNReal.ofReal_le_ofReal
      apply inv_anti₀ (by positivity)
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    refine hle.trans (hmass.trans (le_of_eq ?_))
    apply Finset.sum_congr rfl
    intro g _
    congr 2
    ext z
    simp only [Set.mem_ofPred_eq, hAeq]
    rfl

end PreparedData

/-- The remaining geometric task of `Return.lean`, proved. -/
theorem candidateConversion : CandidateConversion := by
  intro a ha hSTI
  have hd0 : 0 ≤ a.rd := ha.tangent_input.2.2.2.1
  have hd1 : a.rd < 1 := ha.tangent_input.2.2.2.2.1
  obtain ⟨ε₀, hε₀, R₀, hR₀, hmatch⟩ := MatchApply.matching_far_mass a.rd hd0 hd1
  set εm : ℝ := min ε₀ (1 / 2) with hεmdef
  have hεmpos : 0 < εm := lt_min hε₀ (by norm_num)
  have hεm1 : εm ≤ 1 / 2 := min_le_right _ _
  have hεmle : εm ≤ ε₀ := min_le_left _ _
  set θ : ℝ := εm / 16 with hθdef
  have hθpos : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := by linarith
  obtain ⟨σ, C, hs₀, hc₀, hC, hfreq⟩ := PreparedData.frequent_positive_layer ha hSTI hθpos hθ1
  let π : CmpParams := ⟨θ, εm, R₀, σ⟩
  have hpar : 0 < π.σ.s₀ ∧ 0 < π.σ.c₀ ∧ 0 < π.θ ∧ π.θ ≤ π.εm / 16 ∧ 0 < π.εm ∧
      π.εm ≤ 1 / 2 :=
    ⟨hs₀, hc₀, hθpos, le_rfl, hεmpos, hεm1⟩
  have hev := PreparedData.eventually_plankHyp ha π hpar
  have hNt : Tendsto a.tangent atTop atTop := ha.tangent_input.2.1
  have hCN : ∀ᶠ k in atTop, 4000 * C ≤ a.tangent k ^ (θ * σ.c₀) :=
    ((tendsto_rpow_atTop (by positivity)).comp hNt).eventually_ge_atTop _
  have hRN : ∀ᶠ k in atTop, R₀ ≤ a.tangent k ^ σ.c₀ :=
    ((tendsto_rpow_atTop hc₀).comp hNt).eventually_ge_atTop _
  have hlisted : ∃ᶠ k in atTop,
      a.tangentData.ListedAt π.Rlist (π.εm * π.σ.c₀ / 4) (max 729 (2 * C)) 2 k := by
    refine (hfreq.and_eventually (hev.and (hCN.and hRN))).mono ?_
    rintro k ⟨⟨ℓ, hℓ, hmass⟩, hP, hCNk, hRk⟩
    obtain ⟨_, _, s, hs1, hs2, rfl⟩ := hℓ
    have hM : PreparedData.MatchAt (a.tangent k ^ π.σ.c₀) π.εm a.rd :=
      hmatch _ _ hRk hεmpos hεmle
    exact PreparedData.listedAt_of_stage ha π k s ⟨hs1, hs2⟩ hpar (hP s hs1 hs2) hM hC
      hmass hCNk
  have hR1 : 1 < π.Rlist := by
    show 1 < (σ.R : ℝ) + 2 / σ.s₀ + 2 * σ.s₀ + 2 * σ.c₀ + 2
    have : (0 : ℝ) ≤ (σ.R : ℝ) := Nat.cast_nonneg _
    have : 0 < 2 / σ.s₀ := by positivity
    linarith
  have hgain : 0 < π.εm * π.σ.c₀ / 4 := by
    show 0 < εm * σ.c₀ / 4
    positivity
  have hC' : (1 : ℝ) ≤ max 729 (2 * C) := le_trans (by norm_num) (le_max_left _ _)
  exact original_encoding a ha.encoding_core π.Rlist _ _ 2 hR1 hgain hC' hlisted

end Submission.Obl.k4_scalar_candidate_original_return
