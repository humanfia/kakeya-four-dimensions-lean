-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.Jets2.Core, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/Jets2/Core.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/Jets2/Core.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/Jets2/Core.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.FinalNumbers

set_option autoImplicit false

/-!
# The deterministic core of the higher jets, version 2

Adapted from this LOT tree: o229, session x0801, branch `x0801` at `38917d30`, `Jets/Core.lean`,
for rows in `(ℝ²)^*`: the fit is one polynomial per component (`JetFit` of
`Jets2/Interface.lean`), and fiber recovery runs with the measurable set of times where both
components are fitted.

`jets_core`: in a scalar-normal world with constant `Q` (labels `E₁`), given the first-jet
inputs (a row `A`, Taylor estimates on the dyadic cells of the levels `T (ω k + 3)` and the fine
cover of `J₁`) and the schedule hypotheses, some labelled incidence carries a polynomial fit of
degree `D + 1` with error `θ` on labelled times of total length `2⁻ᵀ τ` of its own block.

Proof: choose a dyadic block of length `h = 2⁻ᵀ` carrying half of the labelled mass; weight the
trajectories by their label fraction `a` in that block; Jensen along the tree and a Markov bound
give `∫ treeP_D d(a ν) ≥ 2 m*`; choose one good tree (`tree_exists`); run the jet induction on its
label set (`jet_tree`); the final test bounds the bad test times of the block, and fiber recovery
(`root_fiber`, Tonelli) produces the fitted incidence.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {Λ : Type*} [MeasurableSpace Λ]

/-- **Deterministic higher jets.** -/
theorem jets_core {ν : Measure Λ} {c : Λ → Fin 7 → ℝ} {E₁ : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ}
    {piece : ℝ → Λ → Fin 7 → ℤ} {ζ d : ℝ} {S : Sched} (hS : S.Ok ζ)
    (hSN : ScalarNormal ν c E₁ F piece S.Q ζ d) (hd0 : 0 ≤ d) (hds : d ≤ 1 - 1 / S.s)
    {T : ℕ} (hℓ : S.ell ^ (10 * S.s) = ((2 : ℝ) ^ T)⁻¹)
    (htop : 10 * S.s * (S.D + 1) + 3 * S.s + 1 ≤ S.top)
    {A : ℝ → Fin 2 → ℝ} (hA : ∀ p ∈ E₁, ‖A p.2‖ ≤ S.Q)
    (htaylor : ∀ k, 1 ≤ k → k ≤ S.D → ∀ j : ℤ, ∀ p ∈ E₁, ∀ p' ∈ E₁,
      p.2 ∈ dI (T * (S.ω k + 3)) j → p'.2 ∈ dI (T * (S.ω k + 3)) j →
      ‖F p'.2 - F p.2 - (p'.2 - p.2) • A p.2‖ ≤ S.eT k)
    (hlists : ∀ t, Determined E₁ (fun l => zS F (c l) t) univ t S.q₁
      (fun l => jet (leafRows F A t) (c l) t 1) S.p₁ S.n₁)
    {m₁ : ℝ} (hm₁0 : 0 ≤ m₁) (hm₁ : ENNReal.ofReal m₁ ≤ (ν.prod volume) E₁)
    (hmstar : S.mstar = (m₁ / 4) ^ (2 ^ S.D + 2) / 2)
    {θ τ : ℝ} (hθ : S.ell ^ (10 * S.s * (S.D + 1) + 2 * S.s) ≤ θ) (hτ0 : 0 ≤ τ)
    (hτ : τ * S.Q ^ 3 ≤ 1) :
    ∃ p ∈ E₁, ∃ P : Fin 2 → Polynomial ℝ, JetFit E₁ F (S.D + 1) T
      ((((S.D + 1 : ℕ) : ℝ) + 1) * (S.BR S.D * 2 ^ (S.D + 1))) θ (((2 : ℝ) ^ T)⁻¹ * τ) p P := by
  classical
  have := hSN.prob
  have hE := hSN.measurableSet_E
  have hFm := hSN.measurable_F
  have hQ1 := hS.one_le_Q
  have hQ0 := hS.Q_pos
  have hbig := hS.big
  have hl0 := hS.hell0
  have hl1 := hS.hell1
  have hm0 := hS.hm0
  set h : ℝ := ((2 : ℝ) ^ T)⁻¹ with hh
  have hh0 : 0 < h := by positivity
  have hh1 : h ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  -- the dyadic levels
  set Tl : ℕ → ℕ := fun k => T * (S.ω k + 3) with hTl
  have hTlanti : ∀ k, Tl (k + 2) ≤ Tl (k + 1) := by
    intro k
    have := omegaE_succ_le S.D S.s S.top (k + 1)
    show T * (S.ω (k + 1 + 1) + 3) ≤ T * (S.ω (k + 1) + 3)
    exact Nat.mul_le_mul_left _ (by simp only [Sched.ω]; omega)
  have hlev : levelScale Tl = S.H := S.levelScale_eq hℓ
  have hTD : 1 ≤ S.D → T ≤ Tl S.D := fun _ => by
    simp only [hTl]
    calc T = T * 1 := (mul_one T).symm
      _ ≤ T * (S.ω S.D + 3) := Nat.mul_le_mul_left _ (by omega)
  -- the block and the weight
  obtain ⟨j₀, hj₀⟩ := exists_good_block hE hSN.time_mem Tl ν T hm₁
  set a : Λ → ℝ≥0∞ := fun l => treeP E₁ Tl 0 univ l T j₀ with ha_def
  have ha : Measurable a := measurable_treeP hE Tl 0 MeasurableSet.univ T j₀
  have ha1 : ∀ l, a l ≤ 1 := fun l => treeP_le_one E₁ Tl 0 univ l T j₀
  set μ := ν.withDensity a with hμ
  have hint_a : ∫⁻ l, a l ∂ν ≤ 1 := by
    calc ∫⁻ l, a l ∂ν ≤ ∫⁻ _l, (1 : ℝ≥0∞) ∂ν := lintegral_mono ha1
      _ = 1 := by rw [lintegral_const, measure_univ, one_mul]
  have : IsFiniteMeasure μ :=
    isFiniteMeasure_withDensity (ne_of_lt (lt_of_le_of_lt hint_a ENNReal.one_lt_top))
  have hμle : ∀ X : Set Λ, MeasurableSet X → μ X ≤ ν X := by
    intro X hX
    rw [hμ, withDensity_apply _ hX]
    calc ∫⁻ l in X, a l ∂ν ≤ ∫⁻ _l in X, (1 : ℝ≥0∞) ∂ν := lintegral_mono ha1
      _ = ν X := by rw [setLIntegral_const, one_mul]
  have hμuniv : μ univ ≤ 1 := (hμle univ MeasurableSet.univ).trans prob_le_one
  -- success of the uniform tree
  have hsucc : ENNReal.ofReal (2 * S.mstar) ≤ ∫⁻ l, treeP E₁ Tl S.D univ l T j₀ ∂μ := by
    rw [hμ, lintegral_withDensity_eq_lintegral_mul ν ha
      (measurable_treeP hE Tl S.D MeasurableSet.univ T j₀)]
    have h1 := lintegral_mul_pow_ge ha ha1 hm₁0 hj₀ (2 ^ S.D)
    have e : 2 * S.mstar = (m₁ / 4) ^ (2 ^ S.D + 2) := by rw [hmstar]; ring
    rw [e]
    refine h1.trans (lintegral_mono fun l => ?_)
    simp only [Pi.mul_apply]
    gcongr
    exact treeP_ge_pow E₁ hE Tl hTlanti l S.D T j₀ hTD
  -- the gap loss is small
  have hKg0 : 0 < S.Kg := pow_pos hQ0 3
  have hgap : gapLoss S.Kg S.D ≤ S.mstar := by
    refine (gapLoss_le' hKg0 S.D).trans ?_
    have h2D : (2 : ℝ) ^ (S.D + 1) ≤ S.Q := by
      have h := hS.const_le (c := 1) (by norm_num) (by norm_num)
      have h1 : (2 : ℝ) ^ (S.D + 1) ≤ 2 ^ (S.D + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h2 : (1 : ℝ) ≤ ((S.D : ℝ) + 2) ^ 2 := one_le_pow₀ (by
        have : (0 : ℝ) ≤ S.D := Nat.cast_nonneg _
        linarith)
      nlinarith
    rw [div_le_iff₀ hKg0]
    unfold Sched.Kg
    calc (2 : ℝ) ^ (S.D + 1) ≤ S.Q := h2D
      _ = S.Q * 1 := (mul_one _).symm
      _ ≤ S.Q * (S.Q ^ 2 * S.mstar) := by gcongr; exact hS.hmQ
      _ = S.mstar * S.Q ^ 3 := by ring
  have hgapμ : ENNReal.ofReal (gapLoss S.Kg S.D) * μ univ ≤ ENNReal.ofReal S.mstar := by
    calc ENNReal.ofReal (gapLoss S.Kg S.D) * μ univ ≤ ENNReal.ofReal S.mstar * 1 :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hgap) hμuniv
      _ = ENNReal.ofReal S.mstar := mul_one _
  have hlt : ENNReal.ofReal (gapLoss S.Kg S.D) * μ univ <
      ∫⁻ l, treeP E₁ Tl S.D univ l T j₀ ∂μ := by
    refine lt_of_le_of_lt hgapμ (lt_of_lt_of_le ?_ hsucc)
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  -- the tree
  obtain ⟨tr, hPairs, hCells, htimes, -, hbound⟩ :=
    tree_exists hE Tl hTlanti hKg0 S.D T j₀ hTD univ MeasurableSet.univ μ hlt
  set Lab := tr.labSet E₁ with hLab
  have hLabm : MeasurableSet Lab := TTree.measurableSet_labSet hE tr
  have hμLab : ENNReal.ofReal S.mstar ≤ μ Lab := by
    have h2 : ENNReal.ofReal S.mstar + ENNReal.ofReal S.mstar ≤ μ Lab + ENNReal.ofReal S.mstar := by
      rw [← ENNReal.ofReal_add hm0.le hm0.le]
      calc ENNReal.ofReal (S.mstar + S.mstar) = ENNReal.ofReal (2 * S.mstar) := by ring_nf
        _ ≤ ∫⁻ l, treeP E₁ Tl S.D univ l T j₀ ∂μ := hsucc
        _ ≤ μ Lab + ENNReal.ofReal (gapLoss S.Kg S.D) * μ univ := hbound
        _ ≤ μ Lab + ENNReal.ofReal S.mstar := add_le_add le_rfl hgapμ
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp h2
  have hνLab : ENNReal.ofReal S.mstar ≤ ν Lab := hμLab.trans (hμle Lab hLabm)
  -- the label set is nonempty, so every time of the tree is good
  set Good : Set ℝ := {t | ∃ l, (l, t) ∈ E₁} with hGood
  have hLabne : Lab.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, measure_empty] at hνLab
    have := (ENNReal.ofReal_pos.mpr hm0).trans_le hνLab
    exact lt_irrefl _ this
  obtain ⟨l₀, hl₀⟩ := hLabne
  have htgood : ∀ s, tr.Mem s → s ∈ Good := fun s hs => ⟨l₀, hl₀ s hs⟩
  have hGoodI : Good ⊆ Icc 0 1 := by
    rintro t ⟨l, hl⟩; exact hSN.time_mem (l, t) hl
  -- the first-jet inputs
  have hFJ : FirstJetInput E₁ F c A Good Tl S.eT S.D S.q₁ S.p₁ S.n₁ (S.BR 0) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro t ⟨l, hl⟩
      rw [Sched.BR_zero]
      exact ⟨hSN.row_le (l, t) hl, hA (l, t) hl⟩
    · rintro k hk1 hkD j t ⟨l, hl⟩ s ⟨l', hl'⟩ ht hs
      exact htaylor k hk1 hkD j (l, t) hl (l', s) hl' ht hs
    · intro t _; exact hlists t
  -- the jet induction at the root
  have hPairs' : tr.Pairs S.H S.Kg := hlev ▸ hPairs
  have hmassD : ENNReal.ofReal (S.mass S.D) ≤ ν Lab := by rw [Sched.mass_top]; exact hνLab
  obtain ⟨R, hR0, hR1, hRb, D', hD'sub, hD'm, hloss, hNL⟩ :=
    jet_tree hSN (by linarith [hds, (by positivity : (0 : ℝ) ≤ 1 / S.s)]) hS.treeBudget hFJ hGoodI
      S.D le_rfl tr hPairs' hCells htgood Lab hLabm (fun l hl s hs => hl s hs) hmassD
  -- the retained set keeps half of the weighted mass
  have hμD' : ENNReal.ofReal (S.mstar / 2) ≤ μ D' := by
    have hsplit : μ Lab ≤ μ D' + μ (Lab \ D') := by
      calc μ Lab = μ (D' ∪ (Lab \ D')) := by rw [union_sdiff_cancel hD'sub]
        _ ≤ μ D' + μ (Lab \ D') := measure_union_le _ _
    have hdiff : μ (Lab \ D') ≤ ENNReal.ofReal (S.mstar / 2) :=
      (hμle _ (hLabm.diff hD'm)).trans (hloss.trans (ENNReal.ofReal_le_ofReal hS.loss_top_le))
    have h2 : ENNReal.ofReal (S.mstar / 2) + ENNReal.ofReal (S.mstar / 2) ≤
        μ D' + ENNReal.ofReal (S.mstar / 2) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      calc ENNReal.ofReal (S.mstar / 2 + S.mstar / 2) = ENNReal.ofReal S.mstar := by ring_nf
        _ ≤ μ Lab := hμLab
        _ ≤ μ D' + μ (Lab \ D') := hsplit
        _ ≤ μ D' + ENNReal.ofReal (S.mstar / 2) := add_le_add le_rfl hdiff
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp h2
  -- the root and its block
  set u := tr.root with hu
  have hu_mem : u ∈ dI T j₀ := htimes u (TTree.mem_root tr)
  have hblock : blockIco T u = dI T j₀ := blockIco_eq_dI hu_mem
  have hulab : ∀ l ∈ D', (l, u) ∈ E₁ := fun l hl => hD'sub hl u (TTree.mem_root tr)
  have hu01 : u ∈ Icc (0 : ℝ) 1 := hSN.time_mem (l₀, u) (hl₀ u (TTree.mem_root tr))
  have hu1 : |u| ≤ 1 := abs_le.mpr ⟨by linarith [hu01.1], hu01.2⟩
  set P := rowPolynomial R (S.D + 1) u with hP
  -- the final test at every bad time of the block
  have hL := hS.levels S.D le_rfl
  have hCJ1 := Sched.Ok.one_le_CJ hL
  have hWD := hS.W_pos S.D
  have hζW : ζ ≤ S.W S.D := hS.hζq.trans (hS.hqW.trans (hS.W_mono (Nat.zero_le _)))
  have hθ0 : 0 < θ := lt_of_lt_of_le (by positivity) hθ
  have hr0 : 0 < S.ell ^ S.s := pow_pos hl0 _
  have hr1 : S.ell ^ S.s ≤ 1 := pow_le_one₀ hl0.le hl1
  have hζr : ζ ≤ θ * S.ell ^ S.s := by
    have h1 : ζ ≤ S.ell ^ (10 * S.s * (S.D + 1) + 2 * S.s + S.s) := by
      refine hS.hζq.trans (hS.hqW.trans ?_)
      simp only [Sched.W]
      apply hS.ell_pow_le
      have := top_le_omegaE S.D S.s S.top 0
      simp only [Sched.ω]
      omega
    calc ζ ≤ S.ell ^ (10 * S.s * (S.D + 1) + 2 * S.s + S.s) := h1
      _ = S.ell ^ (10 * S.s * (S.D + 1) + 2 * S.s) * S.ell ^ S.s := pow_add _ _ _
      _ ≤ θ * S.ell ^ S.s := by gcongr
  have hδp : S.W S.D ≤ S.w S.D := by
    calc S.W S.D = 1 * S.W S.D := (one_mul _).symm
      _ ≤ S.CJ S.D * S.W S.D := by gcongr
  set G : Set ℝ := {v | ∀ i, |F v i - (P i).eval v| ≤ θ} with hGdef
  have hGm : MeasurableSet G := by
    have e : G = ⋂ i, {v : ℝ | |F v i - (P i).eval v| ≤ θ} := by
      ext v; simp only [hGdef, mem_setOf_eq, mem_iInter]
    rw [e]
    refine MeasurableSet.iInter fun i => measurableSet_le ?_ measurable_const
    exact continuous_abs.measurable.comp
      (((measurable_pi_apply i).comp hFm).sub (P i).continuous.measurable)
  have hbad : ∀ t' ∈ blockIco T u, t' ∉ G →
      ν {l | l ∈ D' ∧ (l, t') ∈ E₁} ≤ ENNReal.ofReal (S.Q ^ 3)⁻¹ := by
    intro t' ht' hθt
    rw [hblock] at ht'
    have htu : |t' - u| ≤ h := (abs_sub_lt_of_mem_dI ht' hu_mem).le
    have hθ' : θ ≤ ‖F t' - rowPoly R (S.D + 1) u t'‖ := by
      simp only [hGdef, mem_setOf_eq, not_forall, not_le] at hθt
      obtain ⟨i, hi⟩ := hθt
      refine hi.le.trans ?_
      have e : F t' i - (P i).eval t' = (F t' - rowPoly R (S.D + 1) u t') i := by
        rw [hP, rowPolynomial_eval]; rfl
      rw [e]
      exact abs_le_norm _ i
    have := final_test hSN hd0 (by linarith [hds, (by positivity : (0 : ℝ) ≤ 1 / S.s)])
      (D := D') (u := u) (t' := t') (p := S.W S.D) (δ := S.w S.D) (h := h) (θ := θ)
      (r := S.ell ^ S.s) (M := S.D + 1) (by have := hS.hD; omega) hR0 hRb hulab hNL hδp
      hζW (hS.W_le_one _) htu hh1 hθ' hθ0 hr0 hr1 hζr (hS.final_err hℓ htop hθ)
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    exact hS.final_mass hd0 hds hℓ (by have := hS.hs; omega)
  -- the labelled mass of the block
  have hmass : ENNReal.ofReal (h * (S.Q ^ 3)⁻¹ + h * τ) <
      ∫⁻ t' in blockIco T u, ν {l | l ∈ D' ∧ (l, t') ∈ E₁} := by
    rw [hblock, block_lintegral_eq hE Tl ν hD'm T j₀]
    have hμD'eq : ∫⁻ l in D', treeP E₁ Tl 0 univ l T j₀ ∂ν = μ D' := by
      rw [hμ, withDensity_apply _ hD'm]
    rw [hμD'eq]
    have hQ3 : 0 < S.Q ^ 3 := by positivity
    have hτQ : τ ≤ (S.Q ^ 3)⁻¹ := by
      calc τ = τ * S.Q ^ 3 * (S.Q ^ 3)⁻¹ := by field_simp
        _ ≤ 1 * (S.Q ^ 3)⁻¹ := by gcongr
        _ = (S.Q ^ 3)⁻¹ := one_mul _
    have hlt : h * (S.Q ^ 3)⁻¹ + h * τ < h * (S.mstar / 2) := by
      have h4 : 4 * (S.Q ^ 3)⁻¹ < S.mstar := by
        rw [← div_eq_mul_inv, div_lt_iff₀ hQ3]
        calc (4 : ℝ) < S.Q * 1 := by linarith
          _ ≤ S.Q * (S.Q ^ 2 * S.mstar) := by gcongr; exact hS.hmQ
          _ = S.mstar * S.Q ^ 3 := by ring
      have : (S.Q ^ 3)⁻¹ + τ < S.mstar / 2 := by linarith
      calc h * (S.Q ^ 3)⁻¹ + h * τ = h * ((S.Q ^ 3)⁻¹ + τ) := by ring
        _ < h * (S.mstar / 2) := by gcongr
    calc ENNReal.ofReal (h * (S.Q ^ 3)⁻¹ + h * τ) < ENNReal.ofReal (h * (S.mstar / 2)) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hlt
      _ = ENNReal.ofReal h * ENNReal.ofReal (S.mstar / 2) := ENNReal.ofReal_mul hh0.le
      _ ≤ ENNReal.ofReal h * μ D' := by gcongr
  -- fiber recovery
  obtain ⟨l, -, t', hlt'E, ht'B, hfit, hvol⟩ := root_fiber hE hGm hD'm prob_le_one
    (by positivity : (0 : ℝ) ≤ (S.Q ^ 3)⁻¹) (by positivity : 0 ≤ h * τ) hbad hmass
  refine ⟨(l, t'), hlt'E, P, fun i => rowPolynomial_natDegree_le R (S.D + 1) u i,
    fun i k => abs_coeff_rowPolynomial_le hRb (S.D + 1) hu1 i k, hfit, ?_⟩
  refine hvol.trans (measure_mono ?_)
  rintro v ⟨hvB, hvE, hvF⟩
  refine ⟨?_, hvE, hvF⟩
  have hblk : dyadicBlock T t' = dyadicBlock T u := dyadicBlock_eq_of_mem_blockIco ht'B
  show v ∈ dyadicBlock T t'
  rw [hblk]
  exact blockIco_subset_dyadicBlock T u hvB

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
