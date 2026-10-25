-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.CompositionQ.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.Composition
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.BranchesQ
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.QVariant

/-!
# Composition of the quadratic-count trichotomy

`trichotomyDerivedQ_of_branches : StickyBranchStmtQ → NonStickyBranchStmtQ → TrichotomyDerivedQ`:
the proof of `trichotomyDerivedSC_of_branches` (Composition.lean) with the flat output
`FlatPrismsQ`. `o038_of_branchesQ : StatementA → StickyBranchStmtQ → NonStickyBranchStmtQ →
FlatGainQ → O038`.
-/

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy

open MeasureTheory

open Classical in
/-- **The derived trichotomy with the quadratic count, from the two branch statements.** -/
theorem trichotomyDerivedQ_of_branches (hSt : StickyBranchStmtQ) (hNs : NonStickyBranchStmtQ) :
    TrichotomyDerivedQ := by
  obtain ⟨Cp, hCp, hpack⟩ := WangZahlLot.wz_tube_packing_bound
  obtain ⟨D, hD⟩ := canonical_setup
  obtain ⟨B, hB1, hBdef⟩ : ∃ B : ℝ, 1 ≤ B ∧ B = ((200000 : ℕ) : ℝ) ^ 6 :=
    ⟨_, one_le_pow₀ (by norm_num), rfl⟩
  unfold TrichotomyDerivedQ
  beta_reduce
  intro ξ hξ
  refine ⟨ξ / 20, by positivity, ?_⟩
  intro ζ₂ ζ₃ hζ₃ hζ₃₂ hζ₂₁ κ hκ
  have hζ₂ : 0 < ζ₂ := lt_of_lt_of_le hζ₃ hζ₃₂
  have hζ₂ξ : ζ₂ ≤ ξ := by linarith
  set Nmax : ℕ := ⌊256 / ζ₂⌋₊ + 1 with hNmax
  obtain ⟨ζS, hζS, δS, hδS, hStδ⟩ := hSt ξ ζ₂ ζ₃ (κ / 4) hζ₃ hζ₃₂ hζ₂ξ (by positivity) Nmax Cp
  obtain ⟨ζN, hζN, δN, hδN, hNsδ⟩ :=
    hNs (ξ / 20) ζ₂ ζ₃ (κ / 4) hζ₃ hζ₃₂ hζ₂₁ (by positivity) Nmax Cp
  -- the Frostman exponent `c₁` of the prepared family, the input exponent `ζ`
  set c₁ : ℝ := min (min ζS ζN) (ζ₂ / 32) with hc₁
  have hc₁0 : 0 < c₁ := lt_min (lt_min hζS hζN) (by positivity)
  have hc₁S : c₁ ≤ ζS := le_trans (min_le_left _ _) (min_le_left _ _)
  have hc₁N : c₁ ≤ ζN := le_trans (min_le_left _ _) (min_le_right _ _)
  have hc₁ζ₂ : c₁ ≤ ζ₂ / 32 := min_le_right _ _
  set ζ : ℝ := min (min ζS ζN) ζ₂ / 64 with hζdef
  have hζ0 : 0 < ζ := by
    have : 0 < min (min ζS ζN) ζ₂ := lt_min (lt_min hζS hζN) hζ₂
    positivity
  have hζc₁ : ζ ≤ c₁ / 2 := by
    have h1 := min_le_left (min ζS ζN) ζ₂
    have h2 := min_le_right (min ζS ζN) ζ₂
    have h3 : 0 < min (min ζS ζN) ζ₂ := lt_min (lt_min hζS hζN) hζ₂
    rw [hζdef, hc₁]
    rcases le_total (min ζS ζN) (ζ₂ / 32) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  refine ⟨ζ, hζ0, ?_⟩
  intro θ hθ
  -- the thresholds on `δ`
  obtain ⟨δg, hδg, hgrid⟩ := grid_choice ζ₂ hζ₂
  obtain ⟨δa, hδa, hda⟩ := small_const 2 θ hθ
  obtain ⟨δb, hδb, hdb⟩ := small_const (768 * 82 ^ 6) (ζ₂ / 8) (by positivity)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C₁ : ℝ := 1 + |Real.log Cp| / Real.log 2 with hC₁
  set C₂ : ℝ := 4 / Real.log 2 with hC₂
  set A : ℝ := 48 ^ 3 * (6 * (D + 1)) * B ^ Nmax with hA
  set c₀ : ℝ := min (c₁ / 2) (3 * κ / 4) with hc₀
  have hc₀0 : 0 < c₀ := lt_min (by positivity) (by positivity)
  obtain ⟨δc, hδc, hdc⟩ := small_polylog A C₁ C₂ Nmax c₀ (by positivity) (by positivity)
    (by positivity) hc₀0
  refine ⟨min (min (min δS δN) (min δg δa)) (min (min δb δc) (1 / 100)), by positivity, ?_⟩
  intro δ hδ hδ₀ η hη n x v Y hG hFrost
  have hδS' : δ ≤ δS :=
    le_trans hδ₀ (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hδN' : δ ≤ δN :=
    le_trans hδ₀ (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hδg' : δ ≤ δg :=
    le_trans hδ₀ (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hδa' : δ ≤ δa :=
    le_trans hδ₀ (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hδb' : δ ≤ δb :=
    le_trans hδ₀ (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hδc' : δ ≤ δc :=
    le_trans hδ₀ (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hδ100 : δ ≤ 1 / 100 := le_trans hδ₀ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hδ1 : δ ≤ 1 := by linarith
  have hδ1' : δ < 1 := by linarith
  have hinvδ : 1 < 1 / δ := by rw [lt_div_iff₀ hδ]; linarith
  obtain ⟨hn, hv, hTB, hov, hYm, hYT, hdens⟩ := hG
  -- 1. canonicalization
  obtain ⟨k₀, gc, x', v', S₀, hgc, hS₀ne, hnS₀, hv', hcan', hball', hov', hanti', hhalf, hconv⟩ :=
    hD δ hδ hδ100 η (δ ^ (-ζ) * n) n x v Y hn hv hTB hov hYT hdens hFrost
  set m := S₀.card with hmdef
  have hm : 0 < m := Finset.card_pos.2 hS₀ne
  set e : Fin m → Fin k₀ := fun j => (S₀.equivFin.symm j).1 with hedef
  have heS₀ : ∀ j, e j ∈ S₀ := fun j => (S₀.equivFin.symm j).2
  have heinj : Function.Injective e := by
    intro j j' h
    exact S₀.equivFin.symm.injective (Subtype.ext h)
  set x₁ : Fin m → Sp := fun j => x' (e j) with hx₁
  set v₁ : Fin m → Sp := fun j => v' (e j) with hv₁
  have hv₁u : ∀ j, ‖v₁ j‖ = 1 := fun j => hv' (e j)
  have hT₁ : ∀ j, Metric.thickening δ (segment ℝ (x₁ j) (x₁ j + v₁ j)) ⊆
      Metric.ball (0 : Sp) 1 := fun j => hball' (e j)
  have hov₁ : ∀ i j, i ≠ j → volume (Metric.thickening δ (segment ℝ (x₁ i) (x₁ i + v₁ i)) ∩
      Metric.thickening δ (segment ℝ (x₁ j) (x₁ j + v₁ j))) ≤
      (1 / 2 : ENNReal) * volume (Metric.thickening δ (segment ℝ (x₁ i) (x₁ i + v₁ i))) :=
    fun i j hij => hov' (e i) (e j) (heinj.ne hij)
  have hcan₁ : ∀ j, x₁ j = leftStart δ (x₁ j) (v₁ j) := fun j => hcan' (e j)
  have hanti₁ : ∀ i j, 1 ≤ ‖v₁ i + v₁ j‖ := fun i j => hanti' (e i) (heS₀ i) (e j) (heS₀ j)
  have hpack₁ : (m : ℝ) * δ ^ 4 ≤ Cp := hpack δ hδ hδ100 m x₁ v₁ hv₁u hT₁ hov₁
  -- 2. the grid
  obtain ⟨L, top, hL2, hLlow, hLup, hLstep, htop1, htop2, htopN⟩ := hgrid δ hδ hδg'
  have htopNmax : top + 1 ≤ Nmax := by omega
  have hLR : (2 : ℝ) ≤ L := by exact_mod_cast hL2
  have hLup' : (L : ℝ) ≤ δ ^ (-(ζ₂ / 16)) :=
    le_trans hLup (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  -- 3. classes and populations
  obtain ⟨S, hSne, a, hmS, hcls, hbal⟩ := prepare_levels hδ hL2 top x₁ v₁ hm
  rw [← hBdef] at hmS
  set Loss : ℝ := B ^ (top + 1) * ((Nat.log 2 m : ℝ) + 1) ^ (top + 1) with hLoss
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.2 hSne
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnatlog : (Nat.log 2 m : ℝ) * Real.log 2 ≤ Real.log m := by
    have h1 : (2 : ℝ) ^ (Nat.log 2 m) ≤ m := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have := Real.log_le_log (by positivity) h1
    rwa [Real.log_pow] at this
  have hlogm' : Real.log m ≤ Real.log Cp + 4 * Real.log (1 / δ) := by
    have h2 : Real.log ((m : ℝ) * δ ^ 4) ≤ Real.log Cp :=
      Real.log_le_log (mul_pos (by exact_mod_cast hm) (pow_pos hδ 4)) hpack₁
    rw [Real.log_mul (by exact_mod_cast hm.ne') (pow_ne_zero 4 hδ.ne'), Real.log_pow] at h2
    have h3 : Real.log (1 / δ) = - Real.log δ := by rw [one_div, Real.log_inv]
    push_cast at h2
    linarith
  have hlogm : (Nat.log 2 m : ℝ) + 1 ≤ C₁ + C₂ * Real.log (1 / δ) := by
    have h1 : (Nat.log 2 m : ℝ) ≤ (Real.log Cp + 4 * Real.log (1 / δ)) / Real.log 2 := by
      rw [le_div_iff₀ hlog2]; linarith
    have h3 : (Real.log Cp + 4 * Real.log (1 / δ)) / Real.log 2 =
        Real.log Cp / Real.log 2 + 4 / Real.log 2 * Real.log (1 / δ) := by ring
    have h4 : Real.log Cp / Real.log 2 ≤ |Real.log Cp| / Real.log 2 :=
      div_le_div_of_nonneg_right (le_abs_self _) hlog2.le
    rw [hC₁, hC₂]; linarith
  have hM1 : (1 : ℝ) ≤ B := hB1
  have hlog1 : (1 : ℝ) ≤ (Nat.log 2 m : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) (Nat.log 2 m); linarith
  have hLoss_le : Loss ≤ B ^ Nmax * (C₁ + C₂ * Real.log (1 / δ)) ^ Nmax := by
    apply mul_le_mul (pow_le_pow_right₀ hM1 htopNmax) _ (by positivity) (by positivity)
    calc ((Nat.log 2 m : ℝ) + 1) ^ (top + 1) ≤ ((Nat.log 2 m : ℝ) + 1) ^ Nmax :=
          pow_le_pow_right₀ hlog1 htopNmax
      _ ≤ (C₁ + C₂ * Real.log (1 / δ)) ^ Nmax := pow_le_pow_left₀ (by positivity) hlogm Nmax
  have hLossA : 48 ^ 3 * (6 * (D + 1)) * Loss ≤ δ ^ (-c₀) := by
    calc 48 ^ 3 * (6 * (D + 1)) * Loss ≤ 48 ^ 3 * (6 * (D + 1)) *
          (B ^ Nmax * (C₁ + C₂ * Real.log (1 / δ)) ^ Nmax) := by gcongr
      _ = A * (C₁ + C₂ * Real.log (1 / δ)) ^ Nmax := by rw [hA]; ring
      _ ≤ δ ^ (-c₀) := hdc δ hδ hδc'
  have hnS : (n : ℝ) ≤ 6 * (D + 1) * Loss * S.card := by
    calc (n : ℝ) ≤ 6 * (D + 1) * m := hnS₀
      _ ≤ 6 * (D + 1) * (Loss * S.card) := by gcongr
      _ = 6 * (D + 1) * Loss * S.card := by ring
  -- the Frostman constant of `S`
  have hK₀ : 48 ^ 3 * (δ ^ (-ζ) * n) ≤ δ ^ (-c₁) * S.card := by
    have h1 : δ ^ (-ζ) ≤ δ ^ (-(c₁ / 2)) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    have h2 : 48 ^ 3 * (6 * (D + 1)) * Loss ≤ δ ^ (-(c₁ / 2)) :=
      le_trans hLossA (Real.rpow_le_rpow_of_exponent_ge hδ hδ1
        (by have := min_le_left (c₁ / 2) (3 * κ / 4); linarith))
    have h3 : δ ^ (-c₁) = δ ^ (-(c₁ / 2)) * δ ^ (-(c₁ / 2)) := by
      rw [← Real.rpow_add hδ]; congr 1; ring
    have hL0 : 0 ≤ Loss := by positivity
    calc 48 ^ 3 * (δ ^ (-ζ) * n) ≤ 48 ^ 3 * (δ ^ (-ζ) * (6 * (D + 1) * Loss * S.card)) := by
          gcongr
      _ = δ ^ (-ζ) * (48 ^ 3 * (6 * (D + 1)) * Loss) * S.card := by ring
      _ ≤ δ ^ (-(c₁ / 2)) * δ ^ (-(c₁ / 2)) * S.card :=
          mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (by positivity) (by positivity))
            (Nat.cast_nonneg _)
      _ = δ ^ (-c₁) * S.card := by rw [h3]
  have hFS : ∀ W : Set Sp, Convex ℝ W →
      ENNReal.ofReal ((S.filter (fun i => Metric.thickening δ (segment ℝ (x₁ i) (x₁ i + v₁ i)) ⊆
        W)).card : ℝ) ≤ ENNReal.ofReal (δ ^ (-c₁) * S.card) * volume W := by
    intro W hW
    have hcard : (S.filter (fun i => Metric.thickening δ (segment ℝ (x₁ i) (x₁ i + v₁ i)) ⊆
        W)).card ≤ Set.ncard {j | Metric.thickening δ (segment ℝ (x' j) (x' j + v' j)) ⊆ W} := by
      rw [← Set.ncard_coe_finset]
      apply Set.ncard_le_ncard_of_injOn e
      · intro i hi
        exact (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).2
      · exact heinj.injOn
    have hcardR : ((S.filter (fun i => Metric.thickening δ (segment ℝ (x₁ i) (x₁ i + v₁ i)) ⊆
        W)).card : ℝ) ≤ (Set.ncard {j | Metric.thickening δ (segment ℝ (x' j) (x' j + v' j)) ⊆
          W} : ℝ) := by exact_mod_cast hcard
    calc _ ≤ ENNReal.ofReal (Set.ncard {j | Metric.thickening δ (segment ℝ (x' j) (x' j + v' j)) ⊆
          W} : ℝ) := ENNReal.ofReal_le_ofReal hcardR
      _ ≤ ENNReal.ofReal (48 ^ 3 * (δ ^ (-ζ) * n)) * volume W := hconv W hW
      _ ≤ ENNReal.ofReal (δ ^ (-c₁) * S.card) * volume W :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal hK₀) _
  have hprep : ∀ ζF, c₁ ≤ ζF → Prepared δ L top x₁ v₁ S a (δ ^ (-ζF)) := by
    intro ζF hζF
    refine ⟨hv₁u, hT₁, hov₁, hcan₁, hanti₁, hSne, hcls, hbal, fun W hW => ?_⟩
    refine le_trans (hFS W hW) (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)) (Nat.cast_nonneg _)
  -- 4. the profile
  set ρ : ℕ → ℝ := fun k => 2 * δ * (L : ℝ) ^ k with hρdef
  have hρpos : ∀ k, 0 < ρ k := fun k => by simp only [hρdef]; positivity
  have hρmono : ∀ k k', k ≤ k' → ρ k ≤ ρ k' := fun k k' hkk => by
    simp only [hρdef]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) hkk) (by positivity)
  have hρ1 : ∀ k ≤ top, ρ k ≤ 1 := fun k hk => by
    have := hρmono k top hk
    simp only [hρdef] at this ⊢
    linarith
  have hρratio : ∀ k, ρ (k + 1) = (L : ℝ) * ρ k := fun k => by simp only [hρdef]; ring
  set G : ℕ → ℝ := X318.cellProfile δ a ρ top with hGdef
  have hlowX : ∀ k ≤ top, ∀ i ∈ S, 2 ^ a k ≤ X318.cellPop x₁ v₁ S (ρ k / 20) i :=
    fun k hk i hi => (hbal k hk i hi).1
  have hupX : ∀ k ≤ top, ∀ i ∈ S, X318.cellPop x₁ v₁ S (ρ k / 20) i < 2 ^ (a k + 1) :=
    fun k hk i hi => (hbal k hk i hi).2
  have hcontX : ∀ k ≤ top, ∀ i ∈ S, ∀ j ∈ S, X318.lineGridCell (ρ k / 20) (x₁ j) (v₁ j) =
      X318.lineGridCell (ρ k / 20) (x₁ i) (v₁ i) →
      X318.Tube δ (x₁ j) (v₁ j) ⊆ X318.Tube (ρ k) (x₁ i) (v₁ i) := by
    intro k hk i hi j hj hcell
    have hρk : 2 * δ ≤ ρ k := by
      have := hρmono 0 k (Nat.zero_le _)
      simp only [hρdef, pow_zero, mul_one] at this ⊢
      linarith
    have hs : 0 < ρ k / 20 := by have := hρpos k; positivity
    exact subset_of_same_cell hδ hs (by linarith) (hv₁u j) (hv₁u i) (hT₁ j) (hT₁ i) (hcan₁ j)
      (hcan₁ i) hcell
  have hFX : ∀ U : Set Sp, Convex ℝ U →
      ENNReal.ofReal ((S.filter (fun j => X318.Tube δ (x₁ j) (v₁ j) ⊆ U)).card : ℝ) ≤
        ENNReal.ofReal (δ ^ (-c₁) * S.card) * volume U := hFS
  have hG0 : G 0 = 0 := X318.cellProfile_zero δ a hρpos top
  have hGlow : ∀ k ≤ top, -(ζ₂ / 4) ≤ G k := by
    intro k hk
    have hlower := X318.cellProfile_lower_of_family x₁ v₁ S hSne hδ hδ1' a ρ top
      (Real.rpow_pos_of_pos hδ _) hρpos hρ1 (fun i _ => hv₁u i) (fun i _ => hT₁ i) hlowX
      (hupX top le_rfl) hcontX hFX k hk
    have htop4 : δ ^ (ζ₂ / 16) ≤ ρ top ^ 4 := by
      have h1 : (δ ^ (ζ₂ / 64)) ^ 4 ≤ ρ top ^ 4 := pow_le_pow_left₀ (by positivity) htop2 4
      have h2 : (δ ^ (ζ₂ / 64)) ^ 4 = δ ^ (ζ₂ / 16) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]; congr 1; push_cast; ring
      linarith
    have harg : 768 * 82 ^ 6 * δ ^ (-c₁) / ρ top ^ 4 ≤ (1 / δ) ^ (ζ₂ / 4) := by
      rw [one_div_rpow_eq hδ, div_le_iff₀ (by positivity)]
      have hb := hdb δ hδ hδb'
      have hc : δ ^ (-c₁) ≤ δ ^ (-(ζ₂ / 32)) :=
        Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      have hsplit : δ ^ (-(ζ₂ / 4)) * δ ^ (ζ₂ / 16) =
          δ ^ (-(ζ₂ / 8)) * δ ^ (-(ζ₂ / 32)) * δ ^ (-(ζ₂ / 32)) := by
        rw [← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ]; congr 1; ring
      have hone : 1 ≤ δ ^ (-(ζ₂ / 32)) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
      have h1 : 768 * 82 ^ 6 * δ ^ (-c₁) ≤ δ ^ (-(ζ₂ / 8)) * δ ^ (-(ζ₂ / 32)) :=
        mul_le_mul hb hc (by positivity) (by positivity)
      calc 768 * 82 ^ 6 * δ ^ (-c₁) ≤ δ ^ (-(ζ₂ / 8)) * δ ^ (-(ζ₂ / 32)) * δ ^ (-(ζ₂ / 32)) :=
            le_trans h1 (le_mul_of_one_le_right (by positivity) hone)
        _ = δ ^ (-(ζ₂ / 4)) * δ ^ (ζ₂ / 16) := hsplit.symm
        _ ≤ δ ^ (-(ζ₂ / 4)) * ρ top ^ 4 := mul_le_mul_of_nonneg_left htop4 (by positivity)
    have hlog : Real.logb (1 / δ) (768 * 82 ^ 6 * δ ^ (-c₁) / ρ top ^ 4) ≤ ζ₂ / 4 :=
      (Real.logb_le_iff_le_rpow hinvδ (by have := hρpos top; positivity)).2 harg
    linarith
  set s : ℝ := 5 * Real.logb (1 / δ) L with hsdef
  have hlogL : Real.logb (1 / δ) L ≤ ζ₂ / 128 := by
    rw [Real.logb_le_iff_le_rpow hinvδ (by linarith), one_div_rpow_eq hδ]
    exact hLup
  have hlogLpos : 0 < Real.logb (1 / δ) L := Real.logb_pos hinvδ (by linarith)
  have hGstep : ∀ k < top, G (k + 1) - G k ≤ s := by
    intro k hk
    have h1 := X318.cellProfile_step_of_family x₁ v₁ S hSne hδ hδ1' a ρ top hρpos
      (by linarith : (0 : ℝ) < L) hρratio hlowX hupX k hk
    have h2 : Real.logb (1 / δ) (2 * (4 * (L : ℝ) + 2) ^ 6 / (L : ℝ) ^ 2) ≤ s := by
      rw [hsdef]
      calc Real.logb (1 / δ) (2 * (4 * (L : ℝ) + 2) ^ 6 / (L : ℝ) ^ 2)
          ≤ Real.logb (1 / δ) ((L : ℝ) ^ 5) :=
            Real.logb_le_logb_of_le hinvδ (by positivity) hLstep
        _ = 5 * Real.logb (1 / δ) L := by rw [Real.logb_pow]; norm_num
    linarith
  have hprof := profile_dichotomy_step (N := top) (G := G) (ζ := ζ₂ / 4) (ζ₂ := ζ₂ / 2)
    (ξ := ξ / 2) (s := s) hG0 hGlow hGstep (by linarith) (by linarith)
    (by rw [hsdef]; linarith) (by rw [hsdef]; positivity)
  -- 5. the branches
  have htop2' : δ ^ (ξ / 2) ≤ 2 * δ * (L : ℝ) ^ top :=
    le_trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)) htop2
  obtain ⟨kk, g, hginj, hgS, hsize, hout⟩ : ∃ (kk : ℕ) (g : Fin kk → Fin m),
      Function.Injective g ∧ (∀ j, g j ∈ S) ∧ δ ^ (κ / 4) * S.card ≤ kk ∧
      (AllScales ξ δ (fun j => x₁ (g j)) (fun j => v₁ (g j)) ∨
        SBpred (ξ / 20) ζ₂ δ kk
          (fun j => Metric.thickening δ (segment ℝ (x₁ (g j)) (x₁ (g j) + v₁ (g j)))) ∨
        FlatPrismsQ ζ₂ ζ₃ δ
          (fun j => Metric.thickening δ (segment ℝ (x₁ (g j)) (x₁ (g j) + v₁ (g j))))) := by
    rcases hprof with hsticky | ⟨i₀, j₂, hij, hj₂, hmin, hgap, hsep⟩
    · obtain ⟨kk, g, hginj, hgS, hsize, hout⟩ := hStδ δ hδ hδS' L top hL2 hLlow hLup' htopNmax
        htop1 htop2' m x₁ v₁ S a hpack₁ (hprep ζS hc₁S) hsticky
      refine ⟨kk, g, hginj, hgS, hsize, ?_⟩
      rcases hout with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · have hsep' : ξ / 20 ≤ ((j₂ : ℝ) - i₀) * Real.logb (1 / δ) L := by
        have he : ((j₂ : ℝ) - i₀) * s = 5 * (((j₂ : ℝ) - i₀) * Real.logb (1 / δ) L) := by
          rw [hsdef]; ring
        linarith
      have hcast : ((j₂ - i₀ : ℕ) : ℝ) = (j₂ : ℝ) - i₀ := Nat.cast_sub hij.le
      have hLeq : (1 / δ) ^ Real.logb (1 / δ) L = (L : ℝ) :=
        Real.rpow_logb (by positivity) (ne_of_gt hinvδ) (by linarith)
      have hLsep : δ ^ (-(ξ / 20)) ≤ (L : ℝ) ^ (j₂ - i₀) := by
        calc δ ^ (-(ξ / 20)) = (1 / δ) ^ (ξ / 20) := (one_div_rpow_eq hδ _).symm
          _ ≤ (1 / δ) ^ (((j₂ : ℝ) - i₀) * Real.logb (1 / δ) L) :=
              Real.rpow_le_rpow_of_exponent_le hinvδ.le hsep'
          _ = ((1 / δ) ^ Real.logb (1 / δ) L) ^ ((j₂ - i₀ : ℕ) : ℝ) := by
              rw [← Real.rpow_mul (by positivity), hcast, mul_comm]
          _ = (L : ℝ) ^ (j₂ - i₀) := by rw [hLeq, Real.rpow_natCast]
      obtain ⟨kk, g, hginj, hgS, hsize, hout⟩ := hNsδ δ hδ hδN' L top hL2 hLlow hLup' htopNmax
        htop1 m x₁ v₁ S a hpack₁ (hprep ζN hc₁N) i₀ j₂ hij hj₂ hmin hgap hLsep
      refine ⟨kk, g, hginj, hgS, hsize, ?_⟩
      rcases hout with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  -- 6. the derived family
  have hkpos : 0 < kk := by
    rcases Nat.eq_zero_or_pos kk with h | h
    · exfalso
      rw [h, Nat.cast_zero] at hsize
      have : 0 < δ ^ (κ / 4) * S.card := mul_pos (by positivity) hSpos
      linarith
    · exact h
  have h2θ : δ ^ θ ≤ 1 / 2 := by
    have h := hda δ hδ hδa'
    rw [Real.rpow_neg hδ.le] at h
    have hpos : 0 < δ ^ θ := by positivity
    have h' : δ ^ θ ≤ 2⁻¹ := (le_inv_comm₀ (by norm_num) hpos).1 h
    rw [one_div]; exact h'
  refine ⟨kk, fun j => x₁ (g j), fun j => v₁ (g j),
    fun j => Y (gc (e (g j))) ∩ Metric.thickening δ (segment ℝ (x₁ (g j)) (x₁ (g j) + v₁ (g j))),
    ⟨hkpos, fun j => hv₁u (g j), fun j => hT₁ (g j),
      fun i j hij => hov₁ (g i) (g j) (hginj.ne hij),
      fun j => (hYm _).inter Metric.isOpen_thickening.measurableSet,
      fun j => Set.inter_subset_right, fun j => ?_⟩, ?_, ?_, ?_⟩
  · -- density: half of the shading is in the canonical tube
    show ENNReal.ofReal (δ ^ (θ + η) * δ ^ 2) ≤ volume (Y (gc (e (g j))) ∩
      Metric.thickening δ (segment ℝ (x' (e (g j))) (x' (e (g j)) + v' (e (g j)))))
    have hreal : δ ^ (θ + η) * δ ^ 2 ≤ (1 / 2) * (δ ^ η * δ ^ 2) := by
      rw [Real.rpow_add hδ]
      have : 0 ≤ δ ^ η * δ ^ 2 := by positivity
      calc δ ^ θ * δ ^ η * δ ^ 2 = δ ^ θ * (δ ^ η * δ ^ 2) := by ring
        _ ≤ (1 / 2) * (δ ^ η * δ ^ 2) := mul_le_mul_of_nonneg_right h2θ this
    calc ENNReal.ofReal (δ ^ (θ + η) * δ ^ 2) ≤ ENNReal.ofReal ((1 / 2) * (δ ^ η * δ ^ 2)) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ η * δ ^ 2) := by
          rw [ENNReal.ofReal_mul (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num),
            ENNReal.ofReal_ofNat, one_div]
      _ ≤ (1 / 2 : ENNReal) * (2 * volume (Y (gc (e (g j))) ∩
          Metric.thickening δ (segment ℝ (x' (e (g j))) (x' (e (g j)) + v' (e (g j)))))) :=
          mul_le_mul_right (hhalf (e (g j))) _
      _ = volume (Y (gc (e (g j))) ∩
          Metric.thickening δ (segment ℝ (x' (e (g j))) (x' (e (g j)) + v' (e (g j))))) := by
          rw [← mul_assoc, one_div, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top,
            one_mul]
  · -- the size: `δ^κ n ≤ kk`
    have hS_le : (S.card : ℝ) ≤ δ ^ (-(κ / 4)) * kk := by
      have h1 : δ ^ (-(κ / 4)) * (δ ^ (κ / 4) * S.card) = S.card := by
        rw [← mul_assoc, ← Real.rpow_add hδ, neg_add_cancel, Real.rpow_zero, one_mul]
      calc (S.card : ℝ) = δ ^ (-(κ / 4)) * (δ ^ (κ / 4) * S.card) := h1.symm
        _ ≤ δ ^ (-(κ / 4)) * kk := mul_le_mul_of_nonneg_left hsize (by positivity)
    have hloss3 : 6 * (D + 1) * Loss ≤ δ ^ (-(3 * κ / 4)) := by
      have hL0 : 0 ≤ 6 * (D + 1) * Loss := by positivity
      have h48 : 6 * (D + 1) * Loss ≤ 48 ^ 3 * (6 * (D + 1)) * Loss := by
        have : 48 ^ 3 * (6 * (D + 1)) * Loss = 48 ^ 3 * (6 * (D + 1) * Loss) := by ring
        rw [this]; exact le_mul_of_one_le_left hL0 (by norm_num)
      calc 6 * (D + 1) * Loss ≤ 48 ^ 3 * (6 * (D + 1)) * Loss := h48
        _ ≤ δ ^ (-c₀) := hLossA
        _ ≤ δ ^ (-(3 * κ / 4)) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1
            (by have := min_le_right (c₁ / 2) (3 * κ / 4); linarith)
    have hexp : δ ^ κ * (δ ^ (-(3 * κ / 4)) * δ ^ (-(κ / 4))) = 1 := by
      rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
      have : κ + (-(3 * κ / 4) + -(κ / 4)) = 0 := by ring
      rw [this, Real.rpow_zero]
    calc δ ^ κ * (n : ℝ) ≤ δ ^ κ * (6 * (D + 1) * Loss * S.card) :=
          mul_le_mul_of_nonneg_left hnS (by positivity)
      _ ≤ δ ^ κ * (δ ^ (-(3 * κ / 4)) * (δ ^ (-(κ / 4)) * kk)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul hloss3 hS_le (Nat.cast_nonneg _) (by positivity)
      _ = (δ ^ κ * (δ ^ (-(3 * κ / 4)) * δ ^ (-(κ / 4)))) * kk := by ring
      _ = kk := by rw [hexp, one_mul]
  · -- the union
    exact Set.iUnion_subset fun j => Set.inter_subset_left.trans (Set.subset_iUnion Y _)
  · -- the trichotomy
    rcases hout with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

/-- **o038 from `A`, the two branch statements with the quadratic count, and the counted flat
gain** (o071 imported). -/
theorem o038_of_branchesQ (hA : StatementA) (hSt : StickyBranchStmtQ)
    (hNs : NonStickyBranchStmtQ) (hC : FlatGainQ) : O038 :=
  o038_of_repairQ hA (trichotomyDerivedQ_of_branches hSt hNs) WangZahlLot.wz_separated_scales_gain hC

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy
