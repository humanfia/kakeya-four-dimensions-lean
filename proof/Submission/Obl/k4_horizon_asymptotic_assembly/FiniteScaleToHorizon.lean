/- Adapted from this LOT tree, obligation o103, session x0354, commit162b3a6,
Submission/Obl/k4_initial_horizon_bound/FiniteScaleToHorizon.lean.
Named forms and Boolean calculus originally came from o103/x0360, commits642b39c andb0c6023;
the finite interface definitions came from o160/x0559/b0539eb, as attributed below. -/

import Submission.Obl.k4_horizon_asymptotic_assembly.FiniteScaleInterface
import Submission.Obl.k4_horizon_asymptotic_assembly.FiniteScaleChoices
import Submission.Obl.k4_horizon_asymptotic_assembly.Fmt

/-! The asymptotic conversion of the finite weighted atlas contract. All
format exponents are chosen before the requested slack tolerance. -/

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

namespace Submission.Obl.k4_horizon_asymptotic_assembly.Outer

noncomputable def InitialHorizonAt (N K : ℕ → ℝ) (L : ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ)))
    (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (B : (k : ℕ) → Fin (W k) → ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ h : ℝ, L < h → ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
    ∃ κ : ℝ, 1 ≤ κ ∧ K k ≤ κ ∧ κ ≤ N k ^ ε ∧
    ∃ T C : ℕ, ∃ (γ : Fin C → Fin (W k)) (j : Fin C → Fin (2 ^ T))
      (c u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
      (R : Fin C → MvPolynomial (Fin 4) ℝ) (A : Fin C → Set (ℕ × (Fin 6 → ℝ)))
      (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)),
      (2 : ℝ) ^ T ≤ N k ^ h ∧ (C : ℝ) ≤ N k ^ M ∧
      (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧
      (∀ b, Chart (N k) M D κ T ((j b : ℕ) : ℝ) L (B k (γ b)) (E k (γ b))
        (c b) (u b) (Q b) (R b) (A b) (F b)
        (ENNReal.ofReal (N k ^ (-f L) * |(Q b).det| / ((2 : ℝ) ^ T * κ)) ≤
          ((ν k (γ b)).prod volume) (F b))) ∧
      ENNReal.ofReal κ⁻¹ ≤ ∑ b, ENNReal.ofReal (ω k (γ b)) * ((ν k (γ b)).prod volume) (F b)

set_option maxHeartbeats 1600000 in
theorem initial_horizon_from_finite_scale
    {N K : ℕ → ℝ} {L d S η : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ}
    {ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))}
    {E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}
    {g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ →
      ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}
    (hf : FiniteScaleAtlas) (hp : Prob N K L d S η W ω ν E P B f g G)
    (hlight : ∃ H₀ : ℝ, ∀ τ : ℝ, 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ N k ^ (-H₀) →
      finiteScaleLightMass (W k) (ω k) (ν k) (E k) (B k) (dl (N k) L) ρ
        (N k ^ (-f L - τ)) ≤ ENNReal.ofReal (N k ^ (-c))) :
    InitialHorizonAt N K L W ω ν E B f := by
  classical
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη,
    ⟨M₀, D₀, hfmt⟩, hobs, hvobs, hfmono, htyp, hprof, hangular⟩
  rcases hf with ⟨A₀, C₀, hA₀, hC₀, hfinite⟩
  rcases hlight with ⟨H₀, hlight⟩
  have hN1 : ∀ k, 1 ≤ N k := fun k => by linarith [hN k]
  let MH := M₀ + 1
  let J := MH * A₀ + ⌈max H₀ 0⌉₊ + 2
  let MP := ⌈L⌉₊ + 3
  let MF := ⌈|f L|⌉₊
  let MV := MH + (J + 1) + MF + 2 * MP + 4
  let M := MV * C₀
  have hJ : 1 ≤ J := by dsimp [J]; omega
  have hJr : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hJH : H₀ ≤ (J : ℝ) := by
    have hh := Nat.le_ceil (max H₀ 0)
    have hn : (⌈max H₀ 0⌉₊ : ℝ) ≤ J := by exact_mod_cast (show ⌈max H₀ 0⌉₊ ≤ J by dsimp [J]; omega)
    exact (le_max_left _ _).trans (hh.trans hn)
  let dm : ℕ → ℕ := fun k => ⌈N k ^ J⌉₊
  have hmesh : ∀ k, 2 ≤ dm k ∧ N k ^ J ≤ (dm k : ℝ) ∧ (dm k : ℝ) ≤ N k ^ (J + 1) :=
    fun k => initial_integer_mesh_bounds (hN k) hJ
  have hmesh' : ∀ k, (dm k : ℝ) ≤ N k ^ (2 * (J : ℝ)) := by
    intro k
    have heq : 2 * (J : ℝ) = ((2 * J : ℕ) : ℝ) := by push_cast; ring
    rw [heq, Real.rpow_natCast]
    exact (hmesh k).2.2.trans
      (pow_le_pow_right₀ (hN1 k) (show J + 1 ≤ 2 * J by omega))
  intro h hh
  refine ⟨M, max D₀ 4, ?_⟩
  intro ε hε
  let e := min ε 1
  have he : 0 < e := lt_min hε (by norm_num)
  have he1 : e ≤ 1 := min_le_right _ _
  have heε : e ≤ ε := min_le_left _ _
  let ζ := e / (16 * (J : ℝ))
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  obtain ⟨ηg, Cg, hηg, hCg, hfinite⟩ := hfinite ζ hζ
  obtain ⟨csmall, hcsmall, hgood⟩ := hlight (e / 8) (by positivity)
  have hduration := eventually_core_duration_threshold hN1 hNt hK.1 hK.2 hJr hηg
    (Filter.Eventually.of_forall (fun k => by simpa only [Real.rpow_natCast] using (hmesh k).2.1))
  have herror := eventually_initial_relative_error_small hN1 hNt hK.1 hK.2 hJr he Cg hCg.le
    (Filter.Eventually.of_forall (fun k => ⟨Nat.cast_nonneg (dm k), hmesh' k⟩))
  have hslack := eventually_initial_slack_dominates hN1 hNt hK.1 hK.2 he
  have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 hNt hK.1 hK.2 1 (show -csmall < 0 by linarith) (show (0 : ℝ) ≤ 16 by norm_num)
  have htime := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt hNt hh (8 : ℝ)
  have hKN := hK.2 1 (by norm_num)
  apply Filter.Eventually.frequently
  filter_upwards [hgood, hduration, herror, hslack, hsmall, htime, hKN] with
    k hkLight hkDuration hkError hkSlack hkSmall hkTime hkKN
  let Nk := N k
  let Kk := K k
  let T := initialBlockDepth Nk L
  let q : ℝ := ((2 : ℝ) ^ T)⁻¹
  let a := dl Nk L
  let κ := Nk ^ e
  let n₀ := Nk ^ (-f L)
  let θ := n₀ * Nk ^ (-(e / 8))
  let s := (16 * Kk)⁻¹
  let τ₀ := initialFloor n₀ (2 * Kk + 2) q κ
  let H := Nk ^ MH
  let V := 1 + H + Kk + (dm k : ℝ) + (2 : ℝ) ^ T + τ₀⁻¹
  have hNk : 0 < Nk := by dsimp [Nk]; linarith [hN k]
  have hNk1 : 1 ≤ Nk := hN1 k
  have hKk : 0 < Kk := by dsimp [Kk]; linarith [hK.1 k]
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hn₀ : 0 < n₀ := by dsimp [n₀]; positivity
  have hs : 0 < s := by dsimp [s]; positivity
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hτ₀ : 0 < τ₀ := initialFloor_pos hn₀ (by linarith) hq hκ
  have hb := initialBlockDepth_bounds (hN k) hL.le
  have hapos : 0 < a := hb.1
  have ha1 : a ≤ 1 := hb.2.1
  have haq : 8 * q = a := by
    dsimp [q, T, a]
    rw [initialBlockDepth_scale (hN k) hL.le]
    ring
  have hq1 : q ≤ 1 := by linarith
  have hMH : 1 ≤ MH := by dsimp [MH]; omega
  have hNH : Nk ≤ H := by
    dsimp [H]
    simpa only [pow_one] using pow_le_pow_right₀ hNk1 hMH
  have hH2 : 2 ≤ H := (hN k).trans hNH
  have hKH : Kk ≤ H := (show Kk ≤ Nk by simpa only [Real.rpow_one] using hkKN).trans hNH
  have hbaseH : Nk ^ M₀ ≤ H := pow_le_pow_right₀ hNk1 (by dsimp [MH]; omega)
  have hHD : H ^ A₀ ≤ (dm k : ℝ) := by
    calc
      H ^ A₀ = Nk ^ (MH * A₀) := (pow_mul _ _ _).symm
      _ ≤ Nk ^ J := pow_le_pow_right₀ hNk1 (by dsimp [J]; omega)
      _ ≤ _ := (hmesh k).2.1
  have hκslack : 256 * (Kk + 2) ≤ κ := hkSlack
  have hκK : Kk ≤ κ := by linarith
  have hκ1 : 1 ≤ κ := (hK.1 k).trans hκK
  have hκN : κ ≤ Nk := by
    dsimp [κ]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNk1 he1
  have hninv : n₀⁻¹ ≤ Nk ^ MF := by
    dsimp [n₀]
    rw [Real.rpow_neg hNk.le, inv_inv, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hNk1 ((le_abs_self _).trans (Nat.le_ceil _))
  have hqinv : q⁻¹ ≤ Nk ^ MP := by
    have hLceil : L ≤ (⌈L⌉₊ : ℝ) := Nat.le_ceil L
    have hpowL : Nk ^ L ≤ Nk ^ ⌈L⌉₊ := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hNk1 hLceil
    have h8 : (8 : ℝ) ≤ Nk ^ 3 := by
      simpa only [show (2 : ℝ) ^ 3 = 8 by norm_num] using
        pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (hN k) 3
    calc
      q⁻¹ = (2 : ℝ) ^ T := inv_inv _
      _ ≤ 8 * Nk ^ L := hb.2.2.2
      _ ≤ Nk ^ 3 * Nk ^ ⌈L⌉₊ := mul_le_mul h8 hpowL (by positivity) (by positivity)
      _ = Nk ^ MP := by dsimp [MP]; rw [pow_add]; ring
  have hJt : (2 : ℝ) ^ T ≤ Nk ^ MP := by simpa only [q, inv_inv] using hqinv
  have hV : V ≤ Nk ^ MV := initial_raw_budget_power (hN k) (by positivity) hKk.le hn₀
    (by linarith) hq hκ le_rfl hKH (hmesh k).2.2 hJt hninv hqinv hκN
  have hVC : V ^ C₀ ≤ Nk ^ M := by
    calc
      _ ≤ (Nk ^ MV) ^ C₀ := pow_le_pow_left₀ (by dsimp [V]; positivity) hV C₀
      _ = _ := (pow_mul _ _ _).symm
  have hdNat : 0 < dm k := lt_of_lt_of_le (by decide : 0 < 2) (hmesh k).1
  have hρ : 0 < q / (dm k : ℝ) := div_pos hq (by exact_mod_cast hdNat)
  have hρbound : q / (dm k : ℝ) ≤ Nk ^ (-H₀) := by
    have hDpos : (0 : ℝ) < dm k := by exact_mod_cast hdNat
    calc
      _ ≤ (dm k : ℝ)⁻¹ := by rw [div_eq_mul_inv]; nlinarith [inv_pos.mpr hDpos]
      _ ≤ (Nk ^ J)⁻¹ := inv_anti₀ (by positivity) (hmesh k).2.1
      _ = Nk ^ (-(J : ℝ)) := by rw [Real.rpow_neg hNk.le, Real.rpow_natCast]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hNk1 (by linarith [hJH])
  have hθeq : θ = Nk ^ (-f L - e / 8) := by
    dsimp [θ, n₀]
    rw [← Real.rpow_add hNk]
    congr 1
  have hLight : finiteScaleLightMass (W k) (ω k) (ν k) (E k) (B k) a (q / (dm k : ℝ)) θ ≤
      ENNReal.ofReal ((16 * Kk)⁻¹) := by
    have hl := hkLight (q / (dm k : ℝ)) hρ hρbound
    rw [← hθeq] at hl
    apply hl.trans (ENNReal.ofReal_le_ofReal ?_)
    simp only [pow_one, Real.rpow_zero] at hkSmall
    rw [← one_div]
    apply (le_div_iff₀ (by positivity : 0 < 16 * Kk)).mpr
    nlinarith [hkSmall]
  have hdata : ∀ γ, IsProbabilityMeasure (ν k γ) ∧ 0 < B k γ ∧ B k γ ≤ H ∧
      (B k γ)⁻¹ ≤ H ∧ (P k γ).totalDegree ≤ 2 ∧ (∀ v, |(P k γ).coeff v| ≤ H) ∧
      MeasurableSet (E k γ) ∧ E k γ ⊆ univ ×ˢ Icc (0 : ℝ) 1 ∧
      (∀ p ∈ E k γ, (p.1.1 : ℝ) ≤ H ∧ ∀ v, |p.1.2 v| ≤ H) ∧
      (∀ i, Fmt 7 H D₀ {x : Fin 7 → ℝ | ((i, fun v : Fin 6 => x v.castSucc), x 6) ∈ E k γ}) := by
    intro γ
    rcases (hfmt k).2.2.2.1 γ with ⟨hν, hBp, hBu, hBi, hPd, hPc,
      hprior, hEm, hEu, hEb, hEf, htrace, hderiv⟩
    exact ⟨hν, hBp, hBu.trans hbaseH, hBi.trans hbaseH, hPd,
      fun v => (hPc v).trans hbaseH, hEm, hEu,
      fun p hp => ⟨(hEb p hp).1.trans hbaseH, fun v => ((hEb p hp).2 v).trans hbaseH⟩,
      fun i => Fmt.mono (hEf i) hbaseH le_rfl⟩
  have htrace := fun γ => ((hfmt k).2.2.2.1 γ).2.2.2.2.2.2.2.2.2.2.2.1
  have hderiv := fun γ => ((hfmt k).2.2.2.1 γ).2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨Cout, γ, j, cc, uu, Q, R, AA, FF, hcount, hdisj, hcharts, hmass⟩ :=
    hfinite H Kk hH2 (hK.1 k) hKH (W k) D₀ (ω k) (ν k) (E k) (P k) (B k)
      ((hfmt k).1.trans hbaseH) (hfmt k).2.1 (hfmt k).2.2.1 hdata htrace hderiv
      a T hapos ha1 haq.le (dm k) (hmesh k).1 hHD s τ₀ θ n₀ κ hs hτ₀ hθ hn₀
      hκslack hkDuration (initialFloor_constraint hκ.ne').le
  have hrelative : Cg * Kk ^ 3 * τ₀ * (dm k : ℝ) ^ ζ / (s * θ * q ^ 2) ≤ 1 / 4 := by
    rw [initial_relative_error_eq hn₀.ne' hq.ne' hκ.ne' hKk.ne' hNk]
    exact hkError
  have hmassfinite : (∑ γ, ENNReal.ofReal (ω k γ) * ((ν k γ).prod volume) (E k γ)) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro γ _
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    haveI := (hdata γ).1
    have hmassle : ((ν k γ).prod volume) (E k γ) ≤ 1 := by
      calc
        _ ≤ ((ν k γ).prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := measure_mono (hdata γ).2.2.2.2.2.2.2.1
        _ = 1 := by rw [Measure.prod_prod]; simp
    exact ne_top_of_le_ne_top (by simp) hmassle
  have hstart : ENNReal.ofReal Kk⁻¹ ≤ ∑ γ, ENNReal.ofReal (ω k γ) *
      ((ν k γ).prod volume) (E k γ) := by
    simpa only [Measure.restrict_apply_univ] using (hfmt k).2.2.2.2
  have hret := initial_mass_retention hKk hmassfinite hstart hLight hrelative hmass
  have hfloor (b : Fin Cout) : ENNReal.ofReal (Nk ^ (-f L) * |(Q b).det| /
      ((2 : ℝ) ^ T * κ)) ≤ ((ν k (γ b)).prod volume) (FF b) := by
    have hx := (hcharts b).2.2.2.2.2.2.2.2.2.2.2
    simpa only [n₀, q, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using hx
  refine ⟨κ, hκ1, hκK, ?_, T, Cout, γ, j, cc, uu, Q, R, AA, FF,
    hb.2.2.2.trans hkTime.le, hcount.trans hVC, hdisj, ?_, ?_⟩
  · exact Real.rpow_le_rpow_of_exponent_le hNk1 heε
  · intro b
    rcases hcharts b with ⟨hQ, hcu, hbudget, hsmallQ, hR, hRc, hAm, hFm, hAf, hAb, hFb, hex⟩
    exact ⟨hQ, hcu.trans hVC, hbudget.trans hVC, hsmallQ, hR,
      fun v => (hRc v).trans hVC, hAm, hFm,
      fun i => ⟨Fmt.mono (hAf i).1 hVC le_rfl, Fmt.mono (hAf i).2 hVC le_rfl⟩,
      fun z hz => ⟨(hAb z hz).1.trans hVC, fun v => ((hAb z hz).2.1 v).trans hVC,
        (hAb z hz).2.2⟩, hFb, hfloor b⟩
  · apply le_trans (ENNReal.ofReal_le_ofReal (inv_anti₀ (by positivity : 0 < 2 * Kk) ?_)) hret
    linarith

end Submission.Obl.k4_horizon_asymptotic_assembly.Outer
