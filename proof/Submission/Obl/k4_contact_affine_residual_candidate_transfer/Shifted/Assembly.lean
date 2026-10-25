/- Adapted from this LOT tree, obligation o260, session x0919, commit 57638ddd7c07709143f61bbedd02efd72974929b,
   Submission/Obl/k4_contact_shifted_quadratic_candidates/Shifted/Assembly.lean. Original attribution comments are retained below. -/
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.Shifted.FrameCandidates
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.Shifted.Interface
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.Shifted.ResidualCoefficientBudget
import Submission.Obl.k4_profile_density_bounds.Asymptotics

/-!
# Shifted candidates from the candidates of the residual model

Given good frames for a parent depth `s₀` and residual horizon `U'` with
`s₀ + U' ≤ V`, a residual model on them whose candidate statement holds, and a
fixed-power bound on the residual tests, the original data have shifted
candidates below the horizon `V`: each residual candidate at residual depth
`s'` returns, through its frame, at the grid depth
`depth h ≤ s₀ + s'` of its label (`poly_pullback`, `velocity_pullback`).
All losses are charged to `ε` at late indices.
-/

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer.Shifted

open MeasureTheory Set Filter MvPolynomial ProbabilityTheory
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Obl.k4_contact_affine_residual_candidate_transfer
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4ChartLifting

noncomputable section

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable {Rk θ K₂ e₀' : ℝ} {f : Frame D k s₀ U'}

/-- The parent chart constants are bounded by a fixed power of `N`. -/
theorem chartSubst_power (hg : FrameGood f Rk θ K₂ e₀') (hs₀ : 0 ≤ s₀) (hκ1 : D.κ ≤ 1)
    (hKN : 24 * D.K k ^ 4 ≤ D.N k) (j : Fin 4) :
    coeffL1 (chartSubst f j) ≤ D.N k ^ (2 * s₀ + 1) := by
  have hN2 : 2 ≤ D.N k := hg.N_ge
  have hN : 0 < D.N k := lt_of_lt_of_le two_pos hN2
  have hN1 : 1 ≤ D.N k := le_trans one_le_two hN2
  have hK : 1 ≤ D.K k := hg.K_ge
  have hq := f.q₀_pos
  have ha := f.a₀_pos hN
  -- `q₀⁻¹ ≤ K N^s₀`, `a₀⁻¹ = N^s₀`
  have hqinv : f.q₀⁻¹ ≤ D.K k * D.N k ^ s₀ := by
    have h1 := hg.q₀_le_K.2
    calc
      f.q₀⁻¹ ≤ D.K k * D.N k ^ (D.κ * s₀) := h1
      _ ≤ D.K k * D.N k ^ s₀ := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        apply Real.rpow_le_rpow_of_exponent_le hN1
        nlinarith [hg.κ_pos]
  have hainv : f.a₀⁻¹ = D.N k ^ s₀ := by
    rw [Frame.a₀, hg.depth_zero, Real.rpow_neg hN.le, inv_inv]
  have hNs : 1 ≤ D.N k ^ s₀ := Real.one_le_rpow hN1 hs₀
  -- parent row constants
  have ht₀ : |f.t₀| ≤ 1 := by
    have h0 : f.t₀ ∈ f.block 0 f.i₀ := by
      rw [f.parent_block]; exact ⟨le_rfl, by linarith⟩
    simp only [Frame.block, Data.I, mem_Icc] at h0
    have hj : (((D.j k (f.depth 0) f.i₀ : ℕ) : ℝ) + 1) ≤ (2 : ℝ) ^ f.Tl 0 := by
      exact_mod_cast (D.j k (f.depth 0) f.i₀).isLt
    have h2 : (0 : ℝ) < 2 ^ f.Tl 0 := by positivity
    have hnn : 0 ≤ f.t₀ := le_trans (by positivity) h0.1
    rw [abs_of_nonneg hnn]
    exact h0.2.trans ((div_le_one h2).mpr hj)
  have hc (e : Fin 5) : |D.c k (f.depth 0) f.i₀ e| ≤ D.K k := hg.cbound 0 (Nat.zero_le _) f.i₀ e
  have hZ₀ : |f.Z₀| ≤ 2 * D.K k := by
    unfold Frame.Z₀
    calc
      _ ≤ |D.c k (f.depth 0) f.i₀ 0| + |f.t₀| * |D.c k (f.depth 0) f.i₀ 1| := by
        rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ D.K k + 1 * D.K k := add_le_add (hc 0) (mul_le_mul ht₀ (hc 1) (abs_nonneg _) zero_le_one)
      _ = _ := by ring
  have hY₀ : |f.Y₀| ≤ 2 * D.K k + 2 * D.K k ^ 2 := by
    unfold Frame.Y₀
    calc
      _ ≤ |D.c k (f.depth 0) f.i₀ 2| + |f.t₀| * |D.c k (f.depth 0) f.i₀ 3| +
          |D.c k (f.depth 0) f.i₀ 4| * |f.Z₀| := by
        rw [← abs_mul, ← abs_mul]
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ D.K k + 1 * D.K k + D.K k * (2 * D.K k) :=
        add_le_add (add_le_add (hc 2) (mul_le_mul ht₀ (hc 3) (abs_nonneg _) zero_le_one))
          (mul_le_mul (hc 4) hZ₀ (abs_nonneg _) (by linarith))
      _ = _ := by ring
  have hbase := coeffL1_chartSubst f j
  have hfac1 : |f.q₀⁻¹| + |(f.q₀ ^ 2)⁻¹| + |f.a₀⁻¹| ≤ 3 * D.K k ^ 2 * D.N k ^ (2 * s₀) := by
    rw [abs_of_pos (inv_pos.mpr hq), abs_of_pos (inv_pos.mpr (by positivity)),
      abs_of_pos (inv_pos.mpr ha), hainv]
    have hsq : (f.q₀ ^ 2)⁻¹ = (f.q₀⁻¹) ^ 2 := by rw [inv_pow]
    rw [hsq]
    have hq0 : 0 ≤ f.q₀⁻¹ := (inv_pos.mpr hq).le
    have h2s : D.N k ^ (2 * s₀) = (D.N k ^ s₀) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]; congr 1; ring
    rw [h2s]
    have hsq' : f.q₀⁻¹ ^ 2 ≤ (D.K k * D.N k ^ s₀) ^ 2 := pow_le_pow_left₀ hq0 hqinv 2
    have hK2 : 1 ≤ D.K k ^ 2 := one_le_pow₀ hK
    have hX : D.N k ^ s₀ ≤ (D.N k ^ s₀) ^ 2 := by nlinarith
    have hKK : D.K k ≤ D.K k ^ 2 := by nlinarith
    have e1 : f.q₀⁻¹ ≤ D.K k ^ 2 * (D.N k ^ s₀) ^ 2 :=
      hqinv.trans (mul_le_mul hKK hX (by positivity) (by positivity))
    have e2 : f.q₀⁻¹ ^ 2 ≤ D.K k ^ 2 * (D.N k ^ s₀) ^ 2 := by
      rw [mul_pow] at hsq'; exact hsq'
    have e3 : D.N k ^ s₀ ≤ D.K k ^ 2 * (D.N k ^ s₀) ^ 2 :=
      hX.trans (le_mul_of_one_le_left (by positivity) hK2)
    linarith
  have hfac2 : 1 + |f.t₀| + |f.Z₀| + |f.Y₀| ≤ 8 * D.K k ^ 2 := by
    have hK2 : D.K k ≤ D.K k ^ 2 := by nlinarith
    nlinarith
  calc
    coeffL1 (chartSubst f j) ≤ (3 * D.K k ^ 2 * D.N k ^ (2 * s₀)) * (8 * D.K k ^ 2) :=
      hbase.trans (mul_le_mul hfac1 hfac2 (by positivity) (by positivity))
    _ = (24 * D.K k ^ 4) * D.N k ^ (2 * s₀) := by ring
    _ ≤ D.N k * D.N k ^ (2 * s₀) := mul_le_mul_of_nonneg_right hKN (by positivity)
    _ = D.N k ^ (2 * s₀ + 1) := by
      rw [Real.rpow_add hN, Real.rpow_one]; ring

/-- The eventual numeric conditions used by the return of residual candidates. -/
theorem eventually_return_conditions (hD : ContactProblem D) {s₀ U' e₀' : ℝ} (hs₀ : 0 < s₀)
    (gf : GoodFrames D s₀ U' e₀') {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, (∃ f, gf.fr k = some f) ∧
      (∀ f, gf.fr k = some f → U' / f.m ≤ ε / 4) ∧
      (∀ f, gf.fr k = some f → f.H ≤ D.N k ^ (s₀ / 2)) ∧
      D.N k ^ (-(ε / 8)) ≤ gf.θ k ∧ D.K k ≤ D.N k ^ (ε / 8) ∧
      24 * D.K k ^ 4 ≤ D.N k ∧ 2 * D.K k + 1 ≤ D.N k := by
  have p := hD.parameters
  have hN0 : ∀ k, 0 < D.N k := fun k => lt_of_lt_of_le two_pos (p.scale k)
  have h1 := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    p.scale_limit (a := 1 / 2) (b := 1) (by norm_num) 24
  have h2 := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    p.scale_limit (a := 1 / 8) (b := 1) (by norm_num) 3
  filter_upwards [gf.eventually_some, gf.gap_small (ε / 4) (by positivity),
    gf.H_small (s₀ / 2) (by positivity), gf.θ_large (ε / 8) (by positivity),
    p.subpower.2 (ε / 8) (by positivity), p.subpower.2 (1 / 8) (by norm_num), h1, h2]
    with k hsome hgap hH hθ hK hK8 hc1 hc2
  refine ⟨hsome, hgap, hH, hθ, hK, ?_, ?_⟩
  · have hK1 : 1 ≤ D.K k := p.subpower.1 k
    have hpow : D.K k ^ 4 ≤ (D.N k ^ (1 / 8 : ℝ)) ^ 4 := pow_le_pow_left₀ (by linarith) hK8 4
    have e : (D.N k ^ (1 / 8 : ℝ)) ^ 4 = D.N k ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hN0 k).le]; norm_num
    rw [e] at hpow
    rw [Real.rpow_one] at hc1
    linarith
  · have hK1 : 1 ≤ D.K k := p.subpower.1 k
    rw [Real.rpow_one] at hc2
    linarith

/-- Shifted candidates below `V` from the candidates of a residual model on
good frames. -/
theorem shifted_of_residual (hD : ContactProblem D) {V s₀ U' e₀' : ℝ}
    (hs₀ : 0 < s₀) (hU' : 0 < U') (hV : s₀ + U' ≤ V)
    (gf : GoodFrames D s₀ U' e₀') (K' : ℕ → ℝ)
    (hpar : Parameters (residualData D s₀ U' e₀' K' gf.fr))
    (hbasic : (residualData D s₀ U' e₀' K' gf.fr).Basic)
    (hatlas : (residualData D s₀ U' e₀' K' gf.fr).Atlas)
    (hres : (residualData D s₀ U' e₀' K' gf.fr).Candidates) :
    ∃ R : ℝ, 1 < R ∧ ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, ∃ (s v : ℝ) (i : Fin (D.n k s)),
      R⁻¹ ≤ s ∧ s ≤ R ∧ R⁻¹ ≤ v ∧ v ≤ R ∧ s + v ≤ V ∧
        (ShiftedPoly D k R ε s v i ∨ ShiftedVelocity D k R ε s v i) := by
  have p := hD.parameters
  obtain ⟨R', hR'1, hR'⟩ := hres
  let c : ℝ := 2 * U' + 13
  have hc0 : 0 ≤ c := by dsimp only [c]; linarith
  have hFc : ∀ᶠ k in atTop, ∀ s : ℝ, R'⁻¹ ≤ s → s ≤ U' →
      ∀ f, gf.fr k = some f → ∀ i : Fin (f.level (gl f s)).n,
        (1 + ∑ e ∈ ((f.level (gl f s)).F i).support, |((f.level (gl f s)).F i).coeff e|) +
          ∑ e ∈ (X 3 : MvPolynomial (Fin 4) ℝ).support,
            |(X 3 : MvPolynomial (Fin 4) ℝ).coeff e| ≤ D.N k ^ c := by
    exact eventually_residual_coefficient_budget D s₀ U' e₀' K' gf.fr hpar hbasic hatlas hR'1
  set B : ℝ := 2 * s₀ + 1 with hBdef
  set C : ℝ := R' + R' * c with hCdef
  set R : ℝ := max (max R' s₀⁻¹) (max (s₀ + U') (C + 2 * B + 7)) + 1 with hRdef
  have hRR' : R' + 1 ≤ R := by
    have : R' ≤ max (max R' s₀⁻¹) (max (s₀ + U') (C + 2 * B + 7)) :=
      le_max_of_le_left (le_max_left _ _)
    linarith
  have hRs : s₀⁻¹ + 1 ≤ R := by
    have : s₀⁻¹ ≤ max (max R' s₀⁻¹) (max (s₀ + U') (C + 2 * B + 7)) :=
      le_max_of_le_left (le_max_right _ _)
    linarith
  have hRU : s₀ + U' + 1 ≤ R := by
    have : s₀ + U' ≤ max (max R' s₀⁻¹) (max (s₀ + U') (C + 2 * B + 7)) :=
      le_max_of_le_right (le_max_left _ _)
    linarith
  have hRC : C + 2 * B + 7 ≤ R := by
    have : C + 2 * B + 7 ≤ max (max R' s₀⁻¹) (max (s₀ + U') (C + 2 * B + 7)) :=
      le_max_of_le_right (le_max_right _ _)
    linarith
  have hR1 : 1 < R := by linarith
  have hR0 : 0 < R := by linarith
  have hR'0 : 0 < R' := by linarith
  have hRinv : R⁻¹ ≤ s₀ := by
    rw [inv_le_comm₀ hR0 hs₀]; linarith [inv_pos.mpr hs₀]
  have hRinv' : R⁻¹ ≤ R'⁻¹ := inv_anti₀ hR'0 (by linarith)
  refine ⟨R, hR1, fun ε hε => ?_⟩
  have hε' : 0 < ε / 4 := by positivity
  have hfreq := hR' (ε / 4) hε'
  refine (hfreq.and_eventually ((eventually_return_conditions hD hs₀ gf hε).and hFc)).mono ?_
  rintro k ⟨hcand, ⟨⟨f, hfr⟩, hgap, hH, hθ, hK, hKN, hKN2⟩, hFk⟩
  have hg := gf.good k f hfr
  have hN2 : 2 ≤ D.N k := p.scale k
  have hN : 0 < D.N k := lt_of_lt_of_le two_pos hN2
  have hN1 : 1 ≤ D.N k := le_trans one_le_two hN2
  have hK1 : 1 ≤ D.K k := p.subpower.1 k
  obtain ⟨s', v, i, hs1, hs2, hv1, hv2, hsv, halt⟩ := frameCand_of_residual hfr hcand
  have hh : gl f s' ≤ f.m := gridLevel_le _ _ _
  have hm : (0 : ℝ) < f.m := by exact_mod_cast hg.m_pos
  have hη : 0 < U' / f.m := div_pos hU' hm
  have hs'0 : 0 ≤ s' := le_trans (inv_pos.mpr hR'0).le hs1
  have hv0 : 0 ≤ v := le_trans (inv_pos.mpr hR'0).le hv1
  have hhη : ((gl f s' : ℕ) : ℝ) * (U' / f.m) ≤ s' := gridLevel_mul_le hη hs'0 f.m
  have hs'η : s' ≤ ((gl f s' : ℕ) : ℝ) * (U' / f.m) + U' / f.m := by
    apply le_gridLevel_mul_add hη f.m
    rw [mul_div_cancel₀ U' hm.ne']
    linarith
  have hhm : ((gl f s' : ℕ) : ℝ) * (U' / f.m) ≤ U' := by
    have : ((gl f s' : ℕ) : ℝ) ≤ f.m := by exact_mod_cast hh
    calc
      ((gl f s' : ℕ) : ℝ) * (U' / f.m) ≤ f.m * (U' / f.m) := mul_le_mul_of_nonneg_right this hη.le
      _ = U' := mul_div_cancel₀ U' hm.ne'
  have hdepth : f.depth (gl f s') = s₀ + ((gl f s' : ℕ) : ℝ) * (U' / f.m) := hg.depth_eq hh
  have hgap' := hgap f hfr
  have hHa : f.H * f.a₀ ≤ 1 := by
    have hH' := hH f hfr
    have ha : f.a₀ = D.N k ^ (-s₀) := by rw [Frame.a₀, hg.depth_zero]
    rw [ha]
    calc
      f.H * D.N k ^ (-s₀) ≤ D.N k ^ (s₀ / 2) * D.N k ^ (-s₀) :=
        mul_le_mul_of_nonneg_right hH' (by positivity)
      _ = D.N k ^ (-(s₀ / 2)) := by rw [← Real.rpow_add hN]; congr 1; ring
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hθK (a : ℝ) : D.N k ^ (a - ε) * D.K k ≤ D.N k ^ (a - ε / 4) * gf.θ k := by
    calc
      D.N k ^ (a - ε) * D.K k ≤ D.N k ^ (a - ε) * D.N k ^ (ε / 8) :=
        mul_le_mul_of_nonneg_left hK (by positivity)
      _ = D.N k ^ (a - ε / 4) * D.N k ^ (-(ε / 8)) * D.N k ^ (-(ε / 2)) := by
        rw [← Real.rpow_add hN, ← Real.rpow_add hN, ← Real.rpow_add hN]
        congr 1; ring
      _ ≤ D.N k ^ (a - ε / 4) * D.N k ^ (-(ε / 8)) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
      _ ≤ D.N k ^ (a - ε / 4) * gf.θ k := by
        rw [mul_one]; exact mul_le_mul_of_nonneg_left hθ (by positivity)
  refine ⟨f.depth (gl f s'), v, (f.node (gl f s') i).1, ?_, ?_, hRinv'.trans hv1, by linarith, ?_, ?_⟩
  · rw [hdepth]; nlinarith [hhη, hη, (by positivity : (0 : ℝ) ≤ ((gl f s' : ℕ) : ℝ) * (U' / f.m))]
  · rw [hdepth]; linarith
  · rw [hdepth]; linarith
  rcases halt with ⟨Q, hQdeg, hQ, hQc⟩ | ⟨z, hz, hzc⟩
  · left
    have hQ' : ∀ e, |Q.coeff e| ≤ D.N k ^ C := by
      intro e
      have hFb := hFk s' hs1 (by linarith) f hfr i
      have hbase : 1 ≤ (1 + ∑ e ∈ ((f.level (gl f s')).F i).support, |((f.level (gl f s')).F i).coeff e|) +
          ∑ e ∈ (X 3 : MvPolynomial (Fin 4) ℝ).support, |(X 3 : MvPolynomial (Fin 4) ℝ).coeff e| := by
        have h1 : 0 ≤ ∑ e ∈ ((f.level (gl f s')).F i).support, |((f.level (gl f s')).F i).coeff e| :=
          Finset.sum_nonneg (fun _ _ => abs_nonneg _)
        have h2 : 0 ≤ ∑ e ∈ (X 3 : MvPolynomial (Fin 4) ℝ).support,
            |(X 3 : MvPolynomial (Fin 4) ℝ).coeff e| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
        linarith
      calc
        |Q.coeff e| ≤ D.N k ^ R' * ((1 + ∑ e ∈ ((f.level (gl f s')).F i).support,
            |((f.level (gl f s')).F i).coeff e|) + ∑ e ∈ (X 3 : MvPolynomial (Fin 4) ℝ).support,
              |(X 3 : MvPolynomial (Fin 4) ℝ).coeff e|) ^ R' := hQ e
        _ ≤ D.N k ^ R' * (D.N k ^ c) ^ R' := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.rpow_le_rpow (by linarith) hFb hR'0.le
        _ = D.N k ^ C := by
          rw [← Real.rpow_mul hN.le, ← Real.rpow_add hN]; congr 1; ring
    have hpb := poly_pullback hg hh i (s' := s') (v := v) (ε := ε) (ε' := ε / 4) (R := R)
      (B := B) (C := C) Q hQdeg hQ' (by positivity)
      (chartSubst_power hg hs₀.le p.rate_le_one hKN) (by linarith)
      (by rw [hdepth]; linarith) (by rw [hdepth]; linarith) (by linarith) hs₀.le hHa
      (by simpa only [sub_eq_add_neg, neg_mul] using hθK (-D.d * v)) hQc
    exact hpb
  · right
    have hzR : D.N k ^ R' + 2 * D.K k ≤ D.N k ^ R := by
      have hRp : D.N k ^ (R' + 1) ≤ D.N k ^ R := Real.rpow_le_rpow_of_exponent_le hN1 hRR'
      have hsplit : D.N k ^ (R' + 1) = D.N k ^ R' * D.N k := by
        rw [Real.rpow_add hN, Real.rpow_one]
      have hNR : 1 ≤ D.N k ^ R' := Real.one_le_rpow hN1 hR'0.le
      have hstep : D.N k ^ R' * (2 * D.K k + 1) ≤ D.N k ^ R' * D.N k :=
        mul_le_mul_of_nonneg_left hKN2 (by positivity)
      have hK0 : 0 ≤ 2 * D.K k := by linarith
      have hstep2 : 2 * D.K k ≤ D.N k ^ R' * (2 * D.K k) := le_mul_of_one_le_left hK0 hNR
      calc
        D.N k ^ R' + 2 * D.K k ≤ D.N k ^ R' * (2 * D.K k + 1) := by linarith
        _ ≤ D.N k ^ R' * D.N k := hstep
        _ = D.N k ^ (R' + 1) := hsplit.symm
        _ ≤ D.N k ^ R := hRp
    have hKε : D.K k * D.N k ^ (ε / 4) ≤ D.N k ^ ε := by
      calc
        D.K k * D.N k ^ (ε / 4) ≤ D.N k ^ (ε / 8) * D.N k ^ (ε / 4) :=
          mul_le_mul_of_nonneg_right hK (by positivity)
        _ = D.N k ^ (ε / 8 + ε / 4) := by rw [Real.rpow_add hN]
        _ ≤ D.N k ^ ε := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hvp := velocity_pullback hg hh i (s' := s') (v := v) (ε := ε) (ε' := ε / 4)
      (R := R) (R' := R') z hz hzR (by rw [hdepth]; linarith) hKε
      (by simpa using hθK 0) hzc
    exact hvp

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer.Shifted
