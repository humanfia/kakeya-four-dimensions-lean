import Submission.Obl.k4_scalar_candidate_original_return.EncodingStage
import Submission.Obl.k4_scalar_candidate_original_return.EncodingScales
import Submission.Obl.k4_scalar_candidate_original_return.GeometryBudget
import Submission.Obl.k4_scalar_candidate_original_return.OriginalMass

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- Measurable analytical lists on the original terminal observation give the
actual original charts and the separate polynomial and path-slack budgets. -/
theorem original_encoding : Encoding := by
  classical
  intro a ha R gain C p hR hgain hC hlisted
  have hcore := ha
  obtain ⟨hex, hb, hNt, hK, hH, hκ, hrange, hρ, hcharts, hblocks⟩ := ha
  let J := Nat.ceil R
  let C₀ : ℝ := 72 * (J : ℝ) + 500
  let C' := max (4 * C ^ 2) C₀
  let p' := 2 * p + 1
  let R' := R + gain + 2
  have hC0 : 0 < C := by linarith
  have hC' : 1 ≤ C' := by
    apply le_trans _ (le_max_left _ _)
    nlinarith only [hC]
  have hC'0 : 0 < C' := lt_of_lt_of_le zero_lt_one hC'
  have hR' : 1 < R' := by dsimp [R']; linarith
  have hδ : 0 < a.κ * gain / 2 := by positivity
  refine ⟨R', a.κ * gain / 2, C', 1, p', hR', hδ, ?_⟩
  have hev := (hK (a.κ * gain / 4) (by positivity)).and
    ((hblocks R hR).and ((hcore.original_error_le_floor hC0 p).and (hcore.recovery_budget hC'0 p')))
  apply (hlisted.and_eventually hev).mono
  rintro k ⟨hl, hKk, htime, herror, hbudget⟩
  rcases hl with ⟨s, hs0, hs1, m, P, e, n, parent, bin, Q, lists,
    hm, hn, he0, heR, hparent, hP, hQ, hfit, hlist, hlistmeas, hmass⟩
  let q := a.ls k (a.nd k s)
  let A := mergedFitAssignment q e m P bin
  let B := a.rM k + 2 * J + 10
  let V := C * a.H k ^ p
  let ε := recoveryExponent a C' p' k
  have hN : 1 ≤ a.original k := by linarith [hcore.original_ge_two k]
  have hN0 := hcore.original_pos k
  have htpos : 0 < a.tangent k := Real.rpow_pos_of_pos hN0 _
  have hH1 : 1 ≤ a.H k := by linarith [(hb k).2.2.1]
  have hV : 1 ≤ V := by
    have hpow : 1 ≤ a.H k ^ p := one_le_pow₀ hH1
    calc
      (1 : ℝ) ≤ C := hC
      _ ≤ V := by simpa only [V, mul_one] using mul_le_mul_of_nonneg_left hpow hC0.le
  have hR0 : 0 ≤ R := by linarith
  have hRJ : R ≤ (J : ℝ) := Nat.le_ceil R
  have hRPow : a.tangent k ^ R ≤ a.original k ^ J := by
    rw [hcore.tangent_rpow]
    have hr : a.sc k * R ≤ (J : ℝ) :=
      (mul_le_of_le_one_left hR0 (hb k).2.1).trans hRJ
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hN hr
  obtain ⟨r₀, h₀, hq⟩ := hcharts k (a.nd k s)
  have hAprior : ∀ i z, Format 5 (a.original k ^ (a.rM k)) (a.rM k)
      {v | (z, v) ∈ q.prior i} := by
    intro i z
    simpa only [Real.rpow_natCast, PreparedData.original, q] using (hq.2.2.2.2.2.1 i).2.2.2.2.2.2.2.2.1 z
  have hm' : ∀ i, (m i : ℝ) ≤ a.original k ^ J := fun i => (hm i).trans hRPow
  obtain ⟨hAf, hCf⟩ := merged_geometry_format (hex k) q e m P parent bin hparent
    (fun i j => (hP i j).1) (hb k).2.2.2.2.1 (hb k).2.2.2.2.2.1 hm' hAprior
  have hAm : ∀ i, MeasurableSet (A i) := mergedFitAssignment_measurable q e m P bin
    (fun i => (hq.2.2.1 i).1)
  have hAsub : ∀ i, A i ⊆ q.prior (parent i) :=
    mergedFitAssignment_subset q e m P parent bin hparent
  have hdisj : ∀ i j, i ≠ j → parent i = parent j → Disjoint (A i) (A j) :=
    mergedFitAssignment_siblings_disjoint q e m P parent bin hparent
  let S := geometricSelected q parent A
  have hSm : ∀ i, MeasurableSet (S i) := fun i =>
    (k4_scalar_true_atlas_terminal_lists.Exact.event_measurable (hex k) _ _).inter
      ((hAm i).prod measurableSet_Icc)
  have hSsub : ∀ i, S i ⊆ E (a.p k) (a.sm k) (q.world (parent i)) ∩
      (A i ×ˢ I q.T (q.time (parent i))) := fun _ => subset_rfl
  have hcount : (n : ℝ) ≤ a.original k ^ B := by
    calc
      _ ≤ (q.n : ℝ) * a.tangent k ^ R := hn
      _ ≤ a.original k ^ (a.rM k) * a.original k ^ J :=
        mul_le_mul (by simpa only [Real.rpow_natCast, PreparedData.original, q] using hq.2.1)
          hRPow (Real.rpow_pos_of_pos htpos R).le (pow_nonneg hN0.le _)
      _ = a.original k ^ (a.rM k + J) := (pow_add _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ hN (by dsimp [B]; omega)
  have hQB : ∀ i, (Q i).totalDegree ≤ 2 ∧ ∀ d, |(Q i).coeff d| ≤ a.original k ^ B := by
    intro i
    refine ⟨(hQ i).1, fun d => ((hQ i).2 d).trans (hRPow.trans ?_)⟩
    exact pow_le_pow_right₀ hN (by dsimp [B]; omega)
  have hterminal : (a.original k ^ (-L (a.p k)))⁻¹ ≤ a.original k ^ B := by
    rw [Real.rpow_neg (hcore.original_pos k).le, inv_inv]
    have hL := (hb k).2.2.2.2.2.2.1
    have hMB : (a.rM k : ℝ) ≤ (B : ℝ) := by exact_mod_cast (show a.rM k ≤ B by dsimp [B]; omega)
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le hN (hL.trans hMB)
  have hfit' : ∀ i l, l ∈ A i → ∀ t ∈ I q.T (q.time (parent i)),
      |x l t - MvPolynomial.eval ![t, y l t] (Q i)| ≤ a.original k ^ (-(a.sc k * (s + gain))) := by
    intro i l hl t ht
    have hh := hfit i l hl t ht
    change |x l t - MvPolynomial.eval ![t, y l t] (Q i)| ≤ a.tangent k ^ (-s - gain) at hh
    rw [hcore.tangent_rpow, show a.sc k * (-s - gain) = -(a.sc k * (s + gain)) by ring] at hh
    exact hh
  have htime' : (2 : ℝ) ^ q.T ≤ a.original k ^ (a.sc k * (a.κ * s + a.κ * gain / 4)) := by
    calc
      _ ≤ a.rK k * a.tangent k ^ (a.κ * s) := htime s hs0 hs1
      _ ≤ a.tangent k ^ (a.κ * gain / 4) * a.tangent k ^ (a.κ * s) :=
        mul_le_mul_of_nonneg_right hKk (Real.rpow_pos_of_pos htpos _).le
      _ = a.tangent k ^ (a.κ * s + a.κ * gain / 4) := by
        rw [← Real.rpow_add htpos]
        congr 1
        ring
      _ = _ := hcore.tangent_rpow k _
  have hmass' : ENNReal.ofReal V⁻¹ ≤
      ∑ i, ENNReal.ofReal (ω (a.p k) (a.sm k) (q.world (parent i))) *
        mu (a.p k) (a.sm k) (q.world (parent i))
          {z | z ∈ S i ∧ i ∈ lists (q.world (parent i))
            (originalObservation (a.original k ^ (-L (a.p k))) z)} := by
    apply hmass.trans
    have hh := dominated_original_success (hex k) (a.sm k) (a.ρ k) (hρ k)
      (fun i => q.world (parent i))
      (fun i => {z : Inc | z.1 ∈ A i ∧ z.2 ∈ I q.T (q.time (parent i)) ∧
        i ∈ lists (q.world (parent i)) (originalObservation (a.original k ^ (-L (a.p k))) z)})
    calc
      _ ≤ ∑ g, ENNReal.ofReal (ω (a.p k) (a.sm k) g) * a.ρ k g
          {z | ∃ i, q.world (parent i) = g ∧ z.1 ∈ A i ∧
            z.2 ∈ I q.T (q.time (parent i)) ∧
            i ∈ lists (q.world (parent i))
              (originalObservation (a.original k ^ (-L (a.p k))) z)} := by
        apply Finset.sum_le_sum
        intro g _
        apply mul_le_mul_of_nonneg_left _ zero_le
        apply measure_mono
        rintro z ⟨i, hγ, hA, ht, hl⟩
        change q.world (parent i) = g at hγ
        change i ∈ lists g (originalObservation (a.original k ^ (-L (a.p k))) z) at hl
        exact ⟨i, hγ, hA, ht, by simpa only [hγ] using hl⟩
      _ ≤ _ := by
        simpa only [S, geometricSelected, Set.inter_def, mem_ofPred_eq, mem_prod, and_assoc] using hh
  have hεlist : 2 * V ≤ a.original k ^ ε := by
    rw [hcore.rpow_recoveryExponent hC'0]
    have hconst : 2 * C ≤ C' := (by nlinarith only [hC] : 2 * C ≤ 4 * C ^ 2).trans (le_max_left _ _)
    have hpower : a.H k ^ p ≤ a.H k ^ p' := pow_le_pow_right₀ hH1 (by dsimp [p']; omega)
    dsimp [V]
    simpa only [← mul_assoc] using mul_le_mul hconst hpower (by positivity) (by linarith)
  have hεmass : a.original k ^ (-ε) ≤ (4 * V ^ 2)⁻¹ := by
    rw [hcore.neg_rpow_recoveryExponent hC'0]
    have hpower : a.H k ^ (2 * p) ≤ a.H k ^ p' := pow_le_pow_right₀ hH1 (by dsimp [p']; omega)
    have hbound : 4 * V ^ 2 ≤ C' * a.H k ^ p' := by
      calc
        _ = (4 * C ^ 2) * a.H k ^ (2 * p) := by
          dsimp [V]
          rw [mul_pow, ← pow_mul]
          have hpp : p * 2 = 2 * p := by omega
          rw [hpp]
          ring
        _ ≤ _ := mul_le_mul (le_max_left _ _) hpower (by positivity) (by linarith)
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity : 0 < 4 * V ^ 2) hbound
  have hchart := encode_selected_family (hex k) q hq (show a.rM k ≤ B by dsimp [B]; omega)
    ((hb k).2.2.2.2.1.trans (by dsimp [B]; omega))
    ((hb k).2.2.2.2.2.1.trans (by dsimp [B]; omega))
    (hcore.old_slack_le_recoveryExponent hC' (show 1 ≤ p' by dsimp [p']; omega) k)
    parent A Q S hAsub hdisj hAm hSm hSsub htime' hcount hQB hAf hCf hfit'
    hterminal lists hlistmeas V hV hlist hmass'
    (by simpa only [V, PreparedData.original, ← mul_assoc] using herror) hεlist hεmass
  refine ⟨s + gain, a.κ * s + a.κ * gain / 4, 36 * B + 104, ε, ?_, ?_, ?_, ?_, hbudget, hchart⟩
  · have hRR : R ≤ R' := by dsimp [R']; linarith
    have hi : R'⁻¹ ≤ R⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (by linarith : 0 < R) hRR
    exact hi.trans (hs0.trans (by linarith))
  · dsimp [R']
    linarith
  · nlinarith only [mul_pos hκ hgain]
  · have h₁ : 36 ≤ C₀ := by dsimp [C₀]; linarith [Nat.cast_nonneg (α := ℝ) J]
    have h₂ : 72 * (J : ℝ) + 464 ≤ C₀ := by dsimp [C₀]; linarith
    have hc : C₀ ≤ C' := le_max_right _ _
    simp only [pow_one]
    calc
      ((36 * B + 104 : ℕ) : ℝ) = 36 * (a.rM k : ℝ) + (72 * (J : ℝ) + 464) := by
        dsimp [B]
        push_cast
        ring
      _ ≤ C₀ * (a.rM k : ℝ) + C₀ :=
        add_le_add (mul_le_mul_of_nonneg_right h₁ (Nat.cast_nonneg _)) h₂
      _ = C₀ * (1 + (a.rM k : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

end Submission.Obl.k4_scalar_candidate_original_return
