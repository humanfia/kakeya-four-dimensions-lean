import Submission.Obl.k4_scalar_true_atlas_terminal_lists.UniformCutFormat
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.InstallFinite
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.CrowdingTail
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.RecoveryParameters

/-! Terminal observation lists for raw true scalar atlases, with one fixed
complexity exponent before the requested tolerance is chosen. -/

namespace Submission.Obl.k4_scalar_true_atlas_terminal_lists

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

/-- Install terminal observation lists without changing the time exponent. -/
theorem terminal_recovery :
    ∀ p : Data, Exact p → ∀ B : ℕ, 1 ≤ B →
      ∃ B' : ℕ, 1 ≤ B' ∧ ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ δ ≤ 1 ∧
          ∀ᶠ k in atTop, ∀ h : ℝ,
            RawChart p B (L p) (L p) h δ true k →
              Chart p B' (L p) (L p) h ε true k := by
  intro p hp B hB1
  refine ⟨listComplexity p B, listComplexity_pos p B, ?_⟩
  intro ε hε
  let τ := ε / 100
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτε : τ ≤ ε := by dsimp [τ]; linarith
  obtain ⟨c, hc, hband⟩ := hp.2.2.2.2.2.1 (L p) τ hp.length_pos.le le_rfl hτ
  obtain ⟨δ, hδ, hδε, hδ1, hδτ, hparams⟩ :=
    recovery_parameters (N p) hp.resolution_ge hp.resolution_tendsto hε hc
  refine ⟨δ, hδ, hδε, hδ1, ?_⟩
  filter_upwards [hband, hparams] with k hbandk hparamk
  intro h hraw
  obtain ⟨T, n, γ, j, A, C, u, v, J, P, hd⟩ := hraw
  have hN : 1 ≤ N p k := le_trans (by norm_num) (hp.resolution_ge k)
  have hN0 : 0 < N p k := zero_lt_one.trans_le hN
  let Λ := N p k ^ τ
  let R := N p k ^ (ε / 2)
  let X := chartCrossings p k (L p) τ T j u v J P
  let G : Fin (worlds p k) → Set Incidence :=
    fun a => {q | ((labelsAt γ X a (observation p k (L p) q)).card : ℝ) ≤ R}
  have hX : ∀ i, MeasurableSet (X i) := chartCrossings_measurable p k (L p) τ T j u v J P
  have hG : ∀ a, MeasurableSet (G a) := fun a =>
    measurableSet_le ((labelsAt_card_real_measurable γ X hX a).comp
      (observation_measurable p k (L p))) measurable_const
  have hR : 0 < R := Real.rpow_pos_of_pos hN0 _
  have hcommon := hd.mono hN le_rfl le_rfl hδτ
  have hcross : ∀ i q, q ∈ C i → observation p k (L p) q ∈ X i := by
    intro i q hq
    have ha := (hcommon.2.2.2.2.1 i hq).2.1
    have ht := (hcommon.2.2.2.2.1 i hq).2.2
    have hfit := (hcommon.2.2.2.2.2.1 i).2.2.2.2.2.2.2.2.2.2.1 q.1 ha q.2 ht
    exact fitting_incidence_crosses p k T (L p) Λ (j i) (u i) (v i) (J i) (P i)
      q.1 q.2 hN0 ht hfit.1 hfit.2
  have hformat : ∀ i z, Format 6 (N p k ^ (listComplexity p B : ℝ)) (listComplexity p B)
      {w | ((z, fun e : Fin 5 => w e.castSucc), w 5) ∈ C i ∩ G (γ i)} := by
    intro i z
    have hf := hd.cutoff_format hp hδ1 (Λ := Λ) (R := R) i z
    dsimp only [G, X]
    rw [show chartCrossings p k (L p) τ T j u v J P =
      (fun i => crossing (N p k ^ (-L p)) Λ ((j i : ℕ) / (2 : ℝ) ^ T)
        (1 / (2 : ℝ) ^ T) (u i) (v i) (J i) (P i)) from rfl]
    simpa only [mem_inter_iff, mem_ofPred_eq] using hf
  have hhigh : (∑ a, ENNReal.ofReal (weight p k a) * mu p k a
      {q | ENNReal.ofReal (N p k ^ (-profile p (L p)) * N p k ^ τ) <
        density p k a (L p) (observation p k (L p) q)}) ≤ ENNReal.ofReal (N p k ^ (-c)) := by
    apply le_trans _ hbandk
    apply Finset.sum_le_sum
    intro a _
    apply mul_le_mul_of_nonneg_left _ zero_le
    apply measure_mono
    intro q hq
    right
    change ENNReal.ofReal (N p k ^ (-profile p (L p)) * N p k ^ τ) <
      density p k a (L p) (![q.2, y q.1 q.2], ⌊x q.1 q.2 / (N p k ^ (-L p))⌋) at hq
    simpa only [Real.rpow_add hN0] using hq
  have htail := hd.crowding_tail hp hδτ hp.length_pos.le le_rfl hR
  have hΛ : 1 ≤ Λ := Real.one_le_rpow hN hτ.le
  have hH : 2 * Λ ^ 3 * (2 * Λ + 3) ≤ 10 * Λ ^ 4 := by
    have hh : Λ ^ 3 ≤ Λ ^ 4 := by nlinarith [mul_le_mul_of_nonneg_left hΛ (by positivity : 0 ≤ Λ ^ 3)]
    nlinarith
  have hpow4 : Λ ^ 4 = N p k ^ (4 * τ) := by
    dsimp [Λ]
    rw [show 4 * τ = τ * (4 : ℝ) by ring, Real.rpow_mul hN0.le]
    norm_num
  have hslack : (2 * Λ ^ 3 * (2 * Λ + 3)) / R ≤
      10 * N p k ^ (4 * τ - ε / 2) := by
    calc
      _ ≤ 10 * Λ ^ 4 / R := div_le_div_of_nonneg_right hH hR.le
      _ = 10 * (N p k ^ (4 * τ) / N p k ^ (ε / 2)) := by rw [hpow4]; dsimp [R]; ring
      _ = _ := by rw [Real.rpow_sub hN0]
  have hbad : (∑ a, ENNReal.ofReal (weight p k a) * mu p k a (G a)ᶜ) ≤
      ENNReal.ofReal (N p k ^ (-c) + 10 * N p k ^ (4 * τ - ε / 2)) := by
    have hbadset (a : Fin (worlds p k)) : (G a)ᶜ =
        {q | R < ((labelsAt γ X a (observation p k (L p) q)).card : ℝ)} := by
      ext q
      simp only [G, mem_compl_iff, mem_ofPred_eq, not_le]
    simp only [hbadset]
    apply le_trans htail
    calc
      _ ≤ ENNReal.ofReal (N p k ^ (-c)) +
          ENNReal.ofReal (10 * N p k ^ (4 * τ - ε / 2)) :=
        add_le_add hhigh (ENNReal.ofReal_le_ofReal hslack)
      _ = _ := (ENNReal.ofReal_add (Real.rpow_pos_of_pos hN0 _).le (by positivity)).symm
  have hbudget : ENNReal.ofReal (N p k ^ (-ε)) +
      3 * (∑ a, ENNReal.ofReal (weight p k a) * mu p k a (G a)ᶜ) ≤
      ∑ a, ENNReal.ofReal (weight p k a) * mu p k a {q | ∃ i, γ i = a ∧ q ∈ C i} := by
    calc
      _ ≤ ENNReal.ofReal (N p k ^ (-ε)) +
          3 * ENNReal.ofReal (N p k ^ (-c) + 10 * N p k ^ (4 * τ - ε / 2)) := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hbad zero_le)
      _ = ENNReal.ofReal (N p k ^ (-ε) +
          3 * (N p k ^ (-c) + 10 * N p k ^ (4 * τ - ε / 2))) := by
        rw [← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (Real.rpow_pos_of_pos hN0 _).le (by positivity)]
      _ ≤ ENNReal.ofReal (N p k ^ (-δ)) := ENNReal.ofReal_le_ofReal hparamk.2
      _ ≤ _ := hd.2.2.2.2.2.2
  apply install_finite_lists hp hcommon (listComplexity_ge p B) hτε hparamk.1 hR.le
    (Real.rpow_le_rpow_of_exponent_le hN (by linarith : ε / 2 ≤ ε)) X hX G hG hcross
    (fun a q hq => hq) hformat hbudget

end Submission.Obl.k4_scalar_true_atlas_terminal_lists
