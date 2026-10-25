/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/NormalizedProfileZero.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ChosenNormalization
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ProfileZero
import Submission.Obl.k4_scalar_normalized_exact_refinement.Asymptotics

/-! Full-prior saturation gives a nonnegative absolute depth-zero profile
after normalization. The upper density-transfer and exceptional-set
estimates are the accepted o166 estimates, on the identical witness data. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_normalized_exact_refinement

noncomputable section

namespace RefinementWitness

def analysisData {p q : Code} {r b h : ℝ} (w : RefinementWitness p q r b h) :
    Analysis.RefData p q r b h :=
  ⟨w.sample, w.loss, w.exponent, w.T, w.world, w.block, w.assignment, w.selected,
    w.center, w.speed, w.width, w.polynomial, w.lists, w.trajectory,
    w.sample_strictMono, w.loss_pos, w.loss_tendsto, w.exponent_one,
    (fun k => (w.charts k).1), (fun k => (w.charts k).2),
    (fun k i => (w.maps k i).1), (fun k i => (w.maps k i).2.1),
    (fun k i => (w.maps k i).2.2.1), (fun k i => (w.maps k i).2.2.2.1),
    (fun k i => (w.maps k i).2.2.2.2.1), (fun k i => (w.maps k i).2.2.2.2.2),
    (fun k => (w.weights k).1), (fun k i => (w.weights k).2 i)⟩

theorem lam_le_of_saturated {p q : Code} {r b h : ℝ} (w : RefinementWitness p q r b h)
    (hp : Exact p) (σ : ℕ → ℝ) (hsat : w.toRefinementData.Saturated r σ)
    (k : ℕ) (i : Fin (W q k)) :
    w.analysisData.lam k i ≤ N q k ^ (f p r + σ k) := by
  rw [(w.charts k).1]
  change w.width k i / (ν p (w.sample k) (w.world k i) (w.assignment k i)).toReal ≤ _
  have hN : 0 < N p (w.sample k) := by linarith [hp.1.1 (w.sample k)]
  have hν : 0 < (ν p (w.sample k) (w.world k i) (w.assignment k i)).toReal :=
    ENNReal.toReal_pos (w.assignment_mass_pos k i).ne' (w.assignment_mass_ne_top hp k i)
  have hfloor : N p (w.sample k) ^ (-f p r - σ k) * w.width k i ≤
      (ν p (w.sample k) (w.world k i) (w.assignment k i)).toReal := by
    simpa only [ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg hN.le _)
      (w.width_pos k i).le)] using
        ENNReal.toReal_mono (w.assignment_mass_ne_top hp k i) (hsat k i)
  apply (div_le_iff₀ hν).mpr
  calc
    _ = N p (w.sample k) ^ (f p r + σ k) *
        (N p (w.sample k) ^ (-f p r - σ k) * w.width k i) := by
      rw [← mul_assoc, ← Real.rpow_add hN,
        show f p r + σ k + (-f p r - σ k) = 0 by ring, Real.rpow_zero, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hfloor (Real.rpow_nonneg hN.le _)

def upperException {p q : Code} {r b h : ℝ} (w : RefinementWitness p q r b h)
    (s τ : ℝ) (k : ℕ) (i : Fin (W q k)) : Set ((ℕ × ScalarCoeff) × ℝ) :=
  {z | ENNReal.ofReal (w.analysisData.lam k i) *
    (4 * ENNReal.ofReal (N p (w.sample k) ^ (-f p (r + s) + τ))) <
      g q k i s (Analysis.obs (N q k) s z)}

/-- Accepted pure upper-tail transfer, with the original normalizer's
vanishing loss, on the same supplied atlas. -/
theorem upperException_powerSmall {p q : Code} {r b h : ℝ}
    (w : RefinementWitness p q r b h) (hp : Exact p) (hq : Exact q)
    (hLq : L q = L p - r) (hr : 0 ≤ r) {s : ℝ} (hs : 0 ≤ s) (hsL : s ≤ L q)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      (∑ i, ENNReal.ofReal (ω q k i) * mu q k i (w.upperException s τ k i)) ≤
        ENNReal.ofReal (N q k ^ (-c)) := by
  let R := w.analysisData
  have hps : 0 ≤ r + s := add_nonneg hr hs
  have hpsL : r + s ≤ L p := by linarith [hLq]
  obtain ⟨c, hc, htail⟩ := hp.2.2.2.2.2.1 (r + s) τ hps hpsL hτ
  refine ⟨c / 2, by positivity, ?_⟩
  apply Analysis.powerSmall_of_factor hq.1.2.1 (fun k => by linarith [hq.1.1 k])
    w.loss_tendsto 8 (by norm_num) hc
  filter_upwards [R.along htail] with k hk
  have hbound := R.weighted_upper (specExact_of_exact hp) (specExact_of_exact hq).2.1
    hLq hr k s hs hsL (ENNReal.ofReal (N p (w.sample k) ^ (-f p (r + s) + τ)))
  apply hbound.trans
  apply mul_le_mul' (R.Z_inv_le (specExact_of_exact hp).1 k) (mul_le_mul' le_rfl ?_)
  apply le_trans _ hk
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul' le_rfl (measure_mono fun _ hz => Or.inr hz)

/-- A vanishing full-prior saturation loss forces the absolute normalized
profile at depth zero to be nonnegative. Relative-profile bounds may then
be used as absolute upper-density exponents in the tangent preparation. -/
theorem profile_zero_nonneg_of_saturation {p q : Code} {r b h : ℝ}
    (w : RefinementWitness p q r b h) (hp : Exact p) (hq : Exact q)
    (hLq : L q = L p - r) (hr : 0 ≤ r) (σ : ℕ → ℝ)
    (hσ : Tendsto σ atTop (nhds 0)) (hsat : w.toRefinementData.Saturated r σ) :
    0 ≤ f q 0 := by
  by_contra hnot
  have hneg : f q 0 < 0 := lt_of_not_ge hnot
  let τ : ℝ := -f q 0 / 8
  have hτ : 0 < τ := by dsimp [τ]; linarith
  have hL : 0 ≤ L q := (hq.1.2.2.2.2.2.1).le
  let X0 : (k : ℕ) → Fin (W q k) → Set ((ℕ × ScalarCoeff) × ℝ) := fun k i =>
    {z | g q k i 0 (Analysis.obs (N q k) 0 z) < ENNReal.ofReal (N q k ^ (-f q 0 - τ)) ∨
      ENNReal.ofReal (N q k ^ (-f q 0 + τ)) < g q k i 0 (Analysis.obs (N q k) 0 z)}
  let X1 := w.upperException 0 τ
  have hsmall0 : ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      ∑ i, ENNReal.ofReal (ω q k i) * mu q k i (X0 k i) ≤
        ENNReal.ofReal (N q k ^ (-c)) := hq.2.2.2.2.2.1 0 τ le_rfl hL hτ
  have hsmall1 := w.upperException_powerSmall hp hq hLq hr le_rfl hL τ hτ
  let X := ![X0, X1]
  have hsmall : ∀ j : Fin 2, ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      ∑ i, ENNReal.ofReal (ω q k i) * mu q k i (X j k i) ≤
        ENNReal.ofReal (N q k ^ (-c)) := by
    intro j
    fin_cases j
    · exact hsmall0
    · exact hsmall1
  have hgood := Analysis.exists_good_point (specExact_of_exact hq).1 X hsmall
  have hσsmall : ∀ᶠ k in atTop, σ k ≤ τ := hσ.eventually (ge_mem_nhds hτ)
  have hfour : ∀ᶠ k in atTop, (4 : ℝ) ≤ N q k ^ τ :=
    ((tendsto_rpow_atTop hτ).comp hq.1.2.1).eventually (eventually_ge_atTop 4)
  obtain ⟨k, hpoint, hσk, hfourk⟩ := (hgood.and (hσsmall.and hfour)).exists
  obtain ⟨i, z, hz⟩ := hpoint
  have hz0 : z ∉ X0 k i := hz 0
  have hz1 : z ∉ X1 k i := hz 1
  have hlow : ENNReal.ofReal (N q k ^ (-f q 0 - τ)) ≤
      g q k i 0 (Analysis.obs (N q k) 0 z) :=
    not_lt.mp fun hbad => hz0 (Or.inl hbad)
  have hupp : g q k i 0 (Analysis.obs (N q k) 0 z) ≤
      ENNReal.ofReal (w.analysisData.lam k i) *
        (4 * ENNReal.ofReal (N p (w.sample k) ^ (-f p r + τ))) := by
    change ¬ ENNReal.ofReal (w.analysisData.lam k i) *
      (4 * ENNReal.ofReal (N p (w.sample k) ^ (-f p (r + 0) + τ))) <
        g q k i 0 (Analysis.obs (N q k) 0 z) at hz1
    simpa only [add_zero] using not_lt.mp hz1
  have hN : 0 < N q k := by linarith [hq.1.1 k]
  have hN1 : 1 ≤ N q k := by linarith [hq.1.1 k]
  have hlam0 : 0 ≤ w.analysisData.lam k i := by
    change 0 ≤ w.width k i / _
    exact div_nonneg (w.width_pos k i).le ENNReal.toReal_nonneg
  have hpower : w.analysisData.lam k i *
      (4 * N p (w.sample k) ^ (-f p r + τ)) ≤ N q k ^ (3 * τ) := by
    rw [← (w.charts k).1]
    have hcomb : N q k ^ (f p r + σ k) * N q k ^ (-f p r + τ) = N q k ^ (σ k + τ) := by
      rw [← Real.rpow_add hN]
      congr 1
      ring
    calc
      _ ≤ N q k ^ (f p r + σ k) * (4 * N q k ^ (-f p r + τ)) :=
        mul_le_mul_of_nonneg_right (w.lam_le_of_saturated hp σ hsat k i) (by positivity)
      _ = 4 * (N q k ^ (f p r + σ k) * N q k ^ (-f p r + τ)) := by ring
      _ = 4 * N q k ^ (σ k + τ) := by rw [hcomb]
      _ ≤ N q k ^ τ * N q k ^ (σ k + τ) :=
        mul_le_mul_of_nonneg_right hfourk (Real.rpow_nonneg hN.le _)
      _ = N q k ^ (σ k + 2 * τ) := by rw [← Real.rpow_add hN]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [hσk])
  have hthreshold : ENNReal.ofReal (w.analysisData.lam k i) *
      (4 * ENNReal.ofReal (N p (w.sample k) ^ (-f p r + τ))) ≤
        ENNReal.ofReal (N q k ^ (3 * τ)) := by
    rw [show (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ← ENNReal.ofReal_mul hlam0]
    exact ENNReal.ofReal_le_ofReal hpower
  have hstrict : ENNReal.ofReal (N q k ^ (3 * τ)) <
      ENNReal.ofReal (N q k ^ (-f q 0 - τ)) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hN _)).mpr
    apply Real.rpow_lt_rpow_of_exponent_lt (by linarith [hq.1.1 k])
    dsimp [τ]
    linarith
  exact (not_lt_of_ge (hlow.trans (hupp.trans hthreshold))) hstrict

/-- Precisely the true-normalized case has absolute profile zero. -/
theorem profile_zero_eq_of_saturation {p q : Code} {r b h : ℝ}
    (w : RefinementWitness p q r b h) (hp : Exact p) (hq : Exact q)
    (hLq : L q = L p - r) (hr : 0 ≤ r) (σ : ℕ → ℝ)
    (hσ : Tendsto σ atTop (nhds 0)) (hsat : w.toRefinementData.Saturated r σ) :
    f q 0 = 0 :=
  le_antisymm (exact_profile_zero_le hq)
    (w.profile_zero_nonneg_of_saturation hp hq hLq hr σ hσ hsat)

end RefinementWitness

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
