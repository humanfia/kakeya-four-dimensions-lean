/- Adapted from this LOT tree, o151, session x0508, commit 274d45f,
   Submission/Obl/k4_known_atlas_normalization_composition/FiniteLifting.lean. Earlier provenance comments are retained. -/
import Submission.Obl.k4_native_finite_terminal_atlas_lift.FiniteTrueLift
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.Asymptotic

namespace Submission.Obl.k4_native_finite_terminal_atlas_lift

open Filter

namespace Remainder

variable {p q : Data} {r h w : ℝ} (rem : Remainder p q r h w)

theorem liftAtlas_slack_original {k : ℕ} {a : Atlas q k} (hκ : 1 ≤ a.κ) :
    1 ≤ (rem.liftAtlas k a).κ ∧ p.K (rem.φ k) ≤ (rem.liftAtlas k a).κ := by
  refine ⟨hκ.trans (rem.liftAtlas_slack_large hκ).2, (rem.old_slack k).trans ?_⟩
  have hκp : 0 ≤ (rem.parent k).κ := le_trans zero_le_one (rem.slack_one k)
  have hm := mul_le_mul_of_nonneg_left hκ hκp
  change (rem.parent k).κ ≤ 2 * (rem.parent k).κ * a.κ
  simp only [mul_one] at hm
  nlinarith

theorem liftAtlas_slack_bound {k : ℕ} {a : Atlas q k} {ε : ℝ} (hε : 0 < ε)
    (hκ : 1 ≤ a.κ) (hN : 1 ≤ p.N (rem.φ k))
    (he : rem.error k ≤ ε / 4) (hc : 2 ≤ p.N (rem.φ k) ^ (ε / 4))
    (ha : a.κ ≤ q.N k ^ (ε / 4)) : (rem.liftAtlas k a).κ ≤ p.N (rem.φ k) ^ ε := by
  rw [rem.same_base k] at ha
  have hN0 : 0 < p.N (rem.φ k) := lt_of_lt_of_le zero_lt_one hN
  have hprod : (rem.parent k).κ * a.κ ≤
      p.N (rem.φ k) ^ rem.error k * p.N (rem.φ k) ^ (ε / 4) :=
    mul_le_mul (rem.slack_bound k) ha (le_trans zero_le_one hκ) (by positivity)
  calc
    (rem.liftAtlas k a).κ = 2 * ((rem.parent k).κ * a.κ) := by dsimp [liftAtlas]; ring
    _ ≤ 2 * (p.N (rem.φ k) ^ rem.error k * p.N (rem.φ k) ^ (ε / 4)) := by gcongr
    _ ≤ p.N (rem.φ k) ^ (ε / 4) *
        (p.N (rem.φ k) ^ rem.error k * p.N (rem.φ k) ^ (ε / 4)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = p.N (rem.φ k) ^ (ε / 4 + rem.error k + ε / 4) := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)

/-- The concrete affine pullback gives the simultaneous finite lifting
certificate at every positive output tolerance. -/
theorem sampleTransfer (hp : p.Valid) (hr : 0 ≤ r) (hrL : r < p.L) :
    SampleTransfer p q rem.φ h w := by
  intro M D
  refine ⟨rem.liftingExponent M, max rem.D D, fun ε hε => ?_⟩
  have he4 : 0 < ε / 4 := by positivity
  refine ⟨ε / 4, he4, ?_⟩
  have hNt : Tendsto (fun k => p.N (rem.φ k)) atTop atTop :=
    hp.2.1.comp rem.increasing.tendsto_atTop
  have hc : ∀ᶠ k in atTop, 2 ≤ p.N (rem.φ k) ^ (ε / 4) :=
    Submission.Obl.k4_scalar_terminal_chart_packet_extraction.eventually_const_le_rpow hNt 2 he4
  have he : ∀ᶠ k in atTop, rem.error k < ε / 4 :=
    rem.error_limit.eventually (eventually_lt_nhds he4)
  filter_upwards [hc, he] with k hconst herror
  have hN2 : 2 ≤ p.N (rem.φ k) := hp.1 _
  have hN1 : 1 ≤ p.N (rem.φ k) := le_trans (by norm_num) hN2
  have hN0 : 0 < p.N (rem.φ k) := lt_of_lt_of_le zero_lt_one hN1
  constructor
  · intro h' ht
    obtain ⟨a, hκ, hK, hslack, htime, htrue⟩ := ht
    have hold := rem.liftAtlas_trueAt hp hr hrL htrue hκ
    have hslacks := rem.liftAtlas_slack_original hκ
    refine ⟨rem.liftAtlas k a, hslacks.1, hslacks.2,
      rem.liftAtlas_slack_bound hε hκ hN1 herror.le hconst hslack, ?_, hold⟩
    rw [rem.same_base k] at htime
    change (2 : ℝ) ^ ((rem.parent k).T + a.T) ≤ _
    rw [pow_add]
    calc
      _ ≤ p.N (rem.φ k) ^ (h + rem.error k) * p.N (rem.φ k) ^ h' :=
        mul_le_mul (rem.time_bound k) htime (by positivity) (by positivity)
      _ = p.N (rem.φ k) ^ (h + h' + rem.error k) := by
        rw [← Real.rpow_add hN0]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  · intro h' w' ht
    obtain ⟨a, hκ, hK, hslack, htime, hwidth, htrue⟩ := ht
    have hold := rem.liftAtlas_trueAt hp hr hrL htrue hκ
    have hslacks := rem.liftAtlas_slack_original hκ
    refine ⟨rem.liftAtlas k a, hslacks.1, hslacks.2,
      rem.liftAtlas_slack_bound hε hκ hN1 herror.le hconst hslack, ?_, ?_, hold⟩
    · rw [rem.same_base k] at htime
      change (2 : ℝ) ^ ((rem.parent k).T + a.T) ≤ _
      rw [pow_add]
      calc
        _ ≤ p.N (rem.φ k) ^ (h + rem.error k) * p.N (rem.φ k) ^ (h' + ε / 4) :=
          mul_le_mul (rem.time_bound k) htime (by positivity) (by positivity)
        _ = p.N (rem.φ k) ^ (h + h' + (rem.error k + ε / 4)) := by
          rw [← Real.rpow_add hN0]
          congr 1
          ring
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    · intro b
      have hwchild := hwidth b
      rw [rem.same_base k] at hwchild
      have hwmul := determinant_time_mul_bound hN0
        (rem.width_bound k (rem.parentIndex k (a.γ b))) hwchild
      apply hwmul.trans
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)

end Remainder

/-- The finite lifting child follows from the explicit coefficient, interval,
frame, assignment, native test and original-prior transport constructions. -/
theorem finiteLifting : FiniteLifting := by
  intro p q r h w hp hr hrL rem
  exact ⟨rem.φ, rem.increasing.tendsto_atTop, rem.sampleTransfer hp hr hrL⟩

end Submission.Obl.k4_native_finite_terminal_atlas_lift
