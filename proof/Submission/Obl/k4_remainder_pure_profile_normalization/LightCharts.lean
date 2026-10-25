/-
Adapted from this LOT tree, o147, session x0498, commit 5dd59d875729,
Submission/Obl/k4_local_remainder_horizon_transfer/LightCharts.lean.
Earlier provenance is preserved below.
-/
import Submission.Obl.k4_remainder_pure_profile_normalization.AtlasSelection
import Submission.Obl.k4_remainder_pure_profile_normalization.SampleBridge
import Submission.Obl.k4_quadratic_atlas_normalization.MassSelection

/-! Polynomially light assignments can be removed before conditioning. -/

namespace Submission.Obl.k4_remainder_pure_profile_normalization

open MeasureTheory

/-- A selected chart event has at most the mass of its full trajectory assignment. -/
theorem Atlas.KnownAt.mass_le_prior {p : Data} {k M D : ℕ} {a : Atlas p k} {r : ℝ}
    (ha : a.KnownAt M D r)
    (htime : ∀ γ, p.E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1) (b : Fin a.C) :
    ((p.ν k (a.γ b)).prod volume) (a.F b) ≤ p.ν k (a.γ b) (a.A b) := by
  obtain ⟨_, _, _, _, hchart, _⟩ := ha
  have hsel := (hchart b).2.2.2.2.2.2.2.2.2.2.1
  have hsub : a.F b ⊆ a.A b ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro q hq
    obtain ⟨he, hA, _, _⟩ := hsel q hq
    exact ⟨hA, (htime _ he).2⟩
  calc
    _ ≤ ((p.ν k (a.γ b)).prod volume) (a.A b ×ˢ Set.Icc (0 : ℝ) 1) := measure_mono hsub
    _ = _ := by simp

/-- Removing light charts costs at most half the selected mass. All surviving
assignment priors have one fixed reciprocal-polynomial lower bound. -/
theorem Atlas.KnownAt.discard_light {p : Data} {k M D : ℕ} {a : Atlas p k} {r : ℝ}
    (ha : a.KnownAt M D r) {M₀ D₀ : ℕ}
    (hp : Normalization.SampleProblem (p.N k) (p.K k) M₀ D₀
      (p.W k) (p.ω k) (p.ν k) (p.E k) (p.P k) (p.B k))
    (hN : 2 ≤ p.N k) (hκ : 1 ≤ a.κ) (hκN : a.κ ≤ p.N k) :
    ∃ S : Finset (Fin a.C),
      ((a.select S).withSlack (2 * a.κ)).KnownAt M D r ∧
      ∀ b : Fin S.card,
        (p.N k ^ (M + 2))⁻¹ ≤
          (p.ν k (a.γ (a.selectIndex S b)) (a.A (a.selectIndex S b))).toReal := by
  classical
  letI : ∀ γ, IsProbabilityMeasure (p.ν k γ) := hp.prob
  let prior : Fin a.C → ℝ := fun b => (p.ν k (a.γ b) (a.A b)).toReal
  let cutoff : ℝ := (p.N k ^ (M + 2))⁻¹
  let S : Finset (Fin a.C) := Finset.univ.filter fun b => cutoff ≤ prior b
  let lost : ENNReal := ∑ b ∈ Finset.univ.filter (fun b : Fin a.C => ¬ cutoff ≤ prior b),
    ENNReal.ofReal (p.ω k (a.γ b)) * ((p.ν k (a.γ b)).prod volume) (a.F b)
  have hN0 : 0 < p.N k := by linarith
  have hκ0 : 0 < a.κ := by linarith
  have hcut : 0 < cutoff := by dsimp [cutoff]; positivity
  have hcard : (a.C : ℝ) ≤ p.N k ^ M := by obtain ⟨_, hc, _⟩ := ha; exact hc
  have hw1 : ∀ γ, ENNReal.ofReal (p.ω k γ) ≤ 1 := by
    intro γ
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    exact (Finset.single_le_sum (fun γ _ => hp.weight_nonneg γ) (Finset.mem_univ γ)).trans
      hp.weight_sum.le
  have hlost : lost ≤ ENNReal.ofReal ((p.N k ^ 2)⁻¹) := by
    calc
      lost ≤ ∑ b ∈ Finset.univ.filter (fun b : Fin a.C => ¬ cutoff ≤ prior b),
          ENNReal.ofReal cutoff := by
        apply Finset.sum_le_sum
        intro b hb
        have hlt : prior b < cutoff := lt_of_not_ge (Finset.mem_filter.mp hb).2
        calc ENNReal.ofReal (p.ω k (a.γ b)) * ((p.ν k (a.γ b)).prod volume) (a.F b)
            ≤ 1 * p.ν k (a.γ b) (a.A b) :=
              mul_le_mul' (hw1 _) (ha.mass_le_prior hp.event_time b)
          _ = ENNReal.ofReal (prior b) := by
            rw [one_mul, ENNReal.ofReal_toReal (measure_ne_top _ _)]
          _ ≤ ENNReal.ofReal cutoff := ENNReal.ofReal_le_ofReal hlt.le
      _ ≤ (a.C : ENNReal) * ENNReal.ofReal cutoff := by
        rw [Finset.sum_const, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (Finset.card_filter_le (s := Finset.univ) _).trans_eq (by simp)
      _ = ENNReal.ofReal ((a.C : ℝ) * cutoff) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (p.N k ^ M * cutoff) := by
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hcut.le)
      _ = ENNReal.ofReal ((p.N k ^ 2)⁻¹) := by
        congr 1
        dsimp [cutoff]
        rw [pow_add]
        field_simp
  have hsmall : lost ≤ ENNReal.ofReal (a.κ⁻¹ / 2) := by
    refine hlost.trans (ENNReal.ofReal_le_ofReal ?_)
    have hsq : 2 * a.κ ≤ p.N k ^ 2 := by nlinarith
    calc (p.N k ^ 2)⁻¹ ≤ (2 * a.κ)⁻¹ := inv_anti₀ (by positivity) hsq
      _ = a.κ⁻¹ / 2 := by simp [mul_inv_rev, div_eq_mul_inv, mul_comm]
  have hsplit : a.mass = (a.select S).mass + lost := by
    rw [a.select_mass S]
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ (fun b => cutoff ≤ prior b)
      (fun b => ENNReal.ofReal (p.ω k (a.γ b)) * ((p.ν k (a.γ b)).prod volume) (a.F b))).symm
  have hret : ENNReal.ofReal (a.κ⁻¹ / 2) ≤ (a.select S).mass := by
    apply Submission.Obl.k4_quadratic_atlas_normalization.retain_half_mass
      a.mass (a.select S).mass lost a.κ⁻¹ (by positivity)
    · obtain ⟨_, _, _, _, _, hm⟩ := ha; exact hm
    · exact hsplit.le
    · exact hsmall
  refine ⟨S, ha.select S (by linarith) hκ0 (by linarith)
    (fun γ => (hp.scale_pos γ).le) ?_, ?_⟩
  · simpa only [mul_inv_rev, div_eq_mul_inv, mul_comm] using hret
  · intro b
    exact (Finset.mem_filter.mp (S.equivFin.symm b).property).2

end Submission.Obl.k4_remainder_pure_profile_normalization
