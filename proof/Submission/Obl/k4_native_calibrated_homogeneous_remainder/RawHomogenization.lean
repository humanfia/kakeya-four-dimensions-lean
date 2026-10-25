import Submission.Obl.k4_native_calibrated_homogeneous_remainder.CompHomog
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.IncidenceSelection
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.WorldRestriction
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.PolynomialBounds

/-! Apply accepted one-world homogenization to the raw family, before selecting
its chart parameters and world-weight class. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_dyadic_crop_worlds (PriorFormat EventFormat)

/-- Weighted joint typicality at the intrinsic dyadic phase of the encoding. -/
def WeightedJointTypical (p : Data) (R U ρ₀ : ℝ) (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ s u τ : ℝ, 0 ≤ s → s ≤ R → 0 ≤ u → u ≤ U → 0 < τ →
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      ∀ G : Fin (p.W k) → Comp.JObs → ENNReal,
        (∀ b, Measurable (G b) ∧
          Measure.map (Comp.jobs (p.B k b) (Comp.theta (p.N k) ρ₀ s) (Comp.dl (p.N k) u))
            (selected p k b) = Comp.jref.withDensity (G b)) →
        ∑ b, ENNReal.ofReal (p.ω k b) * selected p k b
          {z | ENNReal.ofReal (p.ω k b) *
              G b (Comp.jobs (p.B k b) (Comp.theta (p.N k) ρ₀ s) (Comp.dl (p.N k) u) z) <
                ENNReal.ofReal (p.N k ^ (-F (ρ₀ + s) u - τ)) ∨
            ENNReal.ofReal (p.N k ^ (-F (ρ₀ + s) u + τ)) <
              ENNReal.ofReal (p.ω k b) *
                G b (Comp.jobs (p.B k b) (Comp.theta (p.N k) ρ₀ s) (Comp.dl (p.N k) u) z)} ≤
          ENNReal.ofReal (p.N k ^ (-c))

/-- The raw family admits a further fixed-format selection with one common
weighted joint profile. Its full conditioned priors and tests are unchanged. -/
theorem RawValid.weighted_homogenization {p : Data} (hp : RawValid p)
    (R U : ℝ) (hR : 0 < R) (hU : 0 < U) :
    ∃ (ψ : ℕ → ℕ) (K' : ℕ → ℝ)
      (E' : (k : ℕ) → Fin (p.W (ψ k)) → Set Incidence) (ρ₀ : ℝ) (F : ℝ → ℝ → ℝ),
      StrictMono ψ ∧ 0 ≤ ρ₀ ∧
      RawValid (selectIncidences (p.reindex ψ) K' E') ∧
      (∀ k, p.K (ψ k) ≤ K' k) ∧ (∀ k b, E' k b ⊆ p.E (ψ k) b) ∧
      Submission.Obl.k4_joint_homogenization.ProfileRegular (ρ₀ + R) U F ∧
      WeightedJointTypical (selectIncidences (p.reindex ψ) K' E') R U ρ₀ F := by
  have hp0 := hp
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, M, D, hfmt⟩
  let M₁ := 2 * M + 1
  have hpM : ∀ k, p.N k ^ M ≤ p.N k ^ M₁ := fun k =>
    pow_le_pow_right₀ (by linarith [hN k]) (by dsimp [M₁]; omega)
  have hW : ∀ k, 0 < p.W k ∧ (p.W k : ℝ) ≤ p.N k ^ M₁ := by
    intro k
    refine ⟨?_, (hfmt k).1.trans (hpM k)⟩
    by_contra hn
    have hw : p.W k = 0 := Nat.eq_zero_of_not_pos hn
    have hz : (∑ b, p.ω k b) = 0 := by
      refine Finset.sum_eq_zero fun b _ => ?_
      have hb := b.isLt
      omega
    linarith [(hfmt k).2.2.1]
  have hν : ∀ k b, IsProbabilityMeasure (p.ν k b) ∧ PriorFormat (p.N k ^ M₁) D (p.ν k b) := by
    intro k b
    rcases (hfmt k).2.2.2.1 b with ⟨hν, -, -, -, -, -, hprior, -⟩
    exact ⟨hν, (show PriorFormat (p.N k ^ M) D (p.ν k b) from hprior).mono (hpM k)⟩
  have hE : ∀ k b, EventFormat (p.N k ^ M₁) D (p.E k b) := by
    intro k b
    rcases (hfmt k).2.2.2.1 b with ⟨-, -, -, -, -, -, -, hEm, hEt, hEb, hEf, -⟩
    exact (show EventFormat (p.N k ^ M) D (p.E k b) from ⟨hEm, hEt, hEb, hEf⟩).mono (hpM k)
  have hB : ∀ k b, 0 < p.B k b ∧ p.B k b ≤ p.N k ^ M₁ ∧ (p.B k b)⁻¹ ≤ p.N k ^ M₁ := by
    intro k b
    have hw := (hfmt k).2.2.2.1 b
    exact ⟨hw.2.1, hw.2.2.1.trans (hpM k), hw.2.2.2.1.trans (hpM k)⟩
  have hnat : ∀ k b, ∀ᵐ l ∂p.ν k b, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(WithLp.toLp 2 ![l.2 0 + t * l.2 3, l.2 1 + t * l.2 4] : EuclideanSpace ℝ (Fin 2))‖ +
        ‖(WithLp.toLp 2 ![l.2 3, l.2 4] : EuclideanSpace ℝ (Fin 2))‖ ≤ p.K k ∧
      |p.B k b * (l.2 2 + t * l.2 5)| ≤ p.N k ^ M₁ := by
    intro k b
    rcases (hfmt k).2.2.2.1 b with ⟨-, hB0, hBle, -, -, -, hprior, -, -, -, -, hnat, -⟩
    have hhidden := priorFormat_hidden_bound (hN k) hprior hB0.le hBle
    filter_upwards [hnat, hhidden] with l hl hh t ht
    exact ⟨(hl t ht).1, hh t ht⟩
  have hm : ∀ k, ENNReal.ofReal ((p.K k)⁻¹) ≤
      ∑ b, ENNReal.ofReal (p.ω k b) * ((p.ν k b).prod volume) (p.E k b) := by
    intro k
    simpa only [Measure.restrict_apply_univ] using (hfmt k).2.2.2.2
  obtain ⟨ψ, hψ, K', E', F, hK', hKK', hsub, hEfmt, hmass, hreg, htyp⟩ :=
    Comp.multiworld_homogenization p.N p.K hN hNt hK p.W p.ω p.ν p.E p.B M₁ D hW
      (fun k => (hfmt k).2.1) (fun k => (hfmt k).2.2.1) hν hE hB hnat hm R U hR hU
  refine ⟨ψ, K', E', ((2 * M₁ + 5 : ℕ) : ℝ), F, hψ, by positivity, ?_, hKK', hsub, hreg, htyp⟩
  exact (hp0.reindex hψ.tendsto_atTop).select_incidences K' E' hK' hKK' hsub hEfmt hmass

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
