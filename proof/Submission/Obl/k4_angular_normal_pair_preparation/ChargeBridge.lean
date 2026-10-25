import Submission.Obl.k4_angular_normal_pair_preparation.Numerics
import Submission.Obl.k4_angular_normal_pair_preparation.SourceMass
import Submission.Obl.k4_angular_normal_pair_preparation.ProblemFacts

namespace Submission.Obl.k4_angular_normal_pair_preparation

open MeasureTheory
open scoped ENNReal BigOperators

namespace NativeSample

/-- The per-source analytic bound is enough; all summation, floors and constants
are charged under the original probability laws here. -/
theorem badMass_le_of_source_bounds
    {aligned : Prop} {lam Nk : ℝ} {Wk : ℕ}
    {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure (ℕ × (Fin 6 → ℝ))}
    {Ek : Fin Wk → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {Pk : Fin Wk → MvPolynomial (Fin 4) ℝ} {Bk : Fin Wk → ℝ} {f : ℝ → ℝ}
    {gk : Fin Wk → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {Gk : Fin Wk → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}
    {L S A R e h : ℝ} {M D : ℕ} {depths : Finset ℝ} {ε : ℝ}
    (q : NativeSample aligned lam Nk Wk ωk νk Ek Pk Bk f gk Gk L S (A * e) e (R * e)
      h M D depths ε)
    (hf : SampleFacts Wk ωk νk Ek Bk)
    (hN : 1 ≤ Nk) (hA : 0 ≤ A) (he : 0 ≤ e) (hε : ε ≤ e)
    (hlarge : (2 : ℝ) ^ (32 : ℕ) ≤ Nk ^ e) (hR : 3 * A + 20 ≤ S * R)
    (hpair : ∀ b, ((νk (q.γ b)).prod (volume.prod volume)) (q.badRow (R * e) b) ≤
      ENNReal.ofReal (1 / (2 : ℝ) ^ (q.T + q.s)) *
        ENNReal.ofReal (Nk ^ (-f L - S * (R * e) + A * e) *
          ((1 / (2 : ℝ) ^ q.T) *
            (nativeGeometryLoss q.κ ((2 : ℝ) ^ q.s) (Nk ^ (2 * A * e)) * |(q.Q b).det|)))) :
    q.badMass (R * e) ≤ ENNReal.ofReal (4 * q.κ⁻¹) := by
  classical
  letI := hf.prior_prob
  have hκpow : q.κ ≤ Nk ^ e := q.κ_le.trans
    (Real.rpow_le_rpow_of_exponent_le hN hε)
  have hfloor b := (q.charts b).2.2.2.2.2.2.2.2.2.2.2.1
  have hb := native_exception_budget
    (fun b => ENNReal.ofReal (ωk (q.γ b)))
    (fun b => ((νk (q.γ b)).prod volume) (q.F b))
    (fun b => ((νk (q.γ b)).prod (volume.prod volume)) (q.badRow (R * e) b))
    (fun b => |(q.Q b).det|)
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ (q.T + q.s))
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ q.T) hN hA he hlarge
    (zero_lt_one.trans_le q.κ_one) (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ q.s)
    hκpow q.scale_hi hR (fun b => abs_nonneg _) hfloor hpair
    (q.source_mass_budget hf.weight_nonneg hf.weight_sum hf.event_time)
  convert hb using 1
  unfold badMass
  apply Finset.sum_congr rfl
  intro b _
  rw [ENNReal.ofReal_mul (hf.weight_nonneg _)]

end NativeSample
end Submission.Obl.k4_angular_normal_pair_preparation
