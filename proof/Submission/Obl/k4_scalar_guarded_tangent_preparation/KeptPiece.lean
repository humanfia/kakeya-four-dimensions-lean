import Submission.Obl.k4_scalar_guarded_tangent_preparation.TangentConvert

/-!
# The tangent chart clause of one kept piece

For one piece of a true layer at original depth `sc * dp`, kept by the duration-core
pruning, the chart clause of the tangent input holds at tangent depth `s` with the slack
`K'`, given the profile bound and the node rounding.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open Submission.Obl.k4_scalar_linear_critical_extremizers
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The bounds on the tangent slack used for one kept piece. -/
structure SlackBounds (B H K' : ℝ) : Prop where
  one_le : 1 ≤ K'
  BH : B ^ 2 * H ^ 2 ≤ K'
  upper : 8 * B ^ 3 * H ^ 5 ≤ K'
  band : 4665600 * (8 * B * H ^ 5) ^ 7 ≤ K'
  HB : H * B ≤ K'
  H2 : H ^ 2 ≤ K'
  H1 : H ≤ K'

theorem kept_piece_tangent {p : Code} {m : ℕ} {σ ρ : Fin (p.1 m) → Measure Incidence}
    {Bc : ℕ} {sc dp tm b H B d s K' : ℝ} {f : Layer (p.1 m)}
    (hCD : Split.ChartData p Bc (sc * dp) b (sc * tm) (Real.log H / Real.log (p.N m)) true m
      f.T f.n f.world f.block f.assignment f.witness f.u f.v f.width f.graph f.list)
    (hN₀ : 1 < p.N m) (hsc : 0 < sc) (hdp : 0 ≤ dp) (hH2 : 2 ≤ H) (hB1 : 1 ≤ B)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hJ : ∀ i, (H * (2 : ℝ) ^ f.T)⁻¹ ≤ f.width i)
    (hceil : ∀ g, (σ g).map (pureObservation (p.N m) (sc * dp)) ≤
      ENNReal.ofReal (B * p.N m ^ (-p.profile (sc * dp))) • (volume.prod Measure.count))
    (hρσ : ∀ g, ρ g ≤ σ g)
    (hprof : p.N m ^ |p.profile (sc * dp) - d * (sc * dp)| ≤ B)
    (hround : (p.N m ^ sc) ^ |dp - s| ≤ B)
    (hK : SlackBounds B H K') (i : Fin f.n)
    (hcost : p.prior m (f.world i) (f.assignment i) *
        ENNReal.ofReal ((H ^ 2 * (2 : ℝ) ^ f.T)⁻¹) ≤
      ρ (f.world i) (f.assignment i ×ˢ Split.I f.T (f.block i))) :
    ENNReal.ofReal ((p.N m ^ sc) ^ (-d * s) / (K' * (2 : ℝ) ^ f.T)) ≤
        p.prior m (f.world i) (f.assignment i) ∧
      p.prior m (f.world i) (f.assignment i) ≤
        ENNReal.ofReal (K' * (p.N m ^ sc) ^ (-d * s) / (2 : ℝ) ^ f.T) ∧
      ENNReal.ofReal ((K' * (2 : ℝ) ^ f.T)⁻¹) * p.prior m (f.world i) (f.assignment i) ≤
        ρ (f.world i) (f.assignment i ×ˢ Split.I f.T (f.block i)) ∧
      |f.u i| + |f.v i| ≤ K' ∧ (f.graph i).totalDegree ≤ 2 ∧
      (∀ t ∈ Split.I f.T (f.block i), ∀ w ∈ Set.Icc (-2 : ℝ) 2,
        |MvPolynomial.eval ![t, f.u i + t * f.v i + w / (2 : ℝ) ^ f.T] (f.graph i)| ≤ K') ∧
      (∀ l ∈ f.assignment i, ∀ t ∈ Split.I f.T (f.block i),
        |Split.y l t - f.u i - t * f.v i| ≤ K' / (2 : ℝ) ^ f.T ∧
        |Split.x l t - MvPolynomial.eval ![t, Split.y l t] (f.graph i)| ≤
          K' * (p.N m ^ sc) ^ (-s)) := by
  have pf := pieceFacts_of_chartData (σ := σ) (ρ := ρ) hCD hN₀ hH2 hB1
    (mul_nonneg hsc.le hdp) rfl hJ hceil hρσ i hcost
  obtain ⟨hlow, hup, hrnd⟩ := tangent_exponents hN₀ hsc rfl hd0 hd1 hprof hround
  have hN₀pos : 0 < p.N m := by linarith
  have hHpos : 0 < H := by linarith
  have h2T : (0 : ℝ) < 2 ^ f.T := by positivity
  have hK'pos : 0 < K' := by linarith [hK.one_le]
  have hNs : 0 ≤ (p.N m ^ sc) ^ (-d * s) :=
    Real.rpow_nonneg (Real.rpow_nonneg hN₀pos.le _) _
  have hNs' : 0 ≤ (p.N m ^ sc) ^ (-s) := Real.rpow_nonneg (Real.rpow_nonneg hN₀pos.le _) _
  have hF0 : 0 ≤ p.N m ^ (-p.profile (sc * dp)) := Real.rpow_nonneg hN₀pos.le _
  refine ⟨?_, ?_, ?_, pf.uv.trans hK.H1, pf.deg, fun t ht w hw =>
    (pf.band t ht w hw).trans hK.band, fun l hl t ht => ?_⟩
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) pf.prior_lower
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc (p.N m ^ sc) ^ (-d * s) * (H ^ 2 * 2 ^ f.T)
        ≤ (B ^ 2 * p.N m ^ (-p.profile (sc * dp))) * (H ^ 2 * 2 ^ f.T) := by gcongr
      _ = p.N m ^ (-p.profile (sc * dp)) * ((B ^ 2 * H ^ 2) * 2 ^ f.T) := by ring
      _ ≤ p.N m ^ (-p.profile (sc * dp)) * (K' * 2 ^ f.T) := by gcongr; exact hK.BH
  · refine pf.prior_upper.trans (ENNReal.ofReal_le_ofReal ?_)
    apply div_le_div_of_nonneg_right _ h2T.le
    calc 8 * B * H ^ 5 * p.N m ^ (-p.profile (sc * dp))
        ≤ 8 * B * H ^ 5 * (B ^ 2 * (p.N m ^ sc) ^ (-d * s)) := by
          have : 0 ≤ 8 * B * H ^ 5 := by positivity
          exact mul_le_mul_of_nonneg_left hup this
      _ = (8 * B ^ 3 * H ^ 5) * (p.N m ^ sc) ^ (-d * s) := by ring
      _ ≤ K' * (p.N m ^ sc) ^ (-d * s) := mul_le_mul_of_nonneg_right hK.upper hNs
  · rw [mul_comm]
    refine le_trans ?_ pf.kept
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply ENNReal.ofReal_le_ofReal
    apply inv_anti₀ (by positivity)
    exact mul_le_mul_of_nonneg_right hK.H2 h2T.le
  · obtain ⟨hy, hx⟩ := pf.fit l hl t ht
    refine ⟨hy.trans ?_, hx.trans ?_⟩
    · calc H * f.width i ≤ H * (H / 2 ^ f.T) :=
            mul_le_mul_of_nonneg_left pf.J_le hHpos.le
        _ = H ^ 2 / 2 ^ f.T := by ring
        _ ≤ K' / 2 ^ f.T := div_le_div_of_nonneg_right hK.H2 h2T.le
    · calc H * p.N m ^ (-(sc * dp)) ≤ H * (B * (p.N m ^ sc) ^ (-s)) :=
            mul_le_mul_of_nonneg_left hrnd hHpos.le
        _ = (H * B) * (p.N m ^ sc) ^ (-s) := by ring
        _ ≤ K' * (p.N m ^ sc) ^ (-s) := mul_le_mul_of_nonneg_right hK.HB hNs'

end

end Submission.Obl.k4_scalar_guarded_tangent_preparation
