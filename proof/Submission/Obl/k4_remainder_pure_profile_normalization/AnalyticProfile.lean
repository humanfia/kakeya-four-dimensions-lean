import Submission.Obl.k4_remainder_pure_profile_normalization.Pure

namespace Submission.Obl.k4_remainder_pure_profile_normalization
open MeasureTheory Filter

noncomputable def Data.incidenceLaw (p : Data) (k : ℕ) (b : Fin (p.W k)) :
    Measure Incidence := ((p.ν k b).prod volume).restrict (p.E k b)

/-- The analytic clauses remaining after finite sample normalization. -/
structure AnalyticProfile (p : Data) : Prop where
  pure_law : ∀ k b s, 0 ≤ s → s ≤ p.L → Measurable (p.g k b s) ∧
    (p.incidenceLaw k b).map (obs (p.B k b) (δ (p.N k) s)) =
      (volume.prod Measure.count).withDensity (p.g k b s)
  joint_law : ∀ k b u, 0 < u → u ≤ p.η * p.L → Measurable (p.G k b u) ∧
    (p.incidenceLaw k b).map (fun z =>
      (obs (p.B k b) (δ (p.N k) p.L) z,
        fun j : Fin 2 => ⌊v z.1 j / δ (p.N k) u⌋)) =
      ((volume.prod Measure.count).prod Measure.count).withDensity (p.G k b u)
  increments : ∀ s t, 0 ≤ s → s ≤ t → t ≤ p.L →
    0 ≤ p.f t - p.f s ∧ p.f t - p.f s ≤ t - s
  typical : ∀ s τ, 0 ≤ s → s ≤ p.L → 0 < τ → ∃ c : ℝ, 0 < c ∧
    ∀ᶠ k in atTop, (∑ b, ENNReal.ofReal (p.ω k b) * p.incidenceLaw k b
      {z | p.g k b s (obs (p.B k b) (δ (p.N k) s) z) <
          ENNReal.ofReal (p.N k ^ (-p.f s - τ)) ∨
        ENNReal.ofReal (p.N k ^ (-p.f s + τ)) <
          p.g k b s (obs (p.B k b) (δ (p.N k) s) z)}) ≤
        ENNReal.ofReal (p.N k ^ (-c))
  cap : ∀ s, 0 ≤ s → s ≤ p.L → p.f p.L - p.f s ≤ p.d * (p.L - s)

theorem pureValid_of_samples {p : Data}
    (hN : ∀ k, 2 ≤ p.N k) (ht : Tendsto p.N atTop atTop)
    (hK : (∀ k, 1 ≤ p.K k) ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k in atTop, p.K k ≤ p.N k ^ ε)
    (hL : 0 < p.L) (hd : 0 < p.d) (hd1 : p.d < 1)
    (hS : 0 < p.S) (hη : 0 < p.η)
    (hs : ∃ M D : ℕ, ∀ k, Normalization.SampleProblem (p.N k) (p.K k) M D
      (p.W k) (p.ω k) (p.ν k) (p.E k) (p.P k) (p.B k))
    (ha : AnalyticProfile p) : p.PureValid := by
  refine ⟨hN, ht, hK, hL, hd, hd1, hS, hη, ?_, ha.pure_law,
    ha.joint_law, ha.increments, ha.typical, ha.cap, trivial⟩
  obtain ⟨M, D, hs⟩ := hs
  refine ⟨M, D, fun k => ?_⟩
  let s := hs k
  refine ⟨s.card, s.weight_nonneg, s.weight_sum, fun b => ?_, ?_⟩
  · exact ⟨s.prob b, s.scale_pos b, s.scale_le b, s.scale_inv_le b,
      s.deg b, s.coeff b, s.prior b, s.event_meas b, s.event_time b,
      s.event_bdd b, s.event_fmt b, s.native b, s.lower b⟩
  · simpa only [Measure.restrict_apply_univ] using s.mass

end Submission.Obl.k4_remainder_pure_profile_normalization
