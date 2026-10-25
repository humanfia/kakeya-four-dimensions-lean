import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit.Planar
import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit.Concentrate

/-!
Moved from o217 (branch x0763, same author, session x0763 = x0931), namespace changed.
# The sliced model of the first jet

Paper Proposition 5.4, "Fitting one row component": after slicing, every labeled incidence
`(l,u)` of a trajectory with remaining tangential coordinate `v l` carries a scalar
`L l u = z l + u G(v l) - φ(u) v l + O(Kp)` (display `a04:sliced-model`), with a Lipschitz
slope function `G`, a row `φ` that is Lipschitz with slack `p`, the local upper `d`-count of
the scalars and the sliced cap `a04:sliced-cap`.

This file records the data, the collision equation `a04:collision-dot` and the confinement
it gives for a second trajectory's starting scalar.
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

/-- The data of the sliced model. -/
structure SlicedData (Ω : Type*) [MeasurableSpace Ω] where
  ν : Measure Ω
  E : Set (Ω × ℝ)
  v : Ω → ℝ
  z : Ω → ℝ
  L : Ω → ℝ → ℝ
  G : ℝ → ℝ
  φ : ℝ → ℝ

/-- The hypotheses of the sliced model at scale `p`, with subpower constant `K` and
dimension `d`. -/
structure SlicedHyp {Ω : Type*} [MeasurableSpace Ω] (D : SlicedData Ω) (p K d : ℝ) : Prop where
  finite : IsFiniteMeasure D.ν
  mass_le : D.ν univ ≤ ENNReal.ofReal K
  measE : MeasurableSet D.E
  E01 : ∀ q ∈ D.E, q.2 ∈ Icc (0:ℝ) 1
  measv : Measurable D.v
  measL : Measurable (fun q : Ω × ℝ => D.L q.1 q.2)
  vbound : ∀ l, |D.v l| ≤ K
  zbound : ∀ l, |D.z l| ≤ K
  Glip : ∀ x y, |D.G x - D.G y| ≤ K * |x - y|
  Gbound : ∀ x, |x| ≤ K → |D.G x| ≤ K
  measφ : Measurable D.φ
  φbound : ∀ u ∈ Icc (0:ℝ) 1, |D.φ u| ≤ K
  φlip : ∀ u ∈ Icc (0:ℝ) 1, ∀ u' ∈ Icc (0:ℝ) 1, |D.φ u - D.φ u'| ≤ K * (|u - u'| + p)
  model : ∀ q ∈ D.E,
    |D.L q.1 q.2 - (D.z q.1 + q.2 * D.G (D.v q.1) - D.φ q.2 * D.v q.1)| ≤ K * p
  count : ∀ u, LocalCount {x | ∃ l, (l, u) ∈ D.E ∧ x = D.L l u} p K d
  cap : ∀ (u : ℝ) (c₁ c₂ : ℤ),
    D.ν {l | (l, u) ∈ D.E ∧ ⌊D.v l / p⌋ = c₁ ∧ ⌊D.L l u / p⌋ = c₂} ≤ ENNReal.ofReal (K * p ^ (1 + d))
  mass : ENNReal.ofReal (1 / K) ≤ (D.ν.prod volume) D.E

/-- The collision equation (`a04:collision-dot`): if `l, l'` are labeled at `u₀` and at `u`
with scalars within `p` at `u`, then the dot product of `(u-u₀, -(φ u - φ u₀))` with
`(G(v l) - G(v l'), v l - v l')` is the difference of their starting scalars up to `(4K+1)p`. -/
theorem collision_dot {Ω : Type*} [MeasurableSpace Ω] {D : SlicedData Ω} {p K d : ℝ}
    (H : SlicedHyp D p K d) {l l' : Ω} {u₀ u : ℝ} (h0 : (l, u₀) ∈ D.E) (h0' : (l', u₀) ∈ D.E)
    (h1 : (l, u) ∈ D.E) (h1' : (l', u) ∈ D.E) (hclose : |D.L l u - D.L l' u| ≤ p) :
    |((u - u₀) * (D.G (D.v l) - D.G (D.v l')) - (D.φ u - D.φ u₀) * (D.v l - D.v l'))
      - (D.L l' u₀ - D.L l u₀)| ≤ (4 * K + 1) * p := by
  have m0 := H.model _ h0
  have m0' := H.model _ h0'
  have m1 := H.model _ h1
  have m1' := H.model _ h1'
  simp only at m0 m0' m1 m1'
  have : ((u - u₀) * (D.G (D.v l) - D.G (D.v l')) - (D.φ u - D.φ u₀) * (D.v l - D.v l'))
      - (D.L l' u₀ - D.L l u₀) =
      (D.L l u - D.L l' u)
      - (D.L l u - (D.z l + u * D.G (D.v l) - D.φ u * D.v l))
      + (D.L l' u - (D.z l' + u * D.G (D.v l') - D.φ u * D.v l'))
      + (D.L l u₀ - (D.z l + u₀ * D.G (D.v l) - D.φ u₀ * D.v l))
      - (D.L l' u₀ - (D.z l' + u₀ * D.G (D.v l') - D.φ u₀ * D.v l')) := by ring
  rw [this]
  have a1 := abs_sub (D.L l u - D.L l' u - (D.L l u - (D.z l + u * D.G (D.v l) - D.φ u * D.v l))
      + (D.L l' u - (D.z l' + u * D.G (D.v l') - D.φ u * D.v l'))
      + (D.L l u₀ - (D.z l + u₀ * D.G (D.v l) - D.φ u₀ * D.v l)))
    (D.L l' u₀ - (D.z l' + u₀ * D.G (D.v l') - D.φ u₀ * D.v l'))
  have a2 := abs_add_le (D.L l u - D.L l' u - (D.L l u - (D.z l + u * D.G (D.v l) - D.φ u * D.v l))
      + (D.L l' u - (D.z l' + u * D.G (D.v l') - D.φ u * D.v l')))
    (D.L l u₀ - (D.z l + u₀ * D.G (D.v l) - D.φ u₀ * D.v l))
  have a3 := abs_add_le (D.L l u - D.L l' u - (D.L l u - (D.z l + u * D.G (D.v l) - D.φ u * D.v l)))
    (D.L l' u - (D.z l' + u * D.G (D.v l') - D.φ u * D.v l'))
  have a4 := abs_sub (D.L l u - D.L l' u) (D.L l u - (D.z l + u * D.G (D.v l) - D.φ u * D.v l))
  linarith

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

end
