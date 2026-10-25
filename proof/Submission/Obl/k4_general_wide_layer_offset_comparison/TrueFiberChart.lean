import Submission.Obl.k4_general_wide_layer_offset_comparison.TrueFiberIncidences
import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedComparisonOffsets

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/TrueFiberChart.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open Set MvPolynomial

noncomputable section

/-- The actual physical common-domain chart, with its dummy coordinate
fixed to zero after the matching estimate has returned. -/
def domainMatchingPoint (h g b : ℝ) (D : ℤ × ℤ × ℤ) (z : Fin 3 → ℝ) :
    EuclideanSpace ℝ (Fin 3) :=
  realMatchingPoint (projectedDomainCoordinates (domainTime h D) (32 * h)
    (domainIntercept h g b D) (domainVelocity g D) (32 * b) z)

theorem projectedChartPolynomial_domainMatchingPoint (G : MvPolynomial (Fin 2) ℝ)
    {h g b : ℝ} (hh : 0 < h) (hb : 0 < b) (D : ℤ × ℤ × ℤ) (z : Fin 3 → ℝ) :
    eval (fun i => domainMatchingPoint h g b D z i)
      (projectedChartPolynomial G (domainTime h D) (32 * h)
        (domainIntercept h g b D) (domainVelocity g D) (32 * b)) =
      eval ![z 0, z 2] G := by
  apply projectedChartPolynomial_recover G (by positivity) (by positivity) z
    (fun i => domainMatchingPoint h g b D z i) <;> rfl

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- One original incidence places the entire H-sized fiber in the real
matching half ball. The domain is the literal original long-domain code. -/
theorem AtDepth.trueFiber_matching_bounds {k : ℕ} {r m R H h g b : ℝ}
    (hat : p.AtDepth k r R) (hN : 0 < p.N k) (hH : 2 ≤ H)
    (hK : 0 ≤ p.K k) (hKH : p.K k ≤ H)
    (hh : 0 < h) (hg : 0 < g) (hb : 0 < b) (hmove : h * g = b)
    (hχwidth : p.N k ^ (-m) ≤
      (2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r))
    (hχg : p.N k ^ (-m) ≤ p.N k ^ (-p.ℓ * r))
    (Q : Fin (p.n k r)) (tag : Fin 2 → ℤ) {ω : α × ℝ}
    (hl : ω.1 ∈ p.B k r Q) (ht : ω.2 ∈ block (p.T k r) (p.j k r Q))
    (hz : ⌊p.b k ω.1 0 / p.N k ^ (-m)⌋ = tag 1)
    (hv : ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋ = tag 0)
    (hsmall : H ^ 2 * (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-p.ℓ * r) / b +
      ((2 : ℝ) ^ (-(p.T k r : ℤ))) * g / b) ≤ 1 / 4) :
    let D := p.domainCode k h g b ω
    (∀ z ∈ p.trueFiberBox k r m H Q tag, ‖domainMatchingPoint h g b D z‖ ≤ 1 / 2) ∧
    ∀ z ∈ p.trueFiberBox k r m H Q tag, ∀ z' ∈ p.trueFiberBox k r m H Q tag,
      ‖domainMatchingPoint h g b D z - domainMatchingPoint h g b D z'‖ ≤
        H ^ 2 * (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-p.ℓ * r) / b +
          ((2 : ℝ) ^ (-(p.T k r : ℤ))) * g / b) := by
  dsimp only
  let D := p.domainCode k h g b ω
  let zω : Fin 3 → ℝ := ![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2]
  have hωbox := AtDepth.base_mem_trueFiberBox p hat hN hH hKH Q tag hl hz hv ht
  have hvelocity := AtDepth.trueFiber_long_velocity p hat hN hK hg hχwidth hχg Q tag hl ht hz hv
    (h := h) (b := b)
  have hdist : ∀ z ∈ p.trueFiberBox k r m H Q tag, ∀ z' ∈ p.trueFiberBox k r m H Q tag,
      ‖domainMatchingPoint h g b D z - domainMatchingPoint h g b D z'‖ ≤
        H ^ 2 * (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-p.ℓ * r) / b +
          ((2 : ℝ) ^ (-(p.T k r : ℤ))) * g / b) := by
    intro z hz z' hz'
    exact (realMatchingPoint_dist_le _ _).trans
      (p.trueFiberBox_chart_diameter hN (by linarith) hK hKH hh hg hb hmove Q tag
        ((hat.2.2.2.2.1 Q).2.2.2.1 4) hχwidth hvelocity hz hz')
  have hωnorm : ‖domainMatchingPoint h g b D zω‖ ≤ 1 / 4 := by
    have heq : projectedDomainCoordinates (domainTime h D) (32 * h)
        (domainIntercept h g b D) (domainVelocity g D) (32 * b) zω =
        p.normalizedDomainBase k h g b ω :=
      (p.normalizedDomainBase_on_code (k := k) (h := h) (g := g) (b := b) (ω := ω)
        (d := D) rfl).symm
    change ‖realMatchingPoint _‖ ≤ _
    rw [heq]
    have hinner := p.normalizedDomainBase_inner (k := k) hh hg hb hmove.le ω
    exact (realMatchingPoint_norm_le _).trans (by linarith [hinner 0, hinner 1])
  refine ⟨?_, hdist⟩
  intro z hz
  have hd := (hdist z hz zω hωbox).trans hsmall
  exact (norm_le_norm_sub_add (domainMatchingPoint h g b D z)
    (domainMatchingPoint h g b D zω)).trans (by linarith)

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
