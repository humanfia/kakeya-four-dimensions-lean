import Submission.Obl.k4_general_wide_layer_offset_comparison.TrueFiberGeometry
import Submission.Obl.k4_general_wide_layer_offset_comparison.TrueBinGeometry

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/TrueFiberIncidences.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open Set

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- Every original true incidence with its original two major bins belongs
to the full fiber tested by the compared-sample certificate. -/
theorem AtDepth.base_mem_trueFiberBox {k : ℕ} {r m R H : ℝ}
    (hat : p.AtDepth k r R) (hN : 0 < p.N k) (hH : 2 ≤ H) (hKH : p.K k ≤ H)
    (Q : Fin (p.n k r)) (tag : Fin 2 → ℤ) {l : α}
    (hl : l ∈ p.B k r Q)
    (hz : ⌊p.b k l 0 / p.N k ^ (-m)⌋ = tag 1)
    (hv : ⌊p.b k l 3 / p.N k ^ (-m)⌋ = tag 0)
    {t : ℝ} (ht : t ∈ block (p.T k r) (p.j k r Q)) :
    ![t, (p.x k l t) 1, (p.x k l t) 2] ∈ p.trueFiberBox k r m H Q tag := by
  have hgeo := (hat.2.2.2.2.1 Q).2.2.2.2.2.1 l ((hat.2.2.1 Q).2.2 hl) t ht
  have hbin := intercept_velocity_bin_tube (by positivity : 0 < p.N k ^ (-m)) hz hv
    (Submission.Obl.k4_balanced_native_packet_transport.Pullback.block_subset_unit (p.j k r Q) ht)
  refine ⟨ht, ?_, ?_⟩
  · change |(p.x k l t) 1 - ((tag 1 : ℝ) * p.N k ^ (-m) +
        t * ((tag 0 : ℝ) * p.N k ^ (-m)))| ≤ H * p.N k ^ (-m)
    exact hbin.trans (mul_le_mul_of_nonneg_right hH (by positivity))
  · change |(p.x k l t) 2 - p.c k r Q 2 - t * p.c k r Q 3 -
        p.c k r Q 4 * (p.x k l t) 1| ≤
      H * ((2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r))
    exact hgeo.2.1.trans
      ((mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKH (by positivity)) (by positivity)).trans_eq (by ring))

/-- A retained original incidence supplies the relative-velocity bound
between the true fiber's central line and its actual long-domain chart. -/
theorem AtDepth.trueFiber_long_velocity {k : ℕ} {r m R h g b : ℝ}
    (hat : p.AtDepth k r R) (hN : 0 < p.N k) (hK : 0 ≤ p.K k)
    (hg : 0 < g)
    (hχwidth : p.N k ^ (-m) ≤
      (2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r))
    (hχg : p.N k ^ (-m) ≤ p.N k ^ (-p.ℓ * r))
    (Q : Fin (p.n k r)) (tag : Fin 2 → ℤ) {ω : α × ℝ}
    (hl : ω.1 ∈ p.B k r Q) (ht : ω.2 ∈ block (p.T k r) (p.j k r Q))
    (hz : ⌊p.b k ω.1 0 / p.N k ^ (-m)⌋ = tag 1)
    (hv : ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋ = tag 0) :
    |p.c k r Q 3 + p.c k r Q 4 * ((tag 0 : ℝ) * p.N k ^ (-m)) -
      domainVelocity g (p.domainCode k h g b ω)| ≤ 2 * p.K k * p.N k ^ (-p.ℓ * r) + g := by
  have htrue := (AtDepth.transverse_band_on_major_bin p hat hK (by positivity)
    hχwidth hχg Q ((hat.2.2.1 Q).2.2 hl) (tag 1) (tag 0) hz hv ht).2
  have hlong : |p.b k ω.1 4 - domainVelocity g (p.domainCode k h g b ω)| ≤ g := by
    simpa only [domainVelocity, domainCode, movingDomainCode, sub_zero, zero_add, one_mul] using
      normalized_bin_bound (show (0 : ℝ) < 1 by norm_num) hg
        (x := p.b k ω.1 4) (center := 0) (j := ⌊p.b k ω.1 4 / g⌋) (by simp)
  calc
    _ ≤ |p.c k r Q 3 + p.c k r Q 4 * ((tag 0 : ℝ) * p.N k ^ (-m)) - p.b k ω.1 4| +
        |p.b k ω.1 4 - domainVelocity g (p.domainCode k h g b ω)| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (by simpa only [abs_sub_comm, sub_add_eq_sub_sub] using htrue) hlong

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
