import Submission.Obl.k4_general_wide_layer_offset_comparison.TrueFiberIncidences
import Submission.Obl.k4_general_wide_layer_offset_comparison.ComparisonBandCaps

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ShortDomainFiber.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open Set

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

def shortComparisonCode (k : ℕ) (r m : ℝ) (ω : α × ℝ) :
    (Fin 2 → ℤ) × (ℤ × ℤ × ℤ) :=
  let q := (2 : ℝ) ^ (-(p.T k r : ℤ))
  let g := p.N k ^ (-p.ℓ * r)
  p.comparisonCode k m q g (q * g) ω

/-- An original occurrence anchors its entire short code domain inside
the tested true fiber. Thus full original projected marginal witnesses on
that code domain inherit the whole-fiber polynomial offset estimate. -/
theorem AtDepth.short_code_in_trueFiberBox {k : ℕ} {r m R H : ℝ}
    (hat : p.AtDepth k r R) (hN : 0 < p.N k) (hK : 1 ≤ p.K k)
    (hH : 10 * p.K k ≤ H)
    (hχ : p.N k ^ (-m) ≤
      (2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r))
    (Q : Fin (p.n k r)) (tag : Fin 2 → ℤ) (D : ℤ × ℤ × ℤ)
    (hDt : D.1 = ((p.j k r Q : ℕ) : ℤ))
    {ω₀ ω : α × ℝ} (hω₀ : ω₀ ∈ p.baseGood k) (hl : ω₀.1 ∈ p.B k r Q)
    (hc₀ : p.shortComparisonCode k r m ω₀ = (tag, D))
    (hω : ω ∈ p.baseGood k) (hc : p.shortComparisonCode k r m ω = (tag, D)) :
    ![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2] ∈ p.trueFiberBox k r m H Q tag := by
  let q := (2 : ℝ) ^ (-(p.T k r : ℤ))
  let g := p.N k ^ (-p.ℓ * r)
  have hq : 0 < q := by dsimp [q]; positivity
  have hg : 0 < g := by dsimp [g]; positivity
  have hqg : 0 < q * g := mul_pos hq hg
  have hK0 : 0 ≤ p.K k := zero_le_one.trans hK
  change p.comparisonCode k m q g (q * g) ω₀ = (tag, D) at hc₀
  change p.comparisonCode k m q g (q * g) ω = (tag, D) at hc
  have hread₀ : ⌊ω₀.2 / q⌋ = D.1 :=
    congrArg (fun c : (Fin 2 → ℤ) × (ℤ × ℤ × ℤ) => c.2.1) hc₀
  have hread : ⌊ω.2 / q⌋ = D.1 :=
    congrArg (fun c : (Fin 2 → ℤ) × (ℤ × ℤ × ℤ) => c.2.1) hc
  have hfloor : ⌊ω.2 / q⌋ = ((p.j k r Q : ℕ) : ℤ) := hread.trans hDt
  have hblock : ω.2 ∈ block (p.T k r) (p.j k r Q) := by
    have hlo : ((p.j k r Q : ℕ) : ℝ) ≤ ω.2 / q := by
      simpa only [hfloor, Int.cast_natCast] using Int.floor_le (ω.2 / q)
    have hhi : ω.2 / q ≤ ((p.j k r Q : ℕ) : ℝ) + 1 := by
      simpa only [hfloor, Int.cast_natCast] using (Int.lt_floor_add_one (ω.2 / q)).le
    change _ ≤ ω.2 ∧ ω.2 ≤ _
    constructor
    · simpa only [q, zpow_neg, zpow_natCast, div_eq_mul_inv] using (le_div_iff₀ hq).mp hlo
    · simpa only [q, zpow_neg, zpow_natCast, div_eq_mul_inv] using (div_le_iff₀ hq).mp hhi
  have hc₀t : p.comparisonCode k m q g (q * g) (ω₀.1, ω.2) = (tag, D) := by
    simpa only [comparisonCode, domainCode, movingDomainCode, hread₀, hread] using hc₀
  have hω₀t : (ω₀.1, ω.2) ∈ p.baseGood k := ⟨hω.1, hω₀.2⟩
  have hbox := p.comparisonCode_movingBox hN hq hg hqg le_rfl hω tag D hc
  have hbox₀ := p.comparisonCode_movingBox hN hq hg hqg le_rfl hω₀t tag D hc₀t
  let Y := domainIntercept q g (q * g) D + ω.2 * domainVelocity g D
  let Z := (tag 1 : ℝ) * p.N k ^ (-m) + ω.2 * ((tag 0 : ℝ) * p.N k ^ (-m))
  have hy : |(p.x k ω.1 ω.2) 2 - Y| ≤ 2 * (q * g) := by simpa [Y] using hbox.2 1
  have hy₀ : |(p.x k ω₀.1 ω.2) 2 - Y| ≤ 2 * (q * g) := by simpa [Y] using hbox₀.2 1
  have hz : |(p.x k ω.1 ω.2) 1 - Z| ≤ 2 * p.N k ^ (-m) := by simpa [Z] using hbox.2 0
  have hz₀ : |(p.x k ω₀.1 ω.2) 1 - Z| ≤ 2 * p.N k ^ (-m) := by simpa [Z] using hbox₀.2 0
  have hydiff : |(p.x k ω.1 ω.2) 2 - (p.x k ω₀.1 ω.2) 2| ≤ 4 * (q * g) := by
    exact (abs_sub_le _ Y _).trans (by linarith [hy, (by simpa only [abs_sub_comm] using hy₀ :
      |Y - (p.x k ω₀.1 ω.2) 2| ≤ 2 * (q * g))])
  have hzdiff : |(p.x k ω₀.1 ω.2) 1 - (p.x k ω.1 ω.2) 1| ≤ 4 * p.N k ^ (-m) := by
    exact (abs_sub_le _ Z _).trans (by linarith [hz₀, (by simpa only [abs_sub_comm] using hz :
      |Z - (p.x k ω.1 ω.2) 1| ≤ 2 * p.N k ^ (-m))])
  have hgeo := (hat.2.2.2.2.1 Q).2.2.2.2.2.1 ω₀.1 ((hat.2.2.1 Q).2.2 hl) ω.2 hblock
  have hc4 := (hat.2.2.2.2.1 Q).2.2.2.1 4
  refine ⟨hblock, hz.trans (mul_le_mul_of_nonneg_right (by linarith : 2 ≤ H) (by positivity)), ?_⟩
  change |(p.x k ω.1 ω.2) 2 - p.c k r Q 2 - ω.2 * p.c k r Q 3 -
      p.c k r Q 4 * (p.x k ω.1 ω.2) 1| ≤ H * (q * g)
  calc
    _ = |((p.x k ω.1 ω.2) 2 - (p.x k ω₀.1 ω.2) 2) +
        ((p.x k ω₀.1 ω.2) 2 - p.c k r Q 2 - ω.2 * p.c k r Q 3 -
          p.c k r Q 4 * (p.x k ω₀.1 ω.2) 1) +
        p.c k r Q 4 * ((p.x k ω₀.1 ω.2) 1 - (p.x k ω.1 ω.2) 1)| := by congr 1; ring
    _ ≤ |(p.x k ω.1 ω.2) 2 - (p.x k ω₀.1 ω.2) 2| +
        |(p.x k ω₀.1 ω.2) 2 - p.c k r Q 2 - ω.2 * p.c k r Q 3 -
          p.c k r Q 4 * (p.x k ω₀.1 ω.2) 1| +
        |p.c k r Q 4| * |(p.x k ω₀.1 ω.2) 1 - (p.x k ω.1 ω.2) 1| := by
      simpa only [abs_mul] using abs_add_three
        ((p.x k ω.1 ω.2) 2 - (p.x k ω₀.1 ω.2) 2)
        ((p.x k ω₀.1 ω.2) 2 - p.c k r Q 2 - ω.2 * p.c k r Q 3 -
          p.c k r Q 4 * (p.x k ω₀.1 ω.2) 1)
        (p.c k r Q 4 * ((p.x k ω₀.1 ω.2) 1 - (p.x k ω.1 ω.2) 1))
    _ ≤ 4 * (q * g) + p.K k * q * g + p.K k * (4 * p.N k ^ (-m)) :=
      add_le_add (add_le_add hydiff hgeo.2.1) (mul_le_mul hc4 hzdiff (abs_nonneg _) hK0)
    _ ≤ H * (q * g) := by
      have hχ' : p.N k ^ (-m) ≤ q * g := hχ
      have hn : 5 * p.K k + 4 ≤ H := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hχ' hK0,
        mul_le_mul_of_nonneg_right hn hqg.le]

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
