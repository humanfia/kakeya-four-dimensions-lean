-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.ElementaryRanges.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.PairArea
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.Restricted

noncomputable section

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open MeasureTheory Set
open scoped ENNReal
open WangZahlLot.Obl.wz_jet_close_pair_moment (JetControlled)

/-- The coefficient scale cancels between the two square roots. -/
theorem pair_scale_sqrt_identity {δ D μ : ℝ} (hδ : 0 < δ) (hD : 0 < D) :
    Real.sqrt (δ / D) * Real.sqrt (D * μ / δ) = Real.sqrt μ := by
  rw [← Real.sqrt_mul (div_nonneg hδ.le hD.le)]
  congr 1
  field_simp

/-- A cap on the smaller color verifies the unrestricted moment criterion. -/
theorem pair_product_le_of_min_card {ι : Type*} (A B : Finset ι) {δ D μ F : ℝ}
    (hδ : 0 < δ) (hD : 0 < D)
    (hmin : min (A.card : ℝ) (B.card : ℝ) ≤ F * Real.sqrt (D * μ / δ)) :
    Real.sqrt (δ / D) * (A.card : ℝ) * (B.card : ℝ) ≤
      F * ((A.card : ℝ) + (B.card : ℝ)) * Real.sqrt μ := by
  have hprod := card_product_le_of_min_le A B hmin
  calc
    _ = Real.sqrt (δ / D) * ((A.card : ℝ) * (B.card : ℝ)) := by ring
    _ ≤ Real.sqrt (δ / D) *
        (F * Real.sqrt (D * μ / δ) * ((A.card : ℝ) + (B.card : ℝ))) :=
      mul_le_mul_of_nonneg_left hprod (Real.sqrt_nonneg _)
    _ = F * ((A.card : ℝ) + (B.card : ℝ)) *
        (Real.sqrt (δ / D) * Real.sqrt (D * μ / δ)) := by ring
    _ = _ := by rw [pair_scale_sqrt_identity hδ hD]

/-- The exact area expression is elementary for low richness or small local
curve mass. This is an unrestricted simultaneous-richness estimate. -/
theorem exists_area_constant_of_small_richness_or_card : ∃ C : ℝ, 0 < C ∧
    ∀ {n : ℕ} {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ},
      JetControlled q g → (∀ i, ContDiff ℝ 2 (g i)) →
    ∀ (A B : Finset (Fin n)) (δ D μ τ K a : ℝ),
      0 < δ → 0 < D → 0 < μ → 0 ≤ K →
      (∀ i ∈ A, ∀ j ∈ B, D ≤ dist (q i) (q j)) →
      (μ ≤ δ ^ (-2 * τ) * K ^ (2 * a) ∨
        min (A.card : ℝ) (B.card : ℝ) ≤
          δ ^ (-τ) * K ^ a * Real.sqrt (D * μ / δ)) →
    ∀ E : Set (ℝ × ℝ),
      E ⊆ {p | ENNReal.ofReal μ ≤ finiteMultiplicity A δ g p ∧
        ENNReal.ofReal μ ≤ finiteMultiplicity B δ g p} →
      volume E ≤ ENNReal.ofReal (C * δ ^ (-τ) * K ^ a * δ *
        ((A.card : ℝ) + (B.card : ℝ)) * μ ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨C, hC, hbound⟩ := exists_area_constant_of_first_or_pair
  refine ⟨C, hC, ?_⟩
  intro n q g hjet hg A B δ D μ τ K a hδ hD hμ hK hfar hcase E hE
  have hF : 0 ≤ δ ^ (-τ) * K ^ a := by positivity
  have helem : Real.sqrt μ ≤ δ ^ (-τ) * K ^ a ∨
      Real.sqrt (δ / D) * (A.card : ℝ) * (B.card : ℝ) ≤
        (δ ^ (-τ) * K ^ a) * ((A.card : ℝ) + (B.card : ℝ)) * Real.sqrt μ := by
    rcases hcase with hsmall | hcard
    · left
      have hpow : (δ ^ (-τ) * K ^ a) ^ 2 = δ ^ (-2 * τ) * K ^ (2 * a) := by
        rw [mul_pow, ← Real.rpow_two, ← Real.rpow_two,
          ← Real.rpow_mul hδ.le, ← Real.rpow_mul hK]
        congr 1 <;> congr 1 <;> ring
      have hs := Real.sq_sqrt hμ.le
      rw [← hpow] at hsmall
      nlinarith [Real.sqrt_nonneg μ]
    · exact Or.inr (pair_product_le_of_min_card A B hδ hD hcard)
  convert hbound hjet hg A B δ D μ (δ ^ (-τ) * K ^ a)
    hδ hD hμ hF hfar helem E hE using 1
  congr 1
  ring

/-- The frozen far-scale assumption puts the natural tangency length below
the prescribed slope threshold. Hence a narrow-pair estimate alone gives no
improvement over the unrestricted pair estimate in this regime. -/
theorem natural_length_le_slope_threshold {δ D μ τ : ℝ}
    (hδ : 0 < δ) (hD : 0 < D) (hμ : 0 < μ)
    (hscale : δ * μ * δ ^ (-8 * τ) ≤ D) :
    Real.sqrt (δ / D) ≤ δ ^ (4 * τ) * μ ^ (-(1 / 2 : ℝ)) := by
  have hpos : 0 < δ ^ (8 * τ) / μ := by positivity
  have hδcancel : δ ^ (-8 * τ) * δ ^ (8 * τ) = 1 := by
    rw [← Real.rpow_add hδ]
    convert Real.rpow_zero δ using 1
    congr 1
    ring
  have hmul := mul_le_mul_of_nonneg_right hscale hpos.le
  have hcancel : δ * μ * δ ^ (-8 * τ) * (δ ^ (8 * τ) / μ) = δ := by
    calc
      _ = δ * (δ ^ (-8 * τ) * δ ^ (8 * τ)) * (μ / μ) := by ring
      _ = δ := by rw [hδcancel, div_self hμ.ne', mul_one, mul_one]
  rw [hcancel] at hmul
  have hratio : δ / D ≤ δ ^ (8 * τ) / μ := (div_le_iff₀ hD).mpr (by nlinarith)
  have hsq : (δ ^ (4 * τ) * μ ^ (-(1 / 2 : ℝ))) ^ 2 = δ ^ (8 * τ) / μ := by
    rw [mul_pow, ← Real.rpow_two, ← Real.rpow_two,
      ← Real.rpow_mul hδ.le, ← Real.rpow_mul hμ.le]
    have hx : 4 * τ * 2 = 8 * τ := by ring
    rw [hx]
    norm_num [Real.rpow_neg_one, div_eq_mul_inv]
  have hnonneg : 0 ≤ δ ^ (4 * τ) * μ ^ (-(1 / 2 : ℝ)) := by positivity
  rw [← hsq] at hratio
  nlinarith [Real.sq_sqrt (div_nonneg hδ.le hD.le), Real.sqrt_nonneg (δ / D)]

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
