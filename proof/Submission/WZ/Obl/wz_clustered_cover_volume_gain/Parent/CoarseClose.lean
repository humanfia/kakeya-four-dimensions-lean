-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.CoarseClose.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoarseGeometry

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

noncomputable section

def coarseVolumeConstant : ℝ := max 1 ((volume (ball (0 : Space) 42)).toReal / 8)

namespace Interfaces

/-- The near-round convex factorization bounds the total number of coarse carriers. -/
theorem near_round_carrier_count {δ η h ρ ν t m a b : ℝ} {n N L : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N} {U : Finset (Fin N)}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {g : Fin N → Fin L}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hA : A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f)
    (hcover : Factor.AssignedCover 4 ρ (δ ^ (-ν)) y w U m a b L z e g)
    (hround : δ ^ t * b ≤ a) :
    (L : ℝ) * b ^ 2 ≤ coarseVolumeConstant * δ ^ (-(ν + t)) := by
  have ha : 0 < a := hδ.trans_le (hδρ.trans hcover.width)
  have hb : 0 < b := ha.trans_le hcover.ordered
  have hκ := factored_carrier_katz_count (hδ.trans_le hδρ) (Real.rpow_nonneg hδ.le _) hcover
    (ball (0 : V) 42) (convex_ball _ _)
  have hall : {j | factoringCarrier b (z j) (e j) ⊆ ball 0 42} = Set.univ :=
    Set.eq_univ_of_forall (factored_carrier_subset_ball hδ hδρ hA hC hcover)
  change o (({j | factoringCarrier b (z j) (e j) ⊆ ball 0 42}.ncard : ℝ) * (3 * b) ^ 2) ≤ _ at hκ
  rw [hall, Set.ncard_univ, Nat.card_fin] at hκ
  have hvol : μ (ball (0 : V) 42) ≠ ⊤ := (measure_ball_lt_top : volume (ball (0 : V) 42) < ⊤).ne
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvol) hκ
  simp only [o, ENNReal.toReal_ofReal (by positivity : 0 ≤ (L : ℝ) * (3 * b) ^ 2),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (by positivity : 0 ≤ (9 * b / (8 * a)) * δ ^ (-ν))] at hh
  have hba : b ≤ δ ^ (-t) * a := by
    have hh := mul_le_mul_of_nonneg_left hround (Real.rpow_nonneg hδ.le (-t))
    have he : δ ^ (-t) * δ ^ t = 1 := by rw [← Real.rpow_add hδ]; simp
    simpa only [← mul_assoc, he, one_mul] using hh
  have hratio : b / (8 * a) ≤ δ ^ (-t) / 8 := by
    apply (div_le_iff₀ (by positivity : 0 < 8 * a)).mpr
    nlinarith
  have he : 9 * b / (8 * a) * δ ^ (-ν) * (μ (ball (0 : V) 42)).toReal =
      9 * (b / (8 * a) * δ ^ (-ν) * (μ (ball (0 : V) 42)).toReal) := by ring
  rw [he] at hh
  calc
    _ ≤ b / (8 * a) * δ ^ (-ν) * (μ (ball (0 : V) 42)).toReal := by nlinarith [hh]
    _ ≤ (δ ^ (-t) / 8) * δ ^ (-ν) * (μ (ball (0 : V) 42)).toReal := by gcongr
    _ = ((volume (ball (0 : V) 42)).toReal / 8) * δ ^ (-(ν + t)) := by
      rw [show -(ν + t) = -t + -ν by ring, Real.rpow_add hδ]
      dsimp only [μ]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hδ.le _)

end Interfaces

/-- At a macroscopic coarse scale, the convex count alone supplies the required
coarse multiplicity scale, with an explicit power loss. -/
theorem close_coarse_count_bound {δ b β s C N σ ω : ℝ}
    (hδ : 0 < δ) (hb : 0 < b) (hb8 : b ≤ 8) (hC : 0 ≤ C) (hN : 1 ≤ N)
    (hσ : 0 ≤ σ) (hω : 0 ≤ ω) (hω1 : ω ≤ 1)
    (hscale : δ ^ β ≤ b) (hcount : N * b ^ 2 ≤ C * δ ^ (-s)) :
    N ≤ 8 * C * δ ^ (-s - β * (2 + σ)) * (b ^ (-ω) * (N * b) ^ σ) := by
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  have hinv : b ^ (-2 : ℝ) ≤ δ ^ (-2 * β) := by
    have hh := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hδ β) hscale (by norm_num : (-2 : ℝ) ≤ 0)
    rw [← Real.rpow_mul hδ.le] at hh
    convert hh using 1 <;> ring
  have hN' : N ≤ C * δ ^ (-s - 2 * β) := by
    calc
      N ≤ C * δ ^ (-s) / b ^ 2 := (le_div_iff₀ hb2).mpr hcount
      _ = C * δ ^ (-s) * b ^ (-2 : ℝ) := by rw [Real.rpow_neg hb.le, Real.rpow_two]; ring
      _ ≤ C * δ ^ (-s) * δ ^ (-2 * β) := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by rw [show -s - 2 * β = -s + -2 * β by ring, Real.rpow_add hδ]; ring
  have hpow : δ ^ (β * σ) ≤ (N * b) ^ σ := by
    rw [Real.rpow_mul hδ.le]
    apply Real.rpow_le_rpow (Real.rpow_nonneg hδ.le _) _ hσ
    exact hscale.trans (by nlinarith)
  have hωlow : (1 / 8 : ℝ) ≤ b ^ (-ω) := by
    calc
      (1 / 8 : ℝ) = (8 : ℝ) ^ (-1 : ℝ) := by norm_num
      _ ≤ (8 : ℝ) ^ (-ω) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos hb hb8 (neg_nonpos.mpr hω)
  have hlo : (1 / 8 : ℝ) * δ ^ (β * σ) ≤ b ^ (-ω) * (N * b) ^ σ :=
    mul_le_mul hωlow hpow (Real.rpow_nonneg hδ.le _) (Real.rpow_nonneg hb.le _)
  refine hN'.trans ?_
  calc
    _ = (8 * C * δ ^ (-s - β * (2 + σ))) * ((1 / 8 : ℝ) * δ ^ (β * σ)) := by
      rw [show -s - 2 * β = (-s - β * (2 + σ)) + β * σ by ring, Real.rpow_add hδ]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlo (by positivity)

end

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
