-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.HighLabelSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/HighLabelSelection.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641 commit 8a2b46b, HighLabelSelection.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.SummedNet

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open scoped ENNReal Classical
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover (netConst)

/-- A summed lower estimate on the low labels, compared with a summed volume
cap, leaves at least half the selected body count in the remaining labels. -/
theorem high_label_count_from_low_volume_sum {ι : Type*} (Lab : Finset ι)
    (low : ι → Prop) (card : ι → ℕ) (Γ : ι → Set V) {K J cap : ℝ}
    (hK : 0 < K) (hJ : 0 ≤ J) (hcap : 0 ≤ cap)
    (hlow : (∑ ℓ ∈ Lab.filter low, O (K * card ℓ)) ≤
      O J * ∑ ℓ ∈ Lab.filter low, μ (Γ ℓ))
    (hupper : (∑ ℓ ∈ Lab.filter low, μ (Γ ℓ)) ≤ O cap)
    (hgap : J * cap < K * (∑ ℓ ∈ Lab, (card ℓ : ℝ)) / 2) :
    (∑ ℓ ∈ Lab, (card ℓ : ℝ)) / 2 ≤
      ∑ ℓ ∈ Lab.filter (fun ℓ => ¬ low ℓ), (card ℓ : ℝ) := by
  classical
  have hbound : O (K * ∑ ℓ ∈ Lab.filter low, (card ℓ : ℝ)) ≤ O (J * cap) := by
    calc
      _ = ∑ ℓ ∈ Lab.filter low, O (K * card ℓ) := by
        rw [Finset.mul_sum]
        exact ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity
      _ ≤ O J * ∑ ℓ ∈ Lab.filter low, μ (Γ ℓ) := hlow
      _ ≤ O J * O cap := mul_le_mul' le_rfl hupper
      _ = _ := (ENNReal.ofReal_mul hJ).symm
  have hreal := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hJ hcap)).mp hbound
  have hsmall : (∑ ℓ ∈ Lab.filter low, (card ℓ : ℝ)) <
      (∑ ℓ ∈ Lab, (card ℓ : ℝ)) / 2 := by
    nlinarith only [hreal, hgap, hK]
  have hsplit := Finset.sum_filter_add_sum_filter_not Lab low (fun ℓ => (card ℓ : ℝ))
  linarith only [hsmall, hsplit]

/-- With power-scale balancing and the concentration threshold used in the
first net, its per-body coefficient has the exact scalar form for the cap
comparison. The balancing depth is fixed before delta. -/
theorem low_q_coefficient_power_form {δ ε u ζ σ ω A B J w M : ℝ} {d : ℕ}
    (hδ : 0 < δ) (hd : 0 < d) (hM : 0 < M) :
    lowQCoeff A δ ε B ω σ (J * w) M (δ ^ (-u)) d *
        (δ ^ (-ζ / 2)) ^ (σ / 2) =
      (A * netConst / d) * δ ^ (ε + u) * (4 * B) ^ (ω + σ) * J * w / M *
        δ ^ (-(ζ * σ / 4)) := by
  have hd0 : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr hd).ne'
  have hp : δ ^ u ≠ 0 := (Real.rpow_pos_of_pos hδ u).ne'
  have hpow : (δ ^ (-ζ / 2)) ^ (σ / 2) = δ ^ (-(ζ * σ / 4)) := by
    rw [← Real.rpow_mul hδ.le]
    congr 1
    ring
  rw [hpow]
  dsimp only [lowQCoeff]
  rw [Real.rpow_add hδ, Real.rpow_neg hδ.le]
  field_simp

/-- A large old coefficient converts the complementary net threshold into
an absolute high-overlap bound. -/
theorem high_fibre_weight_of_large_coefficient {δ ζ M R q w : ℝ}
    (hδ : 0 < δ) (hM : δ ^ (-ζ) ≤ M)
    (hhigh : M * R ^ 2 / δ ^ (-ζ / 2) < q * w) :
    δ ^ (-ζ / 2) * R ^ 2 < q * w := by
  calc
    _ = δ ^ (-ζ) * R ^ 2 / δ ^ (-ζ / 2) := by
      rw [mul_div_right_comm, ← Real.rpow_sub hδ]
      congr 2
      ring
    _ ≤ M * R ^ 2 / δ ^ (-ζ / 2) := by gcongr
    _ < _ := hhigh

/-- The explicit net retention factor is a small power of the base scale once
the fixed balancing depth has been paid. -/
theorem balanced_net_power_retention {δ u I N q : ℝ} {d : ℕ}
    (hδ : 0 < δ) (hd : 0 < d) (hI : 0 ≤ I)
    (hsmall : δ ^ u * d ≤ netConst)
    (hret : netConst * I ≤ (d : ℝ) * δ ^ (-u) * N * q) :
    δ ^ (2 * u) * I ≤ N * q := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hpow : 0 < δ ^ u := Real.rpow_pos_of_pos hδ u
  have hcancel : δ ^ u * δ ^ (-u) = 1 := by rw [← Real.rpow_add hδ]; simp
  have H : δ ^ u * netConst * I ≤ (d : ℝ) * (N * q) := by
    calc
      _ = δ ^ u * (netConst * I) := by ring
      _ ≤ δ ^ u * ((d : ℝ) * δ ^ (-u) * N * q) :=
        mul_le_mul_of_nonneg_left hret hpow.le
      _ = (δ ^ u * δ ^ (-u)) * ((d : ℝ) * (N * q)) := by ring
      _ = _ := by rw [hcancel, one_mul]
  have hh := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hpow.le hI)
  have hpow2 : δ ^ (2 * u) = δ ^ u * δ ^ u := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  rw [hpow2]
  nlinarith only [hh, H, hdR]

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
