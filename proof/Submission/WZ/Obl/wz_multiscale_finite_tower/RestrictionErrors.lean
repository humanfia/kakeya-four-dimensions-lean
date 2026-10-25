-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.RestrictionErrors.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.LeafRegularization

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_tower_balanced_refinement (Balanced)

theorem HierarchyRestriction.control_of_power_retention {d θ θ' τ ell g gap : ℝ}
    {J : ℕ} {T : TubeHierarchy J} {S : Finset (Fin (T.layer J).card)}
    (R : HierarchyRestriction T S) (H : HierarchyControl d θ g gap T)
    (hd : 0 < d) (hd1 : d ≤ 1) (hθ : θ ≤ θ') (hτ : τ ≤ θ')
    (hbudget : 3 * θ + τ + ell ≤ θ')
    (hbal : ∀ j, j ≤ J → Balanced S (T.ancestor j) (d ^ (-τ)))
    (hcard : d ^ ell * (T.layer J).card ≤ S.card) :
    HierarchyControl d θ' g gap R.tree := by
  have hcoef : d ^ (-τ) ≤ d ^ (-θ') :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hτ)
  apply R.control H hd hd1 hθ
  · intro j hj i hi k hk
    exact (hbal j hj i hi k hk).trans
      (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _))
  · intro j hj k
    have hh := R.branch_retention H hd.le (Real.rpow_nonneg hd.le _) (Real.rpow_nonneg hd.le _)
      hbal hcard hj k
    have he₁ : d ^ (-θ - ell) * d ^ ell = d ^ (-θ) := by
      rw [← Real.rpow_add hd]
      congr 1
      ring
    have he₂ : d ^ (-θ - ell) * (d ^ (-θ) * d ^ (-τ) * d ^ (-θ)) =
        d ^ (-(3 * θ + τ + ell)) := by
      rw [mul_assoc, ← Real.rpow_add hd, ← Real.rpow_add hd, ← Real.rpow_add hd]
      congr 1
      ring
    have hm := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hd.le (-θ - ell))
    have hcore : d ^ (-θ) * {i | T.parent j i = R.map j k}.ncard ≤
        d ^ (-(3 * θ + τ + ell)) * {i | R.tree.parent j i = k}.ncard := by
      calc
        _ = d ^ (-θ - ell) * (d ^ ell * {i | T.parent j i = R.map j k}.ncard) := by
          rw [← mul_assoc, he₁]
        _ ≤ _ := hm
        _ = _ := by rw [← mul_assoc, he₂]
    exact hcore.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hbudget)) (Nat.cast_nonneg _))

lemma HierarchyRestriction.aligned_family {d θ θ' ell g gap : ℝ} {J : ℕ}
    (C : HierarchyCertificate d θ g gap J) {S : Finset (Fin (C.tree.layer J).card)}
    (R : HierarchyRestriction C.tree S) (hd : 0 < d) (hd1 : d ≤ 1)
    (hθ : θ ≤ θ') (hbudget : θ + ell ≤ θ')
    (hcard : d ^ ell * (C.tree.layer J).card ≤ S.card)
    (Z : Fin (C.tree.layer J).card → Set Space)
    (hZm : ∀ i ∈ S, MeasurableSet (Z i)) (hZY : ∀ i ∈ S, Z i ⊆ C.shading i)
    (hden : ∀ i ∈ S, ENNReal.ofReal (d ^ θ' * d ^ 2) ≤ volume (Z i)) :
    AlignedFamily d (d ^ θ') (d ^ (-θ')) (d ^ (-θ')) C.root_axis C.scalar
      (R.tree.layer J).card (R.tree.layer J).position (R.tree.layer J).direction (Z ∘ R.map J) := by
  have hc : d ^ (-θ) ≤ d ^ (-θ') := Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hθ)
  have hL : d ^ (-θ) * (C.tree.layer J).card ≤ d ^ (-θ') * (R.tree.layer J).card := by
    rw [R.bottom_card]
    calc
      _ = d ^ (-(θ + ell)) * (d ^ ell * (C.tree.layer J).card) := by
        rw [← mul_assoc, ← Real.rpow_add hd]
        congr 2
        ring
      _ ≤ d ^ (-(θ + ell)) * S.card := mul_le_mul_of_nonneg_left hcard (Real.rpow_nonneg hd.le _)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hbudget)) (Nat.cast_nonneg _)
  have hF := C.family.reindex (R.map J) (R.injective J) (R.tree.layer J).card_pos (Z ∘ R.map J)
    (fun i => hZm _ (R.bottom_mem i)) (fun i => hZY _ (R.bottom_mem i))
    (fun i => hden _ (R.bottom_mem i)) hL
  have hF' := hF.mono le_rfl hc le_rfl
  have hx : (R.tree.layer J).position = (C.tree.layer J).position ∘ R.map J := funext (R.position J)
  have hv : (R.tree.layer J).direction = (C.tree.layer J).direction ∘ R.map J := funext (R.direction J)
  rw [hx, hv]
  exact hF'

end WangZahlLot.Obl.wz_multiscale_finite_tower
