-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.CartesianFrostman.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.TruncatedEnergy
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.CircleGeometry

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

attribute [local instance] Classical.propDecidable

noncomputable def cartesianPoint (p : ℝ × ℝ) : Plane := WithLp.toLp 2 ![p.1, p.2]

theorem cartesianPoint_injective : Function.Injective cartesianPoint := by
  intro p q h
  apply Prod.ext
  · exact congrArg (fun x : Plane => x 0) h
  · exact congrArg (fun x : Plane => x 1) h

theorem cartesianPoint_coord_dist (p : ℝ × ℝ) (x : Plane) :
    dist p.1 (x 0) ≤ dist (cartesianPoint p) x ∧
      dist p.2 (x 1) ≤ dist (cartesianPoint p) x := by
  constructor
  · simpa [dist_eq_norm, cartesianPoint] using
      PiLp.norm_apply_le (cartesianPoint p - x) 0
  · simpa [dist_eq_norm, cartesianPoint] using
      PiLp.norm_apply_le (cartesianPoint p - x) 1

def RealFiniteFrostman (δ C σ : ℝ) (A : Finset ℝ) : Prop :=
  ∀ x r : ℝ, δ ≤ r →
    ((A.filter (fun a => dist a x ≤ r)).card : ℝ) ≤ C * r ^ σ * (A.card : ℝ)

/-- Cartesian products of two measures with exponents adding to at least
one satisfy the planar one-dimensional counting bound. -/
theorem cartesian_frostman {δ C D σ τ : ℝ} {A B : Finset ℝ}
    (hδ : 0 < δ) (hC : 1 ≤ C) (hD : 1 ≤ D) (hs : 1 ≤ σ + τ)
    (hA : RealFiniteFrostman δ C σ A) (hB : RealFiniteFrostman δ D τ B) :
    ClosedFiniteFrostman δ (C * D) ((A ×ˢ B).image cartesianPoint) := by
  classical
  let F := (A ×ˢ B).image cartesianPoint
  have hFc : F.card = A.card * B.card := by
    rw [Finset.card_image_of_injective _ cartesianPoint_injective, Finset.card_product]
  intro x r hr
  have hrp : 0 < r := hδ.trans_le hr
  have heq : (↑F : Set Plane) ∩ Metric.closedBall x r =
      (↑(F.filter (fun y => dist y x ≤ r)) : Set Plane) := by
    ext y
    simp
  change (((↑F : Set Plane) ∩ Metric.closedBall x r).ncard : ℝ) ≤ _
  rw [heq, Set.ncard_coe_finset]
  by_cases hr1 : r ≤ 1
  · let SA := A.filter (fun a => dist a (x 0) ≤ r)
    let SB := B.filter (fun b => dist b (x 1) ≤ r)
    have hsub : F.filter (fun y => dist y x ≤ r) ⊆ (SA ×ˢ SB).image cartesianPoint := by
      intro y hy
      obtain ⟨hyF, hyr⟩ := Finset.mem_filter.mp hy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hyF
      have hdist := cartesianPoint_coord_dist p x
      exact Finset.mem_image.mpr ⟨p, Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hp).1, hdist.1.trans hyr⟩,
          Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hp).2, hdist.2.trans hyr⟩⟩, rfl⟩
    have hc : ((F.filter (fun y => dist y x ≤ r)).card : ℝ) ≤
        (SA.card : ℝ) * (SB.card : ℝ) := by
      have hh := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ cartesianPoint_injective, Finset.card_product] at hh
      exact_mod_cast hh
    have hpow : r ^ (σ + τ) ≤ r := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hrp hr1 hs
    calc ((F.filter (fun y => dist y x ≤ r)).card : ℝ) ≤
        (SA.card : ℝ) * (SB.card : ℝ) := hc
      _ ≤ (C * r ^ σ * (A.card : ℝ)) * (D * r ^ τ * (B.card : ℝ)) :=
        mul_le_mul (hA (x 0) r hr) (hB (x 1) r hr) (Nat.cast_nonneg _) (by positivity)
      _ = (C * D) * r ^ (σ + τ) * (F.card : ℝ) := by
        rw [hFc, Nat.cast_mul, Real.rpow_add hrp]
        ring
      _ ≤ (C * D) * r * (F.card : ℝ) := by gcongr
  · have hCD : 1 ≤ C * D := by nlinarith
    have hCr : 1 ≤ C * D * r := by nlinarith [lt_of_not_ge hr1]
    have hc : ((F.filter (fun y => dist y x ≤ r)).card : ℝ) ≤ (F.card : ℝ) := by
      exact_mod_cast Finset.card_filter_le F _
    exact hc.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hCr (Nat.cast_nonneg F.card))

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
