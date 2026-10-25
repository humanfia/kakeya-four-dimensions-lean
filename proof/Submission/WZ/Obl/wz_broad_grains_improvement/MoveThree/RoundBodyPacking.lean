-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.RoundBodyPacking.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/RoundBodyPacking.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.InscribedBodies
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.InnerTubePacking
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.TubeGeometry

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_flat_factored_improvement (BodyPacking)
open WangZahlLot.Obl.wz_two_scale_flat_box_estimate (dilation dilation_tube_image)

noncomputable section

/-- The interior-ball and diameter conclusions of natural normalization
turn a bound on large body overlaps into the required packing coefficient. -/
theorem round_body_packing {ρ : ℝ} (hρ : 0 < ρ) {n K : ℕ} (hK : 0 < K)
    (U : Fin n → Set V) (z : Fin n → V)
    (hconv : ∀ i, Convex ℝ (U i))
    (hball : ∀ i, ball (z i) (ρ / 100) ⊆ U i)
    (hlong : ∀ i, ∃ p ∈ U i, ∃ q ∈ U i, (1 / 4 : ℝ) ≤ dist p q)
    (hdegree : ∀ i, (Finset.univ.filter fun j => O (ρ ^ 2 / 1280000) < μ (U i ∩ U j)).card ≤ K) :
    BodyPacking U (ρ ^ 2 / 64) (10000000 * Real.sqrt K) := by
  classical
  have htubes : ∀ i, ∃ v : V, ‖v‖ = 1 ∧ T (ρ / 200) (z i) ((1 / 16 : ℝ) • v) ⊆ U i := by
    intro i
    obtain ⟨v, hv, hT⟩ := convex_body_inscribed_tube (by positivity : 0 < ρ / 100)
      (hconv i) (hball i) (hlong i)
    refine ⟨v, hv, ?_⟩
    simpa only [show ρ / 100 / 2 = ρ / 200 by ring] using hT
  choose v hv hT using htubes
  let f : V ≃ᵃ[ℝ] V := dilation 0 16 (by norm_num)
  have hvol (W : Set V) : μ (f '' W) = O 4096 * μ W := by
    change volume (AffineMap.homothety (0 : V) (16 : ℝ) '' W) = _
    rw [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin]
    norm_num [O]
  have hTi (i : Fin n) : T (2 * ρ / 25) (f (z i)) (v i) ⊆ f '' U i := by
    have he : f '' T (ρ / 200) (z i) ((1 / 16 : ℝ) • v i) =
        T (2 * ρ / 25) (f (z i)) (v i) := by
      rw [show f = dilation (0 : V) 16 (by norm_num) from rfl,
        dilation_tube_image _ (by norm_num : (0 : ℝ) < 16)]
      rw [show (16 : ℝ) * (ρ / 200) = 2 * ρ / 25 by ring, smul_smul]
      norm_num
    rw [← he]
    exact image_mono (hT i)
  have hdeg : ∀ i, (Finset.univ.filter fun j => O ((2 * ρ / 25) ^ 2 / 2) <
      μ ((f '' U i) ∩ (f '' U j))).card ≤ K := by
    intro i
    apply (Finset.card_le_card ?_).trans (hdegree i)
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    by_contra hn
    have hsmall : μ (U i ∩ U j) ≤ O (ρ ^ 2 / 1280000) := le_of_not_gt hn
    have hupper : μ ((f '' U i) ∩ (f '' U j)) ≤ O ((2 * ρ / 25) ^ 2 / 2) := by
      rw [← Set.image_inter f.injective, hvol]
      calc
        _ ≤ O 4096 * O (ρ ^ 2 / 1280000) := mul_le_mul' le_rfl hsmall
        _ = _ := by rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4096)]; congr 1; ring
    exact not_lt_of_ge hupper hj'
  have hp := body_packing_of_inner_tubes (by positivity : 0 < 2 * ρ / 25) hK
    (fun i => f '' U i) (fun i => f (z i)) v hv hTi hdeg
  intro Q hQ
  have hh := hp (f '' Q) (hQ.affine_image f.toAffineMap)
  have he : {i | f '' U i ⊆ f '' Q} = {i | U i ⊆ Q} := by
    ext i
    exact Set.image_subset_image_iff f.injective
  change O (Real.sqrt (Set.ncard {i | f '' U i ⊆ f '' Q} : ℝ) * (2 * ρ / 25) ^ 2) ≤
    O (1000 * Real.sqrt K) * μ (f '' Q) at hh
  rw [he, hvol] at hh
  calc
    _ = O (625 / 256 : ℝ) *
        O (Real.sqrt (Set.ncard {i | U i ⊆ Q} : ℝ) * (2 * ρ / 25) ^ 2) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 625 / 256)]
      congr 1
      ring
    _ ≤ O (625 / 256 : ℝ) * (O (1000 * Real.sqrt K) * (O 4096 * μ Q)) :=
      mul_le_mul' le_rfl hh
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 625 / 256),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ (625 / 256 : ℝ) * (1000 * Real.sqrt K))]
      congr 2
      ring

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
