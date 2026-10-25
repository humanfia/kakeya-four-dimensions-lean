-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.PrismCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.PrismPieces
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.FactorDyadic

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open MeasureTheory Set

/-- Disjoint prisms satisfy the exact volume-normalized count in every
container. Convexity of the container is unnecessary, so arbitrary local
subcollections can be used in the dagger-box count. -/
theorem prism_count_of_disjoint {a b c : ℝ} {L : ℕ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V) (S : Finset (Fin L))
    (hdisj : (↑S : Set (Fin L)).PairwiseDisjoint (fun j => P a b c (z j) (e j)))
    (W : Set V) :
    o (q {j | j ∈ S ∧ P a b c (z j) (e j) ⊆ W} * (a * b * c)) ≤ μ W := by
  classical
  let J := S.filter (fun j => P a b c (z j) (e j) ⊆ W)
  have hq : q {j | j ∈ S ∧ P a b c (z j) (e j) ⊆ W} = (J.card : ℝ) := by
    change (Set.ncard _ : ℝ) = _
    congr 1
    rw [← Set.ncard_coe_finset]
    congr 1
    ext j
    simp [J]
  have hJdisj : (↑J : Set (Fin L)).PairwiseDisjoint (fun j => P a b c (z j) (e j)) := by
    intro i hi j hj hij
    exact hdisj (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 hij
  have hsub : (⋃ j ∈ J, P a b c (z j) (e j)) ⊆ W := by
    intro p hp
    obtain ⟨j, hj, hpj⟩ := mem_iUnion₂.mp hp
    exact (Finset.mem_filter.mp hj).2 hpj
  have hvol (j : Fin L) : μ (P a b c (z j) (e j)) = o (a * b * c) :=
    Factor.box_volume ha hb hc (z j) (e j)
  rw [hq]
  calc
    o ((J.card : ℝ) * (a * b * c)) = ∑ j ∈ J, μ (P a b c (z j) (e j)) := by
      simp only [hvol, Finset.sum_const, nsmul_eq_mul]
      exact ENNReal.ofReal_mul (Nat.cast_nonneg J.card) |>.trans
        (by rw [ENNReal.ofReal_natCast]; rfl)
    _ = μ (⋃ j ∈ J, P a b c (z j) (e j)) :=
      (measure_biUnion_finset hJdisj (fun j _ => measurableSet_prism _ _ _ (z j) (e j))).symm
    _ ≤ μ W := measure_mono hsub

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
