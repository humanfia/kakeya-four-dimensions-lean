-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.PackingDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.LocalPrismDensity

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open MeasureTheory Set

/-- A packing bound and a matching lower union-volume bound give average
piece density. The common volume scale may be anisotropic. -/
theorem prism_piece_density_of_packing {a b c K B lam : ℝ} {n : ℕ}
    (hK : 0 ≤ K) (hlam : 0 ≤ lam)
    (e : V ≃ₗᵢ[ℝ] V) (F : Finset V) (Y Z : Fin n → Set V) (H : V → Set V)
    (hY : ∀ i, MeasurableSet (Y i))
    (hZ : ∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i)
    (hdisj : (↑F : Set V).PairwiseDisjoint (fun z => P a b c z e))
    (hH : ∀ z ∈ F, MeasurableSet (H z) ∧ H z ⊆ P a b c z e)
    (hunion : (⋃ z ∈ F, H z) = ⋃ i, Z i)
    {M D : ENNReal} (hM0 : M ≠ 0) (hMtop : M ≠ ⊤)
    (hlower : ∀ p ∈ ⋃ i, Y i, M ≤ multiplicity Y p)
    (hupper : ∀ p, multiplicity Y p ≤ 2 * M)
    (hmass : (∑ i, μ (Y i)) ≤ D * ∑ i, μ (Z i))
    (hpacking : o ((F.card : ℝ) * (a * b * c)) ≤ o (K * B))
    (hvol : o (lam * B) ≤ μ (⋃ i, Y i)) :
    o (lam * F.card * (a * b * c)) ≤ (o (2 * K) * D) * ∑ z ∈ F, μ (H z) := by
  have hupperZ (p : V) : multiplicity Z p ≤ 2 * M :=
    (multiplicity_mono (fun i => (hZ i).2) p).trans (hupper p)
  have hret := uniform_volume_retention hY (fun i => (hZ i).1)
    hM0 hMtop hlower hupperZ hmass
  have hHdisj : (↑F : Set V).PairwiseDisjoint H := by
    intro z hz z' hz' hne
    exact (hdisj hz hz' hne).mono (hH z hz).2 (hH z' hz').2
  have hsum : (∑ z ∈ F, μ (H z)) = μ (⋃ i, Z i) :=
    (measure_biUnion_finset hHdisj (fun z hz => (hH z hz).1)).symm.trans (congrArg μ hunion)
  calc
    o (lam * F.card * (a * b * c)) = o lam * o ((F.card : ℝ) * (a * b * c)) := by
      dsimp only [o]
      rw [← ENNReal.ofReal_mul hlam]
      congr 1
      ring
    _ ≤ o lam * o (K * B) := mul_le_mul_right hpacking _
    _ = o K * o (lam * B) := by
      dsimp only [o]
      rw [← ENNReal.ofReal_mul hlam, ← ENNReal.ofReal_mul hK]
      congr 1
      ring
    _ ≤ o K * μ (⋃ i, Y i) := mul_le_mul_right hvol _
    _ ≤ o K * ((D * 2) * μ (⋃ i, Z i)) := mul_le_mul_right hret _
    _ = (o (2 * K) * D) * ∑ z ∈ F, μ (H z) := by
      rw [hsum]
      change ENNReal.ofReal K * ((D * 2) * μ (⋃ i, Z i)) =
        (ENNReal.ofReal (2 * K) * D) * μ (⋃ i, Z i)
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
      norm_num only [Nat.cast_ofNat]
      change ENNReal.ofReal K * ((D * (2 : ENNReal)) * μ (⋃ i, Z i)) =
        ((2 : ENNReal) * ENNReal.ofReal K * D) * μ (⋃ i, Z i)
      ring

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
