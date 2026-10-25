-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.LocalPrismDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.LocalPrismPacking
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.UniformVolumeRetention
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.CoreLevel

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

/-- Uniform multiplicity and a lower union-volume bound give the exact
average-density estimate for disjoint prism pieces in one thin slab. -/
theorem local_prism_piece_average_density {a b c r w t lam : ℝ} {n : ℕ} {p₀ : V}
    (ha : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hw : 0 ≤ w)
    (hwa : w ≤ a) (hr : 0 ≤ r) (hb : b ≤ r) (hc : c ≤ r) (hlam : 0 ≤ lam)
    (e : V ≃ₗᵢ[ℝ] V) (F : Finset V) (Y Z : Fin n → Set V) (H : V → Set V)
    (hY : ∀ i, MeasurableSet (Y i))
    (hZ : ∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i)
    (hdisj : (↑F : Set V).PairwiseDisjoint (fun z => P a b c z e))
    (hH : ∀ z ∈ F, MeasurableSet (H z) ∧ H z ⊆ P a b c z e ∧ (H z).Nonempty)
    (hslab : (⋃ i, Y i) ⊆ ball p₀ r ∩ {p | |e (p - p₀) 0 - t| ≤ w})
    (hunion : (⋃ z ∈ F, H z) = ⋃ i, Z i)
    {M D : ENNReal} (hM0 : M ≠ 0) (hMtop : M ≠ ⊤)
    (hlower : ∀ p ∈ ⋃ i, Y i, M ≤ multiplicity Y p)
    (hupper : ∀ p, multiplicity Y p ≤ 2 * M)
    (hmass : (∑ i, μ (Y i)) ≤ D * ∑ i, μ (Z i))
    (hvol : o (lam * a * r ^ 2) ≤ μ (⋃ i, Y i)) :
    o (lam * F.card * (a * b * c)) ≤ (128 * D) * ∑ z ∈ F, μ (H z) := by
  have hsubset : (⋃ i, Z i) ⊆ ⋃ i, Y i := iUnion_mono fun i => (hZ i).2
  have hmeet (z : V) (hz : z ∈ F) :
      (P a b c z e ∩ (ball p₀ r ∩ {p | |e (p - p₀) 0 - t| ≤ w})).Nonempty := by
    obtain ⟨p, hp⟩ := (hH z hz).2.2
    have hpZ : p ∈ ⋃ i, Z i := hunion ▸ mem_iUnion₂.mpr ⟨z, hz, hp⟩
    exact ⟨p, (hH z hz).2.1 hp, hslab (hsubset hpZ)⟩
  have hpacking := prism_packing_in_local_slab ha hb0 hc0 hr hw hb hc e F hdisj hmeet
  have hpacking' : o ((F.card : ℝ) * (a * b * c)) ≤ o (64 * a * r ^ 2) :=
    hpacking.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (by linarith : 32 * (w + a) ≤ 64 * a) (sq_nonneg r)))
  have hupperZ (p : V) : multiplicity Z p ≤ 2 * M :=
    (multiplicity_mono (fun i => (hZ i).2) p).trans (hupper p)
  have hret := uniform_volume_retention hY (fun i => (hZ i).1)
    hM0 hMtop hlower hupperZ hmass
  have hHdisj : (↑F : Set V).PairwiseDisjoint H := by
    intro z hz z' hz' hne
    exact (hdisj hz hz' hne).mono (hH z hz).2.1 (hH z' hz').2.1
  have hsum : (∑ z ∈ F, μ (H z)) = μ (⋃ i, Z i) := by
    exact (measure_biUnion_finset hHdisj (fun z hz => (hH z hz).1)).symm.trans
      (congrArg μ hunion)
  calc
    o (lam * F.card * (a * b * c)) = o lam * o ((F.card : ℝ) * (a * b * c)) := by
      dsimp only [o]
      rw [← ENNReal.ofReal_mul hlam]
      congr 1
      ring
    _ ≤ o lam * o (64 * a * r ^ 2) := mul_le_mul_right hpacking' _
    _ = 64 * o (lam * a * r ^ 2) := by
      change ENNReal.ofReal lam * ENNReal.ofReal (64 * a * r ^ 2) =
        64 * ENNReal.ofReal (lam * a * r ^ 2)
      rw [← ENNReal.ofReal_mul hlam, ← ENNReal.ofReal_ofNat 64,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64)]
      congr 1
      ring
    _ ≤ 64 * μ (⋃ i, Y i) := mul_le_mul_right hvol _
    _ ≤ 64 * ((D * 2) * μ (⋃ i, Z i)) := mul_le_mul_right hret _
    _ = (128 * D) * ∑ z ∈ F, μ (H z) := by
      rw [hsum]
      calc
        _ = ((64 * 2) * D) * μ (⋃ i, Z i) := by ac_rfl
        _ = _ := by norm_num

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
