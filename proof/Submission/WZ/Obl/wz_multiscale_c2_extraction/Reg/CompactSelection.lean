-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.CompactSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.Transfer

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set Metric MeasureTheory
open scoped ENNReal

/-- Compact approximation can be made separately in every shading while retaining
at least half the total mass, including when some shadings have zero measure. -/
theorem compact_shadings {I : Type*} [Fintype I] (Z : I → Set Space)
    (hmeas : ∀ i, MeasurableSet (Z i)) (hfinite : ∀ i, volume (Z i) ≠ ⊤) :
    ∃ K : I → Set Space, (∀ i, K i ⊆ Z i) ∧ (∀ i, IsCompact (K i)) ∧
      (1 / 2 : ENNReal) * (∑ i, volume (Z i)) ≤ ∑ i, volume (K i) := by
  have hex : ∀ i, ∃ K : Set Space, K ⊆ Z i ∧ IsCompact K ∧
      (1 / 2 : ENNReal) * volume (Z i) ≤ volume K := by
    intro i
    by_cases hzero : volume (Z i) = 0
    · exact ⟨∅, empty_subset _, isCompact_empty, by simp [hzero]⟩
    · obtain ⟨K, hKZ, hK, hmass⟩ := (hmeas i).exists_lt_isCompact_of_ne_top
        (hfinite i) (ENNReal.half_lt_self hzero (hfinite i))
      exact ⟨K, hKZ, hK, by simpa only [div_eq_mul_inv, one_mul, mul_comm] using hmass.le⟩
  choose K hKZ hK hmass using hex
  refine ⟨K, hKZ, hK, ?_⟩
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => hmass i)

/-- A positive power of the tube scale absorbs the fixed compact-approximation loss. -/
theorem compact_shadings_with_power {η a b ε σ δ : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y Z : Fin n → Set Space}
    {f g : ℝ → ℝ} {P : Space → Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hηε : η ≤ ε) (hmassbudget : η + (a + b) ≤ ε)
    (hcoverbudget : 6 * δ ^ (-η) ≤ δ ^ (-ε)) (hcompactbudget : δ ^ b ≤ 1 / 2)
    (hfamily : ExtremalFamily σ η δ n x v Y)
    (hgrains : Grains σ δ (δ ^ (-η)) v Y f P)
    (hZ : ∀ i, Z i ⊆ Y i) (hmeas : ∀ i, MeasurableSet (Z i))
    (hmass : ENNReal.ofReal (δ ^ a) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i))
    (hg : NormalizedC2Slope g)
    (happrox : ∀ p ∈ ⋃ i, Z i, |g (p 2) - f (p 2)| ≤ δ) :
    ∃ K : Fin n → Set Space, (∀ i, K i ⊆ Z i) ∧
      ExtremalFamily σ ε δ n x v K ∧
        Grains σ δ (δ ^ (-ε)) v K g P := by
  have hfinite : ∀ i, volume (Z i) ≠ ⊤ := by
    intro i
    have hZi : Z i ⊆ ball (0 : Space) 1 :=
      (hZ i).trans ((hfamily.1.2.2.2.2.2.1 i).trans (hfamily.1.2.2.1 i))
    exact ((measure_mono hZi).trans_lt measure_ball_lt_top).ne
  obtain ⟨K, hKZ, hK, hKmass⟩ := compact_shadings Z hmeas hfinite
  have hhalf : ENNReal.ofReal (δ ^ b) ≤ (1 / 2 : ENNReal) := by
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hcompactbudget
  have hretained : ENNReal.ofReal (δ ^ (a + b)) * (∑ i, volume (Y i)) ≤
      ∑ i, volume (K i) := by
    calc
      ENNReal.ofReal (δ ^ (a + b)) * (∑ i, volume (Y i))
          = ENNReal.ofReal (δ ^ b) *
              (ENNReal.ofReal (δ ^ a) * (∑ i, volume (Y i))) := by
                rw [Real.rpow_add hδ, ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
                ac_rfl
      _ ≤ (1 / 2 : ENNReal) * (∑ i, volume (Z i)) := mul_le_mul' hhalf hmass
      _ ≤ ∑ i, volume (K i) := hKmass
  have hKY : ∀ i, K i ⊆ Y i := fun i => (hKZ i).trans (hZ i)
  have happroxK : ∀ p ∈ ⋃ i, K i, |g (p 2) - f (p 2)| ≤ δ :=
    fun p hp => happrox p ((iUnion_mono hKZ) hp)
  obtain ⟨hfamilyK, _, hgrainsK⟩ := regularize_family hδ hδ1 hσ0 hσ1 hηε
    hmassbudget hcoverbudget hfamily hgrains hKY hK hretained hg happroxK
  exact ⟨K, hKZ, hfamilyK, hgrainsK⟩

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
