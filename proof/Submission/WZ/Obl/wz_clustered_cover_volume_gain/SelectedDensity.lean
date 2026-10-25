-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.SelectedDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.DensityPower
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.FrozenRefinement

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set MeasureTheory Metric
open scoped ENNReal

def selectedCut {N : ℕ} (U : Finset (Fin N)) (X : Set V) (k : Fin N) : Set V :=
  if k ∈ U then X else ∅

lemma selectedCut_measurable {N : ℕ} (U : Finset (Fin N)) {X : Set V}
    (hX : MeasurableSet X) (k : Fin N) : MeasurableSet (selectedCut U X k) := by
  classical
  by_cases hk : k ∈ U <;> simp only [selectedCut, hk, ite_true, ite_false]
  · exact hX
  · exact MeasurableSet.empty

lemma selectedCut_subset {N : ℕ} (U : Finset (Fin N)) (X : Set V) (k : Fin N) :
    selectedCut U X k ⊆ X := by
  classical
  by_cases hk : k ∈ U <;> simp [selectedCut, hk]

lemma sum_selected_cut {n N : ℕ} {S : Finset (Fin n)} (f : Fin n → Fin N)
    (Z : Fin n → Set V) (U : Finset (Fin N)) (X : Set V)
    (hZ : ∀ i, i ∉ S → Z i = ∅) :
    (∑ i, volume (Z i ∩ selectedCut U X (f i))) =
      ∑ i ∈ S.filter (fun i => f i ∈ U), volume (Z i ∩ X) := by
  classical
  rw [Finset.sum_filter]
  have he : ∀ i, volume (Z i ∩ selectedCut U X (f i)) =
      if f i ∈ U then volume (Z i ∩ X) else 0 := by
    intro i
    by_cases hi : f i ∈ U <;> simp [selectedCut, hi]
  rw [Finset.sum_congr rfl (fun i _ => he i)]
  symm
  apply Finset.sum_subset (Finset.subset_univ S)
  intro i _ hi
  simp [hZ i hi]

lemma frozen_shading_mass_positive {δ h : ℝ} {n N : ℕ} {x v : Fin n → V}
    {Y Z : Fin n → Set V} {S : Finset (Fin n)} {ρ : ℝ}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hA : A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f) :
    0 < ∑ i, volume (Z i) := by
  have hYpos : 0 < ∑ i, volume (Y i) :=
    (ENNReal.ofReal_pos.mpr (show 0 < δ ^ h * n * δ ^ 2 by
      have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hA.1
      positivity)).trans_le hA.2.2.2.1
  have hZpos : 0 < ∑ i ∈ S, volume (Z i) :=
    (by positivity : 0 < O (δ ^ h) * ∑ i, volume (Y i)).trans_le hC.2.1
  exact hZpos.trans_le (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (by intros; positivity))

/-- Choose one ball-density class after selecting complete parent fibres.
The loss is measured against the original fine shading mass. -/
theorem selected_ball_density_power {ε : ℝ} (hε : 0 < ε) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ h τ R : ℝ, h + τ ≤ 1 → 0 < R → R ≤ 1 →
    ∀ (n N : ℕ) (x v : Fin n → V) (Y Z : Fin n → Set V) (S : Finset (Fin n))
      (ρ : ℝ) (y w : Fin N → V) (f : Fin n → Fin N) (U : Finset (Fin N)),
    A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y → C δ h n x v Y S Z ρ N y w f →
    O (δ ^ τ) * ∑ i, volume (Y i) ≤ ∑ i ∈ S.filter (fun i => f i ∈ U), volume (Z i) →
    ∃ (lam : ℝ) (X : Set V), MeasurableSet X ∧ X ⊆ ⋃ i, Y i ∧
      δ ^ 4 / 2 ≤ lam ∧ lam ≤ 4 ∧
      (∀ p ∈ X, O (lam * R ^ 3) ≤ volume ((⋃ i, Y i) ∩ ball p R) ∧
        volume ((⋃ i, Y i) ∩ ball p R) ≤ O (2 * lam * R ^ 3)) ∧
      O (δ ^ (τ + ε)) * ∑ i, volume (Y i) ≤
        ∑ i, volume (Z i ∩ selectedCut U X (f i)) := by
  classical
  obtain ⟨d₀, hd₀, hd₀1, H⟩ := regular_ball_density_power hε
  refine ⟨d₀, hd₀, hd₀1, ?_⟩
  intro δ hδ hδd h τ R hη hR hR1 n N x v Y Z S ρ y w f U hA hC hkeep
  let Y' := fun i => Z i ∩ selectedCut U univ (f i)
  have hsum : (∑ i, volume (Y' i)) = ∑ i ∈ S.filter (fun i => f i ∈ U), volume (Z i) := by
    simpa only [Y', inter_univ] using sum_selected_cut f Z U univ (fun i => (hC.1 i).2.2)
  have hYball : (⋃ i, Y i) ⊆ ball 0 1 := iUnion_subset fun i => (hA.2.1 i).2.2.2.trans (hA.2.1 i).2.1
  have hYU (i) : Y' i ⊆ ⋃ j, Y j := by
    intro p hp
    exact mem_iUnion.mpr ⟨i, (hC.1 i).2.1 hp.1⟩
  have hmass : O (δ ^ (h + τ) * n * δ ^ 2) ≤ ∑ i, volume (Y' i) := by
    calc
      _ = O (δ ^ τ) * O (δ ^ h * n * δ ^ 2) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), Real.rpow_add hδ]
        congr 1
        ring
      _ ≤ O (δ ^ τ) * ∑ i, volume (Y i) := mul_le_mul' le_rfl hA.2.2.2.1
      _ ≤ _ := by rwa [hsum]
  obtain ⟨lam, X, hXm, hXU, hlam, hlam4, hden, hret⟩ := H δ hδ hδd (h + τ) R hη hR hR1 n
    (⋃ i, Y i) Y' (MeasurableSet.iUnion fun i => (hA.2.1 i).2.2.1) hYball hYU hmass
  refine ⟨lam, X, hXm, hXU, hlam, hlam4, hden, ?_⟩
  have he (i) : Y' i ∩ X = Z i ∩ selectedCut U X (f i) := by
    by_cases hi : f i ∈ U <;> simp [Y', selectedCut, hi]
  calc
    _ = O (δ ^ ε) * (O (δ ^ τ) * ∑ i, volume (Y i)) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), ← Real.rpow_add hδ]
      congr 3
      ring
    _ ≤ O (δ ^ ε) * ∑ i, volume (Y' i) := mul_le_mul' le_rfl (by rwa [hsum])
    _ ≤ ∑ i, volume (Y' i ∩ X) := hret
    _ = _ := by simp only [he]

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
