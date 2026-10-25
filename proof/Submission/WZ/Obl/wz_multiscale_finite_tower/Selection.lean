-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.Selection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Restriction
import Submission.WZ.Obl.wz_multiscale_finite_tower.Refinement
import Submission.WZ.Obl.wz_tower_balanced_refinement.Reindex

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_tower_balanced_refinement
  (enumerate enumerate_mem enumerate_injective sum_enumerate)

/-- A weighted bottom selection of a tower gives an admissible retained tower; the density and
mass losses are both paid from the target error budget. -/
theorem retained_tower_of_shading_subset {d η θ ζ ε g M L : ℝ} {B n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hd : 0 < d) (hd1 : d ≤ 1) (hη : 0 ≤ η) (hηζ : η + ζ ≤ ε) (hθε : θ ≤ ε)
    (hA : Admissible d η M L n x v Y) (hT : Tower false d (d ^ (-θ)) g B n x v)
    (S : Finset (Fin n)) (hS : S.Nonempty)
    (Z : Fin n → Set Space) (hZm : ∀ i, MeasurableSet (Z i)) (hZY : ∀ i, Z i ⊆ Y i)
    (hmass : ENNReal.ofReal (d ^ ζ) * (∑ i, volume (Y i)) ≤ ∑ i ∈ S, volume (Z i)) :
    RetainedTower d ε g B n Y := by
  classical
  let m := S.card
  let f : Fin m → Fin n := enumerate S
  have hm : 0 < m := Finset.card_pos.mpr hS
  have hf : Function.Injective f := enumerate_injective S
  have hmn : m ≤ n := by simpa [m] using Finset.card_le_univ S
  have hsum : (∑ i : Fin m, volume (Z (f i))) = ∑ i ∈ S, volume (Z i) :=
    sum_enumerate S (fun i => volume (Z i))
  have hmass' : ENNReal.ofReal (d ^ ζ) * (∑ i, volume (Y i)) ≤
      ∑ i : Fin m, volume (Z (f i)) := by rwa [hsum]
  have hden : ENNReal.ofReal (d ^ ε * m * d ^ 2) ≤ ∑ i : Fin m, volume (Z (f i)) := by
    apply le_trans _ ((mul_le_mul_of_nonneg_left hA.2.2.2.1 (by positivity)).trans hmass')
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _)]
    apply ENNReal.ofReal_le_ofReal
    have hp : d ^ ε ≤ d ^ (η + ζ) := Real.rpow_le_rpow_of_exponent_ge hd hd1 hηζ
    calc
      d ^ ε * m * d ^ 2 ≤ d ^ (η + ζ) * n * d ^ 2 := by gcongr
      _ = d ^ ζ * (d ^ η * n * d ^ 2) := by rw [Real.rpow_add hd]; ring
  let L' : ℝ := L * n / m
  have hL' : L * n ≤ L' * m := by
    dsimp [L']
    rw [div_mul_cancel₀ _ (ne_of_gt (Nat.cast_pos.mpr hm))]
  have hA' : Admissible d ε M L' m (x ∘ f) (v ∘ f) (Z ∘ f) :=
    hA.comp f hf hm (Z ∘ f) (fun i => hZm (f i))
      (fun i => hZY (f i)) hden hL'
  refine ⟨m, x ∘ f, v ∘ f, Z ∘ f, M, L', hA', ?_, ?_, ?_⟩
  · exact Set.iUnion_subset fun i => Set.subset_iUnion_of_subset (f i) (hZY (f i))
  · apply le_trans _ hmass'
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith))) (by positivity)
  · exact (hT.restrict hA.1 hm f hf).mono hd hd1
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)) le_rfl le_rfl

/-- The special case retaining each selected shading unchanged. -/
theorem retained_tower_of_subset {d η θ ζ ε g M L : ℝ} {B n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hd : 0 < d) (hd1 : d ≤ 1) (hη : 0 ≤ η) (hηζ : η + ζ ≤ ε) (hθε : θ ≤ ε)
    (hA : Admissible d η M L n x v Y) (hT : Tower false d (d ^ (-θ)) g B n x v)
    (S : Finset (Fin n)) (hS : S.Nonempty)
    (hmass : ENNReal.ofReal (d ^ ζ) * (∑ i, volume (Y i)) ≤ ∑ i ∈ S, volume (Y i)) :
    RetainedTower d ε g B n Y :=
  retained_tower_of_shading_subset hd hd1 hη hηζ hθε hA hT S hS Y
    (fun i => (hA.2.1 i).2.2.1) (fun _ => Set.Subset.rfl) hmass

end WangZahlLot.Obl.wz_multiscale_finite_tower
