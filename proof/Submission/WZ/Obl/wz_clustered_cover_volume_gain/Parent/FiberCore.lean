-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.FiberCore.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoreLevel

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set
open scoped Classical

noncomputable section

def fiberDensityCost {n N : ℕ} (δ H : ℝ) (S : Finset (Fin n)) (f : Fin n → Fin N)
    (U : Finset (Fin N)) (k : Fin N) : ENNReal :=
  if k ∈ U then ENNReal.ofReal (δ ^ H * (S.filter fun i => f i = k).card * δ ^ 2) else 0

theorem sum_fiberDensityCost_le {n N : ℕ} {δ H : ℝ} (hδ : 0 < δ)
    (S : Finset (Fin n)) (f : Fin n → Fin N) (U : Finset (Fin N)) :
    (∑ k, fiberDensityCost δ H S f U k) ≤ ENNReal.ofReal (δ ^ H * n * δ ^ 2) := by
  classical
  have hcard : (∑ k : Fin N, ((S.filter fun i => f i = k).card : ℝ)) = S.card := by
    have hh := Finset.card_eq_sum_card_fiberwise (s := S) (t := Finset.univ) (f := f)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    exact_mod_cast hh.symm
  calc
    _ ≤ ∑ k : Fin N, ENNReal.ofReal (δ ^ H * (S.filter fun i => f i = k).card * δ ^ 2) := by
      apply Finset.sum_le_sum
      intro k _
      simp only [fiberDensityCost]
      split_ifs <;> simp
    _ = ENNReal.ofReal (δ ^ H * S.card * δ ^ 2) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
      congr 1
      rw [← Finset.sum_mul, ← Finset.mul_sum, hcard]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      gcongr
      exact_mod_cast (show S.card ≤ n by simpa using S.card_le_univ)

theorem fiberDensityCost_budget {n N : ℕ} {δ H r : ℝ} (hδ : 0 < δ)
    (S : Finset (Fin n)) (f : Fin n → Fin N) (U : Finset (Fin N))
    (Y : Fin n → Set Space) (hdense : ENNReal.ofReal (δ ^ r * n * δ ^ 2) ≤ ∑ i, volume (Y i))
    (hsmall : 4 * δ ^ (H - r) ≤ 1) :
    (∑ k, fiberDensityCost δ H S f U k) ≤ (1 / 4 : ENNReal) * ∑ i, volume (Y i) := by
  have hquarter : δ ^ (H - r) ≤ 1 / 4 := by linarith
  have hpow : δ ^ H = δ ^ (H - r) * δ ^ r := by rw [← Real.rpow_add hδ]; congr 1; ring
  calc
    _ ≤ ENNReal.ofReal (δ ^ H * n * δ ^ 2) := sum_fiberDensityCost_le hδ S f U
    _ ≤ ENNReal.ofReal ((1 / 4 : ℝ) * (δ ^ r * n * δ ^ 2)) := by
      apply ENNReal.ofReal_le_ofReal
      rw [hpow]
      calc
        _ = δ ^ (H - r) * (δ ^ r * n * δ ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hquarter (by positivity)
    _ = (1 / 4 : ENNReal) * ENNReal.ofReal (δ ^ r * n * δ ^ 2) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    _ ≤ _ := mul_le_mul_right hdense _

theorem supported_fiber_mass {n N : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin N)
    (Y : Fin n → Set Space) (hoff : ∀ i, i ∉ S → Y i = ∅) (k : Fin N) :
    (∑ i ∈ Finset.univ.filter (fun i => f i = k), volume (Y i)) =
      ∑ i ∈ S.filter (fun i => f i = k), volume (Y i) := by
  classical
  symm
  apply Finset.sum_subset
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  · intro i hi hnot
    have hiS : i ∉ S := fun hiS => hnot (Finset.mem_filter.mpr ⟨hiS, (Finset.mem_filter.mp hi).2⟩)
    simp only [hoff i hiS, measure_empty]

/-- The incidence core with precisely the fine-fiber density thresholds required
by the coarse E application. -/
theorem dense_fiber_core {n N : ℕ} {δ H r M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (S : Finset (Fin n)) (f : Fin n → Fin N) (U : Finset (Fin N))
    (Y : Fin n → Set Space) (hY : ∀ i, MeasurableSet (Y i))
    (hfin : ∀ i, volume (Y i) ≠ ⊤) (hoff : ∀ i, i ∉ S → Y i = ∅)
    (hdense : ENNReal.ofReal (δ ^ r * n * δ ^ 2) ≤ ∑ i, volume (Y i))
    (hsmall : 4 * δ ^ (H - r) ≤ 1)
    (hlevel : ∀ p ∈ ⋃ i, Y i, ENNReal.ofReal M ≤ multiplicity Y p) :
    ∃ Z : Fin n → Set Space, (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      (1 / 2 : ENNReal) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i) ∧
      (∀ k ∈ U, (∃ i ∈ S, f i = k ∧ (Z i).Nonempty) →
        ENNReal.ofReal (δ ^ H * (S.filter fun i => f i = k).card * δ ^ 2) ≤
          ∑ i ∈ S with f i = k, volume (Z i)) ∧
      (∀ p ∈ ⋃ i, Z i, ENNReal.ofReal (M / 4) ≤ multiplicity Z p) := by
  obtain ⟨Z, hZ, hmass, hdens, hpoint⟩ := dense_core_of_uniform_level Y hY hfin f
    (fiberDensityCost δ H S f U) hM hlevel (fiberDensityCost_budget hδ S f U Y hdense hsmall)
  have hZoff (i) (hi : i ∉ S) : Z i = ∅ := Set.eq_empty_of_subset_empty (by simpa [hoff i hi] using (hZ i).2)
  refine ⟨Z, hZ, hmass, ?_, hpoint⟩
  intro k hk hocc
  obtain ⟨i, _, hik, hi⟩ := hocc
  have hh := hdens k ⟨i, hik, hi⟩
  simp only [fiberDensityCost, ite_eq_left hk] at hh
  have he := supported_fiber_mass S f Z hZoff k
  exact hh.trans_eq he

end

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
