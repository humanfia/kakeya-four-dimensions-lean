-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.CommonCut.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainTransfer

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement (Space)

lemma assignedFiber_common_cut {n N : ℕ} (f : Fin n → Fin N) (Y : Fin n → Set Space)
    (C : Fin N → Set Space) (k : Fin N) :
    assignedFiber f (fun i => Y i ∩ C (f i)) k = assignedFiber f Y k ∩ C k := by
  ext p
  constructor
  · rintro ⟨i, hi, hpY, hpC⟩
    exact ⟨⟨i, hi, hpY⟩, hi ▸ hpC⟩
  · rintro ⟨⟨i, hi, hpY⟩, hpC⟩
    exact ⟨i, hi, hpY, hi.symm ▸ hpC⟩

lemma grain_fine_mass_bounds {n N L : ℕ} (f : Fin n → Fin N) (γ : Fin L → Fin N)
    (Z : Fin n → Set Space) (H : Fin L → Set Space) {m M : ℝ}
    (hm : 0 ≤ m) (hM : 0 ≤ M)
    (hZm : ∀ i, MeasurableSet (Z i)) (hHm : ∀ j, MeasurableSet (H j))
    (hdisj : ∀ i j, i ≠ j → γ i = γ j → Disjoint (H i) (H j))
    (heq : ∀ k, assignedFiber γ H k = assignedFiber f Z k)
    (hlevel : ∀ k p, p ∈ assignedFiber f Z k →
      m ≤ fiberBodyCount f Z k p ∧ fiberBodyCount f Z k p ≤ M) :
    ENNReal.ofReal m * ∑ j, volume (H j) ≤ ∑ i, volume (Z i) ∧
      ∑ i, volume (Z i) ≤ ENNReal.ofReal M * ∑ j, volume (H j) := by
  let C := assignedFiber γ H
  have hrestr : (fun i => Z i ∩ C (f i)) = Z := by
    funext i
    apply inter_eq_left.mpr
    intro p hp
    rw [show C (f i) = assignedFiber f Z (f i) from heq (f i)]
    exact ⟨i, rfl, hp⟩
  have hpoint (p : Space) : m * bodyCount H p ≤ bodyCount Z p ∧
      bodyCount Z p ≤ M * bodyCount H p := by
    have hh := restrict_fiber_count_bounds f Z C
      (fun k p hp => hlevel k p ((heq k).subset hp)) p
    rw [hrestr] at hh
    simpa only [C, bodyCount_assignedFiber γ H hdisj p] using hh
  exact ⟨body_mass_le_of_count hHm hZm hm (fun p => (hpoint p).1),
    body_mass_le_mul_of_count hZm hHm hM (fun p => (hpoint p).2)⟩

/-- A common measurable cut in each parent fibre transfers retained fine
incidence mass to retained grain mass, losing only the factor two of G. -/
theorem common_cut_retains_grain_mass {n N L : ℕ} (f : Fin n → Fin N) (γ : Fin L → Fin N)
    (Z : Fin n → Set Space) (H : Fin L → Set Space) (C : Fin N → Set Space) {m t : ℝ}
    (hm : 0 < m) (ht : 0 ≤ t)
    (hZm : ∀ i, MeasurableSet (Z i)) (hHm : ∀ j, MeasurableSet (H j))
    (hCm : ∀ k, MeasurableSet (C k))
    (hdisj : ∀ i j, i ≠ j → γ i = γ j → Disjoint (H i) (H j))
    (heq : ∀ k, assignedFiber γ H k = assignedFiber f Z k)
    (hlevel : ∀ k p, p ∈ assignedFiber f Z k →
      m ≤ fiberBodyCount f Z k p ∧ fiberBodyCount f Z k p ≤ 2 * m)
    (hretain : ENNReal.ofReal t * ∑ i, volume (Z i) ≤ ∑ i, volume (Z i ∩ C (f i))) :
    ENNReal.ofReal (t / 2) * ∑ j, volume (H j) ≤ ∑ j, volume (H j ∩ C (γ j)) := by
  let Z' := fun i => Z i ∩ C (f i)
  let H' := fun j => H j ∩ C (γ j)
  have hZ'm (i) : MeasurableSet (Z' i) := (hZm i).inter (hCm (f i))
  have hH'm (j) : MeasurableSet (H' j) := (hHm j).inter (hCm (γ j))
  have hdisj' : ∀ i j, i ≠ j → γ i = γ j → Disjoint (H' i) (H' j) :=
    fun i j hij he => (hdisj i j hij he).mono inter_subset_left inter_subset_left
  have heq' (k) : assignedFiber γ H' k = assignedFiber f Z' k := by
    rw [assignedFiber_common_cut, assignedFiber_common_cut, heq k]
  have hlevel' (k p) (hp : p ∈ assignedFiber f Z' k) :
      m ≤ fiberBodyCount f Z' k p ∧ fiberBodyCount f Z' k p ≤ 2 * m := by
    have hp' : p ∈ assignedFiber f Z k ∩ C k := by rwa [assignedFiber_common_cut] at hp
    change m ≤ fiberBodyCount f (fun i => Z i ∩ C (f i)) k p ∧ _
    rw [fiberBodyCount_restrict, indicator_of_mem hp'.2]
    exact hlevel k p hp'.1
  have horig := (grain_fine_mass_bounds f γ Z H hm.le (by positivity) hZm hHm hdisj heq hlevel).1
  have hnew := (grain_fine_mass_bounds f γ Z' H' hm.le (by positivity) hZ'm hH'm hdisj' heq' hlevel').2
  apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr (show 0 < 2 * m by positivity)).ne'
    ENNReal.ofReal_ne_top).mp
  calc
    _ = ENNReal.ofReal t * (ENNReal.ofReal m * ∑ j, volume (H j)) := by
      rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * m),
        ← ENNReal.ofReal_mul ht]
      congr 2
      ring
    _ ≤ ENNReal.ofReal t * ∑ i, volume (Z i) := mul_le_mul' le_rfl horig
    _ ≤ ∑ i, volume (Z' i) := hretain
    _ ≤ _ := hnew

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
