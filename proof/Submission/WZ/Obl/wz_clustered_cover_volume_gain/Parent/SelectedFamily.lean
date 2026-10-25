-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.SelectedFamily.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FiberMultiplicity
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoverWeights

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.SelectedFamily

open MeasureTheory Set Finset Interfaces

noncomputable section

/-- Enumeration of a finite selected family in the original indexing. -/
def index {n : ℕ} (S : Finset (Fin n)) (i : Fin S.card) : Fin n :=
  (S.equivFin.symm i : S).val

theorem index_mem {n : ℕ} (S : Finset (Fin n)) (i : Fin S.card) : index S i ∈ S :=
  (S.equivFin.symm i).property

theorem index_injective {n : ℕ} (S : Finset (Fin n)) : Function.Injective (index S) := by
  intro a b hab
  exact S.equivFin.symm.injective (Subtype.ext hab)

/-- The fine tubes lying over a selected family of coarse tubes. -/
def fine {n N : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin N) (Q : Finset (Fin N)) :
    Finset (Fin n) := S.filter fun i => f i ∈ Q

/-- The original assignment expressed in both new finite index sets. -/
def assign {n N : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin N) (Q : Finset (Fin N))
    (a : Fin (fine S f Q).card) : Fin Q.card :=
  Q.equivFin ⟨f (index (fine S f Q) a), (Finset.mem_filter.mp (index_mem (fine S f Q) a)).2⟩

theorem index_assign {n N : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin N)
    (Q : Finset (Fin N)) (a : Fin (fine S f Q).card) :
    index Q (assign S f Q a) = f (index (fine S f Q) a) := by
  simp only [index, assign, Equiv.symm_apply_apply]

theorem assign_eq_iff {n N : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin N)
    (Q : Finset (Fin N)) (a : Fin (fine S f Q).card) (k : Fin Q.card) :
    assign S f Q a = k ↔ f (index (fine S f Q) a) = index Q k := by
  rw [← index_assign S f Q a]
  exact (index_injective Q).eq_iff.symm

/-- The enumeration keeps each selected complete fiber's predicate count
exactly, including the counts appearing in the below-slab condition. -/
theorem fiber_count {n N : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin N)
    (Q : Finset (Fin N)) (k : Fin Q.card) (r : Fin n → Prop) :
    q {a | assign S f Q a = k ∧ r (index (fine S f Q) a)} =
      q {i | i ∈ S ∧ f i = index Q k ∧ r i} := by
  classical
  apply congrArg (fun a : ℕ => (a : ℝ))
  apply Set.ncard_congr (fun a _ => index (fine S f Q) a)
  · intro a ha
    exact ⟨(Finset.mem_filter.mp (index_mem (fine S f Q) a)).1,
      (assign_eq_iff S f Q a k).mp ha.1, ha.2⟩
  · intro a b _ _ hab
    exact index_injective (fine S f Q) hab
  · intro i hi
    have hiP : i ∈ fine S f Q := by
      apply Finset.mem_filter.mpr
      refine ⟨hi.1, ?_⟩
      rw [hi.2.1]
      exact index_mem Q k
    refine ⟨(fine S f Q).equivFin ⟨i, hiP⟩, ?_, ?_⟩
    · refine ⟨(assign_eq_iff S f Q _ k).mpr ?_, ?_⟩
      · simpa only [index, Equiv.symm_apply_apply] using hi.2.1
      · simpa only [index, Equiv.symm_apply_apply] using hi.2.2
    · simp only [index, Equiv.symm_apply_apply]

/-- Admissibility and both counting bounds for an enumerated subshading.
Only the explicit old/new cardinality ratio affects the Frostman bound. -/
theorem admissible_subshading {δ η η' m l l' : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} (P : Finset (Fin n))
    (hA : A δ η m l n x v Y) (hP : P.Nonempty)
    (hZ : ∀ i ∈ P, MeasurableSet (Z i) ∧ Z i ⊆ Y i)
    (hdense : o (δ ^ η' * P.card * δ ^ 2) ≤ ∑ i ∈ P, μ (Z i))
    (hratio : l * n ≤ l' * P.card) :
    A δ η' m l' P.card (x ∘ index P) (v ∘ index P) (Z ∘ index P) := by
  refine ⟨Finset.card_pos.mpr hP, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    exact ⟨(hA.2.1 _).1, (hA.2.1 _).2.1, (hZ _ (index_mem P a)).1,
      (hZ _ (index_mem P a)).2.trans (hA.2.1 _).2.2.2⟩
  · intro a b hab
    exact hA.2.2.1 _ _ ((index_injective P).ne hab)
  · have he : (∑ a, μ ((Z ∘ index P) a)) = ∑ i ∈ P, μ (Z i) :=
      sum_comp_equivFin P (fun i => μ (Z i))
    rwa [he]
  · exact k_comp_injective hA.2.2.2.2.1 (index_injective P)
  · intro u t r hu hr
    apply le_trans _ ((hA.2.2.2.2.2 u t r hu hr).trans ?_)
    · apply ENNReal.ofReal_le_ofReal
      apply Nat.cast_le.mpr
      exact Set.ncard_le_ncard_of_injOn (index P) (fun _ hi => hi)
        (index_injective P).injOn (Set.toFinite _)
    · gcongr
      exact ENNReal.ofReal_le_ofReal hratio

/-- Enumerating a union of complete fibers preserves the full cover interface.
The new shading is indexed by all selected fine tubes; its retention is then
automatic. The old/new coarse cardinality ratio pays for the above-slab count. -/
theorem cover_complete_fibers {δ h h' ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N} (Q : Finset (Fin N))
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh' : 0 ≤ h') (hh : h ≤ h')
    (hC : C δ h n x v Y S Z ρ N y w f)
    (hratio : δ ^ (-h) * N ≤ δ ^ (-h') * Q.card) :
    C δ h' (fine S f Q).card (x ∘ index (fine S f Q)) (v ∘ index (fine S f Q))
      (Z ∘ index (fine S f Q)) Finset.univ (Z ∘ index (fine S f Q))
      ρ Q.card (y ∘ index Q) (w ∘ index Q) (assign S f Q) := by
  classical
  have herr : δ ^ (-h) ≤ δ ^ (-h') :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hiS (a : Fin (fine S f Q).card) : index (fine S f Q) a ∈ S :=
    (Finset.mem_filter.mp (index_mem (fine S f Q) a)).1
  have htotal (k : Fin Q.card) :
      q {a | assign S f Q a = k} = q {i | i ∈ S ∧ f i = index Q k} := by
    simpa only [and_true] using fiber_count S f Q k (fun _ => True)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    exact ⟨(hC.1 _).1, Set.Subset.rfl, by simp⟩
  · calc
      _ ≤ 1 * ∑ a, μ ((Z ∘ index (fine S f Q)) a) := by
        gcongr
        exact (ENNReal.ofReal_le_one).mpr (Real.rpow_le_one hδ.le hδ1 hh')
      _ = _ := one_mul _
  · intro k
    exact hC.2.2.1 (index Q k)
  · intro a _
    have ht := hC.2.2.2.1 _ (hiS a)
    simpa only [Function.comp_apply, ← index_assign S f Q a] using ht
  · intro u t r hu hr
    apply le_trans _ ((hC.2.2.2.2.1 u t r hu hr).trans ?_)
    · apply ENNReal.ofReal_le_ofReal
      apply Nat.cast_le.mpr
      exact Set.ncard_le_ncard_of_injOn (index Q) (fun _ hi => hi)
        (index_injective Q).injOn (Set.toFinite _)
    · gcongr
      exact ENNReal.ofReal_le_ofReal hratio
  · intro k u t r hu hr
    simp only [Finset.mem_univ, true_and, Function.comp_apply]
    rw [fiber_count S f Q k (fun i => T δ (x i) (v i) ⊆
      T (2 * ρ) (y (index Q k) - (1 / 2 : ℝ) • w (index Q k)) (2 • w (index Q k)) ∩
        {p | |inner ℝ u p - t| ≤ r}), htotal]
    apply (hC.2.2.2.2.2.1 (index Q k) u t r hu hr).trans
    gcongr
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right herr (Nat.cast_nonneg _)
  · intro k k'
    simp only [Finset.mem_univ, true_and, htotal]
    exact (hC.2.2.2.2.2.2.1 (index Q k) (index Q k')).trans
      (mul_le_mul_of_nonneg_right herr (Nat.cast_nonneg _))
  · intro k k' hne
    exact hC.2.2.2.2.2.2.2.1 _ _ ((index_injective Q).ne hne)
  · intro a _
    apply le_trans _ ((hC.2.2.2.2.2.2.2.2 _ (hiS a)).trans herr)
    apply Nat.cast_le.mpr
    exact Set.ncard_le_ncard_of_injOn (index Q) (fun _ hi => hi)
      (index_injective Q).injOn (Set.toFinite _)

end
end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.SelectedFamily
