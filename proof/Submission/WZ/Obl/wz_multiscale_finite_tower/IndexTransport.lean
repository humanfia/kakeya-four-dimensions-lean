-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.IndexTransport.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.HierarchyCounts
import Submission.WZ.Obl.wz_multiscale_finite_tower.PhysicalEstimates

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives (ConvexCount SlabBound doubled)
open WangZahlLot.Obl.wz_tower_balanced_refinement (enumerate enumerate_injective enumerate_mem exists_enumerate)

lemma predicate_enumeration {n : ℕ} (P : Fin n → Prop) :
    ∃ m : ℕ, ∃ e : Fin m → Fin n,
      m = {i | P i}.ncard ∧ Function.Injective e ∧ Set.range e = {i | P i} := by
  classical
  let S := Finset.univ.filter P
  have he : (S : Set (Fin n)) = {i | P i} := by ext i; simp [S]
  refine ⟨S.card, enumerate S, ?_, enumerate_injective S, ?_⟩
  · rw [← he, Set.ncard_coe_finset]
  · rw [← he]
    ext i
    constructor
    · rintro ⟨j, rfl⟩
      exact enumerate_mem S j
    · intro hi
      exact exists_enumerate S hi

lemma convexCount_reindex {n m : ℕ} {s L : ℝ} {P : Fin n → Prop} {Q : Fin m → Prop}
    {U : Fin n → Set Space} (h : ConvexCount s L P U) (e : Fin m → Fin n)
    (he : Function.Injective e) (hP : ∀ i, Q i → P (e i)) :
    ConvexCount s L Q (U ∘ e) := by
  intro W hW
  have hc : {i | Q i ∧ (U ∘ e) i ⊆ W}.ncard ≤ {i | P i ∧ U i ⊆ W}.ncard :=
    Set.ncard_le_ncard_of_injOn e (fun i hi => ⟨hP i hi.1, hi.2⟩) he.injOn
  exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc)
    (sq_nonneg s))).trans (h W hW)

lemma slabBound_reindex {n m : ℕ} {L L' : ℝ} {D : Set Space}
    {P : Fin n → Prop} {Q : Fin m → Prop} {U : Fin n → Set Space}
    (h : SlabBound D L P U) (e : Fin m → Fin n) (he : Function.Injective e)
    (hP : ∀ i, Q i → P (e i))
    (hL : L * {i | P i}.ncard ≤ L' * {i | Q i}.ncard) :
    SlabBound D L' Q (U ∘ e) := by
  intro u t r hu hr
  have hc : {i | Q i ∧ (U ∘ e) i ⊆ D ∩ {p | |inner ℝ u p - t| ≤ r}}.ncard ≤
      {i | P i ∧ U i ⊆ D ∩ {p | |inner ℝ u p - t| ≤ r}}.ncard :=
    Set.ncard_le_ncard_of_injOn e (fun i hi => ⟨hP i hi.1, hi.2⟩) he.injOn
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr hc)) le_rfl).trans
    ((h u t r hu hr).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hL) le_rfl))

/-- Enumeration of one occupied fibre gives precisely the physical frame required
by the rescaled alternatives. -/
theorem HierarchyControl.physical_fibre {d θ g gap : ℝ} {J : ℕ} {T : TubeHierarchy J}
    (H : HierarchyControl d θ g gap T) (hd : 0 < d) {j : ℕ} (hj : j < J)
    (Y : Fin (T.layer (j + 1)).card → Set Space)
    (hYm : ∀ i, MeasurableSet (Y i))
    (hYT : ∀ i, Y i ⊆ Tube (T.layer (j + 1)).radius
      ((T.layer (j + 1)).position i) ((T.layer (j + 1)).direction i))
    (hden : ∀ i, ENNReal.ofReal (d ^ θ * (T.layer (j + 1)).radius ^ 2) ≤ volume (Y i))
    (k : Fin (T.layer j).card) :
    ∃ m : ℕ, ∃ e : Fin m → Fin (T.layer (j + 1)).card,
      m = {i | T.parent j i = k}.ncard ∧ Function.Injective e ∧
      Set.range e = {i | T.parent j i = k} ∧
      PhysicalFrame d (T.layer j).radius (T.layer (j + 1)).radius θ
        ((T.layer j).position k) ((T.layer j).direction k) m
        ((T.layer (j + 1)).position ∘ e) ((T.layer (j + 1)).direction ∘ e) (Y ∘ e) := by
  classical
  obtain ⟨m, e, hm, he, hrange⟩ := predicate_enumeration (fun i => T.parent j i = k)
  have hep (i : Fin m) : T.parent j (e i) = k := by
    have : e i ∈ Set.range e := ⟨i, rfl⟩
    simpa only [hrange, mem_setOf_eq] using this
  have hmpos : 0 < m := by
    rw [hm, Set.ncard_pos]
    obtain ⟨i, hi⟩ := T.parent_surjective hj k
    exact ⟨i, hi⟩
  refine ⟨m, e, hm, he, hrange, hmpos, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨(T.layer (j + 1)).unit (e i), ?_, hYm (e i), hYT (e i)⟩
    simpa only [Function.comp_apply, hep i] using H.containment j hj (e i)
  · calc
      _ = ∑ _i : Fin m, ENNReal.ofReal (d ^ θ * (T.layer (j + 1)).radius ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
        congr 1
        ring
      _ ≤ _ := Finset.sum_le_sum fun i _ => hden (e i)
  · exact convexCount_reindex (H.count j hj k) e he (fun i _ => hep i)
  · apply slabBound_reindex (H.slab j hj k) e he (fun i _ => hep i)
    simp only [Set.ofPred_true, Set.ncard_univ, Nat.card_fin, hm]
    exact le_rfl

end WangZahlLot.Obl.wz_multiscale_finite_tower
