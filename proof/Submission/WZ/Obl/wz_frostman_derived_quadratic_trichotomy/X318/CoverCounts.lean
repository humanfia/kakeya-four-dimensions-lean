-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.CoverCounts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.Basic
import Submission.WZ.Obl.wz_concentrated_convex_factorization.Factoring

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file CoverCounts.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory
open WangZahlLot.Obl.wz_concentrated_convex_factorization (incidence_sum ncard_fintype)

attribute [local instance] Classical.propDecidable

/-- The number of members of a finite indexed family contained in a set. -/
noncomputable def contained {n : ℕ} (A : Fin n → Set Space) (U : Set Space) : ℕ :=
  ncard {i | A i ⊆ U}

lemma contained_eq_card {n : ℕ} (A : Fin n → Set Space) (U : Set Space) :
    contained A U = (Finset.univ.filter fun i => A i ⊆ U).card := by
  classical
  exact ncard_fintype _

/-- Double counting incidences, restricted to containers lying inside the test set. -/
lemma cover_incidence_le {n p : ℕ} (A : Fin n → Set Space) (P : Fin p → Set Space)
    {D : ℝ} (_hD : 0 ≤ D)
    (hdegree : ∀ i, (ncard {j | A i ⊆ P j} : ℝ) ≤ D) (U : Set Space) :
    (∑ j ∈ Finset.univ.filter (fun j => P j ⊆ U), (contained A (P j) : ℝ)) ≤
      D * contained A U := by
  classical
  let I := Finset.univ.filter fun i => A i ⊆ U
  let J := Finset.univ.filter fun j => P j ⊆ U
  have hcount (j) (hj : j ∈ J) :
      (I.filter fun i => A i ⊆ P j).card = contained A (P j) := by
    rw [contained_eq_card]
    congr 1
    ext i
    have hPU : P j ⊆ U := (Finset.mem_filter.mp hj).2
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨And.right, fun h => ⟨h.trans hPU, h⟩⟩
  calc
    _ = ∑ j ∈ J, ((I.filter fun i => A i ⊆ P j).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hcount j hj]
    _ = ∑ i ∈ I, ((J.filter fun j => A i ⊆ P j).card : ℝ) := by
      exact_mod_cast (incidence_sum I J (fun i j => A i ⊆ P j)).symm
    _ ≤ ∑ _i ∈ I, D := by
      apply Finset.sum_le_sum
      intro i hi
      have hs : J.filter (fun j => A i ⊆ P j) ⊆
          Finset.univ.filter (fun j => A i ⊆ P j) :=
        Finset.filter_subset_filter _ (Finset.subset_univ _)
      have hd := hdegree i
      rw [ncard_fintype] at hd
      exact (Nat.cast_le.mpr (Finset.card_le_card hs)).trans hd
    _ = D * contained A U := by rw [contained_eq_card]; simp [I, mul_comm]

/-- Balance and coverage give a uniform lower bound on every fibre. -/
lemma cover_fibre_lower {n p : ℕ} (A : Fin n → Set Space) (P : Fin p → Set Space)
    {L : ℝ} (hcover : ∀ i, ∃ j, A i ⊆ P j)
    (hbalance : ∀ j j', (contained A (P j) : ℝ) ≤ L * contained A (P j'))
    (j : Fin p) : (n : ℝ) ≤ L * p * contained A (P j) := by
  classical
  have hc : (n : ℝ) ≤ ∑ j : Fin p, (contained A (P j) : ℝ) := by
    have hone (i : Fin n) : 1 ≤ (Finset.univ.filter fun j => A i ⊆ P j).card := by
      obtain ⟨j, hj⟩ := hcover i
      exact Finset.one_le_card.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
    calc
      (n : ℝ) = ∑ _i : Fin n, (1 : ℝ) := by simp
      _ ≤ ∑ i : Fin n, ((Finset.univ.filter fun j => A i ⊆ P j).card : ℝ) :=
        Finset.sum_le_sum fun i _ => by exact_mod_cast hone i
      _ = ∑ j : Fin p, (contained A (P j) : ℝ) := by
        simp only [contained_eq_card]
        exact_mod_cast incidence_sum Finset.univ Finset.univ (fun i j => A i ⊆ P j)
  calc
    (n : ℝ) ≤ ∑ j' : Fin p, (contained A (P j') : ℝ) := hc
    _ ≤ ∑ _j' : Fin p, L * contained A (P j) :=
      Finset.sum_le_sum fun j' _ => hbalance j' j
    _ = L * p * contained A (P j) := by simp; ring

/-- A balanced cover inherits the global Frostman estimate, with its incidence loss. -/
theorem frostman_of_balanced_cover {n p : ℕ} (A : Fin n → Set Space)
    (P : Fin p → Set Space) (hn : 0 < n) {K L D : ℝ}
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hD : 0 ≤ D) (hF : Frostman K A)
    (hcover : ∀ i, ∃ j, A i ⊆ P j)
    (hbalance : ∀ j j', (contained A (P j) : ℝ) ≤ L * contained A (P j'))
    (hdegree : ∀ i, (ncard {j | A i ⊆ P j} : ℝ) ≤ D) :
    Frostman (K * L * D) P := by
  classical
  intro U hU
  let J := Finset.univ.filter fun j => P j ⊆ U
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hc : (contained P U : ℝ) * n ≤ L * p * (D * contained A U) := by
    calc
      (contained P U : ℝ) * n = ∑ _j ∈ J, (n : ℝ) := by
        rw [contained_eq_card]; simp [J]
      _ ≤ ∑ j ∈ J, L * p * contained A (P j) :=
        Finset.sum_le_sum fun j _ => cover_fibre_lower A P hcover hbalance j
      _ = L * p * ∑ j ∈ J, (contained A (P j) : ℝ) := by rw [Finset.mul_sum]
      _ ≤ L * p * (D * contained A U) :=
        mul_le_mul_of_nonneg_left (cover_incidence_le A P hD hdegree U) (by positivity)
  apply (ENNReal.mul_le_mul_iff_left
    (ENNReal.ofReal_pos.mpr hn0).ne' ENNReal.ofReal_ne_top).mp
  change ENNReal.ofReal (contained P U : ℝ) * ENNReal.ofReal (n : ℝ) ≤ _
  calc
    _ = ENNReal.ofReal ((contained P U : ℝ) * n) :=
      (ENNReal.ofReal_mul (Nat.cast_nonneg _)).symm
    _ ≤ ENNReal.ofReal (L * p * D * contained A U) :=
      ENNReal.ofReal_le_ofReal (by nlinarith only [hc])
    _ = ENNReal.ofReal (L * p * D) * ENNReal.ofReal (contained A U : ℝ) :=
      ENNReal.ofReal_mul (by positivity)
    _ ≤ ENNReal.ofReal (L * p * D) * (ENNReal.ofReal (K * n) * volume U) :=
      mul_le_mul' le_rfl (hF U hU)
    _ = (ENNReal.ofReal ((K * L * D) * p) * volume U) *
        ENNReal.ofReal (n : ℝ) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      rw [mul_right_comm _ (volume U), ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring

lemma Frostman.mono {n : ℕ} {A : Fin n → Set Space} {K L : ℝ}
    (h : Frostman K A) (hKL : K ≤ L) : Frostman L A := by
  intro U hU
  exact (h U hU).trans (mul_le_mul'
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hKL (Nat.cast_nonneg n))) le_rfl)

/-- Restriction costs exactly the reciprocal of the retained proportion. -/
lemma Frostman.restrict {n k : ℕ} {A : Fin n → Set Space} {K L : ℝ}
    (h : Frostman K A) (hK : 0 ≤ K) (g : Fin k → Fin n) (hg : Function.Injective g)
    (hsize : (n : ℝ) ≤ L * k) : Frostman (K * L) (fun j => A (g j)) := by
  intro U hU
  have hc : ncard {j | A (g j) ⊆ U} ≤ ncard {i | A i ⊆ U} :=
    Set.ncard_le_ncard_of_injOn g (fun _ h => h) hg.injOn
  calc
    _ ≤ ENNReal.ofReal (ncard {i | A i ⊆ U} : ℝ) :=
      ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr hc)
    _ ≤ ENNReal.ofReal (K * n) * volume U := h U hU
    _ ≤ ENNReal.ofReal ((K * L) * k) * volume U := by
      apply mul_le_mul' _ le_rfl
      apply ENNReal.ofReal_le_ofReal
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsize hK

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
