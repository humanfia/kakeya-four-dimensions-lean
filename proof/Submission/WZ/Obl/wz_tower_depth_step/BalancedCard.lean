-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_tower_depth_step.BalancedCard.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_tower_depth_step.Basic

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_tower_depth_step

lemma ncard_filter_univ {n : ℕ} (P : Fin n → Prop) [DecidablePred P] :
    Set.ncard {i | P i} = (Finset.univ.filter P).card := by
  have he : (↑(Finset.univ.filter P) : Set (Fin n)) = {i | P i} := by ext i; simp
  rw [← he, Set.ncard_coe_finset]

/-- A uniform lower fibre size bounds any selected collection of parent indices. -/
lemma card_lower_of_fibres {n N : ℕ} (f : Fin n → Fin N) (P : Fin n → Prop)
    (C : Fin N → Prop) {a : ℝ}
    (hbranch : ∀ k, C k → a ≤ (Set.ncard {i | P i ∧ f i = k} : ℝ)) :
    a * (Set.ncard {k | C k} : ℝ) ≤ Set.ncard {i | P i ∧ C (f i)} := by
  classical
  let A := Finset.univ.filter P
  let B := Finset.univ.filter C
  have hfiber (k : Fin N) : (A.filter (fun i => f i = k)).card =
      Set.ncard {i | P i ∧ f i = k} := by
    rw [ncard_filter_univ]
    congr 1
    ext i
    simp [A]
  have hlo : a * B.card ≤ ∑ k ∈ B, ((A.filter (fun i => f i = k)).card : ℝ) := by
    calc
      _ = ∑ _k ∈ B, a := by simp; ring
      _ ≤ _ := Finset.sum_le_sum (fun k hk => by
        rw [hfiber]
        exact hbranch k (Finset.mem_filter.mp hk).2)
  have hs := Finset.sum_card_fiberwise_eq_card_filter A B f
  have hs' : (∑ k ∈ B, ((A.filter (fun i => f i = k)).card : ℝ)) =
      ((A.filter (fun i => f i ∈ B)).card : ℝ) := by exact_mod_cast hs
  rw [hs'] at hlo
  have he : A.filter (fun i => f i ∈ B) = Finset.univ.filter (fun i => P i ∧ C (f i)) := by
    ext i
    simp [A, B]
  simpa only [he, B, ncard_filter_univ] using hlo

/-- A uniform upper fibre size bounds the total number of assigned children. -/
lemma card_upper_of_fibres {n N : ℕ} (f : Fin n → Fin N) (P : Fin n → Prop)
    (Q : Fin N → Prop) {a : ℝ} (hmaps : ∀ i, P i → Q (f i))
    (hbranch : ∀ k, Q k → (Set.ncard {i | P i ∧ f i = k} : ℝ) ≤ a) :
    (Set.ncard {i | P i} : ℝ) ≤ a * Set.ncard {k | Q k} := by
  classical
  let A := Finset.univ.filter P
  let B := Finset.univ.filter Q
  have hfiber (k : Fin N) : (A.filter (fun i => f i = k)).card =
      Set.ncard {i | P i ∧ f i = k} := by
    rw [ncard_filter_univ]
    congr 1
    ext i
    simp [A]
  have hm : (A : Set (Fin n)).MapsTo f B := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmaps i (Finset.mem_filter.mp hi).2⟩
  have hh := Finset.card_eq_sum_card_fiberwise hm
  have hh' : (A.card : ℝ) = ∑ k ∈ B, ((A.filter (fun i => f i = k)).card : ℝ) := by exact_mod_cast hh
  rw [ncard_filter_univ P, ncard_filter_univ Q]
  change (A.card : ℝ) ≤ a * B.card
  rw [hh']
  calc
    _ ≤ ∑ _k ∈ B, a := Finset.sum_le_sum (fun k hk => by
      rw [hfiber]
      exact hbranch k (Finset.mem_filter.mp hk).2)
    _ = _ := by simp; ring

lemma sum_ncard_fibres {n N : ℕ} (f : Fin n → Fin N) (P : Fin n → Prop) :
    (∑ k : Fin N, Set.ncard {i | f i = k ∧ P i}) = Set.ncard {i | P i} := by
  classical
  have hh := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ.filter P) Finset.univ f
  simpa only [ncard_filter_univ, Finset.filter_filter, Finset.mem_univ, and_true,
    Finset.filter_true_of_mem (fun _ _ => True.intro), and_comm] using hh

end WangZahlLot.Obl.wz_tower_depth_step
