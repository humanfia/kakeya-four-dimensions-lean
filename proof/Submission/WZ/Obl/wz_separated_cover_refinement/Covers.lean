-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_cover_refinement.Covers.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_cover_refinement.Geometry
import Submission.WZ.Obl.wz_separated_cover_refinement.Selection

namespace WangZahlLot.Obl.wz_separated_cover_refinement

open Set Metric MeasureTheory
open LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal Classical

set_option maxHeartbeats 1000000

/-- The exact density assumptions, with shading left unchanged by restriction. -/
def Dense (η δ : ℝ) (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) : Prop :=
  0 < n ∧ (∀ i, ‖v i‖ = 1) ∧ (∀ i, Tube δ (x i) (v i) ⊆ ball 0 1) ∧
  (∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
    (1 / 2 : ENNReal) * volume (Tube δ (x i) (v i))) ∧
  (∀ i, MeasurableSet (Y i)) ∧ (∀ i, Y i ⊆ Tube δ (x i) (v i)) ∧
  ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y i)

/-- The six conditions of a balanced local Frostman cover. -/
def CoverAt (δ K ρ : ℝ) {n : ℕ} (x v : Fin n → Space)
    {k : ℕ} (z w : Fin k → Space) : Prop :=
  (∀ j, ‖w j‖ = 1) ∧
  (∀ j j', j ≠ j' → volume (Tube ρ (z j) (w j) ∩ Tube ρ (z j') (w j')) ≤
    (1 / 2 : ENNReal) * volume (Tube ρ (z j) (w j))) ∧
  (∀ i, ∃! j, Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)) ∧
  (∀ j, ∃ i, Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)) ∧
  (∀ j j', (ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)} : ℝ) ≤
    K * (ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j') (w j')} : ℝ)) ∧
  (∀ j, ∀ W : Set Space, Convex ℝ W →
    ENNReal.ofReal ((ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j) ∧
      Tube δ (x i) (v i) ⊆ W} : ℝ) * ρ ^ 2) ≤
    ENNReal.ofReal (K * (ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)} : ℝ)) * volume W)

def SeparatedAt (δ ρ : ℝ) {n : ℕ} (x v : Fin n → Space)
    {k : ℕ} (z w : Fin k → Space) : Prop :=
  ∀ i j j', Tube δ (x i) (v i) ⊆ Dilate ρ (z j) (w j) →
    Tube δ (x i) (v i) ⊆ Dilate ρ (z j') (w j') → j = j'

def Weak (η δ : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ r : ℝ, δ ≤ r → r ≤ 1 → ∃ ρ : ℝ, r ≤ ρ ∧ ρ ≤ 1 ∧ ρ ≤ δ ^ (-η) * r ∧
    ∃ k : ℕ, 0 < k ∧ ∃ z w : Fin k → Space, CoverAt δ (δ ^ (-η)) ρ x v z w

def Strong (η δ : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ r : ℝ, δ ≤ r → r ≤ 1 → ∃ ρ : ℝ, r ≤ ρ ∧ ρ ≤ 1 ∧ ρ ≤ δ ^ (-η) * r ∧
    ∃ k : ℕ, 0 < k ∧ ∃ z w : Fin k → Space,
      CoverAt δ (δ ^ (-η)) ρ x v z w ∧ SeparatedAt δ ρ x v z w

noncomputable def enumerate {I : Type*} (Q : Finset I) : Fin Q.card → I :=
  fun i => (Q.equivFin.symm i).val

theorem enumerate_mem {I : Type*} (Q : Finset I) (i : Fin Q.card) : enumerate Q i ∈ Q :=
  (Q.equivFin.symm i).property

theorem enumerate_injective {I : Type*} (Q : Finset I) : Function.Injective (enumerate Q) :=
  Subtype.val_injective.comp Q.equivFin.symm.injective

theorem enumerate_surjective {I : Type*} (Q : Finset I) {i : I} (hi : i ∈ Q) :
    ∃ a, enumerate Q a = i := by
  exact ⟨Q.equivFin ⟨i, hi⟩, by simp [enumerate]⟩

theorem enumerate_count {I : Type*} (Q : Finset I) (P : I → Prop) [DecidablePred P] :
    ncard {i | P (enumerate Q i)} = (Q.filter P).card := by
  classical
  rw [← ncard_image_of_injective _ (enumerate_injective Q)]
  have he : enumerate Q '' {i | P (enumerate Q i)} = (Q.filter P : Set I) := by
    ext i
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact Finset.mem_filter.mpr ⟨enumerate_mem Q a, ha⟩
    · intro hi
      obtain ⟨hiQ, hiP⟩ := Finset.mem_filter.mp hi
      obtain ⟨a, rfl⟩ := enumerate_surjective Q hiQ
      exact ⟨a, hiP, rfl⟩
  rw [he, ncard_coe_finset]

theorem enumerate_sum {I : Type*} {A : Type*} [AddCommMonoid A]
    (Q : Finset I) (w : I → A) : ∑ i, w (enumerate Q i) = ∑ i ∈ Q, w i := by
  rw [show (∑ i, w (enumerate Q i)) = ∑ i : Q, w i.val from
    Equiv.sum_comp Q.equivFin.symm (fun i : Q => w i.val)]
  exact Finset.sum_coe_sort Q w

theorem ncard_setOf {I : Type*} [Fintype I] (P : I → Prop) [DecidablePred P] :
    ncard {i | P i} = (Finset.univ.filter P).card := by
  have he : {i | P i} = (Finset.univ.filter P : Set I) := by ext i; simp
  rw [he, ncard_coe_finset]

/-- Restrict a cover to occupied coarse tubes. Fibre lower bounds control all losses. -/
theorem restrict_cover {n k B : ℕ} {δ ρ K K' t : ℝ}
    (x v : Fin n → Space) (z w : Fin k → Space)
    (hcover : CoverAt δ K ρ x v z w)
    (f : Fin n → Fin k)
    (hf : ∀ i j, Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j) ↔ f i = j)
    (Q : Finset (Fin n)) (hQ : Q.Nonempty)
    (hret : ∀ j, (Q.filter (fun i => f i = j)).Nonempty →
      t * ((Finset.univ.filter (fun i => f i = j)).card : ℝ) ≤
        ((Q.filter (fun i => f i = j)).card : ℝ))
    (hK' : 0 ≤ K') (hKt : K ≤ K' * t)
    (c : Fin k → Fin B)
    (hc : ∀ j j', j ≠ j' → Conflict δ ρ x v z w j j' → c j ≠ c j')
    (hcolor : ∀ i ∈ Q, ∀ i' ∈ Q, c (f i) = c (f i')) :
    ∃ k' : ℕ, 0 < k' ∧ ∃ z' w' : Fin k' → Space,
      CoverAt δ K' ρ (fun i => x (enumerate Q i)) (fun i => v (enumerate Q i)) z' w' ∧
      SeparatedAt δ ρ (fun i => x (enumerate Q i)) (fun i => v (enumerate Q i)) z' w' := by
  classical
  obtain ⟨hunit, hsep, huniq, hfull, hbal, hfrost⟩ := hcover
  let G := Q.image f
  let b := enumerate G
  have hbmem : ∀ j, b j ∈ G := enumerate_mem G
  have hbinj : Function.Injective b := enumerate_injective G
  have hG : 0 < G.card := Finset.card_pos.mpr (hQ.image f)
  have hparent : ∀ i, ∃ j, f (enumerate Q i) = b j := by
    intro i
    obtain ⟨j, hj⟩ := enumerate_surjective G (Finset.mem_image.mpr
      ⟨enumerate Q i, enumerate_mem Q i, rfl⟩)
    exact ⟨j, hj.symm⟩
  have hoccupied : ∀ j, (Q.filter (fun i => f i = b j)).Nonempty := by
    intro j
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp (hbmem j)
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, he⟩⟩
  have horig : ∀ j, ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)} =
      (Finset.univ.filter (fun i => f i = j)).card := by
    intro j
    simp_rw [hf]
    exact ncard_setOf (fun i : Fin n => f i = j)
  have hnew : ∀ j, ncard {i | Tube δ (x (enumerate Q i)) (v (enumerate Q i)) ⊆
      Tube ρ (z (b j)) (w (b j))} = (Q.filter (fun i => f i = b j)).card := by
    intro j
    simp_rw [hf]
    exact enumerate_count Q (fun i => f i = b j)
  have hcoeff : ∀ j, K * (ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z (b j)) (w (b j))} : ℝ) ≤
      K' * (ncard {i | Tube δ (x (enumerate Q i)) (v (enumerate Q i)) ⊆
        Tube ρ (z (b j)) (w (b j))} : ℝ) := by
    intro j
    rw [horig, hnew]
    calc K * ((Finset.univ.filter (fun i => f i = b j)).card : ℝ)
        ≤ (K' * t) * ((Finset.univ.filter (fun i => f i = b j)).card : ℝ) := by
          gcongr
      _ = K' * (t * ((Finset.univ.filter (fun i => f i = b j)).card : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hret _ (hoccupied j)) hK'
  have hcountle : ∀ P : Fin n → Prop,
      ncard {i | P (enumerate Q i)} ≤ ncard {i | P i} := by
    intro P
    rw [enumerate_count, ncard_setOf]
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ Q))
  refine ⟨G.card, hG, (fun j => z (b j)), (fun j => w (b j)), ?_, ?_⟩
  · refine ⟨(fun j => hunit (b j)), (fun j j' h => hsep _ _ (hbinj.ne h)), ?_, ?_, ?_, ?_⟩
    · intro i
      obtain ⟨j, hj⟩ := hparent i
      refine ⟨j, (hf _ _).mpr hj, ?_⟩
      intro j' hj'
      exact hbinj ((hf _ _).mp hj' |>.symm.trans hj)
    · intro j
      obtain ⟨i, hi⟩ := hoccupied j
      obtain ⟨hiQ, hif⟩ := Finset.mem_filter.mp hi
      obtain ⟨a, rfl⟩ := enumerate_surjective Q hiQ
      exact ⟨a, (hf _ _).mpr hif⟩
    · intro j j'
      exact (Nat.cast_le.mpr (hcountle (fun i => Tube δ (x i) (v i) ⊆
        Tube ρ (z (b j)) (w (b j))))).trans ((hbal _ _).trans (hcoeff j'))
    · intro j W hW
      calc ENNReal.ofReal ((ncard {i | Tube δ (x (enumerate Q i)) (v (enumerate Q i)) ⊆
              Tube ρ (z (b j)) (w (b j)) ∧ Tube δ (x (enumerate Q i)) (v (enumerate Q i)) ⊆ W} : ℝ) * ρ ^ 2)
          ≤ ENNReal.ofReal ((ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z (b j)) (w (b j)) ∧
              Tube δ (x i) (v i) ⊆ W} : ℝ) * ρ ^ 2) := by
            apply ENNReal.ofReal_le_ofReal
            exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hcountle (fun i => Tube δ (x i) (v i) ⊆ Tube ρ (z (b j)) (w (b j)) ∧
              Tube δ (x i) (v i) ⊆ W))) (sq_nonneg _)
        _ ≤ _ := (hfrost _ W hW).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (hcoeff j)) le_rfl)
  · intro i j j' hij hij'
    by_contra hne
    have hcne := hc (b j) (b j') (hbinj.ne hne) ⟨enumerate Q i, hij, hij'⟩
    obtain ⟨a, ha⟩ := hoccupied j
    obtain ⟨a', ha'⟩ := hoccupied j'
    obtain ⟨haQ, haf⟩ := Finset.mem_filter.mp ha
    obtain ⟨haQ', haf'⟩ := Finset.mem_filter.mp ha'
    exact hcne (by simpa only [haf, haf'] using hcolor a haQ a' haQ')

end WangZahlLot.Obl.wz_separated_cover_refinement
