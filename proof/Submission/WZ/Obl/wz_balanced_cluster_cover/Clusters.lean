-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_balanced_cluster_cover.Clusters.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_balanced_cluster_cover.Basic

set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_balanced_cluster_cover

open MeasureTheory Metric Set
open scoped ENNReal

/-- The cluster certificate built from one output of the angular selection. -/
theorem exists_clusters {A C δ θ lam β E : ℝ} {n : ℕ}
    (hA : 1 ≤ A) (hCC₀ : 2 * (2 * A + 2) ^ 3 * (4 * A + 14) ^ 3 ≤ C) (hCA : A + 6 ≤ C)
    (hδ : 0 < δ) (hδθ : δ ≤ θ) (hθ1 : θ ≤ 1) (hlam : 0 < lam) (hE : 0 < E)
    (hEsmall : E * (2 * (2 * (2 * A + 2) ^ 3 * (4 * A + 14) ^ 3) + 768) ≤ δ ^ (A * β))
    (hn : 0 < n) (x v : Fin n → V) (Y Z : Fin n → Set V) (a : V → Fin n)
    (hv : ∀ i, ‖v i‖ = 1)
    (hTB : ∀ i, thickening δ (segment ℝ (x i) (x i + v i)) ⊆ ball 0 1)
    (hYT : ∀ i, Y i ⊆ thickening δ (segment ℝ (x i) (x i + v i)))
    (hZm : ∀ i, MeasurableSet (Z i)) (hZY : ∀ i, Z i ⊆ Y i)
    (ham : ∀ i, MeasurableSet {p | a p = i})
    (hdir : ∀ p i, p ∈ Z i → min ‖v i - v (a p)‖ ‖v i + v (a p)‖ ≤ A * θ)
    (hcount : ∀ p u r, ‖u‖ = 1 → δ ≤ r →
      (Set.ncard {i | p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} : ℝ) ≤
        A * (r / θ) ^ β * (Set.ncard {i | p ∈ Z i} : ℝ))
    (hmass : ENNReal.ofReal (δ ^ (A * β) * (lam * n * δ ^ 2)) ≤ ∑ i, volume (Z i)) :
    ∃ (J : ℕ) (k : Fin J → ℕ) (f : (j : Fin J) → Fin (k j) → Fin n) (z w : Fin J → V)
      (Z' : (j : Fin J) → Fin (k j) → Set V),
      0 < J ∧ (∀ j, 0 < k j) ∧ (∀ j, Function.Injective (f j)) ∧ (∀ j, ‖w j‖ = 1) ∧
      (∀ j i, MeasurableSet (Z' j i)) ∧ (∀ j i, Z' j i ⊆ Y (f j i)) ∧
      (∀ j i, min ‖v (f j i) - w j‖ ‖v (f j i) + w j‖ ≤ C * θ) ∧
      (∀ j i, thickening δ (segment ℝ (x (f j i)) (x (f j i) + v (f j i))) ⊆
        thickening (C * θ) (segment ℝ (z j) (z j + (6 : ℝ) • w j))) ∧
      (∀ j j', j ≠ j' → Disjoint (⋃ i : Fin (k j), Z' j i) (⋃ i : Fin (k j'), Z' j' i)) ∧
      (∀ j, ∀ p u r, ‖u‖ = 1 → δ ≤ r →
        (Set.ncard {i : Fin (k j) | p ∈ Z' j i ∧
            min ‖v (f j i) - u‖ ‖v (f j i) + u‖ ≤ r} : ℝ) ≤
          C * (r / θ) ^ β * (Set.ncard {i : Fin (k j) | p ∈ Z' j i} : ℝ)) ∧
      (∀ j, ENNReal.ofReal ((E * lam) * (k j : ℝ) * δ ^ 2) ≤ ∑ i, volume (Z' j i)) ∧
      E * lam * (n : ℝ) ≤ ∑ j, (k j : ℝ) ∧ ∑ j, (k j : ℝ) ≤ C * (n : ℝ) := by
  classical
  have hθ : 0 < θ := lt_of_lt_of_le hδ hδθ
  set C₀ : ℝ := 2 * (2 * A + 2) ^ 3 * (4 * A + 14) ^ 3 with hC₀
  have hC₀nn : 0 ≤ C₀ := by positivity
  -- the cluster point sets
  set u : V → V := fun p => v (a p) with hu
  set P : (Fin 3 → ℤ) × (Fin 3 → ℤ) → Set V := fun ℓ => {p | lab θ u p = ℓ} with hP
  have hPm : ∀ ℓ, MeasurableSet (P ℓ) := fun ℓ => measurableSet_lab θ v a ham ℓ
  have hPdisj : ∀ ℓ ℓ', ℓ ≠ ℓ' → Disjoint (P ℓ) (P ℓ') := by
    intro ℓ ℓ' h
    rw [Set.disjoint_left]
    intro p hp hp'
    exact h ((show lab θ u p = ℓ from hp).symm.trans hp')
  set S : (Fin 3 → ℤ) × (Fin 3 → ℤ) → Finset (Fin n) :=
    fun ℓ => Finset.univ.filter fun i => (Z i ∩ P ℓ).Nonempty with hS
  have hmemS : ∀ ℓ i, i ∈ S ℓ ↔ (Z i ∩ P ℓ).Nonempty := by
    intro ℓ i
    simp [hS]
  -- volumes
  have hZT : ∀ i, Z i ⊆ thickening δ (segment ℝ (x i) (x i + v i)) :=
    fun i => (hZY i).trans (hYT i)
  have hvolT : ∀ i, volume (thickening δ (segment ℝ (x i) (x i + v i))) ≤
      ENNReal.ofReal (384 * δ ^ 2) :=
    fun i => tube_volume_le hδ (hδθ.trans hθ1) (x i) (v i) (hv i)
  have hpiece : ∀ i ℓ, volume (Z i ∩ P ℓ) ≤ ENNReal.ofReal (384 * δ ^ 2) :=
    fun i ℓ => (measure_mono (inter_subset_left.trans (hZT i))).trans (hvolT i)
  have hpiece_ne : ∀ i ℓ, volume (Z i ∩ P ℓ) ≠ ⊤ :=
    fun i ℓ => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hpiece i ℓ)
  have hZfin : ∀ i, volume (Z i) ≠ ⊤ :=
    fun i => ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((measure_mono (hZT i)).trans (hvolT i))
  -- labels carried by the points of each tube
  set F : Fin n → Finset ((Fin 3 → ℤ) × (Fin 3 → ℤ)) :=
    fun i => labelBox θ A (x i) (v i) with hF
  have hlabF : ∀ i, ∀ p ∈ Z i, lab θ u p ∈ F i := by
    intro i p hp
    exact lab_mem_labelBox hθ hδθ (hv (a p)) (hZT i hp) (hdir p i hp)
  have hcardF : ∀ i, ((F i).card : ℝ) ≤ C₀ :=
    fun i => card_labelBox_le hθ (by linarith) (x i) (v i)
  set Λ := Finset.univ.biUnion F with hΛ
  -- masses of the clusters
  set mass : (Fin 3 → ℤ) × (Fin 3 → ℤ) → ℝ :=
    fun ℓ => ∑ i, (volume (Z i ∩ P ℓ)).toReal with hmass_def
  have hzero : ∀ ℓ i, i ∉ S ℓ → Z i ∩ P ℓ = ∅ := by
    intro ℓ i hi
    rwa [hmemS, Set.not_nonempty_iff_eq_empty] at hi
  have hmass_S : ∀ ℓ, mass ℓ = ∑ i ∈ S ℓ, (volume (Z i ∩ P ℓ)).toReal := by
    intro ℓ
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    rw [hzero ℓ i hi, measure_empty, ENNReal.toReal_zero]
  have hmass_le : ∀ ℓ, mass ℓ ≤ 384 * δ ^ 2 * (S ℓ).card := by
    intro ℓ
    rw [hmass_S]
    calc ∑ i ∈ S ℓ, (volume (Z i ∩ P ℓ)).toReal ≤ ∑ i ∈ S ℓ, 384 * δ ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hpiece i ℓ)
      _ = 384 * δ ^ 2 * (S ℓ).card := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  have hmass_ofReal : ∀ ℓ, ENNReal.ofReal (mass ℓ) = ∑ i, volume (Z i ∩ P ℓ) := by
    intro ℓ
    rw [hmass_def, ENNReal.ofReal_sum_of_nonneg (fun i _ => ENNReal.toReal_nonneg)]
    exact Finset.sum_congr rfl fun i _ => ENNReal.ofReal_toReal (hpiece_ne i ℓ)
  -- total mass
  have htotal : ∑ i, (volume (Z i)).toReal = ∑ ℓ ∈ Λ, mass ℓ := by
    rw [hmass_def, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    have hcover : Z i = ⋃ ℓ ∈ Λ, (Z i ∩ P ℓ) := by
      ext p
      constructor
      · intro hp
        refine mem_iUnion₂.mpr ⟨lab θ u p, ?_, hp, rfl⟩
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hlabF i p hp⟩
      · intro hp
        obtain ⟨ℓ, _, hp⟩ := mem_iUnion₂.mp hp
        exact hp.1
    have hdisj : (Λ : Set ((Fin 3 → ℤ) × (Fin 3 → ℤ))).PairwiseDisjoint
        fun ℓ => Z i ∩ P ℓ := by
      intro ℓ _ ℓ' _ h
      exact (hPdisj ℓ ℓ' h).mono inter_subset_right inter_subset_right
    rw [← ENNReal.toReal_sum (fun ℓ _ => hpiece_ne i ℓ)]
    congr 1
    conv_lhs => rw [hcover]
    exact measure_biUnion_finset hdisj (fun ℓ _ => (hZm i).inter (hPm ℓ))
  have hmassR : δ ^ (A * β) * (lam * n * δ ^ 2) ≤ ∑ i, (volume (Z i)).toReal := by
    have hfin : ∑ i, volume (Z i) ≠ ⊤ := by
      rw [← lt_top_iff_ne_top]
      exact ENNReal.sum_lt_top.mpr fun i _ => lt_top_iff_ne_top.mpr (hZfin i)
    have h := hmass
    rw [← ENNReal.ofReal_toReal hfin, ENNReal.toReal_sum (fun i _ => hZfin i)] at h
    exact (ENNReal.ofReal_le_ofReal_iff
      (Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg)).mp h
  -- double counting of the duplication
  have hdouble : ∑ ℓ ∈ Λ, ((S ℓ).card : ℝ) ≤ C₀ * n := by
    have h1 : ∑ ℓ ∈ Λ, (S ℓ).card = ∑ i : Fin n, (Λ.filter fun ℓ => i ∈ S ℓ).card := by
      have := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (fun ℓ i => i ∈ S ℓ) (s := Λ) (t := (Finset.univ : Finset (Fin n)))
      simpa [Finset.bipartiteAbove, Finset.bipartiteBelow] using this
    have h2 : ∀ i, (Λ.filter fun ℓ => i ∈ S ℓ).card ≤ (F i).card := by
      intro i
      apply Finset.card_le_card
      intro ℓ hℓ
      rw [Finset.mem_filter] at hℓ
      obtain ⟨p, hpZ, hpP⟩ := (hmemS ℓ i).mp hℓ.2
      have hl : lab θ u p = ℓ := hpP
      have := hlabF i p hpZ
      rwa [hl] at this
    calc ∑ ℓ ∈ Λ, ((S ℓ).card : ℝ) = ∑ i : Fin n, ((Λ.filter fun ℓ => i ∈ S ℓ).card : ℝ) := by
          exact_mod_cast h1
      _ ≤ ∑ _i : Fin n, C₀ :=
          Finset.sum_le_sum fun i _ => (Nat.cast_le.mpr (h2 i)).trans (hcardF i)
      _ = C₀ * n := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  -- the clusters that are kept
  set Θ : ℝ := E * lam * δ ^ 2 with hΘ
  have hΘ0 : 0 < Θ := by positivity
  set good : (Fin 3 → ℤ) × (Fin 3 → ℤ) → Prop :=
    fun ℓ => (S ℓ).Nonempty ∧ Θ * (S ℓ).card ≤ mass ℓ with hgood_def
  set G := Λ.filter good with hG
  have hbad : ∀ ℓ, ¬ good ℓ → mass ℓ ≤ Θ * (S ℓ).card := by
    intro ℓ hnot
    rw [hgood_def] at hnot
    simp only [not_and_or] at hnot
    rcases hnot with h | h
    · rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [hmass_S, h]
      simp
    · exact (not_le.mp h).le
  have hgood_le : ∑ ℓ ∈ G, mass ℓ ≤ 384 * δ ^ 2 * ∑ ℓ ∈ G, ((S ℓ).card : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun ℓ _ => hmass_le ℓ
  have hbad_le : ∑ ℓ ∈ Λ.filter (fun ℓ => ¬ good ℓ), mass ℓ ≤ Θ * (C₀ * n) := by
    calc ∑ ℓ ∈ Λ.filter (fun ℓ => ¬ good ℓ), mass ℓ
        ≤ ∑ ℓ ∈ Λ.filter (fun ℓ => ¬ good ℓ), Θ * (S ℓ).card :=
          Finset.sum_le_sum fun ℓ hℓ => hbad ℓ (Finset.mem_filter.mp hℓ).2
      _ ≤ ∑ ℓ ∈ Λ, Θ * (S ℓ).card :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => by positivity)
      _ = Θ * ∑ ℓ ∈ Λ, ((S ℓ).card : ℝ) := by rw [Finset.mul_sum]
      _ ≤ Θ * (C₀ * n) := mul_le_mul_of_nonneg_left hdouble hΘ0.le
  have hsumG : E * lam * n ≤ ∑ ℓ ∈ G, ((S ℓ).card : ℝ) := by
    have h1 : δ ^ (A * β) * (lam * n * δ ^ 2) ≤
        384 * δ ^ 2 * ∑ ℓ ∈ G, ((S ℓ).card : ℝ) + Θ * (C₀ * n) := by
      calc _ ≤ ∑ i, (volume (Z i)).toReal := hmassR
        _ = ∑ ℓ ∈ Λ, mass ℓ := htotal
        _ = ∑ ℓ ∈ G, mass ℓ + ∑ ℓ ∈ Λ.filter (fun ℓ => ¬ good ℓ), mass ℓ :=
          (Finset.sum_filter_add_sum_filter_not _ _ _).symm
        _ ≤ _ := add_le_add hgood_le hbad_le
    set s := ∑ ℓ ∈ G, ((S ℓ).card : ℝ) with hs
    have hδ2 : 0 < δ ^ 2 := by positivity
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h2 : δ ^ (A * β) * (lam * n) ≤ 384 * s + E * lam * (C₀ * n) := by
      have h3 : δ ^ 2 * (δ ^ (A * β) * (lam * n)) ≤ δ ^ 2 * (384 * s + E * lam * (C₀ * n)) := by
        rw [hΘ] at h1
        linarith
      exact le_of_mul_le_mul_left h3 hδ2
    have h4 : E * (2 * C₀ + 768) * (lam * n) ≤ δ ^ (A * β) * (lam * n) :=
      mul_le_mul_of_nonneg_right hEsmall (by positivity)
    have h5 : 0 ≤ E * lam * n * C₀ := by positivity
    have h6 : 0 ≤ E * lam * n := by positivity
    nlinarith
  have hGne : G.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hG0
    rw [hG0, Finset.sum_empty] at hsumG
    have : 0 < E * lam * n := by
      have : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    linarith
  -- enumerate the kept clusters
  set J := G.card with hJ
  set e : Fin J ≃ G := G.equivFin.symm with he
  set ℓ : Fin J → (Fin 3 → ℤ) × (Fin 3 → ℤ) := fun j => (e j).1 with hℓ
  have hℓG : ∀ j, ℓ j ∈ G := fun j => (e j).2
  have hℓinj : Function.Injective ℓ := fun j j' h => e.injective (Subtype.ext h)
  have hgood : ∀ j, good (ℓ j) := fun j => (Finset.mem_filter.mp (hℓG j)).2
  set k : Fin J → ℕ := fun j => (S (ℓ j)).card with hk
  set f : (j : Fin J) → Fin (k j) → Fin n :=
    fun j i => ((S (ℓ j)).equivFin.symm i).1 with hf
  have hfS : ∀ j i, f j i ∈ S (ℓ j) := fun j i => ((S (ℓ j)).equivFin.symm i).2
  have hfinj : ∀ j, Function.Injective (f j) :=
    fun j => Subtype.val_injective.comp (S (ℓ j)).equivFin.symm.injective
  have hfrange : ∀ j i, i ∈ S (ℓ j) → i ∈ Set.range (f j) := by
    intro j i hi
    refine ⟨(S (ℓ j)).equivFin ⟨i, hi⟩, ?_⟩
    simp [hf]
  set pt : (Fin 3 → ℤ) × (Fin 3 → ℤ) → V :=
    fun ℓ => Classical.epsilon fun p => lab θ u p = ℓ with hpt
  set w : Fin J → V := fun j => W θ (ℓ j).1 with hw
  set z : Fin J → V := fun j => proj (w j) (pt (ℓ j)) - (3 : ℝ) • w j with hz
  set Z' : (j : Fin J) → Fin (k j) → Set V := fun j i => Z (f j i) ∩ P (ℓ j) with hZ'
  -- the geometry of a member of a kept cluster
  have hmember : ∀ j i, i ∈ S (ℓ j) → ∃ p, p ∈ Z i ∧ lab θ u p = ℓ j := by
    intro j i hi
    obtain ⟨p, hpZ, hpP⟩ := (hmemS (ℓ j) i).mp hi
    exact ⟨p, hpZ, hpP⟩
  have hgeom : ∀ j i, i ∈ S (ℓ j) →
      ‖w j‖ = 1 ∧ min ‖v i - w j‖ ‖v i + w j‖ ≤ (A + 2) * θ ∧
      thickening δ (segment ℝ (x i) (x i + v i)) ⊆
        thickening ((A + 6) * θ) (segment ℝ (z j) (z j + (6 : ℝ) • w j)) := by
    intro j i hi
    obtain ⟨p, hpZ, hpl⟩ := hmember j i hi
    have hpl1 : (ℓ j).1 = cell θ (v (a p)) := (congrArg Prod.fst hpl).symm
    have hpl2 : (ℓ j).2 = cell θ (proj (W θ (cell θ (v (a p)))) p) :=
      (congrArg Prod.snd hpl).symm
    have hwj : w j = W θ (cell θ (v (a p))) := by simp only [hw, hpl1]
    obtain ⟨hw1, hvw⟩ := dir_close hθ (hv (a p)) (hdir p i hpZ)
    rw [← hwj] at hw1 hvw
    refine ⟨hw1, hvw, ?_⟩
    have hptl : lab θ u (pt (ℓ j)) = ℓ j :=
      Classical.epsilon_spec (p := fun q => lab θ u q = ℓ j) ⟨p, hpl⟩
    have hq1 : (ℓ j).1 = cell θ (u (pt (ℓ j))) := (congrArg Prod.fst hptl).symm
    have hq2 : (ℓ j).2 = cell θ (proj (W θ (cell θ (u (pt (ℓ j))))) (pt (ℓ j))) :=
      (congrArg Prod.snd hptl).symm
    have hwj' : w j = W θ (cell θ (u (pt (ℓ j)))) := by simp only [hw, hq1]
    have hcell : cell θ (proj (w j) p) = cell θ (proj (w j) (pt (ℓ j))) := by
      rw [hwj, ← hpl2]
      rw [← hwj, hwj', ← hq2]
    have hp1 : ‖p‖ < 1 := by
      have := hTB i (hZT i hpZ)
      rwa [mem_ball_zero_iff] at this
    exact tube_subset_cyl hθ hδθ hw1 hp1 (hZT i hpZ) hvw hcell
  have hsum_k : ∑ j, (k j : ℝ) = ∑ ℓ ∈ G, ((S ℓ).card : ℝ) := by
    rw [← Finset.sum_coe_sort G (fun ℓ => ((S ℓ).card : ℝ))]
    exact Equiv.sum_comp e (fun x : G => ((S x.1).card : ℝ))
  refine ⟨J, k, f, z, w, Z', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 0 < J
    exact Finset.card_pos.mpr hGne
  · -- 0 < k j
    intro j
    exact Finset.card_pos.mpr (hgood j).1
  · exact hfinj
  · -- unit axes
    intro j
    obtain ⟨i, hi⟩ := (hgood j).1
    exact (hgeom j i hi).1
  · intro j i
    exact (hZm _).inter (hPm _)
  · intro j i
    exact inter_subset_left.trans (hZY _)
  · intro j i
    have := (hgeom j (f j i) (hfS j i)).2.1
    have hθ' : (A + 2) * θ ≤ C * θ := mul_le_mul_of_nonneg_right (by linarith) hθ.le
    linarith
  · intro j i
    refine (hgeom j (f j i) (hfS j i)).2.2.trans ?_
    exact thickening_mono (mul_le_mul_of_nonneg_right (by linarith) hθ.le) _
  · -- disjoint cluster unions
    intro j j' hjj'
    refine Disjoint.mono (iUnion_subset fun i => inter_subset_right)
      (iUnion_subset fun i => inter_subset_right) (hPdisj _ _ (hℓinj.ne hjj'))
  · -- robust angular counts
    intro j p u' r hu' hr
    have hCnn : 0 ≤ C := by linarith
    have hrθ : 0 ≤ (r / θ) ^ β := Real.rpow_nonneg (div_nonneg (hδ.le.trans hr) hθ.le) _
    by_cases hp : p ∈ P (ℓ j)
    · have e1 : Set.ncard {i : Fin (k j) | p ∈ Z' j i ∧
            min ‖v (f j i) - u'‖ ‖v (f j i) + u'‖ ≤ r} =
          Set.ncard {i : Fin n | p ∈ Z i ∧ min ‖v i - u'‖ ‖v i + u'‖ ≤ r} := by
        have := ncard_comp_eq (f j) (hfinj j)
          (fun i => p ∈ Z i ∩ P (ℓ j) ∧ min ‖v i - u'‖ ‖v i + u'‖ ≤ r)
          (fun i hi => hfrange j i ((hmemS _ _).mpr ⟨p, hi.1⟩))
        rw [this]
        congr 1
        ext i
        simp only [mem_ofPred_eq, mem_inter_iff]
        exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hp⟩, h.2⟩⟩
      have e2 : Set.ncard {i : Fin (k j) | p ∈ Z' j i} = Set.ncard {i : Fin n | p ∈ Z i} := by
        have := ncard_comp_eq (f j) (hfinj j) (fun i => p ∈ Z i ∩ P (ℓ j))
          (fun i hi => hfrange j i ((hmemS _ _).mpr ⟨p, hi⟩))
        rw [this]
        congr 1
        ext i
        simp only [mem_ofPred_eq, mem_inter_iff]
        exact ⟨fun h => h.1, fun h => ⟨h, hp⟩⟩
      rw [e1, e2]
      refine (hcount p u' r hu' hr).trans ?_
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_right (by linarith) hrθ
    · have e1 : {i : Fin (k j) | p ∈ Z' j i ∧
            min ‖v (f j i) - u'‖ ‖v (f j i) + u'‖ ≤ r} = ∅ := by
        ext i
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h => hp h.1.2
      rw [e1, Set.ncard_empty, Nat.cast_zero]
      positivity
  · -- density in every kept cluster
    intro j
    have hsum : ∑ i, volume (Z' j i) = ∑ i, volume (Z i ∩ P (ℓ j)) := by
      have h1 : ∑ i, volume (Z' j i) = ∑ x : S (ℓ j), volume (Z x.1 ∩ P (ℓ j)) :=
        Equiv.sum_comp (S (ℓ j)).equivFin.symm (fun x : S (ℓ j) => volume (Z x.1 ∩ P (ℓ j)))
      rw [h1, Finset.sum_coe_sort (S (ℓ j)) (fun i => volume (Z i ∩ P (ℓ j)))]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      rw [hzero _ i hi, measure_empty]
    rw [hsum, ← hmass_ofReal]
    apply ENNReal.ofReal_le_ofReal
    have := (hgood j).2
    calc E * lam * (k j : ℝ) * δ ^ 2 = Θ * (S (ℓ j)).card := by rw [hΘ]; ring
      _ ≤ mass (ℓ j) := this
  · rw [hsum_k]
    exact hsumG
  · rw [hsum_k]
    calc ∑ ℓ ∈ G, ((S ℓ).card : ℝ) ≤ ∑ ℓ ∈ Λ, ((S ℓ).card : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ C₀ * n := hdouble
      _ ≤ C * n := mul_le_mul_of_nonneg_right hCC₀ (Nat.cast_nonneg _)

end WangZahlLot.Obl.wz_balanced_cluster_cover
