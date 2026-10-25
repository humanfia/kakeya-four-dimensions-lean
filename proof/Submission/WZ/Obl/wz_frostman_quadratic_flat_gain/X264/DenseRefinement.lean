-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.DenseRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.IncidenceSelection
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Packets
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file DenseRefinement.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set
open WangZahlLot.Obl.wz_tower_balanced_refinement
  (enumerate enumerate_mem enumerate_injective exists_enumerate)

open Classical in
/-- Incidence-weighted density selection preserves the exact frozen factorization.
The product of retained prism and packet counts controls the original tube count. -/
theorem Factored.dense_refinement {D b τ : ℝ} {n p : ℕ}
    {T : Fin n → Set Space} {P : Fin p → Set Space}
    (hf : Factored D b T P) (hn : 0 < n) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (w : Fin n → ℝ) (hw : ∀ i, w i ≤ 1)
    (hmass : τ * (∑ j, (Set.ncard {i | T i ⊆ P j} : ℝ)) ≤
      ∑ j, ∑ i ∈ {i | T i ⊆ P j}.toFinset, w i) :
    ∃ (k q : ℕ) (g : Fin k → Fin n) (h : Fin q → Fin p),
      0 < k ∧ 0 < q ∧ Function.Injective g ∧ Function.Injective h ∧
      (∀ i, τ / 2 ≤ w (g i)) ∧
      Factored (4 * D ^ 2 / τ) b (T ∘ g) (P ∘ h) ∧
      ∀ j, τ ^ 2 / (16 * D) * n ≤
        (q : ℝ) * Set.ncard {i | T (g i) ⊆ P (h j)} := by
  classical
  have hD1 : 1 ≤ D := hf.one_le_error hn
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  let F : Fin p → Finset (Fin n) := fun j => {i | T i ⊆ P j}.toFinset
  have hFcard (j : Fin p) : (F j).card = Set.ncard {i | T i ⊆ P j} := by
    simp only [F, Set.ncard_eq_toFinset_card']
  have hF : ∀ j, (F j).Nonempty := by
    intro j
    apply Finset.card_pos.mp
    rw [hFcard]
    exact hf.count_pos hn j
  have hbalance : ∀ j l, ((F j).card : ℝ) ≤ D * (F l).card := by
    intro j l
    simpa only [hFcard] using hf.2.1 j l
  obtain ⟨G, J, hJ, hG, hkeep, hcard, hmassJ⟩ :=
    incidence_density_selection (hf.index_pos hn) F hF w hw hτ hD hbalance
      (by simpa only [hFcard] using hmass)
  let K := G ∩ J.biUnion F
  let g := enumerate K
  let h := enumerate J
  have hK : K.Nonempty := by
    obtain ⟨j, hj⟩ := hJ
    have hpos : (0 : ℝ) < (F j ∩ G).card :=
      lt_of_lt_of_le (mul_pos (by positivity) (Nat.cast_pos.mpr (Finset.card_pos.mpr (hF j))))
        (hkeep j hj)
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (Nat.cast_pos.mp hpos)
    exact ⟨i, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).2,
      Finset.mem_biUnion.mpr ⟨j, hj, (Finset.mem_inter.mp hi).1⟩⟩⟩
  have hcount (j : Fin J.card) :
      Set.ncard {i | T (g i) ⊆ P (h j)} = (F (h j) ∩ G).card := by
    have he : {i | i ∈ K ∧ T i ⊆ P (h j)} = (↑(F (h j) ∩ G) : Set (Fin n)) := by
      ext i
      constructor
      · rintro ⟨hi, hit⟩
        exact Finset.mem_inter.mpr ⟨by simpa only [F, Set.mem_toFinset, Set.mem_setOf_eq] using hit,
          (Finset.mem_inter.mp hi).1⟩
      · intro hi
        obtain ⟨hiF, hiG⟩ := Finset.mem_inter.mp hi
        have hit : T i ⊆ P (h j) := by
          simpa only [F, Set.mem_toFinset, Set.mem_setOf_eq] using hiF
        exact ⟨Finset.mem_inter.mpr ⟨hiG,
          Finset.mem_biUnion.mpr ⟨h j, enumerate_mem J j, hiF⟩⟩, hit⟩
    have hc := WangZahlLot.Obl.wz_nonflat_factored_improvement.enumerate_predicate_count K
      (fun i => T i ⊆ P (h j))
    rw [he, Set.ncard_coe_finset] at hc
    exact hc
  have hcover : ∀ i : Fin K.card, ∃ j : Fin J.card, T (g i) ⊆ P (h j) := by
    intro i
    have hi := enumerate_mem K i
    obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hi).2
    obtain ⟨l, hl⟩ := exists_enumerate J hj
    refine ⟨l, ?_⟩
    change T (g i) ⊆ P (enumerate J l)
    rw [hl]
    simpa only [F, Set.mem_toFinset, Set.mem_setOf_eq] using hij
  let κ := 4 * D / τ
  have hκ : 1 ≤ κ := by
    dsimp [κ]
    rw [le_div_iff₀ hτ]
    linarith
  have hpacket (j : Fin J.card) :
      (Set.ncard {i | T i ⊆ P (h j)} : ℝ) ≤
        κ * Set.ncard {i | T (g i) ⊆ P (h j)} := by
    rw [hcount, ← hFcard]
    dsimp [κ]
    rw [div_mul_eq_mul_div, le_div_iff₀ hτ]
    have hk := hkeep (h j) (enumerate_mem J j)
    have hd : ((F (h j) ∩ G).card : ℝ) ≤ D * (F (h j) ∩ G).card := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hD1
        (show (0 : ℝ) ≤ (F (h j) ∩ G).card from Nat.cast_nonneg _)
    nlinarith
  have hprisms : (p : ℝ) ≤ κ * J.card := by
    dsimp [κ]
    rw [div_mul_eq_mul_div, le_div_iff₀ hτ]
    rw [div_mul_eq_mul_div] at hcard
    have hc := (div_le_iff₀ (by positivity : 0 < 4 * D)).mp hcard
    nlinarith
  refine ⟨K.card, J.card, g, h, Finset.card_pos.mpr hK, Finset.card_pos.mpr hJ,
    enumerate_injective K, enumerate_injective J, ?_, ?_, ?_⟩
  · intro i
    exact hG (g i) (Finset.mem_inter.mp (enumerate_mem K i)).1
  · have herr : D * κ = 4 * D ^ 2 / τ := by dsimp [κ]; ring
    rw [← herr]
    exact hf.restrict hD.le hκ g h (enumerate_injective K) (enumerate_injective J)
      hcover hpacket hprisms
  · intro j
    rw [hcount]
    have hc : (n : ℝ) ≤ ∑ l, ((F l).card : ℝ) := card_le_total_incidence F (by
      intro i
      obtain ⟨l, hl⟩ := hf.1 i
      exact ⟨l, by simpa only [F, Set.mem_toFinset, Set.mem_setOf_eq] using hl⟩)
    exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans
      (retained_packet_product F G J hτ hD hbalance hkeep hmassJ (enumerate_mem J j))

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
