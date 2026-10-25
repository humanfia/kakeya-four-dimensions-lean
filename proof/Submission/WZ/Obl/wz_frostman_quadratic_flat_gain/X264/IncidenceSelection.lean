-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.IncidenceSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.Refinement
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file IncidenceSelection.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open scoped BigOperators

/-- Select dense tubes and dense prism packets using incidence mass. No bound on
how many prisms contain one tube is needed. -/
lemma incidence_density_selection {n p : ℕ} (hp : 0 < p)
    (F : Fin p → Finset (Fin n)) (hF : ∀ j, (F j).Nonempty)
    (w : Fin n → ℝ) (hw : ∀ i, w i ≤ 1)
    {τ D : ℝ} (hτ : 0 < τ) (hD : 0 < D)
    (hbalance : ∀ j k, ((F j).card : ℝ) ≤ D * (F k).card)
    (hmass : τ * (∑ j, ((F j).card : ℝ)) ≤ ∑ j, ∑ i ∈ F j, w i) :
    ∃ (G : Finset (Fin n)) (J : Finset (Fin p)), J.Nonempty ∧
      (∀ i ∈ G, τ / 2 ≤ w i) ∧
      (∀ j ∈ J, τ / 4 * (F j).card ≤ ((F j ∩ G).card : ℝ)) ∧
      τ / (4 * D) * p ≤ (J.card : ℝ) ∧
      τ / 4 * (∑ j, ((F j).card : ℝ)) ≤ ∑ j ∈ J, ((F j ∩ G).card : ℝ) := by
  classical
  letI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  let G := Finset.univ.filter (fun i => τ / 2 ≤ w i)
  let R := fun j => F j ∩ G
  have hR (j : Fin p) : R j = (F j).filter (fun i => τ / 2 ≤ w i) := by
    ext i
    simp [R, G]
  have hpacket (j : Fin p) :
      (∑ i ∈ F j, w i) ≤ ((R j).card : ℝ) + τ / 2 * (F j).card := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (F j) (fun i => τ / 2 ≤ w i) w
    have hhi : (∑ i ∈ (F j).filter (fun i => τ / 2 ≤ w i), w i) ≤ ((R j).card : ℝ) := by
      calc
        _ ≤ ∑ _i ∈ (F j).filter (fun i => τ / 2 ≤ w i), (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => hw i
        _ = _ := by simp [hR]
    have hlo : (∑ i ∈ (F j).filter (fun i => ¬τ / 2 ≤ w i), w i) ≤
        τ / 2 * (F j).card := by
      calc
        _ ≤ ∑ _i ∈ (F j).filter (fun i => ¬τ / 2 ≤ w i), τ / 2 :=
          Finset.sum_le_sum fun i hi => (not_le.mp (Finset.mem_filter.mp hi).2).le
        _ ≤ ∑ _i ∈ F j, τ / 2 := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
        _ = _ := by simp [mul_comm]
    linarith
  have hret : τ / 2 * (∑ j, ((F j).card : ℝ)) ≤ ∑ j, ((R j).card : ℝ) := by
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpacket j)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    linarith
  let J := Finset.univ.filter (fun j => τ / 4 * (F j).card ≤ ((R j).card : ℝ))
  have hbad : (∑ j ∈ Finset.univ.filter (fun j => ¬τ / 4 * (F j).card ≤ ((R j).card : ℝ)),
      ((R j).card : ℝ)) ≤ τ / 4 * (∑ j, ((F j).card : ℝ)) := by
    calc
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j => ¬τ / 4 * (F j).card ≤ ((R j).card : ℝ)),
          τ / 4 * (F j).card :=
        Finset.sum_le_sum fun j hj => (not_le.mp (Finset.mem_filter.mp hj).2).le
      _ ≤ ∑ j, τ / 4 * (F j).card := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
      _ = _ := by rw [Finset.mul_sum]
  have hretJ : τ / 4 * (∑ j, ((F j).card : ℝ)) ≤ ∑ j ∈ J, ((R j).card : ℝ) := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j => τ / 4 * (F j).card ≤ ((R j).card : ℝ)) (fun j => ((R j).card : ℝ))
    change (∑ j ∈ J, ((R j).card : ℝ)) + _ = _ at hsplit
    linarith
  obtain ⟨j₀, _, hmin⟩ := Finset.exists_min_image Finset.univ (fun j => (F j).card)
    Finset.univ_nonempty
  have hmin' (j : Fin p) : ((F j₀).card : ℝ) ≤ (F j).card :=
    Nat.cast_le.mpr (hmin j (Finset.mem_univ _))
  have hminpos : (0 : ℝ) < (F j₀).card := Nat.cast_pos.mpr (Finset.card_pos.mpr (hF j₀))
  have htotal : (p : ℝ) * (F j₀).card ≤ ∑ j, ((F j).card : ℝ) := by
    simpa using Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hmin' j)
  have hupper : (∑ j ∈ J, ((R j).card : ℝ)) ≤ (J.card : ℝ) * (D * (F j₀).card) := by
    calc
      _ ≤ ∑ _j ∈ J, D * (F j₀).card := Finset.sum_le_sum fun j _ =>
        (Nat.cast_le.mpr (Finset.card_le_card (Finset.inter_subset_left : R j ⊆ F j))).trans
          (hbalance j j₀)
      _ = _ := by simp
  have hcard : τ / (4 * D) * p ≤ (J.card : ℝ) := by
    have h := (mul_le_mul_of_nonneg_left htotal (by positivity : 0 ≤ τ / 4)).trans
      (hretJ.trans hupper)
    have hh : τ / 4 * p ≤ (J.card : ℝ) * D := by
      apply (mul_le_mul_iff_left₀ hminpos).mp
      nlinarith only [h]
    apply (mul_le_mul_iff_left₀ hD).mp
    calc
      (τ / (4 * D) * p) * D = τ / 4 * p := by field_simp
      _ ≤ _ := hh
  have hJ : J.Nonempty := by
    apply Finset.card_pos.mp
    apply Nat.cast_pos.mp (show (0 : ℝ) < J.card from lt_of_lt_of_le (by positivity) hcard)
  exact ⟨G, J, hJ, fun i hi => (Finset.mem_filter.mp hi).2,
    fun j hj => (Finset.mem_filter.mp hj).2, hcard, hretJ⟩

/-- The retained prism count times any retained packet count controls the original
incidence count, which is the multiplicative quantity in the two-scale estimate. -/
lemma retained_packet_product {n p : ℕ} (F : Fin p → Finset (Fin n))
    (G : Finset (Fin n)) (J : Finset (Fin p)) {τ D : ℝ} (hτ : 0 < τ) (hD : 0 < D)
    (hbalance : ∀ j k, ((F j).card : ℝ) ≤ D * (F k).card)
    (hkeep : ∀ j ∈ J, τ / 4 * (F j).card ≤ ((F j ∩ G).card : ℝ))
    (hmass : τ / 4 * (∑ j, ((F j).card : ℝ)) ≤ ∑ j ∈ J, ((F j ∩ G).card : ℝ))
    {j : Fin p} (hj : j ∈ J) :
    τ ^ 2 / (16 * D) * (∑ k, ((F k).card : ℝ)) ≤
      (J.card : ℝ) * (F j ∩ G).card := by
  have hretain : ((F j).card : ℝ) ≤ 4 / τ * (F j ∩ G).card := by
    apply (mul_le_mul_iff_left₀ hτ).mp
    have he : (4 / τ * ((F j ∩ G).card : ℝ)) * τ = 4 * (F j ∩ G).card := by
      field_simp
    rw [he]
    nlinarith [hkeep j hj]
  have hsum : (∑ k ∈ J, ((F k ∩ G).card : ℝ)) ≤
      (J.card : ℝ) * (D * (4 / τ * (F j ∩ G).card)) := by
    calc
      _ ≤ ∑ _k ∈ J, D * (4 / τ * (F j ∩ G).card) := by
        apply Finset.sum_le_sum
        intro k hk
        exact (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left)).trans
          ((hbalance k j).trans (mul_le_mul_of_nonneg_left hretain hD.le))
      _ = _ := by simp
  calc
    _ = (τ / (4 * D)) * (τ / 4 * (∑ k, ((F k).card : ℝ))) := by ring
    _ ≤ (τ / (4 * D)) * (∑ k ∈ J, ((F k ∩ G).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ ≤ (τ / (4 * D)) * ((J.card : ℝ) * (D * (4 / τ * (F j ∩ G).card))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp

/-- A covering family has at least one incidence for each original index. -/
lemma card_le_total_incidence {n p : ℕ} (F : Fin p → Finset (Fin n))
    (hcover : ∀ i, ∃ j, i ∈ F j) : (n : ℝ) ≤ ∑ j, ((F j).card : ℝ) := by
  classical
  have hc : (Finset.univ : Finset (Fin n)) ⊆ Finset.univ.biUnion F := by
    intro i hi
    obtain ⟨j, hj⟩ := hcover i
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hj⟩
  have hn : n ≤ ∑ j, (F j).card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_le_card hc).trans Finset.card_biUnion_le
  exact_mod_cast hn

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
