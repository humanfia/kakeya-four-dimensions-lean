-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.GlobalPartition.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.RootPartition

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya

noncomputable section

attribute [local instance] Classical.propDecidable

lemma exists_large_fiber {α β : Type*} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (p : α → β) {D T : ℝ} (hT : 0 ≤ T)
    (hD : ((U.image p).card : ℝ) ≤ D) (hU : D * T < U.card) :
    ∃ b ∈ U.image p, T < ((U.filter (fun i => p i = b)).card : ℝ) := by
  by_contra hn
  have hsmall : ∀ b ∈ U.image p, ((U.filter (fun i => p i = b)).card : ℝ) ≤ T := by
    intro b hb
    by_contra hh
    exact hn ⟨b, hb, not_le.mp hh⟩
  have he := Finset.card_eq_sum_card_image p U
  have hh : (U.card : ℝ) ≤ D * T := by
    calc
      _ = ∑ b ∈ U.image p, ((U.filter (fun i => p i = b)).card : ℝ) := by exact_mod_cast he
      _ ≤ ∑ _b ∈ U.image p, T := Finset.sum_le_sum hsmall
      _ = ((U.image p).card : ℝ) * T := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hD hT
  exact (not_lt_of_ge hh hU)

/-- A usable coarse class includes a thin slice of the omitted slope coordinate. -/
def ThinCoarseClass {n : ℕ} (x v : Fin n → Space) (δ a s : ℝ) (L : ℕ)
    (Q : Finset (Fin n)) : Prop :=
  ∃ c : ℝ, |c| ≤ 3 ∧ (∀ i ∈ Q, |slope (v i) 0 - c| ≤ δ) ∧ CoarseClass x v δ a s L Q

/-- The entire tube family partitions into coarse Frostman classes, up to a controlled
number of tubes. The argument uses only finite density maximization and convex counts. -/
theorem global_coarse_partition {η δ a b s : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {n L : ℕ} (hn : 0 < n) (hL : 3 ≤ L)
    (x v : Fin n → Space)
    (hv : ∀ i, ‖v i‖ = 1) (htrans : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball 0 1)
    (hF : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (Set.ncard {i | Tube δ (x i) (v i) ⊆ W} : ℝ) ≤
        ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume W)
    (hδL : δ ≤ ((2 : ℝ) ^ L)⁻¹) (hs : 0 ≤ s) (hs2 : s ≤ 2)
    (hsmall : 2080000 * δ ^ (a * (2 - s) - η - b) < 1) :
    ∃ F : Finset (Finset (Fin n)),
      (∀ Q ∈ F, Q.Nonempty ∧ ThinCoarseClass x v δ a s L Q) ∧
      (F : Set (Finset (Fin n))).PairwiseDisjoint id ∧
      ((Finset.univ \ F.biUnion id).card : ℝ) ≤ (6 * 81 ^ 3 / δ) * (δ ^ b * (n : ℝ)) := by
  classical
  have hp (i : Fin n) : ‖parameters (x i) (v i)‖ ≤ 5 := by
    have hx : ‖x i‖ ≤ 1 := by
      have hh := hball i ((self_subset_thickening hδ _) (left_mem_segment ℝ _ _))
      exact (by simpa only [mem_ball, dist_zero_right] using hh : ‖x i‖ < 1).le
    exact parameters_norm_le_five hx (hv i) (htrans i)
  let p : Fin n → ℤ × (Fin 3 → ℤ) := fun i =>
    parameterRootLabel δ (slope (v i) 0) (parameters (x i) (v i))
  have select : ∀ S ⊆ (Finset.univ : Finset (Fin n)),
      (6 * 81 ^ 3 / δ) * (δ ^ b * (n : ℝ)) < (S.card : ℝ) →
        ∃ Q ⊆ S, Q.Nonempty ∧ ThinCoarseClass x v δ a s L Q := by
    intro S hS hlarge
    have hrootcount : ((S.image p).card : ℝ) ≤ 6 * 81 ^ 3 / δ := by
      apply (le_div_iff₀ hδ).mpr
      exact parameter_root_count S (fun i => parameters (x i) (v i)) (fun i => slope (v i) 0)
        hδ hδ1 (fun i _ => hp i) (fun i _ => abs_slope_le_two (hv i) (htrans i) 0)
    obtain ⟨r, hr, hcard⟩ := exists_large_fiber S p (by positivity : 0 ≤ δ ^ b * (n : ℝ))
      hrootcount hlarge
    let U := S.filter fun i => p i = r
    have hU : U.Nonempty := Finset.card_pos.mp (by
      have hh : (0 : ℝ) < U.card := (by positivity : 0 < δ ^ b * (n : ℝ)).trans hcard
      exact_mod_cast hh)
    let c := δ * (r.1 : ℝ)
    have hthin : ∀ i ∈ U, |slope (v i) 0 - c| ≤ δ := by
      intro i hi
      have he := congrArg Prod.fst (Finset.mem_filter.mp hi).2
      change ⌊slope (v i) 0 / δ⌋ = r.1 at he
      have hh := root_slope_near (c := slope (v i) 0) hδ
      simpa only [he] using hh
    have hroot : ∀ i ∈ U, ∀ i' ∈ U,
        dyadicLabel 3 (parameters (x i) (v i)) = dyadicLabel 3 (parameters (x i') (v i')) := by
      intro i hi i' hi'
      exact congrArg Prod.snd
        ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hi').2.symm)
    have hc : |c| ≤ 3 := by
      obtain ⟨i, hi⟩ := hU
      have ht := hthin i hi
      have hslope := abs_slope_le_two (hv i) (htrans i) 0
      have htri := abs_sub_le c (slope (v i) 0) 0
      rw [sub_zero, sub_zero, abs_sub_comm c (slope (v i) 0)] at htri
      linarith
    obtain ⟨j, hj3, hjL, hcoarse, i₀, hi₀, hQ, hcount⟩ :=
      exists_coarse_density_cell hδ hn hL x v U hv htrans hball hF hthin hroot
        hδL hs hs2 hsmall hcard.le
    let Q := U.filter (fun i => dyadicLabel j (parameters (x i) (v i)) =
      dyadicLabel j (parameters (x i₀) (v i₀)))
    have hQU : Q ⊆ U := Finset.filter_subset _ _
    refine ⟨Q, hQU.trans (Finset.filter_subset _ _), hQ, c, hc,
      fun i hi => hthin i (hQU hi), j, hj3, hjL, hcoarse, i₀, ?_, ?_, hcount⟩
    · exact Finset.mem_filter.mpr ⟨hi₀, rfl⟩
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  obtain ⟨F, hF', hdisj, hrem⟩ := disjoint_selection_partition Finset.univ
    (ThinCoarseClass x v δ a s L) (by positivity) select
  exact ⟨F, fun Q hQ => (hF' Q hQ).2, hdisj, hrem⟩

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
