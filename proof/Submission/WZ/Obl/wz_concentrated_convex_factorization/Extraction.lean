-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_concentrated_convex_factorization.Extraction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_concentrated_convex_factorization.Saturated
import Submission.WZ.Obl.wz_concentrated_convex_factorization.Blocks
import Submission.WZ.Obl.wz_concentrated_convex_factorization.Pruning
import Submission.WZ.Obl.wz_concentrated_convex_factorization.WidthClasses
import Submission.WZ.Obl.wz_concentrated_convex_factorization.Enumeration

namespace WangZahlLot.Obl.wz_concentrated_convex_factorization

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_tower_balanced_refinement
  (enumerate enumerate_mem enumerate_injective exists_enumerate)
open scoped ENNReal
noncomputable section

/-- Assemble the geometric blocks and prune their incidences. -/
theorem extract_cover {ι : Type*} [DecidableEq ι] {δ m r K : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hm : 1 ≤ m) (hr : 1 ≤ r) (hK : 0 < K)
    (q : ℕ) (hgrid : 2 ≤ δ * r ^ q)
    (x v : ι → Space) (S : Finset ι) (hS : S.Nonempty)
    (hv : ∀ i ∈ S, ‖v i‖ = 1) (hball : ∀ i ∈ S, Tube δ (x i) (v i) ⊆ ball 0 1)
    (hu : Upper (fun i => Tube δ (x i) (v i)) (δ ^ 2) S m)
    (hstable : ∀ R ⊆ S, (S.card : ℝ) ≤ 2 * R.card →
      coefficient (fun i => Tube δ (x i) (v i)) (δ ^ 2) S ≤
        K * coefficient (fun i => Tube δ (x i) (v i)) (δ ^ 2) R) :
    let T := fun i => Tube δ (x i) (v i)
    let c := coefficient T (δ ^ 2) S
    let B := 1024 * K * r ^ 2
    ∃ (a b : ℝ) (R : Finset ι) (N : ℕ) (W : Fin N → Set Space),
      δ ≤ a ∧ a ≤ b ∧ b ≤ 2 ∧ R ⊆ S ∧ R.Nonempty ∧ 0 < N ∧
      (S.card : ℝ) ≤ 4 * (q + 1 : ℝ) ^ 2 * R.card ∧
      (∀ j, ∃ e : AffineIsometryEquiv ℝ Space Space,
        W j = e '' {p : Space | |p 0| ≤ a ∧ |p 1| ≤ b ∧ |p 2| ≤ 2}) ∧
      (∀ j, Convex ℝ (W j) ∧ volume (W j) = ENNReal.ofReal (16 * a * b)) ∧
      (∀ i ∈ R, ∃ j, T i ⊆ W j) ∧
      (∀ i ∈ R, (ncard {j | T i ⊆ W j} : ℝ) ≤ 64 * B) ∧
      (∀ j, c * a * b ≤ 2 * B * (count T R (W j) : ℝ) * δ ^ 2) := by
  classical
  dsimp only
  let T := fun i => Tube δ (x i) (v i)
  let c := coefficient T (δ ^ 2) S
  let B := 1024 * K * r ^ 2
  have hc : 1 ≤ c := one_le_coefficient hm hu
  have hc0 : 0 ≤ c := by linarith
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hB : 0 < B := by dsimp [B]; positivity
  have huc : Upper T (δ ^ 2) S c := coefficient_upper (sq_nonneg δ) hm hu
  let Good : Finset ι → Prop := fun P => ∃ (e : Frame) (z : Space) (a b : ℝ),
    δ ≤ a ∧ a ≤ b ∧ b ≤ 2 ∧ (∀ i ∈ P, T i ⊆ prism e z a b) ∧
      c * a * b ≤ 1024 * K * (P.card : ℝ) * δ ^ 2
  have select : ∀ R ⊆ S, (S.card : ℝ) ≤ 2 * R.card → R.Nonempty →
      ∃ P : Finset ι, P ⊆ R ∧ P.Nonempty ∧ Good P := by
    intro R hRS hhalf hR
    obtain ⟨P, hPR, hP, e, z, a, b, ha, hab, hb, hcov, hsat⟩ := saturated_block
      hδ hδ1 hm x v R hR (fun i hi => hv i (hRS hi))
      (fun i hi => hball i (hRS hi)) (hu.subset (sq_nonneg δ) hRS)
    refine ⟨P, hPR, hP, e, z, a, b, ha, hab, hb, hcov, ?_⟩
    have h0 := mul_le_mul_of_nonneg_right (hstable R hRS hhalf)
      (mul_nonneg (hδ.le.trans ha) (hδ.le.trans (ha.trans hab)))
    have h1 := mul_le_mul_of_nonneg_left hsat hK.le
    dsimp [c, T] at h0 ⊢
    nlinarith
  obtain ⟨F, hF, hFdisj, hFmass⟩ := disjoint_blocks S Good select
  have hFne : F.Nonempty := by
    by_contra h
    have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [he, Finset.biUnion_empty, Finset.card_empty, Nat.cast_zero, mul_zero] at hFmass
    have hspos : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
    linarith
  let P : F → Finset ι := fun j => j.val
  have hdata (j : F) : Good (P j) := (hF j.val j.property).2.2
  choose e z a₀ b₀ hδa hab hb2 hcover hsat using hdata
  have hPS (j : F) : P j ⊆ S := (hF j.val j.property).2.1
  have hPne (j : F) : (P j).Nonempty := (hF j.val j.property).1
  have hd : (Set.univ : Set F).PairwiseDisjoint P := by
    intro j _ j' _ hne
    exact hFdisj j.property j'.property (fun h => hne (Subtype.ext h))
  have hmass : (S.card : ℝ) ≤ 2 * ∑ j : F, ((P j).card : ℝ) := by
    have he : (F.biUnion id).card = ∑ j : F, (P j).card := by
      rw [Finset.card_biUnion hFdisj, ← Finset.sum_attach]
      rfl
    rw [he, Nat.cast_sum] at hFmass
    exact hFmass
  obtain ⟨grid, color, hgr, hcol⟩ := width_classes hδ (by linarith) hr q hgrid
  let col : F → Fin (q + 1) × Fin (q + 1) := fun j => (color (a₀ j), color (b₀ j))
  obtain ⟨t, ht⟩ := weight_class (Finset.univ : Finset F) col (fun j => ((P j).card : ℝ))
  let J := (Finset.univ : Finset F).filter fun j => col j = t
  have hJd : (↑J : Set F).PairwiseDisjoint P := by
    intro j _ j' _ hne
    exact hd (Set.mem_univ _) (Set.mem_univ _) hne
  let A := min (grid t.1) (grid t.2)
  let D := max (grid t.1) (grid t.2)
  have hδA : δ ≤ A := le_min (hgr _).1 (hgr _).1
  have hAD : A ≤ D := min_le_max
  have hD2 : D ≤ 2 := max_le (hgr _).2 (hgr _).2
  have hA0 : 0 ≤ A := hδ.le.trans hδA
  have hD0 : 0 ≤ D := hA0.trans hAD
  let W₀ : F → Set Space := fun j => prism (e j) (z j) A D
  have hrounded (j : F) (hj : j ∈ J) :
      a₀ j ≤ A ∧ b₀ j ≤ D ∧ A * D ≤ r ^ 2 * (a₀ j * b₀ j) := by
    have hjc : col j = t := (Finset.mem_filter.mp hj).2
    have hj0 : color (a₀ j) = t.1 := congrArg Prod.fst hjc
    have hj1 : color (b₀ j) = t.2 := congrArg Prod.snd hjc
    have hca := hcol (a₀ j) (hδa j) ((hab j).trans (hb2 j))
    have hcb := hcol (b₀ j) ((hδa j).trans (hab j)) (hb2 j)
    rw [hj0] at hca
    rw [hj1] at hcb
    refine ⟨le_min hca.1 ((hab j).trans hcb.1), hcb.1.trans (le_max_right _ _), ?_⟩
    have he : A * D = grid t.1 * grid t.2 := by
      exact min_mul_max _ _
    rw [he]
    have hh := mul_le_mul hca.2 hcb.2 (hδ.le.trans (hgr _).1)
      (mul_nonneg hr0.le (hδ.le.trans (hδa j)))
    nlinarith
  have hWvol (j : F) : volume (W₀ j) = ENNReal.ofReal (16 * A * D) :=
    prism_volume (e j) (z j) hA0 hD0
  have hWconv (j : F) : Convex ℝ (W₀ j) := prism_convex _ _ _ _
  have hWcov (j : F) (hj : j ∈ J) (i) (hi : i ∈ P j) : T i ⊆ W₀ j :=
    (hcover j i hi).trans (prism_mono _ _ (hrounded j hj).1 (hrounded j hj).2.1)
  have hWsat (j : F) (hj : j ∈ J) : c * A * D ≤ B * (P j).card * δ ^ 2 := by
    have h0 := mul_le_mul_of_nonneg_left (hrounded j hj).2.2 hc0
    have h1 := mul_le_mul_of_nonneg_left (hsat j) (sq_nonneg r)
    dsimp [B]
    nlinarith
  have hJS : J.biUnion P ⊆ S := by
    intro i hi
    obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
    exact hPS j hij
  have hJmass : (S.card : ℝ) ≤ 2 * (q + 1 : ℝ) ^ 2 * (J.biUnion P).card := by
    have he : (∑ j ∈ J, ((P j).card : ℝ)) = (J.biUnion P).card := by
      exact_mod_cast (Finset.card_biUnion hJd).symm
    have ht' : (∑ j : F, ((P j).card : ℝ)) ≤ (Fintype.card (Fin (q + 1) × Fin (q + 1)) : ℝ) *
        ∑ j ∈ J, ((P j).card : ℝ) := by
      convert ht using 1 <;> simp [J]
      left
      apply Finset.sum_congr
      · ext j
        simp
      · intro j hj
        rfl
    rw [he] at ht'
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at ht'
    nlinarith
  have hinc (j : F) (hj : j ∈ J) :
      (((J.biUnion P).filter fun i => T i ⊆ W₀ j).card : ℝ) ≤ (16 * B) * (P j).card := by
    have hh := (huc.subset (sq_nonneg δ) hJS).real hc0 (hWconv j)
      (by rw [hWvol]; exact ENNReal.ofReal_ne_top)
    rw [hWvol, ENNReal.toReal_ofReal (by positivity)] at hh
    change (((J.biUnion P).filter fun i => T i ⊆ W₀ j).card : ℝ) * δ ^ 2 ≤ _ at hh
    have hs := hWsat j hj
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hδ)).mp
    nlinarith
  obtain ⟨J', R, hJ'J, hRJ, hRmass, hRcover, hdegree, hRcount⟩ :=
    prune_assigned J P (fun i j => T i ⊆ W₀ j) hJd hWcov (by positivity : 0 < 16 * B) hinc
  have hRne : R.Nonempty := by
    have hspos : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
    have hJpos : (0 : ℝ) < (J.biUnion P).card := by
      by_contra hh
      have : ((J.biUnion P).card : ℝ) = 0 := le_antisymm (le_of_not_gt hh) (Nat.cast_nonneg _)
      rw [this, mul_zero] at hJmass
      linarith
    have : (0 : ℝ) < R.card := by linarith
    exact Finset.card_pos.mp (by exact_mod_cast this)
  have hJ'ne : J'.Nonempty := by
    obtain ⟨i, hi⟩ := hRne
    obtain ⟨j, hj, _⟩ := hRcover i hi
    exact ⟨j, hj⟩
  refine ⟨A, D, R, J'.card, fun j => W₀ (enumerate J' j), hδA, hAD, hD2,
    hRJ.trans hJS, hRne, Finset.card_pos.mpr hJ'ne, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hRmass (by positivity : 0 ≤ 2 * (q + 1 : ℝ) ^ 2)]
  · intro j
    exact prism_image _ _ _ _
  · intro j
    exact ⟨hWconv _, hWvol _⟩
  · intro i hi
    obtain ⟨j, hj, hij⟩ := hRcover i hi
    obtain ⟨k, rfl⟩ := exists_enumerate J' hj
    exact ⟨k, hij⟩
  · intro i hi
    change (ncard {j | T i ⊆ W₀ (enumerate J' j)} : ℝ) ≤ 64 * B
    rw [enumerate_ncard J' (fun j => T i ⊆ W₀ j)]
    have hh := hdegree i hi
    change ((J'.filter fun j => T i ⊆ W₀ j).card : ℝ) ≤ 64 * B
    linarith
  · intro j
    have hj := enumerate_mem J' j
    have h1 := hWsat _ (hJ'J hj)
    have h2 := hRcount _ hj
    change c * A * D ≤ 2 * B * (count T R (W₀ (enumerate J' j)) : ℝ) * δ ^ 2
    have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hB.le (sq_nonneg δ))
    dsimp only [count]
    nlinarith

end
end WangZahlLot.Obl.wz_concentrated_convex_factorization
