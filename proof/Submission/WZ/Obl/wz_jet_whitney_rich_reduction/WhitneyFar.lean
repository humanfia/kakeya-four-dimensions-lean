-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_whitney_rich_reduction.WhitneyFar.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_whitney_rich_reduction.WhitneyReduction

/-!
# The restricted Whitney reduction: far scales and transverse transfer (x0284)

Helpers for the reduction child of x0293's split of o117 (`wz_jet_whitney_rich_reduction`):
the localized bipartite estimate there also assumes the far-scale condition `δ μ δ^(-ε) ≤ D`
and fewer than `μ^2/100` transverse A-B pairs at the point.

* `exists_dense_window`: the scale pigeonhole for an arbitrary set of pairs;
* `closeCount_eq_card`: the frozen close-pair count is the number of close incident pairs;
* `rich_point_whitney_far`: the extraction run over the FAR pairs only, so the chosen scale
  satisfies `R ≤ 1.98 D`;
* `transverseAB_le`: the bipartite transverse count is at most the full transverse count at a
  smaller threshold.
-/

namespace WangZahlLot.Obl.wz_jet_whitney_rich_reduction

open Finset MeasureTheory

noncomputable section

variable {n : ℕ}

/-- Pigeonhole over the scales for an arbitrary set of pairs. -/
theorem exists_dense_window (q : Fin n → EuclideanSpace ℝ (Fin 3)) {δ : ℝ} (hδ : 0 < δ)
    (Q : Finset (Fin n × Fin n)) {L : ℕ} (hLpos : 0 < L)
    (hQ : ∀ ij ∈ Q, δ ≤ dist (q ij.1) (q ij.2) ∧ dist (q ij.1) (q ij.2) < δ * (3 / 2) ^ (L - 1)) :
    ∃ m < L, (Q.card : ℝ) / L ≤ ((Q.filter (fun ij => 1.02 * whitneyScale δ m ≤
      dist (q ij.1) (q ij.2) ∧ dist (q ij.1) (q ij.2) ≤ 1.98 * whitneyScale δ m)).card : ℝ) := by
  classical
  set W : ℕ → Finset (Fin n × Fin n) := fun m => Q.filter (fun ij =>
    1.02 * whitneyScale δ m ≤ dist (q ij.1) (q ij.2) ∧
      dist (q ij.1) (q ij.2) ≤ 1.98 * whitneyScale δ m) with hW
  have hsub : Q ⊆ (range L).biUnion W := by
    intro ij hij
    obtain ⟨m, hm, h1, h2⟩ := exists_window hδ (hQ ij hij).1 (hQ ij hij).2
    rw [Finset.mem_biUnion]
    exact ⟨m, Finset.mem_range.mpr hm, Finset.mem_filter.mpr ⟨hij, h1, h2⟩⟩
  have hle : (Q.card : ℝ) ≤ ∑ m ∈ range L, ((W m).card : ℝ) := by
    have := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    exact_mod_cast this
  have hne : (range L).Nonempty := Finset.nonempty_range_iff.mpr (by omega)
  have hconst : ∑ _m ∈ range L, (Q.card : ℝ) / L = Q.card := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  obtain ⟨m, hm, hmle⟩ := Finset.exists_le_of_sum_le
    (f := fun _ => (Q.card : ℝ) / L) (g := fun m => ((W m).card : ℝ)) hne
    (by rw [hconst]; exact hle)
  exact ⟨m, Finset.mem_range.mp hm, hmle⟩

open Classical in
/-- The close-pair count at `p` is the number of close ordered pairs of incident indices. -/
lemma closeCount_eq_card (S : Fin n → Set (ℝ × ℝ)) (d : Fin n → Fin n → ℝ) (R : ℝ)
    (p : ℝ × ℝ) :
    (∑ i, ∑ j, (if d i j < R then (S i ∩ S j).indicator (fun _ => (1 : ENNReal)) p else 0)) =
      ((((univ.filter (fun i => p ∈ S i)) ×ˢ (univ.filter (fun i => p ∈ S i))).filter
        (fun ij => d ij.1 ij.2 < R)).card : ENNReal) := by
  rw [← Finset.sum_product' (f := fun i j => (if d i j < R then
    (S i ∩ S j).indicator (fun _ => (1 : ENNReal)) p else 0))]
  have h : ∀ ij : Fin n × Fin n, (if d ij.1 ij.2 < R then
      (S ij.1 ∩ S ij.2).indicator (fun _ => (1 : ENNReal)) p else 0) =
      if (d ij.1 ij.2 < R ∧ (p ∈ S ij.1 ∧ p ∈ S ij.2)) then 1 else 0 := by
    intro ij
    by_cases h1 : d ij.1 ij.2 < R
    · by_cases h2 : p ∈ S ij.1 ∩ S ij.2
      · rw [if_pos h1, Set.indicator_of_mem h2, if_pos ⟨h1, h2⟩]
      · rw [if_pos h1, Set.indicator_of_notMem h2, if_neg]
        rintro ⟨-, h3⟩; exact h2 h3
    · rw [if_neg h1, if_neg]
      rintro ⟨h3, -⟩; exact h1 h3
  simp_rw [h]
  rw [Finset.sum_boole]
  congr 2
  ext ij
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
  tauto

open Classical in
/-- Pointwise Whitney extraction at far scales. -/
theorem rich_point_whitney_far (q : Fin n → EuclideanSpace ℝ (Fin 3)) (S : Fin n → Set (ℝ × ℝ))
    {δ lam R : ℝ} (hδ : 0 < δ) (hq : ∀ i, ‖q i‖ ≤ 10) {L : ℕ} (hδ1 : δ ≤ 1)
    (hL : 20 < δ * (3 / 2) ^ (L - 1)) (hlam : 1 < lam) (hRδ : δ ≤ R) {p : ℝ × ℝ}
    (hp : ENNReal.ofReal lam ≤ multOn S univ p)
    (hfar : ((univ.filter (fun i => p ∈ S i)).card : ℝ) ^ 2 / 2 ≤
      ((((univ.filter (fun i => p ∈ S i)) ×ˢ (univ.filter (fun i => p ∈ S i))).filter
        (fun ij => R ≤ dist (q ij.1) (q ij.2))).card : ℝ)) :
    ∃ m < L, R ≤ 1.98 * whitneyScale δ m ∧ ∃ kk ∈ whitneyPairs q (whitneyScale δ m),
      p ∈ biRichSet q S (whitneyScale δ m) ((lam - 1) / (4 * 801 ^ 3 * L)) kk := by
  classical
  set F := univ.filter (fun i => p ∈ S i) with hF
  set Q := (F ×ˢ F).filter (fun ij => R ≤ dist (q ij.1) (q ij.2)) with hQ
  have hLpos : 0 < L := by
    by_contra h0
    push Not at h0
    have : L = 0 := by omega
    subst this
    norm_num at hL
    linarith
  have hcard : lam ≤ (F.card : ℝ) := by
    rw [multOn_eq_card] at hp
    rw [← ENNReal.ofReal_natCast] at hp
    exact (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg _)).mp hp
  have hFpos : (0 : ℝ) < F.card := by linarith
  obtain ⟨m, hm, hshell⟩ := exists_dense_window q hδ Q hLpos (by
    intro ij hij
    have h := (Finset.mem_filter.mp hij).2
    exact ⟨hRδ.trans h, (dist_le_twenty hq _ _).trans_lt hL⟩)
  set D := whitneyScale δ m with hD_def
  have hD : 0 < D := whitneyScale_pos hδ m
  have hLr : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hQpos : (0 : ℝ) < (Q.filter (fun ij => 1.02 * D ≤ dist (q ij.1) (q ij.2) ∧
      dist (q ij.1) (q ij.2) ≤ 1.98 * D)).card := by
    have h1 : (0 : ℝ) < (Q.card : ℝ) / L := by
      apply div_pos _ hLr
      have : (0 : ℝ) < (F.card : ℝ) ^ 2 / 2 := by positivity
      linarith
    linarith
  obtain ⟨ij, hij⟩ := Finset.card_pos.mp (by exact_mod_cast hQpos)
  have hRD : R ≤ 1.98 * D := by
    have h1 := (Finset.mem_filter.mp hij).2
    have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hij).1).2
    linarith [h1.2]
  set μ := (lam - 1) / (4 * 801 ^ 3 * L) with hμ_def
  have hμ0 : 0 ≤ μ := by
    rw [hμ_def]; apply div_nonneg (by linarith); positivity
  have hsubW : Q.filter (fun ij => 1.02 * D ≤ dist (q ij.1) (q ij.2) ∧
      dist (q ij.1) (q ij.2) ≤ 1.98 * D) ⊆ (F ×ˢ F).filter (fun ij =>
      1.02 * D ≤ dist (q ij.1) (q ij.2) ∧ dist (q ij.1) (q ij.2) ≤ 1.98 * D) := by
    intro ij hij
    rw [Finset.mem_filter] at hij ⊢
    exact ⟨(Finset.mem_filter.mp hij.1).1, hij.2⟩
  have hW : ((Q.filter (fun ij => 1.02 * D ≤ dist (q ij.1) (q ij.2) ∧
      dist (q ij.1) (q ij.2) ≤ 1.98 * D)).card : ℝ) ≤ (((F ×ˢ F).filter (fun ij =>
      1.02 * D ≤ dist (q ij.1) (q ij.2) ∧ dist (q ij.1) (q ij.2) ≤ 1.98 * D)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubW
  have hkey : 2 * μ * 801 ^ 3 * F.card < (F.card : ℝ) ^ 2 / 2 / L := by
    rw [hμ_def, lt_div_iff₀ hLr]
    have h1 : 2 * ((lam - 1) / (4 * 801 ^ 3 * L)) * 801 ^ 3 * F.card * L =
        (lam - 1) / 2 * F.card := by
      field_simp
      ring
    rw [h1]
    have h2 : (F.card : ℝ) ^ 2 / 2 = F.card / 2 * F.card := by ring
    rw [h2]
    apply mul_lt_mul_of_pos_right _ hFpos
    linarith
  have hQL : (F.card : ℝ) ^ 2 / 2 / L ≤ (Q.card : ℝ) / L :=
    div_le_div_of_nonneg_right hfar hLr.le
  obtain ⟨kk, hkk, h1, h2⟩ := exists_rich_whitney_pair q hD hμ0 F
    ((hkey.trans_le hQL).trans_le (hshell.trans hW))
  refine ⟨m, hm, hRD, kk, hkk, ?_, ?_⟩
  · rw [multOn_eq_card]
    have : (cubeSet q (D / 200) kk.1).filter (fun i => p ∈ S i) =
        F ∩ cubeSet q (D / 200) kk.1 := by
      ext i; simp [hF, Finset.mem_filter, Finset.mem_inter, and_comm]
    rw [this, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal h1
  · rw [multOn_eq_card]
    have : (cubeSet q (D / 200) kk.2).filter (fun i => p ∈ S i) =
        F ∩ cubeSet q (D / 200) kk.2 := by
      ext i; simp [hF, Finset.mem_filter, Finset.mem_inter, and_comm]
    rw [this, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal h2

/-- The bipartite transverse count is at most the full transverse count at a smaller
threshold. -/
lemma transverseAB_le (S : Fin n → Set (ℝ × ℝ)) (d : Fin n → Fin n → ℝ)
    (hd : ∀ i j, 0 ≤ d i j) (gap : Fin n → Fin n → ℝ × ℝ → ℝ) {κ κ' : ℝ} (hκ : κ ≤ κ')
    (A B : Finset (Fin n)) (hAB : ∀ i ∈ A, ∀ j ∈ B, i ≠ j) (p : ℝ × ℝ) :
    ∑ i ∈ A, ∑ j ∈ B, (S i ∩ S j ∩ {p | κ' * d i j ≤ gap i j p}).indicator
        (fun _ => (1 : ENNReal)) p ≤
      ∑ i, ∑ j, (if i = j then 0 else (S i ∩ S j ∩ {p | κ * d i j ≤ gap i j p}).indicator
        (fun _ => (1 : ENNReal)) p) := by
  calc ∑ i ∈ A, ∑ j ∈ B, (S i ∩ S j ∩ {p | κ' * d i j ≤ gap i j p}).indicator
        (fun _ => (1 : ENNReal)) p
      ≤ ∑ i ∈ A, ∑ j ∈ B, (if i = j then 0 else
          (S i ∩ S j ∩ {p | κ * d i j ≤ gap i j p}).indicator (fun _ => (1 : ENNReal)) p) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        rw [if_neg (hAB i hi j hj)]
        apply Set.indicator_le_indicator_of_subset _ (fun _ => zero_le)
        intro x hx
        refine ⟨hx.1, ?_⟩
        have h1 : κ * d i j ≤ κ' * d i j := mul_le_mul_of_nonneg_right hκ (hd i j)
        exact h1.trans hx.2
    _ ≤ ∑ i, ∑ j ∈ B, (if i = j then 0 else
          (S i ∩ S j ∩ {p | κ * d i j ≤ gap i j p}).indicator (fun _ => (1 : ENNReal)) p) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun _ _ _ => zero_le)
    _ ≤ ∑ i, ∑ j, (if i = j then 0 else
          (S i ∩ S j ∩ {p | κ * d i j ≤ gap i j p}).indicator (fun _ => (1 : ENNReal)) p) := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B) (fun _ _ _ => zero_le)

end

end WangZahlLot.Obl.wz_jet_whitney_rich_reduction
