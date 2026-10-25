-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.PathLemma.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# The graph lemma of Balog–Szemerédi–Gowers

A dense bipartite relation `G ⊆ A × B` contains large sets `A' ⊆ A`, `B' ⊆ B` such that
every pair `(a, b) ∈ A' × B'` is joined by many paths `a – y – x – b` of length three in `G`.
The sets do not depend on any additive structure, so the lemma can be used for all
projections of `G` at once (`DenseProjection.lean`).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open scoped BigOperators

section PathLemma

variable {X Y : Type*} [DecidableEq X] [DecidableEq Y]

/-- The paths `a – y – x – b` of length three in `G`, recorded as the pairs `(x, y)`. -/
def pathSet (A : Finset X) (B : Finset Y) (G : Finset (X × Y)) (a : X) (b : Y) :
    Finset (X × Y) :=
  (A ×ˢ B).filter (fun q => (a, q.2) ∈ G ∧ q ∈ G ∧ (q.1, b) ∈ G)

omit [DecidableEq X] [DecidableEq Y] in
theorem card_filter_product_eq_sum (s : Finset X) (t : Finset Y) (P : X × Y → Prop)
    [DecidablePred P] :
    ((s ×ˢ t).filter P).card = ∑ x ∈ s, (t.filter (fun y => P (x, y))).card := by
  rw [Finset.card_filter, Finset.sum_product]
  exact Finset.sum_congr rfl (fun x _ => (Finset.card_filter _ _).symm)

omit [DecidableEq X] [DecidableEq Y] in
theorem sum_card_filter_swap (s : Finset X) (t : Finset Y) (P : X → Y → Prop)
    [∀ x y, Decidable (P x y)] :
    ∑ y ∈ t, (s.filter (fun x => P x y)).card = ∑ x ∈ s, (t.filter (fun y => P x y)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

/-- The neighbourhood of `y` inside `S`. -/
def leftNbhd (S : Finset X) (G : Finset (X × Y)) (y : Y) : Finset X :=
  S.filter (fun x => (x, y) ∈ G)

/-- The common neighbourhood of `x` and `x'` inside `B`. -/
def commonNbhd (B : Finset Y) (G : Finset (X × Y)) (x x' : X) : Finset Y :=
  B.filter (fun y => (x, y) ∈ G ∧ (x', y) ∈ G)

/-- Double counting of the pairs of left vertices with a common neighbour. -/
theorem sum_card_pairs_filter (S : Finset X) (B : Finset Y) (G : Finset (X × Y))
    (P : X → X → Prop) [∀ x x', Decidable (P x x')] :
    ∑ y ∈ B, (((leftNbhd S G y) ×ˢ (leftNbhd S G y)).filter (fun p => P p.1 p.2)).card =
      ∑ x ∈ S, ∑ x' ∈ S, if P x x' then (commonNbhd B G x x').card else 0 := by
  have h1 (y : Y) : (((leftNbhd S G y) ×ˢ (leftNbhd S G y)).filter (fun p => P p.1 p.2)).card =
      ∑ x ∈ S, ∑ x' ∈ S,
        if (x, y) ∈ G ∧ (x', y) ∈ G ∧ P x x' then 1 else 0 := by
    rw [Finset.card_filter, Finset.sum_product]
    simp only [leftNbhd, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    split_ifs with hx
    · refine Finset.sum_congr rfl (fun x' _ => ?_)
      by_cases hx' : (x', y) ∈ G <;> by_cases hp : P x x' <;> simp [hx, hx', hp]
    · symm
      apply Finset.sum_eq_zero
      intro x' _
      simp [hx]
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x' _ => ?_)
  by_cases hp : P x x'
  · simp only [hp, ite_true, commonNbhd, Finset.card_filter, and_true]
  · simp [hp]

/-- The degree of `x` into `B`. -/
def rightDeg (B : Finset Y) (G : Finset (X × Y)) (x : X) : ℕ :=
  (B.filter (fun y => (x, y) ∈ G)).card

/-- Pairs of `S` with fewer than `θ` common neighbours. -/
noncomputable def badPairs (S : Finset X) (B : Finset Y) (G : Finset (X × Y)) (θ : ℝ) :
    Finset (X × X) :=
  (S ×ˢ S).filter (fun p => ((commonNbhd B G p.1 p.2).card : ℝ) < θ)

theorem card_eq_sum_rightDeg (A : Finset X) (B : Finset Y) (G : Finset (X × Y))
    (hG : G ⊆ A ×ˢ B) : (G.card : ℝ) = ∑ x ∈ A, (rightDeg B G x : ℝ) := by
  have hGeq : G = (A ×ˢ B).filter (fun q => q ∈ G) := by
    ext q
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨hG h, h⟩, fun h => h.2⟩
  have h1 : G.card = ((A ×ˢ B).filter (fun q => q ∈ G)).card := congrArg Finset.card hGeq
  rw [h1, card_filter_product_eq_sum]
  push_cast
  rfl

/-- Steps A and C of the graph lemma: a vertex `y0` whose neighbourhood `X2` among the
high-degree vertices is large and has few bad pairs. -/
theorem bsg_popular_vertex (A : Finset X) (B : Finset Y) (G : Finset (X × Y))
    (hG : G ⊆ A ×ˢ B) (hA : A.Nonempty) (hB : B.Nonempty) {α : ℝ} (hα : 0 < α)
    (hdense : α * (A.card : ℝ) * (B.card : ℝ) ≤ (G.card : ℝ)) :
    ∃ X2 : Finset X, X2 ⊆ A ∧ (∀ x ∈ X2, α * (B.card : ℝ) / 2 ≤ (rightDeg B G x : ℝ)) ∧
      α * (A.card : ℝ) / 3 ≤ (X2.card : ℝ) ∧
      (16 / α) * ((badPairs X2 B G (α ^ 3 / 128 * (B.card : ℝ))).card : ℝ) ≤
        (X2.card : ℝ) ^ 2 := by
  classical
  obtain ⟨nA, hnA⟩ : ∃ n : ℝ, n = (A.card : ℝ) := ⟨_, rfl⟩
  obtain ⟨nB, hnB⟩ : ∃ n : ℝ, n = (B.card : ℝ) := ⟨_, rfl⟩
  rw [← hnA, ← hnB] at hdense ⊢
  have hnA0 : 0 < nA := by rw [hnA]; exact_mod_cast hA.card_pos
  have hnB0 : 0 < nB := by rw [hnB]; exact_mod_cast hB.card_pos
  have hGsum := card_eq_sum_rightDeg A B G hG
  -- Step A
  obtain ⟨X1, hX1⟩ : ∃ S : Finset X, S = A.filter (fun x => α * nB / 2 ≤ (rightDeg B G x : ℝ)) :=
    ⟨_, rfl⟩
  have hX1A : X1 ⊆ A := hX1 ▸ Finset.filter_subset _ _
  have hX1deg : ∀ x ∈ X1, α * nB / 2 ≤ (rightDeg B G x : ℝ) := by
    intro x hx
    rw [hX1] at hx
    exact (Finset.mem_filter.mp hx).2
  have hX1sum : α * nA * nB / 2 ≤ ∑ x ∈ X1, (rightDeg B G x : ℝ) := by
    have hsplit := Finset.sum_filter_add_sum_filter_not A
      (fun x => α * nB / 2 ≤ (rightDeg B G x : ℝ)) (fun x => (rightDeg B G x : ℝ))
    have hlow : ∑ x ∈ A.filter (fun x => ¬ α * nB / 2 ≤ (rightDeg B G x : ℝ)),
        (rightDeg B G x : ℝ) ≤ nA * (α * nB / 2) := by
      calc _ ≤ ∑ x ∈ A.filter (fun x => ¬ α * nB / 2 ≤ (rightDeg B G x : ℝ)), α * nB / 2 :=
            Finset.sum_le_sum (fun x hx => (not_le.mp (Finset.mem_filter.mp hx).2).le)
        _ = ((A.filter (fun x => ¬ α * nB / 2 ≤ (rightDeg B G x : ℝ))).card : ℝ) *
              (α * nB / 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ nA * (α * nB / 2) := by
            gcongr
            rw [hnA]
            exact_mod_cast Finset.card_filter_le _ _
    rw [hX1]
    linarith
  -- Step C
  have hfsum : ∑ y ∈ B, ((leftNbhd X1 G y).card : ℝ) = ∑ x ∈ X1, (rightDeg B G x : ℝ) := by
    have h := sum_card_filter_swap X1 B (fun x y => (x, y) ∈ G)
    exact_mod_cast h
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = α ^ 3 / 128 * nB := ⟨_, rfl⟩
  have hsq : ∑ y ∈ B, ((leftNbhd X1 G y).card : ℝ) ^ 2 =
      ∑ x ∈ X1, ∑ x' ∈ X1, ((commonNbhd B G x x').card : ℝ) := by
    have h := sum_card_pairs_filter X1 B G (fun _ _ => True)
    simp only [Finset.filter_true, ite_true, Finset.card_product] at h
    have h' : ∑ y ∈ B, (((leftNbhd X1 G y).card * (leftNbhd X1 G y).card : ℕ) : ℝ) =
        ∑ x ∈ X1, ∑ x' ∈ X1, (((commonNbhd B G x x').card : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [← h']
    refine Finset.sum_congr rfl (fun y _ => ?_)
    push_cast
    ring
  have hbad : ∑ y ∈ B, ((badPairs (leftNbhd X1 G y) B G θ).card : ℝ) ≤ nA ^ 2 * θ := by
    have h := sum_card_pairs_filter X1 B G (fun x x' => ((commonNbhd B G x x').card : ℝ) < θ)
    have h' : ∑ y ∈ B, ((badPairs (leftNbhd X1 G y) B G θ).card : ℝ) =
        ∑ x ∈ X1, ∑ x' ∈ X1, ((if ((commonNbhd B G x x').card : ℝ) < θ then
          (commonNbhd B G x x').card else 0 : ℕ) : ℝ) := by
      simp only [badPairs]
      exact_mod_cast h
    rw [h']
    have hX1c : (X1.card : ℝ) ≤ nA := by rw [hnA]; exact_mod_cast Finset.card_le_card hX1A
    have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
    calc ∑ x ∈ X1, ∑ x' ∈ X1, ((if ((commonNbhd B G x x').card : ℝ) < θ then
          (commonNbhd B G x x').card else 0 : ℕ) : ℝ)
        ≤ ∑ x ∈ X1, ∑ x' ∈ X1, θ := by
          apply Finset.sum_le_sum
          intro x _
          apply Finset.sum_le_sum
          intro x' _
          by_cases hb : ((commonNbhd B G x x').card : ℝ) < θ
          · simp only [hb, ite_true]
            exact hb.le
          · simp only [hb, ite_false, Nat.cast_zero]
            exact hθ0
      _ = (X1.card : ℝ) ^ 2 * θ := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ nA ^ 2 * θ := by gcongr
  have hcs : (∑ y ∈ B, ((leftNbhd X1 G y).card : ℝ)) ^ 2 ≤
      nB * ∑ y ∈ B, ((leftNbhd X1 G y).card : ℝ) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := B) (f := fun y => ((leftNbhd X1 G y).card : ℝ))
    rw [hnB]
    simpa using this
  have hmain : ∑ y ∈ B, α ^ 2 * nA ^ 2 / 8 ≤ ∑ y ∈ B, (((leftNbhd X1 G y).card : ℝ) ^ 2 -
      (16 / α) * ((badPairs (leftNbhd X1 G y) B G θ).card : ℝ)) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, ← hnB]
    have hfs : α * nA * nB / 2 ≤ ∑ y ∈ B, ((leftNbhd X1 G y).card : ℝ) := hfsum ▸ hX1sum
    have hsq2 : (α * nA * nB / 2) ^ 2 ≤ nB * ∑ y ∈ B, ((leftNbhd X1 G y).card : ℝ) ^ 2 :=
      (pow_le_pow_left₀ (by positivity) hfs 2).trans hcs
    have hlb : (16 / α) * ∑ y ∈ B, ((badPairs (leftNbhd X1 G y) B G θ).card : ℝ) ≤
        (16 / α) * (nA ^ 2 * θ) := mul_le_mul_of_nonneg_left hbad (by positivity)
    have hid : (16 / α) * (nA ^ 2 * θ) = nA ^ 2 * nB * (α ^ 2 / 8) := by
      rw [hθ]; field_simp; ring
    have hsq3 : nB * (α ^ 2 * nA ^ 2 / 4) ≤ ∑ y ∈ B, ((leftNbhd X1 G y).card : ℝ) ^ 2 := by
      have : nB * (nB * (α ^ 2 * nA ^ 2 / 4)) ≤
          nB * ∑ y ∈ B, ((leftNbhd X1 G y).card : ℝ) ^ 2 := by
        have e : nB * (nB * (α ^ 2 * nA ^ 2 / 4)) = (α * nA * nB / 2) ^ 2 := by ring
        rw [e]; exact hsq2
      exact le_of_mul_le_mul_left this hnB0
    have e2 : nB * (α ^ 2 * nA ^ 2 / 8) = nB * (α ^ 2 * nA ^ 2 / 4) - nA ^ 2 * nB * (α ^ 2 / 8) := by
      ring
    rw [e2]
    linarith
  obtain ⟨y0, hy0B, hy0⟩ := Finset.exists_le_of_sum_le hB hmain
  refine ⟨leftNbhd X1 G y0, (Finset.filter_subset _ _).trans hX1A,
    fun x hx => hX1deg x (Finset.mem_filter.mp hx).1, ?_, ?_⟩
  · have hbn : (0 : ℝ) ≤ (16 / α) * ((badPairs (leftNbhd X1 G y0) B G θ).card : ℝ) := by
      positivity
    have h9 : (α * nA / 3) ^ 2 ≤ ((leftNbhd X1 G y0).card : ℝ) ^ 2 := by
      have e : (α * nA / 3) ^ 2 = α ^ 2 * nA ^ 2 / 9 := by ring
      have : α ^ 2 * nA ^ 2 / 9 ≤ α ^ 2 * nA ^ 2 / 8 := by
        have : 0 ≤ α ^ 2 * nA ^ 2 := by positivity
        linarith
      linarith
    have hpos : 0 ≤ α * nA / 3 := by positivity
    exact (pow_le_pow_iff_left₀ hpos (Nat.cast_nonneg _) (by norm_num)).mp h9
  · rw [← hθ]
    have : 0 ≤ α ^ 2 * nA ^ 2 / 8 := by positivity
    linarith

/-- **Graph lemma of Balog–Szemerédi–Gowers.** In a relation `G ⊆ A × B` of density `α`,
there are `A' ⊆ A` and `B' ⊆ B` of proportional size such that every pair of `A' × B'` is
joined by at least `α ^ 5 * #A * #B / 3072` paths of length three. -/
theorem bsg_path_lemma (A : Finset X) (B : Finset Y) (G : Finset (X × Y)) (hG : G ⊆ A ×ˢ B)
    (hA : A.Nonempty) (hB : B.Nonempty) {α : ℝ} (hα : 0 < α)
    (hdense : α * (A.card : ℝ) * (B.card : ℝ) ≤ (G.card : ℝ)) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, α * (A.card : ℝ) / 6 ≤ (A'.card : ℝ) ∧
      α * (B.card : ℝ) / 4 ≤ (B'.card : ℝ) ∧
      ∀ a ∈ A', ∀ b ∈ B',
        α ^ 5 * (A.card : ℝ) * (B.card : ℝ) / 3072 ≤ ((pathSet A B G a b).card : ℝ) := by
  classical
  obtain ⟨X2, hX2A, hX2deg, hX2low, hX2bad⟩ := bsg_popular_vertex A B G hG hA hB hα hdense
  obtain ⟨nA, hnA⟩ : ∃ n : ℝ, n = (A.card : ℝ) := ⟨_, rfl⟩
  obtain ⟨nB, hnB⟩ : ∃ n : ℝ, n = (B.card : ℝ) := ⟨_, rfl⟩
  rw [← hnA] at hX2low ⊢
  rw [← hnB] at hX2bad hX2deg ⊢
  have hnA0 : 0 < nA := by rw [hnA]; exact_mod_cast hA.card_pos
  have hnB0 : 0 < nB := by rw [hnB]; exact_mod_cast hB.card_pos
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = α ^ 3 / 128 * nB := ⟨_, rfl⟩
  rw [← hθ] at hX2bad
  obtain ⟨m2, hm2⟩ : ∃ m : ℝ, m = (X2.card : ℝ) := ⟨_, rfl⟩
  rw [← hm2] at hX2low hX2bad
  have hm2pos : 0 < m2 := lt_of_lt_of_le (by positivity) hX2low
  -- Step D
  let bc : X → ℕ := fun x => (X2.filter (fun x' => ((commonNbhd B G x x').card : ℝ) < θ)).card
  have hbcsum : ∑ x ∈ X2, (bc x : ℝ) = ((badPairs X2 B G θ).card : ℝ) := by
    have h := card_filter_product_eq_sum X2 X2
      (fun p => ((commonNbhd B G p.1 p.2).card : ℝ) < θ)
    simp only [badPairs]
    exact_mod_cast h.symm
  obtain ⟨A', hA'⟩ : ∃ S : Finset X, S = X2.filter (fun x => (bc x : ℝ) ≤ α * m2 / 8) :=
    ⟨_, rfl⟩
  have hA'X2 : A' ⊆ X2 := hA' ▸ Finset.filter_subset _ _
  have hA'bc : ∀ a ∈ A', (bc a : ℝ) ≤ α * m2 / 8 := by
    intro a ha
    rw [hA'] at ha
    exact (Finset.mem_filter.mp ha).2
  have hA'card : m2 / 2 ≤ (A'.card : ℝ) := by
    obtain ⟨R, hR⟩ : ∃ S : Finset X, S = X2.filter (fun x => ¬ (bc x : ℝ) ≤ α * m2 / 8) :=
      ⟨_, rfl⟩
    have hRA : (A'.card : ℝ) + (R.card : ℝ) = m2 := by
      rw [hA', hR, hm2]
      exact_mod_cast Finset.card_filter_add_card_filter_not _
    have hRsum : (R.card : ℝ) * (α * m2 / 8) ≤ ∑ x ∈ R, (bc x : ℝ) := by
      calc (R.card : ℝ) * (α * m2 / 8) = ∑ x ∈ R, α * m2 / 8 := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ x ∈ R, (bc x : ℝ) := by
            apply Finset.sum_le_sum
            intro x hx
            rw [hR] at hx
            exact (not_le.mp (Finset.mem_filter.mp hx).2).le
    have hRle : ∑ x ∈ R, (bc x : ℝ) ≤ ∑ x ∈ X2, (bc x : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (hR ▸ Finset.filter_subset _ _)
        (fun _ _ _ => Nat.cast_nonneg _)
    -- (16/α) * bad ≤ m2^2, so R * (α m2 / 8) ≤ α m2^2 / 16
    have hbad' : ((badPairs X2 B G θ).card : ℝ) ≤ α * m2 ^ 2 / 16 := by
      have h := hX2bad
      rw [div_mul_eq_mul_div, div_le_iff₀ hα] at h
      linarith
    have hR2 : (R.card : ℝ) * (α * m2 / 8) ≤ α * m2 ^ 2 / 16 := by linarith
    have hR3 : (R.card : ℝ) ≤ m2 / 2 := by
      have hαm : 0 < α * m2 := by positivity
      have e : α * m2 ^ 2 / 16 = (m2 / 2) * (α * m2 / 8) := by ring
      rw [e] at hR2
      exact le_of_mul_le_mul_right hR2 (by positivity)
    linarith
  have hA'low : α * nA / 6 ≤ (A'.card : ℝ) := by linarith
  -- Step E
  obtain ⟨B', hB'⟩ : ∃ S : Finset Y,
      S = B.filter (fun y => α * m2 / 4 ≤ ((leftNbhd X2 G y).card : ℝ)) := ⟨_, rfl⟩
  have hB'B : B' ⊆ B := hB' ▸ Finset.filter_subset _ _
  have hB'mem : ∀ y ∈ B', α * m2 / 4 ≤ ((leftNbhd X2 G y).card : ℝ) := by
    intro y hy
    rw [hB'] at hy
    exact (Finset.mem_filter.mp hy).2
  have hB'low : α * nB / 4 ≤ (B'.card : ℝ) := by
    have hsw : ∑ y ∈ B, ((leftNbhd X2 G y).card : ℝ) = ∑ x ∈ X2, (rightDeg B G x : ℝ) := by
      have h := sum_card_filter_swap X2 B (fun x y => (x, y) ∈ G)
      exact_mod_cast h
    have hlow : m2 * (α * nB / 2) ≤ ∑ x ∈ X2, (rightDeg B G x : ℝ) := by
      calc m2 * (α * nB / 2) = ∑ x ∈ X2, α * nB / 2 := by
            rw [Finset.sum_const, nsmul_eq_mul, hm2]
        _ ≤ ∑ x ∈ X2, (rightDeg B G x : ℝ) := Finset.sum_le_sum hX2deg
    have hsplit := Finset.sum_filter_add_sum_filter_not B
      (fun y => α * m2 / 4 ≤ ((leftNbhd X2 G y).card : ℝ))
      (fun y => ((leftNbhd X2 G y).card : ℝ))
    rw [← hB'] at hsplit
    have hin : ∑ y ∈ B', ((leftNbhd X2 G y).card : ℝ) ≤ (B'.card : ℝ) * m2 := by
      calc ∑ y ∈ B', ((leftNbhd X2 G y).card : ℝ) ≤ ∑ y ∈ B', m2 := by
            apply Finset.sum_le_sum
            intro y _
            rw [hm2]
            exact_mod_cast Finset.card_filter_le _ _
        _ = (B'.card : ℝ) * m2 := by rw [Finset.sum_const, nsmul_eq_mul]
    have hout : ∑ y ∈ B.filter (fun y => ¬ α * m2 / 4 ≤ ((leftNbhd X2 G y).card : ℝ)),
        ((leftNbhd X2 G y).card : ℝ) ≤ nB * (α * m2 / 4) := by
      calc _ ≤ ∑ y ∈ B.filter (fun y => ¬ α * m2 / 4 ≤ ((leftNbhd X2 G y).card : ℝ)),
            α * m2 / 4 :=
            Finset.sum_le_sum (fun y hy => (not_le.mp (Finset.mem_filter.mp hy).2).le)
        _ = ((B.filter (fun y => ¬ α * m2 / 4 ≤
              ((leftNbhd X2 G y).card : ℝ))).card : ℝ) * (α * m2 / 4) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ nB * (α * m2 / 4) := by
            gcongr
            rw [hnB]
            exact_mod_cast Finset.card_filter_le _ _
    have hkey : m2 * (α * nB / 4) ≤ (B'.card : ℝ) * m2 := by nlinarith
    have hkey' : (α * nB / 4) * m2 ≤ (B'.card : ℝ) * m2 := by linarith
    exact le_of_mul_le_mul_right hkey' hm2pos
  -- Step F
  refine ⟨A', hA'X2.trans hX2A, B', hB'B, hA'low, hB'low, ?_⟩
  intro a ha b hb
  obtain ⟨Good, hGood⟩ : ∃ S : Finset X,
      S = (leftNbhd X2 G b).filter (fun x' => ¬ ((commonNbhd B G a x').card : ℝ) < θ) :=
    ⟨_, rfl⟩
  have hGoodcard : α * m2 / 8 ≤ (Good.card : ℝ) := by
    have hsplit : (((leftNbhd X2 G b).filter
          (fun x' => ((commonNbhd B G a x').card : ℝ) < θ)).card : ℝ) + (Good.card : ℝ) =
        ((leftNbhd X2 G b).card : ℝ) := by
      rw [hGood]
      exact_mod_cast Finset.card_filter_add_card_filter_not _
    have hsub : (leftNbhd X2 G b).filter (fun x' => ((commonNbhd B G a x').card : ℝ) < θ) ⊆
        X2.filter (fun x' => ((commonNbhd B G a x').card : ℝ) < θ) :=
      Finset.filter_subset_filter _ (Finset.filter_subset _ _)
    have hle : (((leftNbhd X2 G b).filter
          (fun x' => ((commonNbhd B G a x').card : ℝ) < θ)).card : ℝ) ≤ (bc a : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have h1 := hB'mem b hb
    have h2 := hA'bc a ha
    linarith
  have hsubset : (Good ×ˢ B).filter (fun q => (a, q.2) ∈ G ∧ (q.1, q.2) ∈ G) ⊆
      pathSet A B G a b := by
    intro q hq
    obtain ⟨hqprod, hqa, hqG⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hqprod
    rw [hGood] at hq1
    have hq1N : q.1 ∈ leftNbhd X2 G b := (Finset.mem_filter.mp hq1).1
    have hq1X2 : q.1 ∈ X2 := (Finset.mem_filter.mp hq1N).1
    have hq1b : (q.1, b) ∈ G := (Finset.mem_filter.mp hq1N).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hX2A hq1X2, hq2⟩, hqa, ?_, hq1b⟩
    simpa using hqG
  have hcount : ((Good ×ˢ B).filter (fun q => (a, q.2) ∈ G ∧ (q.1, q.2) ∈ G)).card =
      ∑ x' ∈ Good, (commonNbhd B G a x').card := by
    rw [card_filter_product_eq_sum]
    rfl
  have hcodeg : ∀ x' ∈ Good, θ ≤ ((commonNbhd B G a x').card : ℝ) := by
    intro x' hx'
    rw [hGood] at hx'
    exact not_lt.mp (Finset.mem_filter.mp hx').2
  have hsum : (Good.card : ℝ) * θ ≤ ((pathSet A B G a b).card : ℝ) := by
    calc (Good.card : ℝ) * θ = ∑ x' ∈ Good, θ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x' ∈ Good, ((commonNbhd B G a x').card : ℝ) := Finset.sum_le_sum hcodeg
      _ = (((Good ×ˢ B).filter (fun q => (a, q.2) ∈ G ∧ (q.1, q.2) ∈ G)).card : ℝ) := by
          rw [hcount]; push_cast; rfl
      _ ≤ ((pathSet A B G a b).card : ℝ) := by exact_mod_cast Finset.card_le_card hsubset
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have h1 : α * (α * nA / 3) / 8 ≤ (Good.card : ℝ) := by
    have : α * (α * nA / 3) / 8 ≤ α * m2 / 8 := by gcongr
    linarith
  have h2 : α * (α * nA / 3) / 8 * θ ≤ (Good.card : ℝ) * θ :=
    mul_le_mul_of_nonneg_right h1 hθ0
  have hid : α * (α * nA / 3) / 8 * θ = α ^ 5 * nA * nB / 3072 := by
    rw [hθ]; ring
  linarith

end PathLemma

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
