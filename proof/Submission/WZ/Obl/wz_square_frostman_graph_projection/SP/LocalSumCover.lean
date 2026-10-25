-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.LocalSumCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.CartesianFrostman
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CoverCounting

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise

/-- Distinct points more than twice the cover radius apart occupy distinct
members of every cover. -/
theorem separated_indexed_card_le_cover {I X : Type*} [Fintype I] [PseudoMetricSpace X]
    (f : I → X) {δ : ℝ} (hsep : ∀ i j, i ≠ j → 2 * δ < dist (f i) (f j))
    {m : ℕ} (cc : Fin m → X) (hcov : Covers δ (Set.range f) cc) :
    (Fintype.card I : ℝ) ≤ (m : ℝ) := by
  classical
  have hchoice (i : I) : ∃ j : Fin m, dist (f i) (cc j) ≤ δ := by
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcov ⟨i, rfl⟩)
    exact ⟨j, hj⟩
  choose g hg using hchoice
  have hinj : Function.Injective g := by
    intro i j hij
    by_contra hne
    have hdist := dist_triangle (f i) (cc (g i)) (f j)
    rw [hij, dist_comm (cc (g j)) (f j)] at hdist
    have hi := hg i
    rw [hij] at hi
    linarith [hg j, hsep i j hne]
  have hcard := Fintype.card_le_of_injective g hinj
  simpa only [Fintype.card_fin] using (Nat.cast_le (α := ℝ)).mpr hcard

/-- A global cover of `A + S`, combined with Frostman control of `A`,
controls covers of every small part of `S`. The scale loss is absolute. -/
theorem local_cover_of_sum_cover (A S : Finset ℝ) {δ C σ R z : ℝ}
    (hδ : 0 < δ) (hδR : δ ≤ R) (hC : 0 ≤ C) (hA : A.Nonempty)
    (hAF : RealFiniteFrostman δ C σ A)
    (hS : ∀ s ∈ S, dist s z ≤ R)
    {m : ℕ} (cc : Fin m → ℝ)
    (hcov : Covers δ (↑(A + S) : Set ℝ) cc) :
    ∃ (n : ℕ) (centers : Fin n → ℝ), Covers (4 * δ) (↑S : Set ℝ) centers ∧
      (n : ℝ) ≤ C * (8 * R) ^ σ * (m : ℝ) := by
  classical
  have hR : 0 < R := hδ.trans_le hδR
  obtain ⟨k, a, haA, hasep, hacov⟩ :=
    exists_separated_cover A.finite_toSet.totallyBounded (by positivity : 0 < 8 * R)
  obtain ⟨n, s, hsS, hssep, hscov⟩ :=
    exists_separated_cover S.finite_toSet.totallyBounded (by positivity : 0 < 4 * δ)
  have hAk : 1 ≤ (k : ℝ) * (C * (8 * R) ^ σ) := by
    have hcount := WangZahlLot.Obl.wz_separated_projection_dichotomy.card_le_cover_mul_fiber_bound A id
      (show Covers (8 * R) (id '' (↑A : Set ℝ)) a by simpa only [Set.image_id] using hacov)
      (fun i => hAF (a i) (8 * R) (by linarith))
    have hAp : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
    apply (mul_le_mul_iff_right₀ hAp).mp
    convert hcount using 1 <;> ring
  have hsdist (i j : Fin n) : dist (s i) (s j) ≤ 2 * R := by
    have hh := dist_triangle (s i) z (s j)
    rw [dist_comm z (s j)] at hh
    linarith [hS (s i) (hsS i), hS (s j) (hsS j)]
  let f (p : Fin k × Fin n) := a p.1 + s p.2
  have hsep (p q : Fin k × Fin n) (hpq : p ≠ q) : 2 * δ < dist (f p) (f q) := by
    by_cases hfirst : p.1 = q.1
    · have hsecond : p.2 ≠ q.2 := fun h => hpq (Prod.ext hfirst h)
      have hh := hssep p.2 q.2 hsecond
      simpa only [f, hfirst, dist_add_left] using (by linarith : 2 * δ < dist (s p.2) (s q.2))
    · have hh := dist_triangle (a p.1 + s p.2) (a q.1 + s q.2) (a q.1 + s p.2)
      rw [dist_add_right, dist_add_left] at hh
      have ha := hasep p.1 q.1 hfirst
      have hs := hsdist q.2 p.2
      dsimp [f]
      linarith
  have hcov' : Covers δ (Set.range f) cc := by
    rintro x ⟨p, rfl⟩
    exact hcov (Finset.add_mem_add (haA p.1) (hsS p.2))
  have hkn := separated_indexed_card_le_cover f hsep cc hcov'
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] at hkn
  refine ⟨n, s, hscov, ?_⟩
  have h1 := mul_le_mul_of_nonneg_right hAk (Nat.cast_nonneg (α := ℝ) n)
  have h2 := mul_le_mul_of_nonneg_left hkn
    (mul_nonneg hC (Real.rpow_nonneg (by positivity : 0 ≤ 8 * R) σ))
  nlinarith only [h1, h2]

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
