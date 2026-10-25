-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.PolyMethod.LineCells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# A line meets few sign cells

`line_sign_cells_ncard`: for polynomials `P j` on `ℝ³` and a line `t ↦ a + t • u`, the number
of sign patterns `s : Fin J → Bool` realized on the line is at most `∑ j, deg (P j) + 1`.

If some `P j` vanishes identically on the line no pattern is realized. Otherwise the
restrictions `q j` are nonzero univariate polynomials of degree `≤ deg (P j)`; a realized
pattern is determined by the number of roots of `∏ j, q j` below any of its witnesses (between
consecutive roots no `q j` changes sign, by the intermediate value theorem).
-/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.PolyMethod

namespace LineAux

/-- The restriction of `P` to the line `t ↦ a + t • u`, as a univariate polynomial in `t`. -/
noncomputable def lineRestrict (P : MvPolynomial (Fin 3) ℝ) (a u : EuclideanSpace ℝ (Fin 3)) :
    Polynomial ℝ :=
  MvPolynomial.aeval (fun i => Polynomial.C (u i) * Polynomial.X + Polynomial.C (a i)) P

lemma eval_lineRestrict (P : MvPolynomial (Fin 3) ℝ) (a u : EuclideanSpace ℝ (Fin 3)) (t : ℝ) :
    (lineRestrict P a u).eval t = MvPolynomial.eval (fun i => (a + t • u) i) P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [lineRestrict]
  | add p q hp hq =>
    simp only [lineRestrict, map_add, Polynomial.eval_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p n hp =>
    simp only [lineRestrict, map_mul, Polynomial.eval_mul, MvPolynomial.aeval_X] at hp ⊢
    rw [hp, MvPolynomial.eval_X]
    congr 1
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

lemma natDegree_lineRestrict_le (P : MvPolynomial (Fin 3) ℝ) (a u : EuclideanSpace ℝ (Fin 3)) :
    (lineRestrict P a u).natDegree ≤ P.totalDegree := by
  have := MvPolynomial.aeval_natDegree_le (m := P.totalDegree) (n := 1) P le_rfl
    (fun i => Polynomial.C (u i) * Polynomial.X + Polynomial.C (a i))
    (fun i => Polynomial.natDegree_linear_le)
  simpa [lineRestrict] using this

lemma exists_root_of_sign_change {p : Polynomial ℝ} {t1 t2 : ℝ} (h1 : 0 < p.eval t1)
    (h2 : p.eval t2 < 0) : ∃ r ∈ Set.uIcc t1 t2, p.eval r = 0 := by
  obtain ⟨r, hr, hr0⟩ := intermediate_value_uIcc (a := t1) (b := t2) (f := fun x => p.eval x)
    p.continuous.continuousOn (Set.mem_uIcc.2 (Or.inr ⟨h2.le, h1.le⟩))
  exact ⟨r, hr, hr0⟩

lemma card_filter_lt_lt_of_mem {R : Finset ℝ} {t1 t2 r : ℝ} (hr : r ∈ R) (h1 : t1 ≤ r)
    (h2 : r < t2) : (R.filter (· < t1)).card < (R.filter (· < t2)).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨r, Finset.mem_filter.2 ⟨hr, h2⟩,
      fun h => absurd (Finset.mem_filter.1 h).2 (not_lt.2 h1)⟩
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, by linarith [hx.2]⟩

end LineAux

open LineAux in
/-- A line meets at most `∑ deg + 1` sign cells. -/
theorem line_sign_cells_ncard (J : ℕ) (P : Fin J → MvPolynomial (Fin 3) ℝ)
    (a u : EuclideanSpace ℝ (Fin 3)) :
    {s : Fin J → Bool | ∃ t : ℝ, ∀ j,
        if s j = true then 0 < MvPolynomial.eval (fun i => (a + t • u) i) (P j)
        else MvPolynomial.eval (fun i => (a + t • u) i) (P j) < 0}.ncard ≤
      (∑ j, (P j).totalDegree) + 1 := by
  classical
  set q : Fin J → Polynomial ℝ := fun j => lineRestrict (P j) a u with hq_def
  have hqe : ∀ j t, (q j).eval t = MvPolynomial.eval (fun i => (a + t • u) i) (P j) :=
    fun j t => eval_lineRestrict _ _ _ _
  simp only [← hqe]
  set S := {s : Fin J → Bool | ∃ t : ℝ, ∀ j,
      if s j = true then 0 < (q j).eval t else (q j).eval t < 0} with hS
  by_cases hzero : ∃ j, q j = 0
  · obtain ⟨j0, hj0⟩ := hzero
    have hSe : S = ∅ := by
      ext s
      simp only [hS, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      intro t ht
      have h := ht j0
      rw [hj0, Polynomial.eval_zero] at h
      split_ifs at h <;> exact lt_irrefl _ h
    rw [hSe, Set.ncard_empty]
    exact Nat.zero_le _
  simp only [not_exists] at hzero
  set Q : Polynomial ℝ := ∏ j, q j with hQ_def
  have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hzero j
  set R : Finset ℝ := Q.roots.toFinset with hR_def
  have hRcard : R.card ≤ ∑ j, (P j).totalDegree := by
    calc R.card ≤ Q.roots.card := Multiset.toFinset_card_le _
      _ ≤ Q.natDegree := Polynomial.card_roots' _
      _ ≤ ∑ j, (q j).natDegree := Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ j, (P j).totalDegree :=
          Finset.sum_le_sum fun j _ => natDegree_lineRestrict_le _ _ _
  have hmemR : ∀ r, (∃ j, (q j).eval r = 0) → r ∈ R := by
    rintro r ⟨j, hj⟩
    rw [hR_def, Multiset.mem_toFinset, Polynomial.mem_roots hQ0, Polynomial.IsRoot.def,
      hQ_def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) hj
  have hnotR : ∀ r, r ∈ R → ∃ j, (q j).eval r = 0 := by
    intro r hr
    rw [hR_def, Multiset.mem_toFinset, Polynomial.mem_roots hQ0, Polynomial.IsRoot.def,
      hQ_def, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hr
    obtain ⟨j, _, hj⟩ := hr
    exact ⟨j, hj⟩
  have hwit : ∀ s ∈ S, ∃ t : ℝ, ∀ j,
      if s j = true then 0 < (q j).eval t else (q j).eval t < 0 := fun s hs => hs
  choose! τ hτ using hwit
  have hτR : ∀ s ∈ S, τ s ∉ R := by
    intro s hs hR
    obtain ⟨j, hj⟩ := hnotR _ hR
    have h := hτ s hs j
    rw [hj] at h
    split_ifs at h <;> exact lt_irrefl _ h
  let F : (Fin J → Bool) → ℕ := fun s => (R.filter (· < τ s)).card
  have hF_mem : ∀ s ∈ S, F s ∈ (Finset.range (R.card + 1) : Set ℕ) := by
    intro s _
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (Finset.card_filter_le _ _)
  have hF_inj : Set.InjOn F S := by
    intro s1 hs1 s2 hs2 hF
    by_contra hne
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
    have hroot : ∃ r ∈ Set.uIcc (τ s1) (τ s2), (q j).eval r = 0 := by
      have h1 := hτ s1 hs1 j
      have h2 := hτ s2 hs2 j
      cases hb1 : s1 j <;> cases hb2 : s2 j <;> simp only [hb1, hb2] at h1 h2 hj
      · exact absurd rfl hj
      · obtain ⟨r, hr, hr0⟩ := exists_root_of_sign_change h2 h1
        exact ⟨r, Set.uIcc_comm (τ s1) (τ s2) ▸ hr, hr0⟩
      · exact exists_root_of_sign_change h1 h2
      · exact absurd rfl hj
    obtain ⟨r, hr, hr0⟩ := hroot
    have hrR : r ∈ R := hmemR r ⟨j, hr0⟩
    have hr1 : r ≠ τ s1 := fun h => hτR s1 hs1 (h ▸ hrR)
    have hr2 : r ≠ τ s2 := fun h => hτR s2 hs2 (h ▸ hrR)
    rcases Set.mem_uIcc.1 hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (card_filter_lt_lt_of_mem hrR h1 (lt_of_le_of_ne h2 hr2)).ne hF
    · exact (card_filter_lt_lt_of_mem hrR h1 (lt_of_le_of_ne h2 hr1)).ne' hF
  calc S.ncard ≤ (Finset.range (R.card + 1) : Set ℕ).ncard :=
        Set.ncard_le_ncard_of_injOn F hF_mem hF_inj (Finset.finite_toSet _)
    _ = R.card + 1 := by rw [Set.ncard_coe_finset, Finset.card_range]
    _ ≤ (∑ j, (P j).totalDegree) + 1 := by omega

end WangZahlLot.Obl.wz_coarse_tube_grains.PolyMethod
