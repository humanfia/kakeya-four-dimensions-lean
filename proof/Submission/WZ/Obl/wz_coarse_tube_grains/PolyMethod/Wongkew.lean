-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.PolyMethod.Wongkew.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# A Wongkew-type bound by recursion on the degree

For a grid of closed cubes of side `h` with corner `c` in `ℝ³` (coordinates `Fin 3 → ℝ`), a cube
meeting the zero set of a nonzero polynomial `Q` either meets it on an edge (counted with
univariate root bounds on grid lines and Schwartz–Zippel for grid lines inside `Z(Q)`), or
contains a zero of a nonzero partial derivative of `Q` (an interior extremum of `Q` on a face or
on the cube). Induction on the degree gives at most `27 · 3^D · N^2` cubes of an `N × N × N` grid,
hence `|N_ρ(Z(Q)) ∩ cube_s| ≤ C · 3^D · ρ · s^2`.
-/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.PolyMethod
namespace Wongkew

open MvPolynomial

/-- The closed cube with index `k` of the grid with corner `c` and spacing `h`. -/
def gcube (c : Fin 3 → ℝ) (h : ℝ) {N : ℕ} (k : Fin 3 → Fin N) : Set (Fin 3 → ℝ) :=
  {x | ∀ a, c a + (k a : ℝ) * h ≤ x a ∧ x a ≤ c a + ((k a : ℝ) + 1) * h}

/-- `x` lies on an edge of the grid cube `k`: it is in the cube and two of its coordinates are
endpoints of the cube's coordinate intervals. -/
def OnEdge (c : Fin 3 → ℝ) (h : ℝ) {N : ℕ} (k : Fin 3 → Fin N) (x : Fin 3 → ℝ) : Prop :=
  x ∈ gcube c h k ∧ ∃ a b, a ≠ b ∧
    (x a = c a + (k a : ℝ) * h ∨ x a = c a + ((k a : ℝ) + 1) * h) ∧
    (x b = c b + (k b : ℝ) * h ∨ x b = c b + ((k b : ℝ) + 1) * h)

namespace EdgeAux

theorem card_cells_le_two (c0 r : ℝ) {h : ℝ} (hh : 0 < h) (N : ℕ) :
    (Finset.univ.filter (fun i : Fin N =>
      c0 + (i : ℝ) * h ≤ r ∧ r ≤ c0 + ((i : ℝ) + 1) * h)).card ≤ 2 := by
  classical
  have key : ∀ i j : Fin N, (c0 + (i : ℝ) * h ≤ r ∧ r ≤ c0 + ((i : ℝ) + 1) * h) →
      (c0 + (j : ℝ) * h ≤ r ∧ r ≤ c0 + ((j : ℝ) + 1) * h) → (j : ℕ) ≤ (i : ℕ) + 1 := by
    intro i j hi hj
    have h1 : (j : ℝ) * h ≤ ((i : ℝ) + 1) * h := by linarith [hi.2, hj.1]
    have h2 : (j : ℝ) ≤ (i : ℝ) + 1 := le_of_mul_le_mul_right h1 hh
    exact_mod_cast h2
  by_contra H
  obtain ⟨i, hi, j, hj, l, hl, hij, hil, hjl⟩ := Finset.two_lt_card.mp (not_le.mp H)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj hl
  have := key i j hi hj
  have := key j i hj hi
  have := key i l hi hl
  have := key l i hl hi
  have := key j l hj hl
  have := key l j hl hj
  have hij' : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
  have hil' : (i : ℕ) ≠ l := fun e => hil (Fin.ext e)
  have hjl' : (j : ℕ) ≠ l := fun e => hjl (Fin.ext e)
  omega

open Classical in
theorem card_root_cells_le (q : Polynomial ℝ) (hq : q ≠ 0) (c0 : ℝ) {h : ℝ} (hh : 0 < h)
    (N : ℕ) :
    (Finset.univ.filter (fun i : Fin N => ∃ t, c0 + (i : ℝ) * h ≤ t ∧
      t ≤ c0 + ((i : ℝ) + 1) * h ∧ q.eval t = 0)).card ≤ 2 * q.natDegree := by
  classical
  calc _ ≤ (q.roots.toFinset.biUnion (fun r => Finset.univ.filter (fun i : Fin N =>
          c0 + (i : ℝ) * h ≤ r ∧ r ≤ c0 + ((i : ℝ) + 1) * h))).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        obtain ⟨t, ht1, ht2, ht3⟩ := hi
        simp only [Finset.mem_biUnion, Multiset.mem_toFinset, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact ⟨t, (Polynomial.mem_roots hq).mpr ht3, ht1, ht2⟩
    _ ≤ ∑ r ∈ q.roots.toFinset, (Finset.univ.filter (fun i : Fin N =>
          c0 + (i : ℝ) * h ≤ r ∧ r ≤ c0 + ((i : ℝ) + 1) * h)).card := Finset.card_biUnion_le
    _ ≤ ∑ r ∈ q.roots.toFinset, 2 := Finset.sum_le_sum (fun r _ => card_cells_le_two c0 r hh N)
    _ = 2 * q.roots.toFinset.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 2 * q.natDegree := by
        gcongr
        exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' q)

theorem third_axis : ∀ a b : Fin 3, a ≠ b →
    ∃ a' : Fin 3, a' ≠ a ∧ a' ≠ b ∧ ∀ b', b' ≠ a' → b' = a ∨ b' = b := by
  decide

open Classical in
/-- Cubes meeting the zero set on an edge segment parallel to axis `0`, the other two
coordinates of the segment being `g 0 (k 1)` and `g 1 (k 2)`. -/
theorem card_axis0_le (D : ℕ) (Q : MvPolynomial (Fin 3) ℝ) (hQ : Q ≠ 0)
    (hdeg : Q.totalDegree ≤ D) (c0 : ℝ) {h : ℝ} (hh : 0 < h) (N : ℕ)
    (g : Fin 2 → Fin N → ℝ) (hg : ∀ j, Function.Injective (g j)) :
    (Finset.univ.filter (fun k : Fin 3 → Fin N => ∃ t, c0 + (k 0 : ℝ) * h ≤ t ∧
        t ≤ c0 + ((k 0 : ℝ) + 1) * h ∧
        eval (Fin.cons t (fun j => g j (k j.succ)) : Fin 3 → ℝ) Q = 0)).card ≤
      3 * D * N ^ 2 := by
  classical
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
  set Qt := finSuccEquiv ℝ 2 Q with hQt
  have hQt0 : Qt ≠ 0 := by
    rw [hQt]; exact (EmbeddingLike.map_ne_zero_iff).mpr hQ
  let pt : (Fin 2 → Fin N) → (Fin 2 → ℝ) := fun ℓ j => g j (ℓ j)
  let q : (Fin 2 → Fin N) → Polynomial ℝ := fun ℓ => Qt.map (eval (pt ℓ))
  have hq_eval : ∀ ℓ t, (q ℓ).eval t = eval (Fin.cons t (pt ℓ) : Fin 3 → ℝ) Q := by
    intro ℓ t
    rw [eval_eq_eval_mv_eval']
  have hq_deg : ∀ ℓ, (q ℓ).natDegree ≤ D := by
    intro ℓ
    calc (q ℓ).natDegree ≤ Qt.natDegree := Polynomial.natDegree_map_le
      _ = degreeOf 0 Q := natDegree_finSuccEquiv Q
      _ ≤ Q.totalDegree := degreeOf_le_totalDegree Q 0
      _ ≤ D := hdeg
  set P := Qt.leadingCoeff with hPdef
  have hP : P ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQt0
  have hPdeg : P.totalDegree ≤ D := by
    have := totalDegree_coeff_finSuccEquiv_add_le Q Qt.natDegree hP
    have h2 : P.totalDegree ≤ Q.totalDegree := by
      simp only [hPdef, Polynomial.leadingCoeff, hQt] at this ⊢
      omega
    omega
  have hqP : ∀ ℓ, q ℓ = 0 → eval (pt ℓ) P = 0 := by
    intro ℓ hℓ
    have := congrArg (fun p => Polynomial.coeff p Qt.natDegree) hℓ
    simpa [q, Polynomial.coeff_map] using this
  -- Schwartz–Zippel: few lines on which the restriction of `Q` vanishes identically
  have hbad : (Finset.univ.filter (fun ℓ : Fin 2 → Fin N => q ℓ = 0)).card ≤ D * N := by
    let Sg : Fin 2 → Finset ℝ := fun j => Finset.univ.image (g j)
    have hSg : ∀ j, (Sg j).card = N := fun j => by
      simp [Sg, Finset.card_image_of_injective _ (hg j)]
    have h1 : (Finset.univ.filter (fun ℓ : Fin 2 → Fin N => q ℓ = 0)).card ≤
        ((Fintype.piFinset Sg).filter (fun x => eval x P = 0)).card := by
      apply Finset.card_le_card_of_injOn pt
      · intro ℓ hℓ
        simp only [Finset.coe_filter, Finset.mem_univ, true_and,
          Fintype.mem_piFinset] at hℓ ⊢
        refine ⟨fun j => ?_, hqP ℓ hℓ⟩
        simp [Sg, pt]
      · intro ℓ1 _ ℓ2 _ heq
        funext j
        exact hg j (congrFun heq j)
    have h2 := schwartz_zippel_sup_sum hP Sg
    have h3 : (P.support.sup fun s ↦ ∑ i, ((s i : ℚ≥0) / ((Sg i).card : ℚ≥0))) ≤
        (D : ℚ≥0) / N := by
      apply Finset.sup_le
      intro s hs
      simp only [hSg]
      rw [← Finset.sum_div]
      gcongr
      have := le_totalDegree hs
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
      exact_mod_cast this.trans hPdeg
    rw [show (∏ i, ((Sg i).card : ℚ≥0)) = (N : ℚ≥0) ^ 2 by simp [hSg]] at h2
    have h4 := h2.trans h3
    have hNpos : (0 : ℚ≥0) < N := by exact_mod_cast hN
    rw [div_le_div_iff₀ (by positivity) hNpos] at h4
    have h5 : (((Fintype.piFinset Sg).filter (fun x => eval x P = 0)).card : ℚ≥0) ≤ D * N := by
      have : (((Fintype.piFinset Sg).filter (fun x => eval x P = 0)).card : ℚ≥0) * N ≤
          (D * N) * N := by
        calc _ ≤ (D : ℚ≥0) * N ^ 2 := h4
          _ = (D * N) * N := by ring
      exact le_of_mul_le_mul_right this hNpos
    exact h1.trans (by exact_mod_cast h5)
  -- count along each line
  set S := (Finset.univ.filter (fun k : Fin 3 → Fin N => ∃ t, c0 + (k 0 : ℝ) * h ≤ t ∧
        t ≤ c0 + ((k 0 : ℝ) + 1) * h ∧
        eval (Fin.cons t (fun j => g j (k j.succ)) : Fin 3 → ℝ) Q = 0)) with hS
  have hfiber : ∀ ℓ : Fin 2 → Fin N, (S.filter (fun k => Fin.tail k = ℓ)).card ≤
      (if q ℓ = 0 then N else 2 * D) := by
    intro ℓ
    have h1 : (S.filter (fun k => Fin.tail k = ℓ)).card ≤
        (Finset.univ.filter (fun i : Fin N => ∃ t, c0 + (i : ℝ) * h ≤ t ∧
          t ≤ c0 + ((i : ℝ) + 1) * h ∧ (q ℓ).eval t = 0)).card := by
      apply Finset.card_le_card_of_injOn (fun k => k 0)
      · intro k hk
        simp only [hS, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and]
          at hk ⊢
        obtain ⟨⟨t, ht1, ht2, ht3⟩, hkℓ⟩ := hk
        refine ⟨t, ht1, ht2, ?_⟩
        rw [hq_eval]
        subst hkℓ
        exact ht3
      · intro k1 hk1 k2 hk2 heq
        simp only [hS, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and]
          at hk1 hk2
        rw [← Fin.cons_self_tail k1, ← Fin.cons_self_tail k2, hk1.2, hk2.2]
        simp only at heq
        rw [heq]
    split_ifs with hq0
    · exact h1.trans ((Finset.card_le_univ _).trans (by simp))
    · exact h1.trans ((card_root_cells_le (q ℓ) hq0 c0 hh N).trans (by linarith [hq_deg ℓ]))
  calc S.card = ∑ ℓ : Fin 2 → Fin N, (S.filter (fun k => Fin.tail k = ℓ)).card :=
        Finset.card_eq_sum_card_fiberwise (fun k _ => Finset.mem_univ (Fin.tail k))
    _ ≤ ∑ ℓ : Fin 2 → Fin N, (if q ℓ = 0 then N else 2 * D) :=
        Finset.sum_le_sum (fun ℓ _ => hfiber ℓ)
    _ ≤ ∑ ℓ : Fin 2 → Fin N, (2 * D + if q ℓ = 0 then N else 0) := by
        apply Finset.sum_le_sum; intro ℓ _; split_ifs <;> omega
    _ = 2 * D * N ^ 2 + N * (Finset.univ.filter (fun ℓ : Fin 2 → Fin N => q ℓ = 0)).card := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
          Fintype.card_fin, Fintype.card_fin, Finset.sum_ite, Finset.sum_const_zero,
          Finset.sum_const, smul_eq_mul, smul_eq_mul]
        ring
    _ ≤ 2 * D * N ^ 2 + N * (D * N) := by gcongr
    _ = 3 * D * N ^ 2 := by ring

open Classical in
/-- The cubes meeting the zero set on one of the edge segments parallel to axis `a` whose other two
coordinates are `c b + (k b + e j) * h` for `b = swap 0 a j.succ`. -/
theorem card_class_le (D : ℕ) (Q : MvPolynomial (Fin 3) ℝ) (hQ : Q ≠ 0)
    (hdeg : Q.totalDegree ≤ D) (c : Fin 3 → ℝ) {h : ℝ} (hh : 0 < h) (N : ℕ) (a : Fin 3)
    (e : Fin 2 → ℝ) :
    (Finset.univ.filter (fun k : Fin 3 → Fin N => ∃ x ∈ gcube c h k, eval x Q = 0 ∧
        ∀ j : Fin 2, x (Equiv.swap 0 a j.succ) =
          c (Equiv.swap 0 a j.succ) + ((k (Equiv.swap 0 a j.succ) : ℝ) + e j) * h)).card ≤
      3 * D * N ^ 2 := by
  classical
  set σ := Equiv.swap (0 : Fin 3) a with hσ
  have hσσ : ∀ i, σ (σ i) = i := fun i => Equiv.swap_apply_self _ _ _
  have hσ0 : σ 0 = a := Equiv.swap_apply_left _ _
  let g : Fin 2 → Fin N → ℝ := fun j l => c (σ j.succ) + ((l : ℝ) + e j) * h
  have hg : ∀ j, Function.Injective (g j) := by
    intro j l1 l2 hl
    simp only [g] at hl
    have h1 : ((l1 : ℝ) + e j) * h = ((l2 : ℝ) + e j) * h := add_left_cancel hl
    have h2 : ((l1 : ℕ) : ℝ) = (l2 : ℕ) := by
      have := mul_right_cancel₀ hh.ne' h1
      linarith
    exact Fin.ext (by exact_mod_cast h2)
  have hQ' : rename σ Q ≠ 0 := fun h0 =>
    hQ (rename_injective σ σ.injective (by rw [h0, map_zero]))
  have hdeg' : (rename σ Q).totalDegree ≤ D := (totalDegree_rename_le σ Q).trans hdeg
  refine le_trans ?_ (card_axis0_le D (rename σ Q) hQ' hdeg' (c a) hh N g hg)
  apply Finset.card_le_card_of_injOn (fun k => k ∘ σ)
  · intro k hk
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hk ⊢
    obtain ⟨x, hx, hx0, hxe⟩ := hk
    have hxa := hx a
    refine ⟨x a, ?_, ?_, ?_⟩
    · simpa [Function.comp, hσ0] using hxa.1
    · simpa [Function.comp, hσ0] using hxa.2
    · rw [eval_rename]
      have key : ∀ i' : Fin 3,
          (Fin.cons (x a) (fun j => g j ((k ∘ σ) j.succ)) : Fin 3 → ℝ) i' = x (σ i') := by
        intro i'
        refine Fin.cases ?_ (fun j => ?_) i'
        · simp [hσ0]
        · simp only [Fin.cons_succ, g, Function.comp]
          exact (hxe j).symm
      have hpt : ((Fin.cons (x a) (fun j => g j ((k ∘ σ) j.succ)) : Fin 3 → ℝ) ∘ σ) = x := by
        funext i
        exact (key (σ i)).trans (congrArg x (hσσ i))
      rw [hpt]
      exact hx0
  · intro k1 _ k2 _ heq
    funext i
    have := congrFun heq (σ i)
    simpa [hσσ] using this

end EdgeAux

open Classical in
/-- Cubes whose edges meet the zero set. -/
theorem card_edge_cubes_le (D : ℕ) (Q : MvPolynomial (Fin 3) ℝ) (hQ : Q ≠ 0)
    (hdeg : Q.totalDegree ≤ D) (c : Fin 3 → ℝ) {h : ℝ} (hh : 0 < h) (N : ℕ) :
    (Finset.univ.filter (fun k : Fin 3 → Fin N =>
      ∃ x, OnEdge c h k x ∧ eval x Q = 0)).card ≤ 36 * D * N ^ 2 := by
  classical
  let cls : Fin 3 × (Fin 2 → Fin 2) → Finset (Fin 3 → Fin N) := fun p =>
    Finset.univ.filter (fun k : Fin 3 → Fin N => ∃ x ∈ gcube c h k, eval x Q = 0 ∧
        ∀ j : Fin 2, x (Equiv.swap 0 p.1 j.succ) =
          c (Equiv.swap 0 p.1 j.succ) +
            ((k (Equiv.swap 0 p.1 j.succ) : ℝ) + (((p.2 j : ℕ) : ℝ))) * h)
  have hcover : (Finset.univ.filter (fun k : Fin 3 → Fin N =>
      ∃ x, OnEdge c h k x ∧ eval x Q = 0)) ⊆ Finset.univ.biUnion cls := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    obtain ⟨x, ⟨hx, a, b, hab, ha, hb⟩, hx0⟩ := hk
    obtain ⟨a', ha'a, ha'b, hothers⟩ := EdgeAux.third_axis a b hab
    have hend : ∀ b', b' ≠ a' →
        (x b' = c b' + (k b' : ℝ) * h ∨ x b' = c b' + ((k b' : ℝ) + 1) * h) := by
      intro b' hb'
      rcases hothers b' hb' with rfl | rfl
      · exact ha
      · exact hb
    have hσne : ∀ j : Fin 2, Equiv.swap 0 a' j.succ ≠ a' := by
      intro j heq
      have : Equiv.swap 0 a' j.succ = Equiv.swap 0 a' 0 := by rw [heq, Equiv.swap_apply_left]
      exact Fin.succ_ne_zero j ((Equiv.swap 0 a').injective this)
    let ε : Fin 2 → Fin 2 := fun j =>
      if x (Equiv.swap 0 a' j.succ) =
          c (Equiv.swap 0 a' j.succ) + (k (Equiv.swap 0 a' j.succ) : ℝ) * h then 0 else 1
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine ⟨(a', ε), ?_⟩
    simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨x, hx, hx0, fun j => ?_⟩
    simp only [ε]
    split_ifs with hj
    · simp [hj]
    · rcases hend _ (hσne j) with h1 | h1
      · exact absurd h1 hj
      · simp [h1]
  calc _ ≤ (Finset.univ.biUnion cls).card := Finset.card_le_card hcover
    _ ≤ ∑ p, (cls p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p : Fin 3 × (Fin 2 → Fin 2), 3 * D * N ^ 2 :=
        Finset.sum_le_sum (fun p _ => EdgeAux.card_class_le D Q hQ hdeg c hh N p.1
          (fun j => ((p.2 j : ℕ) : ℝ)))
    _ = 36 * D * N ^ 2 := by simp; ring


namespace ExtremumAux

/-- Derivative of a polynomial along a coordinate line. -/
theorem hasDerivAt_eval_update (Q : MvPolynomial (Fin 3) ℝ) (x : Fin 3 → ℝ) (a : Fin 3)
    (t : ℝ) :
    HasDerivAt (fun s => eval (Function.update x a s) Q)
      (eval (Function.update x a t) (pderiv a Q)) t := by
  induction Q using MvPolynomial.induction_on generalizing t with
  | C r => simpa [pderiv_C] using hasDerivAt_const t r
  | add p q hp hq =>
    simp only [map_add]
    exact (hp t).add (hq t)
  | mul_X p i hp =>
    have hX : HasDerivAt (fun s => Function.update x a s i)
        (eval (Function.update x a t) (pderiv a (X i))) t := by
      by_cases hi : i = a
      · subst hi
        simp only [Function.update_self, pderiv_X_self, map_one]
        exact hasDerivAt_id t
      · simp only [Function.update_of_ne hi, pderiv_X_of_ne hi, map_zero]
        exact hasDerivAt_const t (x i)
    have h2 := (hp t).mul hX
    simp only [map_mul, eval_X, pderiv_mul, map_add]
    exact h2

/-- If `pderiv a Q = 0`, then `Q` is constant along coordinate lines in direction `a`. -/
theorem eval_update_of_pderiv_eq_zero (Q : MvPolynomial (Fin 3) ℝ) (a : Fin 3)
    (hQ : pderiv a Q = 0) (x : Fin 3 → ℝ) (s : ℝ) :
    eval (Function.update x a s) Q = eval x Q := by
  have hd : ∀ t, HasDerivAt (fun s => eval (Function.update x a s) Q) 0 t := by
    intro t
    simpa [hQ] using hasDerivAt_eval_update Q x a t
  have := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv)
    s (x a)
  simpa [Function.update_eq_self] using this

/-- Fermat's rule along a coordinate line, minimum version. -/
theorem eval_pderiv_eq_zero_of_isMinOn (Q : MvPolynomial (Fin 3) ℝ) {S : Set (Fin 3 → ℝ)}
    {p : Fin 3 → ℝ} (hp : IsMinOn (fun x => eval x Q) S p) (b : Fin 3)
    (hS : ∀ᶠ s in nhds (p b), Function.update p b s ∈ S) :
    eval p (pderiv b Q) = 0 := by
  have hmin : IsLocalMin (fun s => eval (Function.update p b s) Q) (p b) := by
    filter_upwards [hS] with s hs
    rw [Function.update_eq_self]
    exact isMinOn_iff.mp hp _ hs
  have := hmin.hasDerivAt_eq_zero (hasDerivAt_eval_update Q p b (p b))
  rwa [Function.update_eq_self] at this

/-- Fermat's rule along a coordinate line, maximum version. -/
theorem eval_pderiv_eq_zero_of_isMaxOn (Q : MvPolynomial (Fin 3) ℝ) {S : Set (Fin 3 → ℝ)}
    {p : Fin 3 → ℝ} (hp : IsMaxOn (fun x => eval x Q) S p) (b : Fin 3)
    (hS : ∀ᶠ s in nhds (p b), Function.update p b s ∈ S) :
    eval p (pderiv b Q) = 0 := by
  have hmax : IsLocalMax (fun s => eval (Function.update p b s) Q) (p b) := by
    filter_upwards [hS] with s hs
    rw [Function.update_eq_self]
    exact isMaxOn_iff.mp hp _ hs
  have := hmax.hasDerivAt_eq_zero (hasDerivAt_eval_update Q p b (p b))
  rwa [Function.update_eq_self] at this

theorem update_mem_gcube {c : Fin 3 → ℝ} {h : ℝ} {N : ℕ} {k : Fin 3 → Fin N}
    {x : Fin 3 → ℝ} (hx : x ∈ gcube c h k) (a : Fin 3) {s : ℝ}
    (hs1 : c a + (k a : ℝ) * h ≤ s) (hs2 : s ≤ c a + ((k a : ℝ) + 1) * h) :
    Function.update x a s ∈ gcube c h k := by
  intro i
  by_cases hi : i = a
  · subst hi
    simp only [Function.update_self]
    exact ⟨hs1, hs2⟩
  · simp only [Function.update_of_ne hi]
    exact hx i

theorem isCompact_gcube (c : Fin 3 → ℝ) (h : ℝ) {N : ℕ} (k : Fin 3 → Fin N) :
    IsCompact (gcube c h k) := by
  have : gcube c h k = Set.pi Set.univ
      (fun a => Set.Icc (c a + (k a : ℝ) * h) (c a + ((k a : ℝ) + 1) * h)) := by
    ext x
    simp only [gcube, Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Icc]
  rw [this]
  exact isCompact_univ_pi (fun a => isCompact_Icc)

theorem third_axis : ∀ a b : Fin 3, a ≠ b → ∃ d, d ≠ a ∧ d ≠ b ∧ ∀ i, i = a ∨ i = b ∨ i = d := by
  decide

/-- A point of the cube that is not on an edge has two distinct free coordinates. -/
theorem exists_two_free {c : Fin 3 → ℝ} {h : ℝ} {N : ℕ} {k : Fin 3 → Fin N} {p : Fin 3 → ℝ}
    (hpB : p ∈ gcube c h k) (hpE : ¬ OnEdge c h k p) :
    ∃ a b : Fin 3, a ≠ b ∧
      (c a + (k a : ℝ) * h < p a ∧ p a < c a + ((k a : ℝ) + 1) * h) ∧
      (c b + (k b : ℝ) * h < p b ∧ p b < c b + ((k b : ℝ) + 1) * h) := by
  have hne : ∀ a b : Fin 3, a ≠ b →
      (p a = c a + (k a : ℝ) * h ∨ p a = c a + ((k a : ℝ) + 1) * h) →
      ¬ (p b = c b + (k b : ℝ) * h ∨ p b = c b + ((k b : ℝ) + 1) * h) :=
    fun a b hab ha hb => hpE ⟨hpB, a, b, hab, ha, hb⟩
  have strict : ∀ i, ¬ (p i = c i + (k i : ℝ) * h ∨ p i = c i + ((k i : ℝ) + 1) * h) →
      (c i + (k i : ℝ) * h < p i ∧ p i < c i + ((k i : ℝ) + 1) * h) := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := not_or.mp hi
    exact ⟨lt_of_le_of_ne (hpB i).1 (Ne.symm hi1), lt_of_le_of_ne (hpB i).2 hi2⟩
  by_cases h0 : (p 0 = c 0 + (k 0 : ℝ) * h ∨ p 0 = c 0 + ((k 0 : ℝ) + 1) * h)
  · exact ⟨1, 2, by decide, strict 1 (hne 0 1 (by decide) h0), strict 2 (hne 0 2 (by decide) h0)⟩
  · by_cases h1 : (p 1 = c 1 + (k 1 : ℝ) * h ∨ p 1 = c 1 + ((k 1 : ℝ) + 1) * h)
    · exact ⟨0, 2, by decide, strict 0 h0, strict 2 (hne 1 2 (by decide) h1)⟩
    · exact ⟨0, 1, by decide, strict 0 h0, strict 1 h1⟩

theorem isPreconnected_seg (x : Fin 3 → ℝ) (i : Fin 3) (u v : ℝ) :
    IsPreconnected ((fun s => Function.update x i s) '' Set.Icc u v) := by
  have hc : Continuous (fun s : ℝ => Function.update x i s) :=
    continuous_const.update i continuous_id
  exact isPreconnected_Icc.image _ hc.continuousOn

theorem seg_subset_edges {c : Fin 3 → ℝ} {h : ℝ} {N : ℕ} {k : Fin 3 → Fin N}
    {x : Fin 3 → ℝ} (hx : x ∈ gcube c h k) (i a b : Fin 3) (hab : a ≠ b) (hai : a ≠ i)
    (hbi : b ≠ i)
    (ha : x a = c a + (k a : ℝ) * h ∨ x a = c a + ((k a : ℝ) + 1) * h)
    (hb : x b = c b + (k b : ℝ) * h ∨ x b = c b + ((k b : ℝ) + 1) * h) :
    (fun s => Function.update x i s) '' Set.Icc (c i + (k i : ℝ) * h) (c i + ((k i : ℝ) + 1) * h)
      ⊆ {y | OnEdge c h k y} := by
  rintro _ ⟨s, hs, rfl⟩
  refine ⟨update_mem_gcube hx i hs.1 hs.2, a, b, hab, ?_, ?_⟩
  · simpa only [Function.update_of_ne hai] using ha
  · simpa only [Function.update_of_ne hbi] using hb

/-- The union of the edges of a grid cube is preconnected. -/
theorem isPreconnected_edges (c : Fin 3 → ℝ) {h : ℝ} (hh : 0 < h) {N : ℕ}
    (k : Fin 3 → Fin N) : IsPreconnected {x | OnEdge c h k x} := by
  have hle : ∀ a, c a + (k a : ℝ) * h ≤ c a + ((k a : ℝ) + 1) * h := fun a => by linarith
  refine isPreconnected_of_forall (fun a => c a + (k a : ℝ) * h) ?_
  rintro y ⟨hyB, a, b, hab, hya, hyb⟩
  obtain ⟨d, hda, hdb, hall⟩ := third_axis a b hab
  obtain ⟨y1, hy1⟩ : ∃ y1, y1 = Function.update y d (c d + (k d : ℝ) * h) := ⟨_, rfl⟩
  obtain ⟨y2, hy2⟩ : ∃ y2, y2 = Function.update y1 a (c a + (k a : ℝ) * h) := ⟨_, rfl⟩
  have hy1B : y1 ∈ gcube c h k := hy1 ▸ update_mem_gcube hyB d le_rfl (hle d)
  have hy2B : y2 ∈ gcube c h k := hy2 ▸ update_mem_gcube hy1B a le_rfl (hle a)
  have hy1b : y1 b = y b := by rw [hy1, Function.update_of_ne hdb.symm]
  have hy1d : y1 d = c d + (k d : ℝ) * h := by rw [hy1, Function.update_self]
  have hy2a : y2 a = c a + (k a : ℝ) * h := by rw [hy2, Function.update_self]
  have hy2d : y2 d = c d + (k d : ℝ) * h := by rw [hy2, Function.update_of_ne hda, hy1d]
  have hy3 : Function.update y2 b (c b + (k b : ℝ) * h) = fun a => c a + (k a : ℝ) * h := by
    funext i
    rcases hall i with rfl | rfl | rfl
    · rw [Function.update_of_ne hab, hy2a]
    · rw [Function.update_self]
    · rw [Function.update_of_ne hdb, hy2d]
  have hT1 := seg_subset_edges hyB d a b hab hda.symm hdb.symm hya hyb
  have hT2 := seg_subset_edges hy1B a b d hdb.symm hab.symm hda (by rw [hy1b]; exact hyb)
    (Or.inl hy1d)
  have hT3 := seg_subset_edges hy2B b a d hda.symm hab hdb (Or.inl hy2a) (Or.inl hy2d)
  refine ⟨_ ∪ _ ∪ _, Set.union_subset (Set.union_subset hT1 hT2) hT3, ?_, ?_, ?_⟩
  · exact Or.inr ⟨_, ⟨le_rfl, hle b⟩, hy3⟩
  · exact Or.inl (Or.inl ⟨y d, hyB d, Function.update_eq_self d y⟩)
  · refine ((isPreconnected_seg y d _ _).union y1 ?_ ?_ (isPreconnected_seg y1 a _ _)).union y2
      ?_ ?_ (isPreconnected_seg y2 b _ _)
    · exact ⟨_, ⟨le_rfl, hle d⟩, hy1.symm⟩
    · exact ⟨y1 a, hy1B a, Function.update_eq_self a y1⟩
    · exact Or.inr ⟨_, ⟨le_rfl, hle a⟩, hy2.symm⟩
    · exact ⟨y2 b, hy2B b, Function.update_eq_self b y2⟩

end ExtremumAux

open ExtremumAux in
/-- A cube meeting the zero set but none of its edges contains a zero of a nonzero partial
derivative (an interior extremum of `Q` on a face or on the cube). -/
theorem exists_pderiv_zero_of_no_edge (Q : MvPolynomial (Fin 3) ℝ) (hQ : Q ≠ 0)
    (c : Fin 3 → ℝ) {h : ℝ} (hh : 0 < h) {N : ℕ} (k : Fin 3 → Fin N)
    (hz : ∃ x ∈ gcube c h k, eval x Q = 0)
    (hedge : ∀ x, OnEdge c h k x → eval x Q ≠ 0) :
    ∃ a, pderiv a Q ≠ 0 ∧ ∃ x ∈ gcube c h k, eval x (pderiv a Q) = 0 := by
  obtain ⟨z, hzB, hz0⟩ := hz
  have hle : ∀ a, c a + (k a : ℝ) * h ≤ c a + ((k a : ℝ) + 1) * h := fun a => by linarith
  -- two distinct partial derivatives cannot both vanish identically
  have two : ∀ a b : Fin 3, a ≠ b → pderiv a Q ≠ 0 ∨ pderiv b Q ≠ 0 := by
    intro a b hab
    by_cases ha : pderiv a Q = 0
    swap
    · exact Or.inl ha
    by_cases hb : pderiv b Q = 0
    swap
    · exact Or.inr hb
    exfalso
    obtain ⟨z1, hz1⟩ : ∃ z1, z1 = Function.update z a (c a + (k a : ℝ) * h) := ⟨_, rfl⟩
    obtain ⟨z2, hz2⟩ : ∃ z2, z2 = Function.update z1 b (c b + (k b : ℝ) * h) := ⟨_, rfl⟩
    have hz1B : z1 ∈ gcube c h k := hz1 ▸ update_mem_gcube hzB a le_rfl (hle a)
    have hz2B : z2 ∈ gcube c h k := hz2 ▸ update_mem_gcube hz1B b le_rfl (hle b)
    have hz2Q : eval z2 Q = 0 := by
      rw [hz2, eval_update_of_pderiv_eq_zero Q b hb, hz1, eval_update_of_pderiv_eq_zero Q a ha,
        hz0]
    refine hedge z2 ⟨hz2B, a, b, hab, Or.inl ?_, Or.inl ?_⟩ hz2Q
    · rw [hz2, Function.update_of_ne hab, hz1, Function.update_self]
    · rw [hz2, Function.update_self]
  -- an extremum of `Q` on the cube off the edges is a critical point in two directions
  have key : ∀ x ∈ gcube c h k, ¬ OnEdge c h k x →
      (IsMinOn (fun x => eval x Q) (gcube c h k) x ∨
        IsMaxOn (fun x => eval x Q) (gcube c h k) x) →
      ∃ a, pderiv a Q ≠ 0 ∧ ∃ x ∈ gcube c h k, eval x (pderiv a Q) = 0 := by
    intro x hxB hxE hext
    obtain ⟨a, b, hab, ha, hb⟩ := exists_two_free hxB hxE
    have hnhds : ∀ i, (c i + (k i : ℝ) * h < x i ∧ x i < c i + ((k i : ℝ) + 1) * h) →
        ∀ᶠ s in nhds (x i), Function.update x i s ∈ gcube c h k := by
      intro i hi
      filter_upwards [Ioo_mem_nhds hi.1 hi.2] with s hs
      exact update_mem_gcube hxB i hs.1.le hs.2.le
    have hcrit : ∀ i, (c i + (k i : ℝ) * h < x i ∧ x i < c i + ((k i : ℝ) + 1) * h) →
        eval x (pderiv i Q) = 0 := by
      intro i hi
      rcases hext with hmin | hmax
      · exact eval_pderiv_eq_zero_of_isMinOn Q hmin i (hnhds i hi)
      · exact eval_pderiv_eq_zero_of_isMaxOn Q hmax i (hnhds i hi)
    rcases two a b hab with h' | h'
    · exact ⟨a, h', x, hxB, hcrit a ha⟩
    · exact ⟨b, h', x, hxB, hcrit b hb⟩
  have hcont : ContinuousOn (fun x => eval x Q) (gcube c h k) :=
    (MvPolynomial.continuous_eval Q).continuousOn
  obtain ⟨p, hpB, hpmin⟩ := (isCompact_gcube c h k).exists_isMinOn ⟨z, hzB⟩ hcont
  obtain ⟨q, hqB, hqmax⟩ := (isCompact_gcube c h k).exists_isMaxOn ⟨z, hzB⟩ hcont
  by_cases hpE : OnEdge c h k p
  · by_cases hqE : OnEdge c h k q
    · exfalso
      have hp0 : eval p Q < 0 :=
        lt_of_le_of_ne (hz0 ▸ isMinOn_iff.mp hpmin z hzB) (hedge p hpE)
      have hq0 : 0 < eval q Q :=
        lt_of_le_of_ne (hz0 ▸ isMaxOn_iff.mp hqmax z hzB) (hedge q hqE).symm
      obtain ⟨x, hxE, hx0⟩ := (isPreconnected_edges c hh k).intermediate_value hpE hqE
        (MvPolynomial.continuous_eval Q).continuousOn ⟨hp0.le, hq0.le⟩
      exact hedge x hxE hx0
    · exact key q hqB hqE (Or.inr hqmax)
  · exact key p hpB hpE (Or.inl hpmin)


namespace CountAux

/-- Differentiating lowers the total degree by one. -/
theorem totalDegree_pderiv_le {D : ℕ} (Q : MvPolynomial (Fin 3) ℝ) (a : Fin 3)
    (hQ : Q.totalDegree ≤ D + 1) : (pderiv a Q).totalDegree ≤ D := by
  apply Finset.sup_le
  intro m hm
  rw [mem_support_iff, coeff_pderiv] at hm
  have h1 : Q.coeff (m + Finsupp.single a 1) ≠ 0 := left_ne_zero_of_mul hm
  have h2 := le_totalDegree (mem_support_iff.mpr h1)
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_single_index rfl] at h2
  omega

theorem eighteen_le (D : ℕ) : 18 * D + 27 ≤ 27 * 3 ^ D := by
  induction D with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

open Classical in
/-- The strengthened invariant behind `card_zero_cubes_le`, proved by induction on `D`. -/
theorem card_zero_cubes_aux (D : ℕ) : ∀ (Q : MvPolynomial (Fin 3) ℝ), Q ≠ 0 →
    Q.totalDegree ≤ D → ∀ (c : Fin 3 → ℝ) {h : ℝ}, 0 < h → ∀ (N : ℕ),
    (Finset.univ.filter (fun k : Fin 3 → Fin N => ∃ x ∈ gcube c h k, eval x Q = 0)).card +
      (18 * D + 27) * N ^ 2 ≤ 27 * 3 ^ D * N ^ 2 := by
  induction D with
  | zero =>
    intro Q hQ hdeg c h hh N
    have hC : Q = C (Q.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hdeg)
    have hne : Q.coeff 0 ≠ 0 := by
      intro h0; apply hQ; rw [hC, h0, map_zero]
    have hempty : (Finset.univ.filter
        (fun k : Fin 3 → Fin N => ∃ x ∈ gcube c h k, eval x Q = 0)) = ∅ := by
      apply Finset.filter_false_of_mem
      rintro k - ⟨x, -, hx⟩
      rw [hC, eval_C] at hx
      exact hne hx
    rw [hempty, Finset.card_empty]
    simp
  | succ D ih =>
    intro Q hQ hdeg c h hh N
    set F := Finset.univ.filter (fun k : Fin 3 → Fin N => ∃ x ∈ gcube c h k, eval x Q = 0)
      with hF
    set E := Finset.univ.filter (fun k : Fin 3 → Fin N => ∃ x, OnEdge c h k x ∧ eval x Q = 0)
      with hE_def
    let T : Fin 3 → Finset (Fin 3 → Fin N) := fun a =>
      Finset.univ.filter (fun k : Fin 3 → Fin N =>
        pderiv a Q ≠ 0 ∧ ∃ x ∈ gcube c h k, eval x (pderiv a Q) = 0)
    have hsub : F ⊆ E ∪ Finset.univ.biUnion T := by
      intro k hk
      rw [hF, Finset.mem_filter] at hk
      by_cases hed : ∃ x, OnEdge c h k x ∧ eval x Q = 0
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hed⟩)
      · push Not at hed
        obtain ⟨a, ha, hx⟩ := exists_pderiv_zero_of_no_edge Q hQ c hh k hk.2 hed
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨a, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, hx⟩⟩)
    have hE : E.card ≤ 36 * (D + 1) * N ^ 2 := card_edge_cubes_le (D + 1) Q hQ hdeg c hh N
    have hT : ∀ a, (T a).card + (18 * D + 27) * N ^ 2 ≤ 27 * 3 ^ D * N ^ 2 := by
      intro a
      by_cases ha : pderiv a Q = 0
      · have : T a = ∅ := by
          apply Finset.filter_false_of_mem
          rintro k - ⟨hne, -⟩
          exact hne ha
        rw [this, Finset.card_empty, zero_add]
        exact Nat.mul_le_mul_right _ (eighteen_le D)
      · have heq : T a = Finset.univ.filter
            (fun k : Fin 3 → Fin N => ∃ x ∈ gcube c h k, eval x (pderiv a Q) = 0) := by
          apply Finset.filter_congr
          intro k _
          simp [ha]
        rw [heq]
        exact ih (pderiv a Q) ha (totalDegree_pderiv_le Q a hdeg) c hh N
    have hcard : F.card ≤ E.card + ∑ a, (T a).card :=
      (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left Finset.card_biUnion_le _))
    rw [Fin.sum_univ_three] at hcard
    have h0 := hT 0
    have h1 := hT 1
    have h2 := hT 2
    rw [pow_succ 3 D]
    nlinarith

/-- Volume of a coordinate box in `EuclideanSpace ℝ (Fin 3)`. -/
theorem volume_box (lo hi : Fin 3 → ℝ) :
    MeasureTheory.volume
        ((WithLp.ofLp : EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℝ)) ⁻¹' Set.Icc lo hi) =
      ∏ i, ENNReal.ofReal (hi i - lo i) := by
  rw [(PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]

/-- A point of the box `∏ [c i, c i + N h)` lies in some closed grid cube. -/
theorem exists_gcube_mem (c : Fin 3 → ℝ) {h : ℝ} (hh : 0 < h) (N : ℕ) (z : Fin 3 → ℝ)
    (hz : ∀ i, c i ≤ z i ∧ z i < c i + N * h) : ∃ k : Fin 3 → Fin N, z ∈ gcube c h k := by
  have key : ∀ i, ∃ j : Fin N, c i + (j : ℝ) * h ≤ z i ∧ z i ≤ c i + ((j : ℝ) + 1) * h := by
    intro i
    have ht0 : 0 ≤ (z i - c i) / h := div_nonneg (by linarith [(hz i).1]) hh.le
    have hlt : ⌊(z i - c i) / h⌋₊ < N := by
      rw [Nat.floor_lt ht0, div_lt_iff₀ hh]; linarith [(hz i).2]
    refine ⟨⟨⌊(z i - c i) / h⌋₊, hlt⟩, ?_, ?_⟩
    · have := Nat.floor_le ht0
      rw [le_div_iff₀ hh] at this
      simp only
      linarith
    · have := Nat.lt_floor_add_one ((z i - c i) / h)
      rw [div_lt_iff₀ hh] at this
      simp only
      linarith
  choose k hk using key
  exact ⟨k, hk⟩

end CountAux

open Classical in
/-- Number of grid cubes meeting the zero set of a nonzero polynomial of degree `≤ D`. -/
theorem card_zero_cubes_le (D : ℕ) (Q : MvPolynomial (Fin 3) ℝ) (hQ : Q ≠ 0)
    (hdeg : Q.totalDegree ≤ D) (c : Fin 3 → ℝ) {h : ℝ} (hh : 0 < h) (N : ℕ) :
    (Finset.univ.filter (fun k : Fin 3 → Fin N => ∃ x ∈ gcube c h k, eval x Q = 0)).card ≤
      27 * 3 ^ D * N ^ 2 := by
  exact le_of_add_le_left (CountAux.card_zero_cubes_aux D Q hQ hdeg c hh N)

/-- Wongkew-type bound: the `ρ`-neighbourhood of the zero set of a nonzero polynomial of degree
`≤ D` meets a cube of side `s ≥ ρ` in volume at most `12000 · 3^D · ρ · s^2`. -/
theorem volume_thickening_zeroSet_cube_le (D : ℕ) (Q : MvPolynomial (Fin 3) ℝ) (hQ : Q ≠ 0)
    (hdeg : Q.totalDegree ≤ D) (c : EuclideanSpace ℝ (Fin 3)) {s ρ : ℝ} (hρ : 0 < ρ)
    (hρs : ρ ≤ s) :
    MeasureTheory.volume
        (Metric.thickening ρ
            {z : EuclideanSpace ℝ (Fin 3) | MvPolynomial.eval (fun i => z i) Q = 0} ∩
          {x : EuclideanSpace ℝ (Fin 3) | ∀ i, c i ≤ x i ∧ x i ≤ c i + s}) ≤
      ENNReal.ofReal (12000 * 3 ^ D * ρ * s ^ 2) := by
  classical
  have hs : 0 < s := lt_of_lt_of_le hρ hρs
  set L : ℝ := s + 2 * ρ with hL
  have hLpos : 0 < L := by rw [hL]; linarith
  set N : ℕ := ⌈L / ρ⌉₊ with hN
  have hNpos : 0 < N := Nat.ceil_pos.mpr (div_pos hLpos hρ)
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  set h : ℝ := L / N with hh_def
  have hh : 0 < h := div_pos hLpos hNR
  have hNh : (N : ℝ) * h = L := by rw [hh_def]; field_simp
  have hhρ : h ≤ ρ := by
    rw [hh_def, div_le_iff₀ hNR]
    have := Nat.le_ceil (L / ρ)
    rw [div_le_iff₀ hρ] at this
    linarith
  have hNρ : (N : ℝ) * ρ ≤ 4 * s := by
    have h1 := Nat.ceil_lt_add_one (div_pos hLpos hρ).le
    have h2 : (N : ℝ) * ρ < L + ρ := by
      calc (N : ℝ) * ρ < (L / ρ + 1) * ρ := mul_lt_mul_of_pos_right h1 hρ
        _ = L + ρ := by field_simp
    rw [hL] at h2
    linarith
  set c' : Fin 3 → ℝ := fun i => c i - ρ with hc'
  set F := Finset.univ.filter (fun k : Fin 3 → Fin N => ∃ x ∈ gcube c' h k, eval x Q = 0)
    with hF
  have hFcard : F.card ≤ 27 * 3 ^ D * N ^ 2 := card_zero_cubes_le D Q hQ hdeg c' hh N
  set lo : (Fin 3 → Fin N) → Fin 3 → ℝ := fun k i => c' i + (k i : ℝ) * h - ρ with hlo
  set hi : (Fin 3 → Fin N) → Fin 3 → ℝ := fun k i => c' i + ((k i : ℝ) + 1) * h + ρ with hhi
  set B : (Fin 3 → Fin N) → Set (EuclideanSpace ℝ (Fin 3)) := fun k =>
    (WithLp.ofLp : EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℝ)) ⁻¹' Set.Icc (lo k) (hi k) with hB
  have hsub : Metric.thickening ρ
        {z : EuclideanSpace ℝ (Fin 3) | MvPolynomial.eval (fun i => z i) Q = 0} ∩
      {x : EuclideanSpace ℝ (Fin 3) | ∀ i, c i ≤ x i ∧ x i ≤ c i + s} ⊆ ⋃ k ∈ F, B k := by
    rintro x ⟨hx1, hx2⟩
    rw [Metric.mem_thickening_iff] at hx1
    obtain ⟨z, hz, hdist⟩ := hx1
    have hcoord : ∀ i, |x i - z i| < ρ := fun i => by
      have := PiLp.dist_apply_le x z i
      rw [Real.dist_eq] at this
      linarith
    obtain ⟨k, hk⟩ := CountAux.exists_gcube_mem c' hh N (fun i => z i) (by
      intro i
      have h1 := hcoord i
      have h2 := hx2 i
      rw [abs_lt] at h1
      rw [hNh, hc', hL]
      constructor
      · linarith
      · linarith)
    refine Set.mem_biUnion (x := k) ?_ ?_
    · rw [hF, Finset.coe_filter]
      exact ⟨Finset.mem_univ _, _, hk, hz⟩
    · show WithLp.ofLp x ∈ Set.Icc (lo k) (hi k)
      constructor
      · intro i
        have h1 := hk i
        have h2 := hcoord i
        rw [abs_lt] at h2
        simp only [hlo]
        linarith [h1.1]
      · intro i
        have h1 := hk i
        have h2 := hcoord i
        rw [abs_lt] at h2
        simp only [hhi]
        linarith [h1.2]
  have hvolB : ∀ k, MeasureTheory.volume (B k) ≤ ENNReal.ofReal (27 * ρ ^ 3) := by
    intro k
    rw [hB]
    simp only
    rw [CountAux.volume_box]
    have hdiff : ∀ i, hi k i - lo k i = h + 2 * ρ := by
      intro i; simp only [hhi, hlo]; ring
    simp only [hdiff, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← ENNReal.ofReal_pow (by linarith)]
    apply ENNReal.ofReal_le_ofReal
    have : h + 2 * ρ ≤ 3 * ρ := by linarith
    calc (h + 2 * ρ) ^ 3 ≤ (3 * ρ) ^ 3 := pow_le_pow_left₀ (by linarith) this 3
      _ = 27 * ρ ^ 3 := by ring
  calc MeasureTheory.volume (Metric.thickening ρ
          {z : EuclideanSpace ℝ (Fin 3) | MvPolynomial.eval (fun i => z i) Q = 0} ∩
        {x : EuclideanSpace ℝ (Fin 3) | ∀ i, c i ≤ x i ∧ x i ≤ c i + s})
      ≤ MeasureTheory.volume (⋃ k ∈ F, B k) := MeasureTheory.measure_mono hsub
    _ ≤ ∑ k ∈ F, MeasureTheory.volume (B k) := MeasureTheory.measure_biUnion_finset_le F B
    _ ≤ ∑ k ∈ F, ENNReal.ofReal (27 * ρ ^ 3) := Finset.sum_le_sum (fun k _ => hvolB k)
    _ = ENNReal.ofReal ((F.card : ℝ) * (27 * ρ ^ 3)) := by
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (12000 * 3 ^ D * ρ * s ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      have hFR : (F.card : ℝ) ≤ 27 * 3 ^ D * (N : ℝ) ^ 2 := by exact_mod_cast hFcard
      have hNρ0 : 0 ≤ (N : ℝ) * ρ := by positivity
      calc (F.card : ℝ) * (27 * ρ ^ 3) ≤ (27 * 3 ^ D * (N : ℝ) ^ 2) * (27 * ρ ^ 3) :=
            mul_le_mul_of_nonneg_right hFR (by positivity)
        _ = 729 * 3 ^ D * ρ * ((N : ℝ) * ρ) ^ 2 := by ring
        _ ≤ 729 * 3 ^ D * ρ * (4 * s) ^ 2 := by gcongr
        _ = 11664 * 3 ^ D * ρ * s ^ 2 := by ring
        _ ≤ 12000 * 3 ^ D * ρ * s ^ 2 := by gcongr; norm_num

end Wongkew
end WangZahlLot.Obl.wz_coarse_tube_grains.PolyMethod
