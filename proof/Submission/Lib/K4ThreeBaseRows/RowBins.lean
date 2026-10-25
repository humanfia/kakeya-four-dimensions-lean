/-
Adapted from: here:o266
Original: session x0947, branch x0947 of o266, file
Submission/Obl/k4_narrow_original_potential_atlas/RowBinLists.lean (commit 25f714dc).
Moved into a library namespace; imports only Mathlib and modules already in lib.
-/

import Submission.Lib.K4ThreeBaseRows.EntryPruning

/-! COARSE ROW LISTS (paper, §6, end of the proof of `a05:velocity-graph`), with THREE spanning base
directions `(1, V₀, V₁)`.

Each fine cell `c` of a coarse physical cell carries a row `G c ∈ ℝ³`, with `|G| ≤ K`. It also has
three witnesses: planar velocities `Vw c i`, with `|V| ≤ K`, and `X'` values `Xw c i`. These fit the
graph, `|X' - G · (1, V)| ≤ ε`, and span, `|det(1, V_i)| ≥ δ`. Their `X'` bins at width `s` lie in
derivative lists `L(velocity bin)` of size `≤ KL`, and their velocity-bin tuple has product palette
`K₁ ∏ π ≥ 1`.

- `abs_le_of_mulVec`: a spanning triple pins a vector, `|u| ≤ 6A² e/δ`.
- `rows_close`: cells with the same velocity-bin tuple and `X'` bins have rows within `D`.
- `card_rowBins_tuple_le`: one velocity-bin tuple permits at most `KL³ (2D/s + 2)³` row bins.
- `coarse_row_bins_card_le`: all occurring row bins number at most
  `K₁ KL³ (2D/s + 2)³ (Σ π)³`. Every occurring tuple pays its row bins through its product
  palette, so there is no alphabet factor. The list is the set of OCCURRING row bins, manufactured
  from the witnesses. -/

namespace Submission.Lib.K4ThreeBaseRows

open Finset

noncomputable section

namespace RowBinLists

open Full7EntryPruning (binsAround floor_mem_binsAround card_binsAround_le floor_bounds)

theorem abs_minor_le {a b c d A : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ A) (hc : |c| ≤ A)
    (hd : |d| ≤ A) : |a * b - c * d| ≤ 2 * A ^ 2 := by
  have hA : 0 ≤ A := (abs_nonneg _).trans ha
  have h1 : |a * b| ≤ A ^ 2 := by rw [abs_mul, sq]; exact mul_le_mul ha hb (abs_nonneg _) hA
  have h2 : |c * d| ≤ A ^ 2 := by rw [abs_mul, sq]; exact mul_le_mul hc hd (abs_nonneg _) hA
  calc |a * b - c * d| ≤ |a * b| + |c * d| := abs_sub _ _
    _ ≤ 2 * A ^ 2 := by linarith

theorem abs_neg_minor_le {a b c d A : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ A) (hc : |c| ≤ A)
    (hd : |d| ≤ A) : |-(a * b) + c * d| ≤ 2 * A ^ 2 := by
  rw [neg_add_eq_sub, abs_sub_comm]
  exact abs_minor_le ha hb hc hd

/-- The adjugate of a `3 × 3` matrix with entries `≤ A` has entries `≤ 2A²`. -/
theorem abs_adjugate_le {M : Matrix (Fin 3) (Fin 3) ℝ} {A : ℝ} (hM : ∀ i k, |M i k| ≤ A)
    (k i : Fin 3) : |M.adjugate k i| ≤ 2 * A ^ 2 := by
  rw [Matrix.adjugate_fin_three]
  fin_cases k <;> fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val',
      Matrix.cons_val_fin_one] <;>
    first
    | exact abs_minor_le (hM _ _) (hM _ _) (hM _ _) (hM _ _)
    | exact abs_neg_minor_le (hM _ _) (hM _ _) (hM _ _) (hM _ _)

/-- **Stability of a spanning triple.** If `|det M| ≥ δ > 0`, the entries are `≤ A`, and
`|(M u)_i| ≤ e`, then `|u_k| ≤ 6 A² e / δ`. -/
theorem abs_le_of_mulVec {M : Matrix (Fin 3) (Fin 3) ℝ} {A δ e : ℝ} (hM : ∀ i k, |M i k| ≤ A)
    (hδ : 0 < δ) (hdet : δ ≤ |M.det|) {u : Fin 3 → ℝ} (hu : ∀ i, |M.mulVec u i| ≤ e)
    (k : Fin 3) : |u k| ≤ 6 * A ^ 2 * e / δ := by
  have he : 0 ≤ e := (abs_nonneg _).trans (hu 0)
  have hkey : M.det * u k = ∑ i, M.adjugate k i * M.mulVec u i := by
    have h := congrFun (Matrix.mulVec_mulVec u M.adjugate M) k
    rw [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at h
    calc M.det * u k = (M.det • u) k := by simp only [Pi.smul_apply, smul_eq_mul]
      _ = M.adjugate.mulVec (M.mulVec u) k := h.symm
      _ = ∑ i, M.adjugate k i * M.mulVec u i := by simp only [Matrix.mulVec, dotProduct]
  have hsum : |M.det| * |u k| ≤ 6 * A ^ 2 * e := by
    rw [← abs_mul, hkey]
    calc |∑ i, M.adjugate k i * M.mulVec u i| ≤ ∑ i, |M.adjugate k i * M.mulVec u i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 3, 2 * A ^ 2 * e := Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          exact mul_le_mul (abs_adjugate_le hM k i) (hu i) (abs_nonneg _) (by positivity)
      _ = 6 * A ^ 2 * e := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  rw [le_div_iff₀ hδ]
  calc |u k| * δ ≤ |u k| * |M.det| := mul_le_mul_of_nonneg_left hdet (abs_nonneg _)
    _ = |M.det| * |u k| := mul_comm _ _
    _ ≤ _ := hsum

/-! ### Lifted directions -/

/-- The lifted base direction `(1, V₀, V₁)`. -/
def lift (V : Fin 2 → ℝ) : Fin 3 → ℝ := ![1, V 0, V 1]

/-- The row evaluation `G · (1, V₀, V₁)`. -/
def rowEval (G : Fin 3 → ℝ) (V : Fin 2 → ℝ) : ℝ := G 0 + G 1 * V 0 + G 2 * V 1

/-- The matrix whose rows are the three lifted witness directions. -/
def witnessMatrix (V : Fin 3 → Fin 2 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i k => lift (V i) k

theorem witnessMatrix_mulVec (V : Fin 3 → Fin 2 → ℝ) (u : Fin 3 → ℝ) (i : Fin 3) :
    (witnessMatrix V).mulVec u i = rowEval u (V i) := by
  simp only [witnessMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply, lift,
    rowEval, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

theorem abs_witnessMatrix_le {V : Fin 3 → Fin 2 → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hV : ∀ i k, |V i k| ≤ K) (i k : Fin 3) : |witnessMatrix V i k| ≤ 1 + K := by
  have h0 := hV i 0
  have h1 := hV i 1
  fin_cases k <;>
    simp only [witnessMatrix, Matrix.of_apply, lift, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, abs_one] <;> linarith

/-- Two cells whose witnesses agree to `s` in velocity and `X'` have rows within
`D = 6 (1+K)² (2ε + s + 2Ks) / δ`. -/
theorem rows_close {G G' : Fin 3 → ℝ} {V V' : Fin 3 → Fin 2 → ℝ} {X X' : Fin 3 → ℝ}
    {K ε s δ : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K) (hV : ∀ i k, |V i k| ≤ K)
    (hdet : δ ≤ |(witnessMatrix V).det|) (hG' : ∀ k, |G' k| ≤ K)
    (hfit : ∀ i, |X i - rowEval G (V i)| ≤ ε) (hfit' : ∀ i, |X' i - rowEval G' (V' i)| ≤ ε)
    (hVV : ∀ i k, |V' i k - V i k| ≤ s) (hXX : ∀ i, |X i - X' i| ≤ s) (k : Fin 3) :
    |G k - G' k| ≤ 6 * (1 + K) ^ 2 * (2 * ε + s + 2 * K * s) / δ := by
  have hk := abs_le_of_mulVec (M := witnessMatrix V) (u := G - G') (e := 2 * ε + s + 2 * K * s)
    (abs_witnessMatrix_le hK hV) hδ hdet ?_ k
  · simpa only [Pi.sub_apply] using hk
  intro i
  rw [witnessMatrix_mulVec]
  have e1 : rowEval (G - G') (V i) = -(X i - rowEval G (V i)) + (X i - X' i) +
      (X' i - rowEval G' (V' i)) + (G' 1 * (V' i 0 - V i 0) + G' 2 * (V' i 1 - V i 1)) := by
    simp only [rowEval, Pi.sub_apply]
    ring
  rw [e1]
  have h4 : |G' 1 * (V' i 0 - V i 0) + G' 2 * (V' i 1 - V i 1)| ≤ 2 * K * s := by
    calc |G' 1 * (V' i 0 - V i 0) + G' 2 * (V' i 1 - V i 1)|
        ≤ |G' 1 * (V' i 0 - V i 0)| + |G' 2 * (V' i 1 - V i 1)| := abs_add_le _ _
      _ ≤ K * s + K * s := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul (hG' 1) (hVV i 0) (abs_nonneg _) hK)
            (mul_le_mul (hG' 2) (hVV i 1) (abs_nonneg _) hK)
      _ = 2 * K * s := by ring
  calc |-(X i - rowEval G (V i)) + (X i - X' i) + (X' i - rowEval G' (V' i)) +
        (G' 1 * (V' i 0 - V i 0) + G' 2 * (V' i 1 - V i 1))|
      ≤ |-(X i - rowEval G (V i))| + |X i - X' i| + |X' i - rowEval G' (V' i)| +
        |G' 1 * (V' i 0 - V i 0) + G' 2 * (V' i 1 - V i 1)| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact abs_add_le _ _
    _ ≤ ε + s + ε + 2 * K * s := by
        rw [abs_neg]
        linarith [hfit i, hXX i, hfit' i, h4]
    _ = 2 * ε + s + 2 * K * s := by ring

/-- Two reals in the same bin of width `s` are within `s`. -/
theorem abs_sub_le_of_floor_eq {x y s : ℝ} (hs : 0 < s) (h : ⌊x / s⌋ = ⌊y / s⌋) :
    |x - y| ≤ s := by
  obtain ⟨hx1, hx2⟩ := floor_bounds (x := x) hs
  obtain ⟨hy1, hy2⟩ := floor_bounds (x := y) hs
  rw [h] at hx1 hx2
  rw [abs_le]
  constructor <;> linarith

/-! ### Row bins -/

/-- The velocity bin of a planar velocity at width `s`. -/
def vbin (s : ℝ) (V : Fin 2 → ℝ) : Fin 2 → ℤ := fun k => ⌊V k / s⌋

/-- The row bin of a row at width `s`. -/
def rowBin (s : ℝ) (G : Fin 3 → ℝ) : Fin 3 → ℤ := fun k => ⌊G k / s⌋

variable {ι : Type*} [DecidableEq ι]

/-- The row-closeness radius. -/
def rowRadius (K ε s δ : ℝ) : ℝ := 6 * (1 + K) ^ 2 * (2 * ε + s + 2 * K * s) / δ

/-- **One velocity-bin tuple permits at most `KL³ (2D/s + 2)³` row bins.** -/
theorem card_rowBins_tuple_le (cells : Finset ι) (G : ι → Fin 3 → ℝ)
    (Vw : ι → Fin 3 → Fin 2 → ℝ) (Xw : ι → Fin 3 → ℝ) (L : (Fin 2 → ℤ) → Finset ℤ)
    {K ε s δ KL : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hG : ∀ c ∈ cells, ∀ k, |G c k| ≤ K) (hV : ∀ c ∈ cells, ∀ i k, |Vw c i k| ≤ K)
    (hfit : ∀ c ∈ cells, ∀ i, |Xw c i - rowEval (G c) (Vw c i)| ≤ ε)
    (hdet : ∀ c ∈ cells, δ ≤ |(witnessMatrix (Vw c)).det|)
    (hlist : ∀ c ∈ cells, ∀ i, ⌊Xw c i / s⌋ ∈ L (vbin s (Vw c i)))
    (hLcard : ∀ β, ((L β).card : ℝ) ≤ KL) (t : Fin 3 → Fin 2 → ℤ) :
    (((cells.filter fun c => (fun i => vbin s (Vw c i)) = t).image
      fun c => rowBin s (G c)).card : ℝ) ≤
      KL ^ 3 * (2 * rowRadius K ε s δ / s + 2) ^ 3 := by
  classical
  set D := rowRadius K ε s δ with hD
  have hD0 : 0 ≤ D := by rw [hD]; unfold rowRadius; positivity
  set Ct := cells.filter fun c => (fun i => vbin s (Vw c i)) = t with hCt
  let Xset : Finset (Fin 3 → ℤ) := Fintype.piFinset fun i => L (t i)
  let Ctx : (Fin 3 → ℤ) → Finset ι := fun x => Ct.filter fun c => (fun i => ⌊Xw c i / s⌋) = x
  -- rows of one (tuple, X'-choice) class lie in one box
  have hbox : ∀ x, (((Ctx x).image fun c => rowBin s (G c)).card : ℝ) ≤
      (2 * D / s + 2) ^ 3 := by
    intro x
    by_cases hne : (Ctx x).Nonempty
    · obtain ⟨c₀, hc₀⟩ := hne
      have hc₀' := Finset.mem_filter.mp hc₀
      have hc₀c := (Finset.mem_filter.mp hc₀'.1).1
      have hc₀t := (Finset.mem_filter.mp hc₀'.1).2
      let box : Finset (Fin 3 → ℤ) := Fintype.piFinset fun k => binsAround s (G c₀ k) D
      have hsub : ((Ctx x).image fun c => rowBin s (G c)) ⊆ box := by
        intro g hg
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hg
        have hc' := Finset.mem_filter.mp hc
        have hcc := (Finset.mem_filter.mp hc'.1).1
        have hct := (Finset.mem_filter.mp hc'.1).2
        rw [Fintype.mem_piFinset]
        intro k
        apply floor_mem_binsAround hs
        refine rows_close hδ hK (hV c hcc) (hdet c hcc) (hG c₀ hc₀c) (hfit c hcc) (hfit c₀ hc₀c)
          ?_ ?_ k
        · intro i k'
          have hb : vbin s (Vw c i) = vbin s (Vw c₀ i) := by
            have := congrFun (hct.trans hc₀t.symm) i
            exact this
          have hk' := congrFun hb k'
          rw [abs_sub_comm]
          exact abs_sub_le_of_floor_eq hs hk'
        · intro i
          have := congrFun (hc'.2.trans hc₀'.2.symm) i
          exact abs_sub_le_of_floor_eq hs this
      calc (((Ctx x).image fun c => rowBin s (G c)).card : ℝ) ≤ (box.card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ = ∏ k : Fin 3, ((binsAround s (G c₀ k) D).card : ℝ) := by
            simp only [box, Fintype.card_piFinset]
            push_cast
            rfl
        _ ≤ ∏ _k : Fin 3, (2 * D / s + 2) :=
            Finset.prod_le_prod₀ (fun k _ => Nat.cast_nonneg _)
              (fun k _ => card_binsAround_le hs hD0)
        _ = (2 * D / s + 2) ^ 3 := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.image_empty, Finset.card_empty,
        Nat.cast_zero]
      positivity
  -- the tuple's rows are covered by the classes of its `X'` choices
  have hcover : (Ct.image fun c => rowBin s (G c)) ⊆
      Xset.biUnion fun x => (Ctx x).image fun c => rowBin s (G c) := by
    intro g hg
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hg
    have hc' := Finset.mem_filter.mp hc
    refine Finset.mem_biUnion.mpr ⟨fun i => ⌊Xw c i / s⌋, ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i
      have h := hlist c hc'.1 i
      rwa [show t i = vbin s (Vw c i) from (congrFun hc'.2 i).symm]
    · exact Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, rfl⟩, rfl⟩
  have hXcard : (Xset.card : ℝ) ≤ KL ^ 3 := by
    simp only [Xset, Fintype.card_piFinset]
    push_cast
    calc ∏ i : Fin 3, ((L (t i)).card : ℝ) ≤ ∏ _i : Fin 3, KL :=
          Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hLcard _)
      _ = KL ^ 3 := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hKL : 0 ≤ KL := (Nat.cast_nonneg _).trans (hLcard (fun _ => 0))
  calc ((Ct.image fun c => rowBin s (G c)).card : ℝ)
      ≤ ((Xset.biUnion fun x => (Ctx x).image fun c => rowBin s (G c)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hcover
    _ ≤ ∑ x ∈ Xset, (((Ctx x).image fun c => rowBin s (G c)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ Xset, (2 * D / s + 2) ^ 3 := Finset.sum_le_sum fun x _ => hbox x
    _ = (Xset.card : ℝ) * (2 * D / s + 2) ^ 3 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ KL ^ 3 * (2 * D / s + 2) ^ 3 :=
        mul_le_mul_of_nonneg_right hXcard (by positivity)

/-- **Coarse row lists.** The row bins occurring in a coarse cell number at most
`K₁ KL³ (2D/s + 2)³ (Σ_β π β)³`. Each occurring velocity-bin tuple has product palette
`∏ π ≥ 1/K₁` and permits at most `KL³ (2D/s + 2)³` row bins. The tuples range over `Bv³`, whose
product palette sums to `(Σ π)³`. -/
theorem coarse_row_bins_card_le (cells : Finset ι) (G : ι → Fin 3 → ℝ)
    (Vw : ι → Fin 3 → Fin 2 → ℝ) (Xw : ι → Fin 3 → ℝ) (L : (Fin 2 → ℤ) → Finset ℤ)
    (π : (Fin 2 → ℤ) → ℝ) (Bv : Finset (Fin 2 → ℤ)) {K ε s δ K₁ KL : ℝ} (hs : 0 < s)
    (hδ : 0 < δ) (hK : 0 ≤ K) (hε : 0 ≤ ε) (hK₁ : 0 ≤ K₁)
    (hG : ∀ c ∈ cells, ∀ k, |G c k| ≤ K) (hV : ∀ c ∈ cells, ∀ i k, |Vw c i k| ≤ K)
    (hfit : ∀ c ∈ cells, ∀ i, |Xw c i - rowEval (G c) (Vw c i)| ≤ ε)
    (hdet : ∀ c ∈ cells, δ ≤ |(witnessMatrix (Vw c)).det|)
    (hlist : ∀ c ∈ cells, ∀ i, ⌊Xw c i / s⌋ ∈ L (vbin s (Vw c i)))
    (hLcard : ∀ β, ((L β).card : ℝ) ≤ KL) (hπ0 : ∀ β, 0 ≤ π β)
    (hBv : ∀ c ∈ cells, ∀ i, vbin s (Vw c i) ∈ Bv)
    (hpal : ∀ c ∈ cells, 1 ≤ K₁ * ∏ i, π (vbin s (Vw c i))) :
    ((cells.image fun c => rowBin s (G c)).card : ℝ) ≤
      K₁ * (KL ^ 3 * (2 * rowRadius K ε s δ / s + 2) ^ 3) * (∑ β ∈ Bv, π β) ^ 3 := by
  classical
  set Kt := KL ^ 3 * (2 * rowRadius K ε s δ / s + 2) ^ 3 with hKt
  have hKL : 0 ≤ KL := (Nat.cast_nonneg _).trans (hLcard (fun _ => 0))
  have hD0 : 0 ≤ rowRadius K ε s δ := by unfold rowRadius; positivity
  have hKt0 : 0 ≤ Kt := by rw [hKt]; positivity
  let tup : ι → Fin 3 → Fin 2 → ℤ := fun c i => vbin s (Vw c i)
  let T : Finset (Fin 3 → Fin 2 → ℤ) := cells.image tup
  let w : (Fin 3 → Fin 2 → ℤ) → ℝ := fun t => ∏ i, π (t i)
  have hw0 : ∀ t, 0 ≤ w t := fun t => Finset.prod_nonneg fun i _ => hπ0 _
  have hcover : (cells.image fun c => rowBin s (G c)) ⊆
      T.biUnion fun t => (cells.filter fun c => (fun i => vbin s (Vw c i)) = t).image
        fun c => rowBin s (G c) := by
    intro g hg
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hg
    exact Finset.mem_biUnion.mpr ⟨tup c, Finset.mem_image.mpr ⟨c, hc, rfl⟩,
      Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, rfl⟩, rfl⟩⟩
  have hTsub : T ⊆ Fintype.piFinset fun _ : Fin 3 => Bv := by
    intro t ht
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ht
    rw [Fintype.mem_piFinset]
    exact fun i => hBv c hc i
  have hpalT : ∀ t ∈ T, 1 ≤ K₁ * w t := by
    intro t ht
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ht
    exact hpal c hc
  calc ((cells.image fun c => rowBin s (G c)).card : ℝ)
      ≤ ((T.biUnion fun t => (cells.filter fun c => (fun i => vbin s (Vw c i)) = t).image
          fun c => rowBin s (G c)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hcover
    _ ≤ ∑ t ∈ T, (((cells.filter fun c => (fun i => vbin s (Vw c i)) = t).image
          fun c => rowBin s (G c)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ t ∈ T, Kt * (K₁ * w t) := by
        refine Finset.sum_le_sum fun t ht => ?_
        calc (((cells.filter fun c => (fun i => vbin s (Vw c i)) = t).image
              fun c => rowBin s (G c)).card : ℝ) ≤ Kt :=
              card_rowBins_tuple_le cells G Vw Xw L hs hδ hK hε hG hV hfit hdet hlist hLcard t
          _ = Kt * 1 := (mul_one _).symm
          _ ≤ Kt * (K₁ * w t) := mul_le_mul_of_nonneg_left (hpalT t ht) hKt0
    _ = K₁ * Kt * ∑ t ∈ T, w t := by rw [Finset.mul_sum]; congr 1; ext t; ring
    _ ≤ K₁ * Kt * ∑ t ∈ Fintype.piFinset (fun _ : Fin 3 => Bv), w t :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hTsub
          fun t _ _ => hw0 t) (mul_nonneg hK₁ hKt0)
    _ = K₁ * Kt * (∑ β ∈ Bv, π β) ^ 3 := by
        congr 1
        rw [← Finset.prod_univ_sum (fun _ : Fin 3 => Bv) (fun _ β => π β), Finset.prod_const,
          Finset.card_univ, Fintype.card_fin]

/-- **Coarse row lists, weighted-witness form.** Each fine cell `c` supports a finite set `Tc c` of
velocity-bin triples. For each `t ∈ Tc c` it has its own witnesses `Vw c t`, `Xw c t`: literal
bins `t`, the fit, the spanning determinant, and the `X'` lists. Its TOTAL supported product
palette satisfies `K₁ Σ_{t ∈ Tc c} ∏ π(t_i) ≥ 1`; no single tuple needs a large weight. Then the
occurring row bins number at most `K₁ KL³ (2D/s + 2)³ (Σ π)³`.

Proof: charge each occurring row bin's representative cell with its whole tuple sum. For a fixed
tuple, the representatives supporting it have distinct row bins, and `card_rowBins_tuple_le`
bounds them. -/
theorem coarse_row_bins_card_le_weighted (cells : Finset ι) (G : ι → Fin 3 → ℝ)
    (Tc : ι → Finset (Fin 3 → Fin 2 → ℤ))
    (Vw : ι → (Fin 3 → Fin 2 → ℤ) → Fin 3 → Fin 2 → ℝ)
    (Xw : ι → (Fin 3 → Fin 2 → ℤ) → Fin 3 → ℝ) (L : (Fin 2 → ℤ) → Finset ℤ)
    (π : (Fin 2 → ℤ) → ℝ) (Bv : Finset (Fin 2 → ℤ)) {K ε s δ K₁ KL : ℝ} (hs : 0 < s)
    (hδ : 0 < δ) (hK : 0 ≤ K) (hε : 0 ≤ ε) (hK₁ : 0 ≤ K₁)
    (hG : ∀ c ∈ cells, ∀ k, |G c k| ≤ K)
    (hV : ∀ c ∈ cells, ∀ t ∈ Tc c, ∀ i k, |Vw c t i k| ≤ K)
    (hbin : ∀ c ∈ cells, ∀ t ∈ Tc c, ∀ i, vbin s (Vw c t i) = t i)
    (hfit : ∀ c ∈ cells, ∀ t ∈ Tc c, ∀ i, |Xw c t i - rowEval (G c) (Vw c t i)| ≤ ε)
    (hdet : ∀ c ∈ cells, ∀ t ∈ Tc c, δ ≤ |(witnessMatrix (Vw c t)).det|)
    (hlist : ∀ c ∈ cells, ∀ t ∈ Tc c, ∀ i, ⌊Xw c t i / s⌋ ∈ L (t i))
    (hLcard : ∀ β, ((L β).card : ℝ) ≤ KL) (hπ0 : ∀ β, 0 ≤ π β)
    (hBv : ∀ c ∈ cells, ∀ t ∈ Tc c, ∀ i, t i ∈ Bv)
    (hpal : ∀ c ∈ cells, 1 ≤ K₁ * ∑ t ∈ Tc c, ∏ i, π (t i)) :
    ((cells.image fun c => rowBin s (G c)).card : ℝ) ≤
      K₁ * (KL ^ 3 * (2 * rowRadius K ε s δ / s + 2) ^ 3) * (∑ β ∈ Bv, π β) ^ 3 := by
  classical
  set Kt := KL ^ 3 * (2 * rowRadius K ε s δ / s + 2) ^ 3 with hKt
  have hKL : 0 ≤ KL := (Nat.cast_nonneg _).trans (hLcard (fun _ => 0))
  have hD0 : 0 ≤ rowRadius K ε s δ := by unfold rowRadius; positivity
  have hKt0 : 0 ≤ Kt := by rw [hKt]; positivity
  set RB := cells.image fun c => rowBin s (G c) with hRB
  let w : (Fin 3 → Fin 2 → ℤ) → ℝ := fun t => ∏ i, π (t i)
  have hw0 : ∀ t, 0 ≤ w t := fun t => Finset.prod_nonneg fun i _ => hπ0 _
  let P : Finset (Fin 3 → Fin 2 → ℤ) := Fintype.piFinset fun _ : Fin 3 => Bv
  -- representatives
  have hex : ∀ g : RB, ∃ c ∈ cells, rowBin s (G c) = g.1 := fun g => Finset.mem_image.mp g.2
  let rep : RB → ι := fun g => (hex g).choose
  have hrep_mem : ∀ g, rep g ∈ cells := fun g => (hex g).choose_spec.1
  have hrep_bin : ∀ g, rowBin s (G (rep g)) = g.1 := fun g => (hex g).choose_spec.2
  -- the per-tuple count of representatives
  have hcount : ∀ t ∈ P, (((RB.attach).filter fun g => t ∈ Tc (rep g)).card : ℝ) ≤ Kt := by
    intro t _
    set Sg := (RB.attach).filter fun g => t ∈ Tc (rep g) with hSg
    set Ct := Sg.image rep with hCt
    have hCt_cells : ∀ c ∈ Ct, c ∈ cells ∧ t ∈ Tc c := by
      intro c hc
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hc
      exact ⟨hrep_mem g, (Finset.mem_filter.mp hg).2⟩
    have hfilt : (Ct.filter fun c => (fun i => vbin s (Vw c t i)) = t) = Ct := by
      apply Finset.filter_true_of_mem
      intro c hc
      obtain ⟨hcc, hct⟩ := hCt_cells c hc
      funext i
      exact hbin c hcc t hct i
    have htuple := card_rowBins_tuple_le Ct G (fun c => Vw c t) (fun c => Xw c t) L hs hδ hK hε
      (fun c hc => hG c (hCt_cells c hc).1)
      (fun c hc => hV c (hCt_cells c hc).1 t (hCt_cells c hc).2)
      (fun c hc => hfit c (hCt_cells c hc).1 t (hCt_cells c hc).2)
      (fun c hc => hdet c (hCt_cells c hc).1 t (hCt_cells c hc).2)
      (fun c hc i => by
        have h := hlist c (hCt_cells c hc).1 t (hCt_cells c hc).2 i
        rwa [← hbin c (hCt_cells c hc).1 t (hCt_cells c hc).2 i] at h)
      hLcard t
    rw [hfilt] at htuple
    have himg : (Ct.image fun c => rowBin s (G c)) = Sg.image Subtype.val := by
      rw [hCt, Finset.image_image]
      apply Finset.image_congr
      intro g _
      exact hrep_bin g
    have hcard : (Sg.card : ℝ) = ((Ct.image fun c => rowBin s (G c)).card : ℝ) := by
      rw [himg, Finset.card_image_of_injective _ Subtype.val_injective]
    rw [hcard]
    exact htuple
  -- charge each row bin with the whole supported tuple sum of its representative
  have hsub : ∀ g : RB, ∑ t ∈ Tc (rep g), w t = ∑ t ∈ P, if t ∈ Tc (rep g) then w t else 0 := by
    intro g
    rw [← Finset.sum_filter]
    apply Finset.sum_subset
    · intro t ht
      refine Finset.mem_filter.mpr ⟨?_, ht⟩
      rw [Fintype.mem_piFinset]
      exact fun i => hBv _ (hrep_mem g) t ht i
    · intro t ht hnot
      exact absurd (Finset.mem_filter.mp ht).2 hnot
  calc (RB.card : ℝ) = ∑ _g ∈ RB.attach, (1 : ℝ) := by
        rw [Finset.sum_const, Finset.card_attach, nsmul_eq_mul, mul_one]
    _ ≤ ∑ g ∈ RB.attach, K₁ * ∑ t ∈ Tc (rep g), w t :=
        Finset.sum_le_sum fun g _ => hpal _ (hrep_mem g)
    _ = K₁ * ∑ g ∈ RB.attach, ∑ t ∈ P, if t ∈ Tc (rep g) then w t else 0 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun g _ => by rw [hsub g]
    _ = K₁ * ∑ t ∈ P, w t * (((RB.attach).filter fun g => t ∈ Tc (rep g)).card : ℝ) := by
        rw [Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ K₁ * ∑ t ∈ P, w t * Kt := by
        gcongr with t ht
        · exact hw0 t
        · exact hcount t ht
    _ = K₁ * Kt * ∑ t ∈ P, w t := by rw [← Finset.sum_mul]; ring
    _ = K₁ * Kt * (∑ β ∈ Bv, π β) ^ 3 := by
        congr 1
        rw [← Finset.prod_univ_sum (fun _ : Fin 3 => Bv) (fun _ β => π β), Finset.prod_const,
          Finset.card_univ, Fintype.card_fin]

end RowBinLists

end

end Submission.Lib.K4ThreeBaseRows
