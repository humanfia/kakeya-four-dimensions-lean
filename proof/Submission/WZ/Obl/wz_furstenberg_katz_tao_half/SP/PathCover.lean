-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.PathCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.PathLemma
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.RealSeparatedCounts
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.GridCoverCard
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.ScalarAlgebra

/-!
# Projections of a full product from projections of a dense subset

If every pair `(a, b) ∈ A' × B'` is joined by `P` paths of length three in `G ⊆ A × B`, then
`a + t b = (a + t y) - (x + t y) + (x + t b)` with all three terms in the projection of `G`.
Counting grid cells gives a cover of `A' + t B'` by `O(m ^ 3 / (P t))` balls when the
projection of `G` is covered by `m` balls. The sets `A'`, `B'` do not depend on `t`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open scoped Pointwise

/-- A finite set of reals is covered by closed `δ`-balls centred at its occupied grid cells. -/
theorem cover_of_grid_image {δ : ℝ} (hδ : 0 < δ) (Z : Finset ℝ) :
    RealCoverBound δ Z ((Z.image (realGridIndex δ)).card : ℝ) := by
  classical
  let W := Z.image (realGridIndex δ)
  let e := Fintype.equivFin W
  refine ⟨Fintype.card W, fun i => δ * ((e.symm i).1 : ℝ), ?_, by simp [W]⟩
  intro x hx
  have hw : realGridIndex δ x ∈ W := Finset.mem_image_of_mem _ hx
  refine Set.mem_iUnion.mpr ⟨e ⟨_, hw⟩, ?_⟩
  simp only [Equiv.symm_apply_apply, Metric.mem_closedBall, Real.dist_eq]
  have h := realGridIndex_error hδ x
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A `δ`-separated set meets an affine preimage `{y | ⌊(a + s y) / δ⌋ = i}` in at most
`1 / s + 2` points. -/
theorem grid_fiber_card_le {δ s a : ℝ} (hδ : 0 < δ) (hs : 0 < s) (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y) (i : ℤ) :
    ((S.filter (fun y => realGridIndex δ (a + s * y) = i)).card : ℝ) ≤ 1 / s + 2 := by
  have hball : ∀ y ∈ S.filter (fun y => realGridIndex δ (a + s * y) = i),
      dist y ((δ * i + δ / 2 - a) / s) ≤ δ / 2 / s := by
    intro y hy
    have hi := (Finset.mem_filter.mp hy).2
    have h := realGridIndex_error hδ (a + s * y)
    rw [hi] at h
    have e : y - (δ * i + δ / 2 - a) / s = (a + s * y - δ * i - δ / 2) / s := by
      field_simp
      ring
    rw [Real.dist_eq, e, abs_div, abs_of_pos hs]
    apply div_le_div_of_nonneg_right _ hs.le
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h := real_separated_ball_card hδ (by positivity) _
    (fun x hx y hy hne => hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hne)
    hball
  have e : 2 * (δ / 2 / s) + 2 * δ = (1 / s + 2) * δ := by field_simp
  rw [e] at h
  exact le_of_mul_le_mul_right h hδ

/-- The triples of grid cells of the three projected edges of the paths from `a` to `b`. -/
noncomputable def pathTriples (A B : Finset ℝ) (G : Finset (ℝ × ℝ)) (δ t a b : ℝ) :
    Finset (ℤ × ℤ × ℤ) :=
  (pathSet A B G a b).image (fun q => (realGridIndex δ (a + t * q.2),
    realGridIndex δ (q.1 + t * q.2), realGridIndex δ (q.1 + t * b)))

theorem pathTriples_subset (A B : Finset ℝ) (G : Finset (ℝ × ℝ)) (δ t a b : ℝ) :
    pathTriples A B G δ t a b ⊆
      (G.image (fun g => realGridIndex δ (g.1 + t * g.2))) ×ˢ
        ((G.image (fun g => realGridIndex δ (g.1 + t * g.2))) ×ˢ
          (G.image (fun g => realGridIndex δ (g.1 + t * g.2)))) := by
  intro τ hτ
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hτ
  obtain ⟨_, h1, h2, h3⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ h1,
    Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ h2, Finset.mem_image_of_mem _ h3⟩⟩

/-- Few paths share a triple of grid cells: `#paths ≤ (9 / t) * #triples`. -/
theorem pathSet_card_le_triples (A B : Finset ℝ) (G : Finset (ℝ × ℝ)) {δ t a b : ℝ}
    (hδ : 0 < δ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hAsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ dist x y)
    (hBsep : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ dist x y) :
    ((pathSet A B G a b).card : ℝ) * t ≤ 9 * ((pathTriples A B G δ t a b).card : ℝ) := by
  classical
  let f : ℝ × ℝ → ℤ × ℤ × ℤ := fun q => (realGridIndex δ (a + t * q.2),
    realGridIndex δ (q.1 + t * q.2), realGridIndex δ (q.1 + t * b))
  have hcard := Finset.card_eq_sum_card_image f (pathSet A B G a b)
  have hfib : ∀ τ ∈ (pathSet A B G a b).image f,
      (((pathSet A B G a b).filter (fun q => f q = τ)).card : ℝ) * t ≤ 9 := by
    intro τ _
    have hsub : (pathSet A B G a b).filter (fun q => f q = τ) ⊆
        (A.filter (fun x => realGridIndex δ (t * b + 1 * x) = τ.2.2)) ×ˢ
          (B.filter (fun y => realGridIndex δ (a + t * y) = τ.1)) := by
      intro q hq
      obtain ⟨hqP, hqf⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqAB, _, _, _⟩ := Finset.mem_filter.mp hqP
      obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hqAB
      have h1 : realGridIndex δ (a + t * q.2) = τ.1 := by rw [← hqf]
      have h3 : realGridIndex δ (q.1 + t * b) = τ.2.2 := by rw [← hqf]
      refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hq1, ?_⟩,
        Finset.mem_filter.mpr ⟨hq2, h1⟩⟩
      rw [← h3]
      ring_nf
    have hA := grid_fiber_card_le (a := t * b) hδ one_pos A hAsep τ.2.2
    have hB := grid_fiber_card_le (a := a) hδ ht B hBsep τ.1
    have hle : (((pathSet A B G a b).filter (fun q => f q = τ)).card : ℝ) ≤
        ((A.filter (fun x => realGridIndex δ (t * b + 1 * x) = τ.2.2)).card : ℝ) *
          ((B.filter (fun y => realGridIndex δ (a + t * y) = τ.1)).card : ℝ) := by
      rw [← Nat.cast_mul, ← Finset.card_product]
      exact_mod_cast Finset.card_le_card hsub
    have hBt : ((B.filter (fun y => realGridIndex δ (a + t * y) = τ.1)).card : ℝ) * t ≤ 3 := by
      have : (1 / t + 2) * t ≤ 3 := by
        field_simp
        linarith
      calc _ ≤ (1 / t + 2) * t := mul_le_mul_of_nonneg_right hB ht.le
        _ ≤ 3 := this
    have hA3 : ((A.filter (fun x => realGridIndex δ (t * b + 1 * x) = τ.2.2)).card : ℝ) ≤ 3 := by
      have : (1 : ℝ) / 1 + 2 = 3 := by norm_num
      linarith
    calc (((pathSet A B G a b).filter (fun q => f q = τ)).card : ℝ) * t
        ≤ ((A.filter (fun x => realGridIndex δ (t * b + 1 * x) = τ.2.2)).card : ℝ) *
          ((B.filter (fun y => realGridIndex δ (a + t * y) = τ.1)).card : ℝ) * t :=
          mul_le_mul_of_nonneg_right hle ht.le
      _ = ((A.filter (fun x => realGridIndex δ (t * b + 1 * x) = τ.2.2)).card : ℝ) *
          (((B.filter (fun y => realGridIndex δ (a + t * y) = τ.1)).card : ℝ) * t) := by ring
      _ ≤ 3 * 3 := by
          apply mul_le_mul hA3 hBt (by positivity) (by norm_num)
      _ = 9 := by norm_num
  have hsum : ((pathSet A B G a b).card : ℝ) * t =
      ∑ τ ∈ (pathSet A B G a b).image f,
        (((pathSet A B G a b).filter (fun q => f q = τ)).card : ℝ) * t := by
    rw [← Finset.sum_mul]
    congr 1
    exact_mod_cast hcard
  rw [hsum]
  calc ∑ τ ∈ (pathSet A B G a b).image f,
        (((pathSet A B G a b).filter (fun q => f q = τ)).card : ℝ) * t
      ≤ ∑ τ ∈ (pathSet A B G a b).image f, (9 : ℝ) := Finset.sum_le_sum hfib
    _ = 9 * ((pathTriples A B G δ t a b).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        rfl

/-- Path triples of two sums in grid cells at distance at least four are disjoint. -/
theorem pathTriples_disjoint (A B : Finset ℝ) (G : Finset (ℝ × ℝ)) {δ t a b a' b' : ℝ}
    (hδ : 0 < δ) (hfar : 4 ≤ |realGridIndex δ (a + t * b) - realGridIndex δ (a' + t * b')|) :
    Disjoint (pathTriples A B G δ t a b) (pathTriples A B G δ t a' b') := by
  rw [Finset.disjoint_left]
  intro τ h1 h2
  obtain ⟨q, _, hq⟩ := Finset.mem_image.mp h1
  obtain ⟨q', _, hq'⟩ := Finset.mem_image.mp h2
  have e := hq.trans hq'.symm
  simp only [Prod.mk.injEq] at e
  obtain ⟨ei, ej, ek⟩ := e
  -- the sums lie within `3δ` of each other
  have g1 := realGridIndex_error hδ (a + t * q.2)
  have g2 := realGridIndex_error hδ (q.1 + t * q.2)
  have g3 := realGridIndex_error hδ (q.1 + t * b)
  have g1' := realGridIndex_error hδ (a' + t * q'.2)
  have g2' := realGridIndex_error hδ (q'.1 + t * q'.2)
  have g3' := realGridIndex_error hδ (q'.1 + t * b')
  rw [ei] at g1
  rw [ej] at g2
  rw [ek] at g3
  have hclose : |(a + t * b) - (a' + t * b')| < 3 * δ := by
    rw [abs_lt]
    constructor <;> nlinarith
  have w1 := realGridIndex_error hδ (a + t * b)
  have w2 := realGridIndex_error hδ (a' + t * b')
  set w := realGridIndex δ (a + t * b)
  set w' := realGridIndex δ (a' + t * b')
  have hw : |((w - w' : ℤ) : ℝ)| < 4 := by
    rw [Int.cast_sub, abs_lt]
    rw [abs_lt] at hclose
    constructor
    · by_contra hc
      have hc' := not_lt.mp hc
      nlinarith
    · by_contra hc
      have hc' := not_lt.mp hc
      nlinarith
  have hw' : |w - w'| < 4 := by
    have := hw
    rw [← Int.cast_abs] at this
    exact_mod_cast this
  omega

/-- **Projections of the full product from paths.** If every pair of `A' × B'` is joined by
`P` paths of length three in `G ⊆ A × B`, and the projection `x + t y` of `G` is covered by
`m` balls of radius `δ`, then `A' + t B'` is covered by `7776 m ^ 3 / (P t)` such balls. -/
theorem path_projection_cover (A B : Finset ℝ) (G : Finset (ℝ × ℝ)) (A' B' : Finset ℝ)
    {δ t P : ℝ} (hδ : 0 < δ) (ht : 0 < t) (ht1 : t ≤ 1) (hP : 0 < P)
    (hAsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ dist x y)
    (hBsep : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ dist x y)
    (hpaths : ∀ a ∈ A', ∀ b ∈ B', P ≤ ((pathSet A B G a b).card : ℝ))
    {m : ℕ} (c : Fin m → ℝ)
    (hcov : Covers δ ((fun p : ℝ × ℝ => p.1 + t * p.2) '' (↑G : Set (ℝ × ℝ))) c) :
    RealCoverBound δ (A' + realScalarImage t B') (7776 * (m : ℝ) ^ 3 / (P * t)) := by
  classical
  obtain ⟨WG, hWG⟩ : ∃ S : Finset ℤ, S = G.image (fun g => realGridIndex δ (g.1 + t * g.2)) :=
    ⟨_, rfl⟩
  have hWGc : (WG.card : ℝ) ≤ 6 * (m : ℝ) := by
    have hcov' : Covers δ (↑(G.image (fun p : ℝ × ℝ => p.1 + t * p.2)) : Set ℝ) c := by
      rw [Finset.coe_image]
      exact hcov
    have h := grid_image_card_le_cover hδ (G.image (fun p : ℝ × ℝ => p.1 + t * p.2)) c hcov'
    rw [Finset.image_image] at h
    rw [hWG]
    exact h
  obtain ⟨W, hW⟩ : ∃ S : Finset ℤ, S = (A' + realScalarImage t B').image (realGridIndex δ) :=
    ⟨_, rfl⟩
  have hrep : ∀ w ∈ W, ∃ ab : ℝ × ℝ, ab.1 ∈ A' ∧ ab.2 ∈ B' ∧
      realGridIndex δ (ab.1 + t * ab.2) = w := by
    intro w hw
    rw [hW] at hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨a, ha, u, hu, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨(a, b), ha, hb, rfl⟩
  choose! rep hrepA hrepB hrepw using hrep
  have htri : ∀ w ∈ W,
      P * t / 9 ≤ ((pathTriples A B G δ t (rep w).1 (rep w).2).card : ℝ) := by
    intro w hw
    have h1 := hpaths _ (hrepA w hw) _ (hrepB w hw)
    have h2 := pathSet_card_le_triples A B G (a := (rep w).1) (b := (rep w).2) hδ ht ht1
      hAsep hBsep
    have h3 : P * t ≤ ((pathSet A B G (rep w).1 (rep w).2).card : ℝ) * t :=
      mul_le_mul_of_nonneg_right h1 ht.le
    linarith
  have hclass : ∀ r : ℤ,
      ((W.filter (fun w => w % 4 = r)).card : ℝ) * (P * t / 9) ≤ (WG.card : ℝ) ^ 3 := by
    intro r
    have hdisj : (↑(W.filter (fun w => w % 4 = r)) : Set ℤ).PairwiseDisjoint
        (fun w => pathTriples A B G δ t (rep w).1 (rep w).2) := by
      intro w hw w' hw' hne
      have hw1 := Finset.mem_filter.mp hw
      have hw1' := Finset.mem_filter.mp hw'
      apply pathTriples_disjoint A B G hδ
      rw [hrepw w hw1.1, hrepw w' hw1'.1]
      have h1 := hw1.2
      have h2 := hw1'.2
      rw [le_abs]
      omega
    have hcardU := Finset.card_biUnion hdisj
    have hsubU : (W.filter (fun w => w % 4 = r)).biUnion
        (fun w => pathTriples A B G δ t (rep w).1 (rep w).2) ⊆ WG ×ˢ (WG ×ˢ WG) := by
      intro τ hτ
      obtain ⟨w, _, hτw⟩ := Finset.mem_biUnion.mp hτ
      rw [hWG]
      exact pathTriples_subset A B G δ t _ _ hτw
    have hle : (((W.filter (fun w => w % 4 = r)).biUnion
        (fun w => pathTriples A B G δ t (rep w).1 (rep w).2)).card : ℝ) ≤
          (WG.card : ℝ) ^ 3 := by
      have h := Finset.card_le_card hsubU
      rw [Finset.card_product, Finset.card_product] at h
      have h' : (((W.filter (fun w => w % 4 = r)).biUnion
          (fun w => pathTriples A B G δ t (rep w).1 (rep w).2)).card : ℝ) ≤
            ((WG.card * (WG.card * WG.card) : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      linarith [show (WG.card : ℝ) ^ 3 = (WG.card : ℝ) * ((WG.card : ℝ) * (WG.card : ℝ)) by ring]
    calc ((W.filter (fun w => w % 4 = r)).card : ℝ) * (P * t / 9)
        = ∑ w ∈ W.filter (fun w => w % 4 = r), P * t / 9 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ w ∈ W.filter (fun w => w % 4 = r),
            ((pathTriples A B G δ t (rep w).1 (rep w).2).card : ℝ) :=
          Finset.sum_le_sum (fun w hw => htri w (Finset.mem_filter.mp hw).1)
      _ = (((W.filter (fun w => w % 4 = r)).biUnion
            (fun w => pathTriples A B G δ t (rep w).1 (rep w).2)).card : ℝ) := by
          rw [hcardU]
          push_cast
          rfl
      _ ≤ (WG.card : ℝ) ^ 3 := hle
  have hWsum : (W.card : ℝ) =
      ∑ r ∈ Finset.Ico (0 : ℤ) 4, ((W.filter (fun w => w % 4 = r)).card : ℝ) := by
    have h := Finset.card_eq_sum_card_fiberwise (f := fun w : ℤ => w % 4) (s := W)
      (t := Finset.Ico (0 : ℤ) 4) (by
        intro w _
        simp only [Finset.coe_Ico, Set.mem_Ico]
        omega)
    exact_mod_cast h
  have hWbound : (W.card : ℝ) * (P * t / 9) ≤ 4 * (WG.card : ℝ) ^ 3 := by
    rw [hWsum, Finset.sum_mul]
    calc ∑ r ∈ Finset.Ico (0 : ℤ) 4, ((W.filter (fun w => w % 4 = r)).card : ℝ) * (P * t / 9)
        ≤ ∑ r ∈ Finset.Ico (0 : ℤ) 4, (WG.card : ℝ) ^ 3 := Finset.sum_le_sum (fun r _ => hclass r)
      _ = 4 * (WG.card : ℝ) ^ 3 := by simp
  have hcovW := cover_of_grid_image hδ (A' + realScalarImage t B')
  rw [← hW] at hcovW
  apply hcovW.mono subset_rfl
  have hPt : 0 < P * t := by positivity
  rw [le_div_iff₀ hPt]
  have hm : (WG.card : ℝ) ^ 3 ≤ (6 * (m : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) hWGc 3
  nlinarith

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
