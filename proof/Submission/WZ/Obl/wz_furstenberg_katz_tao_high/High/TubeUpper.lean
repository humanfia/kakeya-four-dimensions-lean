-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.TubeUpper.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o222/x0722 High/TubeUpper.lean (c61cafd).
-- Adapted from local obligation o157, branch x0675, commit 5a2c82ba2c9f.
-- Source: High/TubeUpper.lean. Shared half definitions imported from accepted o213.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.WideStripPacking
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.SharedAssembly

/-!
# Upper bound for the lines in a coarse tube

`tube_lines_upper`: in a regularized failed bush estimate with lines `cls` (into `J₀`) and coarse
tubes `tb` at scale `w` (a `StripSep w` family `J₁`), every occupied tube holds at most
`K ^ 3 #J₀ / #T` lines (`lines_per_tube_le`), and the coarse Cauchy--Schwarz with all pins as
points (`cell_tubes_bound`, pins within `26 w` of their tubes by `pin_near_tube`) gives
`#T ≥ B ^ 2 / C`, `B` = tubes per pin. Hence `N(j) B ^ 2 ≤ K ^ 3 C #J₀`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_tower_balanced_refinement

attribute [local instance] Classical.propDecidable

/-- The Cauchy--Schwarz constant with all pins as points (width `26 w`, separation `w`). -/
noncomputable def pinConst (w CY : ℝ) (KY : ℕ) : ℝ :=
  128000 * (64 * (26 * w) / w + 2) * (36 * (26 * w) / w + 2) * CY *
    (1 + Real.log (1 / (26 * w))) * ((KY : ℝ) + 1) ^ 2

theorem tube_lines_upper {r s ε₀ η η' K w B : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : FailData r s ε₀ η P D) (hK : 0 ≤ K) (hrw : r ≤ w) (hw2 : 26 * w ≤ 1 / 2)
    {cls tb : E2 × E2 → E2 × E2} {J₀ J₁ : Finset (E2 × E2)}
    (hclsJ : ∀ q ∈ D, cls q ∈ J₀) (hJ₀D : J₀ ⊆ D)
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
      (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r))
    (hJ₁ : J₁ ⊆ J₀) (hJ₁sep : ∀ x ∈ J₁, ∀ y ∈ J₁, x ≠ y → StripSep w x y)
    (htbJ : ∀ ℓ ∈ J₀, tb ℓ ∈ J₁)
    (htbgeo : ∀ ℓ ∈ J₀, |inner ℝ (ℓ.1 - (tb ℓ).1) (tb ℓ).2| < 9 * w ∧
      (dist ℓ.2 (tb ℓ).2 < w ∨ dist ℓ.2 (-(tb ℓ).2) < w))
    {S : Finset (E2 × E2)} (hSD : S ⊆ D) (hS : FailData r s ε₀ η' (S.image Prod.fst) S)
    (htube : ∀ q ∈ S, ∀ q' ∈ S, ((S.filter (fun a => tb (cls a) = tb (cls q))).card : ℝ) ≤
      K * (S.filter (fun a => tb (cls a) = tb (cls q'))).card)
    (hline : ∀ q ∈ S, ∀ q' ∈ S, ((S.filter (fun a => cls a = cls q)).card : ℝ) ≤
      K * (S.filter (fun a => cls a = cls q')).card)
    (hB : 0 ≤ B) (hBpin : ∀ p ∈ S.image Prod.fst, B ≤ ((pinTubes S cls tb p).card : ℝ))
    (KY : ℕ) (hKY : ((S.image Prod.fst).card : ℝ) ≤ 2 ^ KY)
    {q₀ : E2 × E2} (hq₀ : q₀ ∈ S) :
    (((S.filter (fun a => tb (cls a) = tb (cls q₀))).image cls).card : ℝ) * B ^ 2 ≤
      K ^ 3 * pinConst w (r ^ (-η') / r / ((S.image Prod.fst).card : ℝ)) KY * J₀.card := by
  classical
  have hr := hS.r_pos
  have hw : 0 < w := hr.trans_le hrw
  set Q := S.image Prod.fst with hQ
  set T := S.image (fun a => tb (cls a)) with hT
  have hcls1 : ∀ a ∈ D, ‖(cls a).2‖ = 1 := fun a ha => (h.D_mem _ (hJ₀D (hclsJ a ha))).2
  have hQpos : (0 : ℝ) < Q.card := by
    obtain ⟨a, ha⟩ := hS.P_ne
    exact_mod_cast Finset.card_pos.mpr ⟨a, ha⟩
  -- the pins are normalized 1-Frostman at scale `w`
  have hCY0 : 0 ≤ r ^ (-η') / r / (Q.card : ℝ) :=
    div_nonneg (div_nonneg (Real.rpow_nonneg hr.le _) hr.le) hQpos.le
  have hYfr : ∀ (x : E2) (t : ℝ), w ≤ t →
      ((Q.filter (fun z => z ∈ Metric.closedBall x t)).card : ℝ) ≤
        (r ^ (-η') / r / (Q.card : ℝ)) * t * Q.card := by
    intro x t ht
    have h1 := hS.P_kt x t (hrw.trans ht)
    have heq : Q.filter (fun z => z ∈ Metric.closedBall x t) = Q.filter (fun p => dist p x ≤ t) := by
      ext z; simp [Metric.mem_closedBall]
    rw [heq]
    calc ((Q.filter (fun p => dist p x ≤ t)).card : ℝ) ≤ r ^ (-η') * (t / r) := h1
      _ = (r ^ (-η') / r / (Q.card : ℝ)) * t * Q.card := by field_simp
  have hY4 : ∀ y ∈ Q, ‖y‖ ≤ 4 := fun y hy => hS.P_norm y hy
  have hTJ₁ : T ⊆ J₁ := by
    intro j hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
    exact htbJ _ (hclsJ a (hSD ha))
  have hTprop : ∀ j ∈ T, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1 := by
    intro j hj
    have hjD := hJ₀D (hJ₁ (hTJ₁ hj))
    exact ⟨h.P_norm _ (h.D_mem j hjD).1, (h.D_mem j hjD).2⟩
  have hinc : ∀ y ∈ Q, B ≤ ((T.filter (fun j => |inner ℝ (y - j.1) j.2| < 26 * w)).card : ℝ) := by
    intro y hy
    refine (hBpin y hy).trans ?_
    have hsub : pinTubes S cls tb y ⊆ T.filter (fun j => |inner ℝ (y - j.1) j.2| < 26 * w) := by
      intro j hj
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨hbS, hby⟩ := Finset.mem_filter.mp hb
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨b, hbS, rfl⟩, ?_⟩
      have hbD := hSD hbS
      have hℓJ := hclsJ b hbD
      have hj1 : ‖(tb (cls b)).2‖ = 1 := (h.D_mem _ (hJ₀D (hJ₁ (htbJ _ hℓJ)))).2
      have hnear := pin_near_tube (h.P_norm _ (h.D_mem b hbD).1)
        (h.P_norm _ (h.D_mem _ (hJ₀D hℓJ)).1) (hcls1 b hbD) hj1
        (hgeo b hbD).1 (htbgeo _ hℓJ).1 (htbgeo _ hℓJ).2
      rw [← hby]
      linarith
    exact_mod_cast Finset.card_le_card hsub
  have hQne : Q.Nonempty := hS.P_ne
  have hCS := cell_tubes_bound hw (by linarith : w ≤ 26 * w) hw2 hCY0 hB Q hQne hY4 hYfr T hTprop
    (fun x hx y hy hne => hJ₁sep x (hTJ₁ hx) y (hTJ₁ hy) hne) KY hKY hinc
  have hCSeq : 128000 * (64 * (26 * w) / w + 2) * (36 * (26 * w) / w + 2) *
      (r ^ (-η') / r / (Q.card : ℝ)) * (1 + Real.log (1 / (26 * w))) * ((KY : ℝ) + 1) ^ 2 *
        T.card = pinConst w (r ^ (-η') / r / (Q.card : ℝ)) KY * T.card := by
    unfold pinConst; ring
  rw [hCSeq] at hCS
  have hlpt := lines_per_tube_le hK htube hline hq₀
  have himgJ : ((S.image cls).card : ℝ) ≤ J₀.card := by
    have : S.image cls ⊆ J₀ := by
      intro ℓ hℓ
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hℓ
      exact hclsJ a (hSD ha)
    exact_mod_cast Finset.card_le_card this
  have hN0 : (0 : ℝ) ≤ (((S.filter (fun a => tb (cls a) = tb (cls q₀))).image cls).card : ℝ) :=
    Nat.cast_nonneg _
  calc (((S.filter (fun a => tb (cls a) = tb (cls q₀))).image cls).card : ℝ) * B ^ 2
      ≤ (((S.filter (fun a => tb (cls a) = tb (cls q₀))).image cls).card : ℝ) *
          (pinConst w (r ^ (-η') / r / (Q.card : ℝ)) KY * T.card) :=
        mul_le_mul_of_nonneg_left hCS hN0
    _ = pinConst w (r ^ (-η') / r / (Q.card : ℝ)) KY *
          ((((S.filter (fun a => tb (cls a) = tb (cls q₀))).image cls).card : ℝ) * T.card) := by ring
    _ ≤ pinConst w (r ^ (-η') / r / (Q.card : ℝ)) KY * (K ^ 3 * (S.image cls).card) := by
        apply mul_le_mul_of_nonneg_left hlpt
        unfold pinConst
        have hlog : 0 ≤ Real.log (1 / (26 * w)) := by
          apply Real.log_nonneg
          rw [le_div_iff₀ (by linarith)]
          linarith
        have h1 : (0 : ℝ) ≤ 64 * (26 * w) / w + 2 := by
          have : 0 ≤ 64 * (26 * w) / w := div_nonneg (by linarith) hw.le
          linarith
        have h2 : (0 : ℝ) ≤ 36 * (26 * w) / w + 2 := by
          have : 0 ≤ 36 * (26 * w) / w := div_nonneg (by linarith) hw.le
          linarith
        have h3 : (0 : ℝ) ≤ 1 + Real.log (1 / (26 * w)) := by linarith
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) h2)
          hCY0) h3) (sq_nonneg _)
    _ ≤ pinConst w (r ^ (-η') / r / (Q.card : ℝ)) KY * (K ^ 3 * J₀.card) := by
        apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left himgJ (pow_nonneg hK 3))
        unfold pinConst
        have hlog : 0 ≤ Real.log (1 / (26 * w)) := by
          apply Real.log_nonneg
          rw [le_div_iff₀ (by linarith)]
          linarith
        have h1 : (0 : ℝ) ≤ 64 * (26 * w) / w + 2 := by
          have : 0 ≤ 64 * (26 * w) / w := div_nonneg (by linarith) hw.le
          linarith
        have h2 : (0 : ℝ) ≤ 36 * (26 * w) / w + 2 := by
          have : 0 ≤ 36 * (26 * w) / w := div_nonneg (by linarith) hw.le
          linarith
        have h3 : (0 : ℝ) ≤ 1 + Real.log (1 / (26 * w)) := by linarith
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) h2)
          hCY0) h3) (sq_nonneg _)
    _ = _ := by ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

/-- `|⟪v, e⟫| ≤ |⟪v, ± f⟫| + 8 |e ∓ f|` for `‖v‖ ≤ 8`. -/
theorem inner_le_of_close {v e f : E2} {A d : ℝ} (hv : ‖v‖ ≤ 8) (hA : |inner ℝ v f| < A)
    (hd : dist e f < d ∨ dist e (-f) < d) : |inner ℝ v e| < A + 8 * d := by
  rcases hd with h | h
  · have e1 : inner ℝ v e = inner ℝ v f + inner ℝ v (e - f) := by
      rw [← inner_add_right]; congr 1; abel
    have e2 : |inner ℝ v (e - f)| ≤ ‖v‖ * ‖e - f‖ := abs_real_inner_le_norm _ _
    have e3 : ‖v‖ * ‖e - f‖ ≤ 8 * d := by
      have hd' : ‖e - f‖ ≤ d := by rw [← dist_eq_norm]; exact h.le
      nlinarith [norm_nonneg v, norm_nonneg (e - f)]
    rw [e1]
    calc |inner ℝ v f + inner ℝ v (e - f)| ≤ |inner ℝ v f| + |inner ℝ v (e - f)| := abs_add_le _ _
      _ < A + 8 * d := by linarith
  · have e1 : inner ℝ v e = -inner ℝ v f + inner ℝ v (e + f) := by
      rw [inner_add_right]; ring
    have e2 : |inner ℝ v (e + f)| ≤ ‖v‖ * ‖e + f‖ := abs_real_inner_le_norm _ _
    have e3 : ‖v‖ * ‖e + f‖ ≤ 8 * d := by
      have hd' : ‖e + f‖ ≤ d := by
        have : dist e (-f) = ‖e + f‖ := by rw [dist_eq_norm, sub_neg_eq_add]
        rw [← this]; exact h.le
      nlinarith [norm_nonneg v, norm_nonneg (e + f)]
    rw [e1]
    calc |-inner ℝ v f + inner ℝ v (e + f)| ≤ |-inner ℝ v f| + |inner ℝ v (e + f)| := abs_add_le _ _
      _ = |inner ℝ v f| + |inner ℝ v (e + f)| := by rw [abs_neg]
      _ < A + 8 * d := by linarith

/-- Closeness of unit normals up to sign composes. -/
theorem normal_close_trans {a b c : E2} {d₁ d₂ : ℝ}
    (h₁ : dist a b < d₁ ∨ dist a (-b) < d₁) (h₂ : dist b c < d₂ ∨ dist b (-c) < d₂) :
    dist a c < d₁ + d₂ ∨ dist a (-c) < d₁ + d₂ := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · left; linarith [dist_triangle a b c]
  · right; linarith [dist_triangle a b (-c)]
  · right
    have : dist (-b) (-c) = dist b c := by rw [dist_neg_neg]
    linarith [dist_triangle a (-b) (-c)]
  · left
    have : dist (-b) c = dist b (-c) := by
      rw [dist_eq_norm, dist_eq_norm]
      rw [show -b - c = -(b - -c) by abel, norm_neg]
    linarith [dist_triangle a (-b) c]

theorem normal_close_symm {a b : E2} {d : ℝ} (h : dist a b < d ∨ dist a (-b) < d) :
    dist b a < d ∨ dist b (-a) < d := by
  rcases h with h | h
  · left; rwa [dist_comm]
  · right
    have : dist b (-a) = dist a (-b) := by
      rw [dist_eq_norm, dist_eq_norm, show b - -a = a - -b by abel]
    rwa [this]

/-- Lines close at scale `W` have tubes (of a `w`-family) close at scale `25 W + 42 w`. -/
theorem tubes_close_of_lines_close {ℓ ℓ₀ k k₀ : E2 × E2} {W w : ℝ}
    (hℓ4 : ‖ℓ.1‖ ≤ 4) (hℓ₀4 : ‖ℓ₀.1‖ ≤ 4) (hk4 : ‖k.1‖ ≤ 4) (hk₀4 : ‖k₀.1‖ ≤ 4)
    (hclose : |inner ℝ (ℓ.1 - ℓ₀.1) ℓ₀.2| < 9 * W ∧ (dist ℓ.2 ℓ₀.2 < W ∨ dist ℓ.2 (-ℓ₀.2) < W))
    (hk : |inner ℝ (ℓ.1 - k.1) k.2| < 9 * w ∧ (dist ℓ.2 k.2 < w ∨ dist ℓ.2 (-k.2) < w))
    (hk₀ : |inner ℝ (ℓ₀.1 - k₀.1) k₀.2| < 9 * w ∧ (dist ℓ₀.2 k₀.2 < w ∨ dist ℓ₀.2 (-k₀.2) < w)) :
    ¬ StripSep (25 * W + 42 * w) k k₀ := by
  -- normals of the tubes
  have hn1 : dist k.2 ℓ.2 < w ∨ dist k.2 (-ℓ.2) < w := normal_close_symm hk.2
  have hn2 : dist k.2 ℓ₀.2 < w + W ∨ dist k.2 (-ℓ₀.2) < w + W := normal_close_trans hn1 hclose.2
  have hn3 : dist k.2 k₀.2 < w + W + w ∨ dist k.2 (-k₀.2) < w + W + w :=
    normal_close_trans hn2 hk₀.2
  -- offsets
  have hv1 : ‖ℓ.1 - k.1‖ ≤ 8 := norm_le_eight_of_norm_le_four hℓ4 hk4
  have hv2 : ‖ℓ.1 - ℓ₀.1‖ ≤ 8 := norm_le_eight_of_norm_le_four hℓ4 hℓ₀4
  have hv3 : ‖ℓ₀.1 - k₀.1‖ ≤ 8 := norm_le_eight_of_norm_le_four hℓ₀4 hk₀4
  have t1 : |inner ℝ (k.1 - ℓ.1) k.2| < 9 * w := by
    rw [show k.1 - ℓ.1 = -(ℓ.1 - k.1) by abel, inner_neg_left, abs_neg]; exact hk.1
  have t2 : |inner ℝ (ℓ.1 - ℓ₀.1) k.2| < 9 * W + 8 * (w + W) := inner_le_of_close hv2 hclose.1 hn2
  have t3 : |inner ℝ (ℓ₀.1 - k₀.1) k.2| < 9 * w + 8 * (w + W + w) :=
    inner_le_of_close hv3 hk₀.1 hn3
  have hsplit : inner ℝ (k.1 - k₀.1) k.2 =
      inner ℝ (k.1 - ℓ.1) k.2 + inner ℝ (ℓ.1 - ℓ₀.1) k.2 + inner ℝ (ℓ₀.1 - k₀.1) k.2 := by
    rw [← inner_add_left, ← inner_add_left]; congr 1; abel
  have hoff : |inner ℝ (k.1 - k₀.1) k.2| < 25 * W + 42 * w := by
    rw [hsplit]
    calc |inner ℝ (k.1 - ℓ.1) k.2 + inner ℝ (ℓ.1 - ℓ₀.1) k.2 + inner ℝ (ℓ₀.1 - k₀.1) k.2|
        ≤ |inner ℝ (k.1 - ℓ.1) k.2 + inner ℝ (ℓ.1 - ℓ₀.1) k.2| + |inner ℝ (ℓ₀.1 - k₀.1) k.2| :=
          abs_add_le _ _
      _ ≤ |inner ℝ (k.1 - ℓ.1) k.2| + |inner ℝ (ℓ.1 - ℓ₀.1) k.2| + |inner ℝ (ℓ₀.1 - k₀.1) k.2| := by
          linarith [abs_add_le (inner ℝ (k.1 - ℓ.1) k.2) (inner ℝ (ℓ.1 - ℓ₀.1) k.2)]
      _ < 25 * W + 42 * w := by linarith
  unfold StripSep
  push Not
  have hwW : w + W + w ≤ 25 * W + 42 * w := by
    have h0 : 0 ≤ W := by
      rcases hclose.2 with h | h <;> linarith [dist_nonneg (x := ℓ.2) (y := ℓ₀.2),
        dist_nonneg (x := ℓ.2) (y := -ℓ₀.2)]
    have h0' : 0 ≤ w := by
      rcases hk.2 with h | h <;> linarith [dist_nonneg (x := ℓ.2) (y := k.2),
        dist_nonneg (x := ℓ.2) (y := -k.2)]
    linarith
  refine ⟨?_, hoff⟩
  intro hfar
  rcases hn3 with h | h
  · linarith
  · linarith

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

attribute [local instance] Classical.propDecidable

/-- Lines within `(9 W, W)` of a line `ℓ₀` lie in the `O(1)` tubes of the `w`-family near the
tube of `ℓ₀`, so they number at most `2 (64 W' / w + 2) (36 W' / w + 2) N_max`,
`W' = 25 W + 42 w`. -/
theorem lines_near_le {S : Finset (E2 × E2)} {cls tb : E2 × E2 → E2 × E2} {W w Nmax : ℝ}
    (hw : 0 < w) (hW0 : 0 ≤ W) (hW' : 25 * W + 42 * w ≤ 1 / 2)
    (hT4 : ∀ q ∈ S, ‖(tb (cls q)).1‖ ≤ 4 ∧ ‖(tb (cls q)).2‖ = 1)
    (hℓ4 : ∀ q ∈ S, ‖(cls q).1‖ ≤ 4)
    (hsep : ∀ x ∈ S.image (fun a => tb (cls a)), ∀ y ∈ S.image (fun a => tb (cls a)), x ≠ y →
      StripSep w x y)
    (htbgeo : ∀ q ∈ S, |inner ℝ ((cls q).1 - (tb (cls q)).1) (tb (cls q)).2| < 9 * w ∧
      (dist (cls q).2 (tb (cls q)).2 < w ∨ dist (cls q).2 (-(tb (cls q)).2) < w))
    (hN : ∀ q ∈ S, (((S.filter (fun a => tb (cls a) = tb (cls q))).image cls).card : ℝ) ≤ Nmax)
    {q₀ : E2 × E2} (hq₀ : q₀ ∈ S) :
    ((((S.image cls).filter (fun ℓ => |inner ℝ (ℓ.1 - (cls q₀).1) (cls q₀).2| < 9 * W ∧
        (dist ℓ.2 (cls q₀).2 < W ∨ dist ℓ.2 (-(cls q₀).2) < W))).card : ℝ)) ≤
      2 * (64 * (25 * W + 42 * w) / w + 2) * (36 * (25 * W + 42 * w) / w + 2) * Nmax := by
  classical
  set T := S.image (fun a => tb (cls a)) with hT
  set W' := 25 * W + 42 * w with hW'def
  set k₀ := tb (cls q₀) with hk₀
  have hk₀T : k₀ ∈ T := Finset.mem_image.mpr ⟨q₀, hq₀, rfl⟩
  set Near := (S.image cls).filter (fun ℓ => |inner ℝ (ℓ.1 - (cls q₀).1) (cls q₀).2| < 9 * W ∧
        (dist ℓ.2 (cls q₀).2 < W ∨ dist ℓ.2 (-(cls q₀).2) < W)) with hNear
  set T' := T.filter (fun j => ¬ StripSep W' j k₀ ∨ ¬ StripSep W' k₀ j) with hT'
  -- every near line has its tube in T'
  have hmaps : ∀ ℓ ∈ Near, ∃ q ∈ S, cls q = ℓ ∧ tb (cls q) ∈ T' := by
    intro ℓ hℓ
    obtain ⟨hℓS, hclose⟩ := Finset.mem_filter.mp hℓ
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hℓS
    refine ⟨q, hq, rfl, Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨q, hq, rfl⟩, Or.inl ?_⟩⟩
    exact tubes_close_of_lines_close (hℓ4 q hq) (hℓ4 q₀ hq₀) (hT4 q hq).1 (hT4 q₀ hq₀).1
      hclose (htbgeo q hq) (htbgeo q₀ hq₀)
  -- count by tubes
  have hcover : Near ⊆ T'.biUnion (fun j => (S.filter (fun a => tb (cls a) = j)).image cls) := by
    intro ℓ hℓ
    obtain ⟨q, hq, hqℓ, hqT'⟩ := hmaps ℓ hℓ
    exact Finset.mem_biUnion.mpr ⟨tb (cls q), hqT', Finset.mem_image.mpr
      ⟨q, Finset.mem_filter.mpr ⟨hq, rfl⟩, hqℓ⟩⟩
  have h1 : (Near.card : ℝ) ≤ ∑ j ∈ T', (((S.filter (fun a => tb (cls a) = j)).image cls).card : ℝ) := by
    have := (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    exact_mod_cast this
  have h2 : ∑ j ∈ T', (((S.filter (fun a => tb (cls a) = j)).image cls).card : ℝ) ≤ T'.card * Nmax := by
    calc ∑ j ∈ T', (((S.filter (fun a => tb (cls a) = j)).image cls).card : ℝ)
        ≤ ∑ _j ∈ T', Nmax := by
          apply Finset.sum_le_sum
          intro j hj
          obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hj).1
          exact hN q hq
      _ = T'.card * Nmax := by rw [Finset.sum_const, nsmul_eq_mul]
  -- the neighbour tubes are few
  have hTprop : ∀ j ∈ T, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1 := by
    intro j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    exact hT4 q hq
  have hsep' : (T : Set (E2 × E2)).Pairwise
      (WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs.StripSep w) :=
    fun x hx y hy hne => hsep x hx y hy hne
  have hWpos : 0 < W' := by rw [hW'def]; linarith
  have hcount := strip_neighbor_count hw hWpos hW' T hTprop hsep' hk₀T
  have hT'eq : T' = T.filter (fun j => ¬ WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs.StripSep W' j k₀ ∨
      ¬ WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs.StripSep W' k₀ j) := rfl
  rw [← hT'eq] at hcount
  have hN0 : 0 ≤ Nmax := (Nat.cast_nonneg _).trans (hN q₀ hq₀)
  calc (Near.card : ℝ) ≤ T'.card * Nmax := h1.trans h2
    _ ≤ (2 * (64 * W' / w + 2) * (36 * W' / w + 2)) * Nmax := mul_le_mul_of_nonneg_right hcount hN0
end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
