-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.TubeLines.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o222/x0722 High/TubeLines.lean (c61cafd).
-- Adapted from local obligation o157, branch x0675, commit 5a2c82ba2c9f.
-- Source: High/TubeLines.lean. Shared half definitions imported from accepted o213.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.Classes

/-!
# Lines in a coarse tube: the quadratic lower bound (counting core)

Labels `S` (pairs (pin, normal)) are sent to lines by `cls` and lines to coarse tubes by
`tb`. Fix a label `q₀` with pin `p` and tube `j = tb (cls q₀)`, and let `m` be the number of
labels of `p` in `j`. Assume
* the labels per (pin, tube) are balanced: every occupied (pin, tube) has at least `m / K`;
* the lines are balanced: all occupied lines carry the same number of labels up to `K`;
* a (pin, line) pair carries at most `n` labels;
* every line has at most half of its labels within `c` of any of its pins (two ends);
* a pin at distance at least `c` from `p` lies on at most `μ` of the lines of `p` in `j`.
Then `m ^ 2 ≤ 2 n ^ 2 K ^ 3 μ #(lines in j)` (at most `n` labels per (pin, line)) (x0665's step (1) of 2026-10-13T12:26Z): the far pins of
the `m` lines of `p` number `≳ m k / (K μ)`, each has `≳ m / K` labels in `j`, and a line
of `j` collects at most `K k` labels.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

theorem tube_lines_quadratic {S : Finset (E2 × E2)} {cls tb : E2 × E2 → E2 × E2}
    {K c μ : ℝ} (hK : 0 < K) (hμ : 0 ≤ μ) (npc : ℕ) {q₀ : E2 × E2} (hq₀ : q₀ ∈ S)
    (hbal : ∀ q ∈ S,
      ((S.filter (fun q' => q'.1 = q₀.1 ∧ tb (cls q') = tb (cls q₀))).card : ℝ) ≤
        K * (S.filter (fun q' => q'.1 = q.1 ∧ tb (cls q') = tb (cls q))).card)
    (hcls : ∀ q ∈ S, ∀ q' ∈ S, ((S.filter (fun q'' => cls q'' = cls q)).card : ℝ) ≤
        K * (S.filter (fun q'' => cls q'' = cls q')).card)
    (hpc : ∀ (x : E2) (ℓ : E2 × E2), (S.filter (fun q => q.1 = x ∧ cls q = ℓ)).card ≤ npc)
    (hfar : ∀ q ∈ S, 2 * ((((S.filter (fun q' => cls q' = cls q)).filter
        (fun q' => dist q'.1 q.1 < c)).card : ℝ)) ≤ (S.filter (fun q' => cls q' = cls q)).card)
    (hmult : ∀ x : E2, c ≤ dist x q₀.1 →
      ((((S.filter (fun q => q.1 = q₀.1 ∧ tb (cls q) = tb (cls q₀))).image cls).filter
        (fun ℓ => ∃ q' ∈ S, q'.1 = x ∧ cls q' = ℓ)).card : ℝ) ≤ μ) :
    ((S.filter (fun q => q.1 = q₀.1 ∧ tb (cls q) = tb (cls q₀))).card : ℝ) ^ 2 ≤
      2 * (npc : ℝ) ^ 2 * K ^ 3 * μ *
        ((S.filter (fun q => tb (cls q) = tb (cls q₀))).image cls).card := by
  classical
  set p := q₀.1 with hp
  set j := tb (cls q₀) with hj
  set A := S.filter (fun q => q.1 = p ∧ tb (cls q) = j) with hA
  set Λp := A.image cls with hΛp
  set Λj := (S.filter (fun q => tb (cls q) = j)).image cls with hΛj
  set F : E2 × E2 → Finset (E2 × E2) := fun ℓ => S.filter (fun q'' => cls q'' = ℓ) with hF
  set k : ℝ := ((F (cls q₀)).card : ℝ) with hk
  have hkpos : 0 < k := by
    have hmem : q₀ ∈ F (cls q₀) := Finset.mem_filter.mpr ⟨hq₀, rfl⟩
    have hpos : 0 < (F (cls q₀)).card := Finset.card_pos.mpr ⟨q₀, hmem⟩
    rw [hk]
    exact_mod_cast hpos
  have hFle : ∀ q ∈ S, ((F (cls q)).card : ℝ) ≤ K * k := fun q hq => hcls q hq q₀ hq₀
  have hFge : ∀ q ∈ S, k ≤ K * (F (cls q)).card := fun q hq => hcls q₀ hq₀ q hq
  -- Step 1: m ≤ npc #Λp
  have hstep1 : (A.card : ℝ) ≤ npc * Λp.card := by
    have h := Finset.card_le_mul_card_image A npc (fun ℓ _ => by
      refine (Finset.card_le_card ?_).trans (hpc p ℓ)
      intro q hq
      simp only [Finset.mem_filter, hA] at hq ⊢
      exact ⟨hq.1.1, hq.1.2.1, hq.2⟩)
    exact_mod_cast h
  -- Step 2: the far labels of the lines of p
  set FarAll := S.filter (fun q' => cls q' ∈ Λp ∧ c ≤ dist q'.1 p) with hFarAll
  have hstep2 : (Λp.card : ℝ) * (k / (2 * K)) ≤ FarAll.card := by
    have hsum : (FarAll.card : ℝ) = ∑ ℓ ∈ Λp, ((FarAll.filter (fun q' => cls q' = ℓ)).card : ℝ) := by
      have := Finset.card_eq_sum_card_fiberwise (f := cls) (s := FarAll) (t := Λp)
        (fun q hq => (Finset.mem_filter.mp hq).2.1)
      exact_mod_cast this
    rw [hsum]
    calc (Λp.card : ℝ) * (k / (2 * K)) = ∑ _ℓ ∈ Λp, k / (2 * K) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro ℓ hℓ
        obtain ⟨q, hqA, rfl⟩ := Finset.mem_image.mp hℓ
        have hqS : q ∈ S := (Finset.mem_filter.mp hqA).1
        have hqp : q.1 = p := (Finset.mem_filter.mp hqA).2.1
        have hf := hfar q hqS
        -- the far part of the line
        have hsplit : ((F (cls q)).card : ℝ) ≤
            (((F (cls q)).filter (fun q' => dist q'.1 q.1 < c)).card : ℝ) +
              ((FarAll.filter (fun q' => cls q' = cls q)).card : ℝ) := by
          have hsub : F (cls q) ⊆ (F (cls q)).filter (fun q' => dist q'.1 q.1 < c) ∪
              FarAll.filter (fun q' => cls q' = cls q) := by
            intro q' hq'
            have hq'S : q' ∈ S := (Finset.mem_filter.mp hq').1
            have hq'c : cls q' = cls q := (Finset.mem_filter.mp hq').2
            by_cases hd : dist q'.1 q.1 < c
            · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hq', hd⟩)
            · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨?_, hq'c⟩)
              refine Finset.mem_filter.mpr ⟨hq'S, ?_, ?_⟩
              · rw [hq'c]; exact Finset.mem_image.mpr ⟨q, hqA, rfl⟩
              · rw [← hqp]; exact not_lt.mp hd
          have hc1 := Finset.card_le_card hsub
          have hc2 := Finset.card_union_le ((F (cls q)).filter (fun q' => dist q'.1 q.1 < c))
            (FarAll.filter (fun q' => cls q' = cls q))
          have hc3 := hc1.trans hc2
          exact_mod_cast hc3
        have hge := hFge q hqS
        have hKk : k / (2 * K) ≤ ((F (cls q)).card : ℝ) / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        have : ((F (cls q)).card : ℝ) / 2 ≤ ((FarAll.filter (fun q' => cls q' = cls q)).card : ℝ) := by
          change 2 * ((((S.filter (fun q' => cls q' = cls q)).filter
            (fun q' => dist q'.1 q.1 < c)).card : ℝ)) ≤ ((F (cls q)).card : ℝ) at hf
          linarith
        linarith
  -- Step 3: far pins
  set X := FarAll.image Prod.fst with hX
  have hstep3 : (FarAll.card : ℝ) ≤ npc * μ * X.card := by
    have hsum : (FarAll.card : ℝ) = ∑ x ∈ X, ((FarAll.filter (fun q' => q'.1 = x)).card : ℝ) := by
      have := Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := FarAll) (t := X)
        (fun q hq => Finset.mem_image.mpr ⟨q, hq, rfl⟩)
      exact_mod_cast this
    rw [hsum]
    calc ∑ x ∈ X, ((FarAll.filter (fun q' => q'.1 = x)).card : ℝ) ≤ ∑ _x ∈ X, npc * μ := by
          apply Finset.sum_le_sum
          intro x hx
          obtain ⟨q₁, hq₁, rfl⟩ := Finset.mem_image.mp hx
          have hdist : c ≤ dist q₁.1 p := (Finset.mem_filter.mp hq₁).2.2
          set Λx := Λp.filter (fun ℓ => ∃ q' ∈ S, q'.1 = q₁.1 ∧ cls q' = ℓ) with hΛx
          have hfib : ((FarAll.filter (fun q' => q'.1 = q₁.1)).card : ℝ) ≤ npc * Λx.card := by
            have h := Finset.card_le_mul_card_image (FarAll.filter (fun q' => q'.1 = q₁.1)) npc
              (f := cls) (fun ℓ _ => by
                refine (Finset.card_le_card ?_).trans (hpc q₁.1 ℓ)
                intro q hq
                simp only [Finset.mem_filter] at hq ⊢
                exact ⟨(Finset.mem_filter.mp hq.1.1).1, hq.1.2, hq.2⟩)
            have hsub : (FarAll.filter (fun q' => q'.1 = q₁.1)).image cls ⊆ Λx := by
              intro ℓ hℓ
              obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hℓ
              have hq' := Finset.mem_filter.mp hq
              exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq'.1).2.1,
                ⟨q, (Finset.mem_filter.mp hq'.1).1, hq'.2, rfl⟩⟩
            have h2 := Finset.card_le_card hsub
            have h3 : (FarAll.filter (fun q' => q'.1 = q₁.1)).card ≤ npc * Λx.card :=
              h.trans (Nat.mul_le_mul_left npc h2)
            exact_mod_cast h3
          have hmu : (Λx.card : ℝ) ≤ μ := hmult q₁.1 hdist
          have hn0 : (0 : ℝ) ≤ npc := Nat.cast_nonneg _
          nlinarith
      _ = npc * μ * X.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  -- Step 4: every far pin has many labels in j
  have hstep4 : ∀ x ∈ X, (A.card : ℝ) ≤
      K * (S.filter (fun q' => q'.1 = x ∧ tb (cls q') = j)).card := by
    intro x hx
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hx
    have hq'S : q' ∈ S := (Finset.mem_filter.mp hq').1
    have hcl : cls q' ∈ Λp := (Finset.mem_filter.mp hq').2.1
    obtain ⟨q, hqA, hqc⟩ := Finset.mem_image.mp hcl
    have htb : tb (cls q') = j := by rw [← hqc]; exact (Finset.mem_filter.mp hqA).2.2
    have h := hbal q' hq'S
    rw [htb] at h
    exact h
  -- Step 5: labels of j at far pins
  set Y := S.filter (fun y => tb (cls y) = j ∧ y.1 ∈ X) with hY
  have hYlow : (X.card : ℝ) * (A.card / K) ≤ Y.card := by
    have hsum : (Y.card : ℝ) = ∑ x ∈ X, ((Y.filter (fun y => y.1 = x)).card : ℝ) := by
      have := Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := Y) (t := X)
        (fun y hy => (Finset.mem_filter.mp hy).2.2)
      exact_mod_cast this
    rw [hsum]
    calc (X.card : ℝ) * (A.card / K) = ∑ _x ∈ X, (A.card : ℝ) / K := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro x hx
        have h4 := hstep4 x hx
        have heq : Y.filter (fun y => y.1 = x) = S.filter (fun q' => q'.1 = x ∧ tb (cls q') = j) := by
          ext y
          simp only [hY, Finset.mem_filter]
          constructor
          · rintro ⟨⟨hyS, hyj, _⟩, hyx⟩; exact ⟨hyS, hyx, hyj⟩
          · rintro ⟨hyS, hyx, hyj⟩; exact ⟨⟨hyS, hyj, hyx ▸ hx⟩, hyx⟩
        rw [heq, div_le_iff₀ hK]
        linarith
  have hYup : (Y.card : ℝ) ≤ Λj.card * (K * k) := by
    have hsum : (Y.card : ℝ) = ∑ ℓ ∈ Λj, ((Y.filter (fun y => cls y = ℓ)).card : ℝ) := by
      have := Finset.card_eq_sum_card_fiberwise (f := cls) (s := Y) (t := Λj)
        (fun y hy => Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hy).1, (Finset.mem_filter.mp hy).2.1⟩, rfl⟩)
      exact_mod_cast this
    rw [hsum]
    calc ∑ ℓ ∈ Λj, ((Y.filter (fun y => cls y = ℓ)).card : ℝ) ≤ ∑ _ℓ ∈ Λj, K * k := by
          apply Finset.sum_le_sum
          intro ℓ hℓ
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hℓ
          have hyS : y ∈ S := (Finset.mem_filter.mp hy).1
          have hsub : Y.filter (fun y' => cls y' = cls y) ⊆ F (cls y) := by
            intro y' hy'
            have h' := Finset.mem_filter.mp hy'
            exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h'.1).1, h'.2⟩
          have hc := Finset.card_le_card hsub
          have hc' : ((Y.filter (fun y' => cls y' = cls y)).card : ℝ) ≤ ((F (cls y)).card : ℝ) := by
            exact_mod_cast hc
          exact hc'.trans (hFle y hyS)
      _ = Λj.card * (K * k) := by rw [Finset.sum_const, nsmul_eq_mul]
  -- Step 6: combine
  have hm0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  have hX0 : (0 : ℝ) ≤ X.card := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ npc := Nat.cast_nonneg _
  -- A k / (2K) ≤ npc Λp k / (2K) ≤ npc FarAll ≤ npc^2 μ X
  have hchain : (A.card : ℝ) * k / (2 * K) ≤ (npc : ℝ) ^ 2 * μ * X.card := by
    have h1 : (A.card : ℝ) * k / (2 * K) ≤ (npc : ℝ) * ((Λp.card : ℝ) * (k / (2 * K))) := by
      rw [div_le_iff₀ (by positivity)]
      have : (npc : ℝ) * ((Λp.card : ℝ) * (k / (2 * K))) * (2 * K) = npc * Λp.card * k := by
        field_simp
      rw [this]
      nlinarith
    have h2 : (npc : ℝ) * ((Λp.card : ℝ) * (k / (2 * K))) ≤ (npc : ℝ) * FarAll.card :=
      mul_le_mul_of_nonneg_left hstep2 hn0
    have h3 : (npc : ℝ) * FarAll.card ≤ (npc : ℝ) * (npc * μ * X.card) :=
      mul_le_mul_of_nonneg_left hstep3 hn0
    calc (A.card : ℝ) * k / (2 * K) ≤ (npc : ℝ) * (npc * μ * X.card) := h1.trans (h2.trans h3)
      _ = (npc : ℝ) ^ 2 * μ * X.card := by ring
  have hfinal : (A.card : ℝ) * k / (2 * K) * (A.card / K) ≤
      (npc : ℝ) ^ 2 * μ * (Λj.card * (K * k)) := by
    calc (A.card : ℝ) * k / (2 * K) * (A.card / K) ≤ (npc : ℝ) ^ 2 * μ * X.card * (A.card / K) :=
          mul_le_mul_of_nonneg_right hchain (by positivity)
      _ = (npc : ℝ) ^ 2 * μ * ((X.card : ℝ) * (A.card / K)) := by ring
      _ ≤ (npc : ℝ) ^ 2 * μ * Y.card := mul_le_mul_of_nonneg_left hYlow (by positivity)
      _ ≤ (npc : ℝ) ^ 2 * μ * (Λj.card * (K * k)) := mul_le_mul_of_nonneg_left hYup (by positivity)
  have hrhs : (npc : ℝ) ^ 2 * μ * (Λj.card * (K * k)) * (2 * K * K) =
      (2 * (npc : ℝ) ^ 2 * K ^ 3 * μ * Λj.card) * k := by ring
  have hlhs : (A.card : ℝ) * k / (2 * K) * (A.card / K) * (2 * K * K) = (A.card : ℝ) ^ 2 * k := by
    field_simp
  have h8 : 0 < 2 * K * K := by positivity
  have hmul := mul_le_mul_of_nonneg_right hfinal h8.le
  rw [hrhs, hlhs] at hmul
  exact le_of_mul_le_mul_right hmul hkpos

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

/-- A pin `x` at distance `d` from `p` lies on at most `2 r ^ (-η) 52 ^ s d ^ (-s)` of the
lines (classes) of a set `A` of labels of `p`: the labels of `p` in those classes have
normals `e` with `|⟪x - p, e⟫| < 26 r` (`cls_pair_geom`), and these are few by Katz--Tao
(`fcls_card_strip`). -/
theorem far_pin_multiplicity {r s ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : FailData r s ε₀ η P D) {cls : E2 × E2 → E2 × E2}
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
      (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r))
    {A : Finset (E2 × E2)} (hA : A ⊆ D) {p : E2} (hp : p ∈ P) (hAp : ∀ q ∈ A, q.1 = p)
    {x : E2} (hx : x ∈ P) (hxp : x ≠ p) :
    (((A.image cls).filter (fun ℓ => ∃ q' ∈ D, q'.1 = x ∧ cls q' = ℓ)).card : ℝ) ≤
      2 * r ^ (-η) * ((52 : ℝ) ^ s * (dist x p) ^ (-s)) := by
  classical
  set A' := A.filter (fun q => ∃ q' ∈ D, q'.1 = x ∧ cls q' = cls q) with hA'
  have himg : (A.image cls).filter (fun ℓ => ∃ q' ∈ D, q'.1 = x ∧ cls q' = ℓ) = A'.image cls := by
    ext ℓ
    simp only [Finset.mem_filter, Finset.mem_image, hA']
    constructor
    · rintro ⟨⟨q, hq, rfl⟩, hex⟩; exact ⟨q, ⟨hq, hex⟩, rfl⟩
    · rintro ⟨q, ⟨hq, hex⟩, rfl⟩; exact ⟨⟨q, hq, rfl⟩, hex⟩
  rw [himg]
  have h1 : (A'.image cls).card ≤ A'.card := Finset.card_image_le
  have h2 : A'.card = (A'.image Prod.snd).card := by
    rw [Finset.card_image_of_injOn]
    intro a ha b hb hab
    have ha' := hAp a (Finset.mem_filter.mp ha).1
    have hb' := hAp b (Finset.mem_filter.mp hb).1
    exact Prod.ext (ha'.trans hb'.symm) hab
  have h3 : A'.image Prod.snd ⊆
      (bushOf D p).filter (fun e => |inner ℝ (x - p) e| < 26 * r) := by
    intro e he
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hqA, q', hq'D, hq'x, hq'c⟩ := Finset.mem_filter.mp hq
    have hqD := hA hqA
    have hqp := hAp q hqA
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [mem_bushOf]
      rw [show (p, q.2) = q from Prod.ext hqp.symm rfl]
      exact hqD
    · obtain ⟨g1, g2⟩ := hgeo q hqD
      obtain ⟨g3, g4⟩ := hgeo q' hq'D
      rw [hq'c] at g3 g4
      have := (cls_pair_geom (h.P_norm _ (h.D_mem q hqD).1) (h.P_norm _ (h.D_mem q' hq'D).1)
        g1 g2 g3 g4).1
      rw [hq'x, hqp] at this
      exact this
  have h4 := fcls_card_strip h hp hx hxp
  have h5 : ((A'.image cls).card : ℝ) ≤
      (((bushOf D p).filter (fun e => |inner ℝ (x - p) e| < 26 * r)).card : ℝ) := by
    have := h1.trans (h2.le.trans (Finset.card_le_card h3))
    exact_mod_cast this
  exact h5.trans h4

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

/-- A pin carries at most `4 r ^ (-η)` labels of one class: their normals are within `2 r` of
`± ℓ.2` (class geometry) and the bush is Katz--Tao at radius `2 r` (`fcls_card_B`). -/
theorem pin_class_labels {r s ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : FailData r s ε₀ η P D) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {cls : E2 × E2 → E2 × E2}
    (hcls1 : ∀ q ∈ D, ‖(cls q).2‖ = 1)
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
      (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r))
    {S : Finset (E2 × E2)} (hSD : S ⊆ D) (x : E2) (ℓ : E2 × E2) :
    ((S.filter (fun q => q.1 = x ∧ cls q = ℓ)).card : ℝ) ≤ 4 * r ^ (-η) := by
  classical
  by_cases hne : (S.filter (fun q => q.1 = x ∧ cls q = ℓ)).Nonempty
  · obtain ⟨q₁, hq₁⟩ := hne
    obtain ⟨hq₁S, hq₁x, hq₁c⟩ := Finset.mem_filter.mp hq₁
    have hq₁D := hSD hq₁S
    have hxP : x ∈ P := hq₁x ▸ (h.D_mem q₁ hq₁D).1
    have hℓ1 : ‖ℓ.2‖ = 1 := hq₁c ▸ hcls1 q₁ hq₁D
    have hr := h.r_pos
    have hsub : (S.filter (fun q => q.1 = x ∧ cls q = ℓ)).image Prod.snd ⊆
        (bushOf D x).filter (fun e' => dist e' ℓ.2 ≤ 2 * r ∨ dist e' (-ℓ.2) ≤ 2 * r) := by
      intro e he
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hqS, hqx, hqc⟩ := Finset.mem_filter.mp hq
      have hqD := hSD hqS
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [mem_bushOf, ← hqx]; exact hqD
      · have hg := (hgeo q hqD).2
        rw [hqc] at hg
        rcases hg with h1 | h1
        · left; linarith
        · right; linarith
    have hinj : ((S.filter (fun q => q.1 = x ∧ cls q = ℓ)).image Prod.snd).card =
        (S.filter (fun q => q.1 = x ∧ cls q = ℓ)).card := by
      apply Finset.card_image_of_injOn
      intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp ha).2.1
      have hb' := (Finset.mem_filter.mp hb).2.1
      exact Prod.ext (ha'.trans hb'.symm) hab
    have h1 := Finset.card_le_card hsub
    rw [hinj] at h1
    exact (by exact_mod_cast h1 : ((S.filter (fun q => q.1 = x ∧ cls q = ℓ)).card : ℝ) ≤ _).trans
      (fcls_card_B h hs0 hs1 hxP hℓ1)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg h.r_pos.le _)

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
