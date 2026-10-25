-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.SharedAssembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o222/x0722 High/SharedAssembly.lean (c61cafd).
-- Adapted from local obligation o157, branch x0675, commit 5a2c82ba2c9f.
-- Source: High/SharedAssembly.lean. Shared half definitions imported from accepted o213.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.SharedArcs
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.AtScale
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Regularity.BalancedQuotients

/-!
# The quadratic lower bound for lines in a coarse tube, from a failed bush estimate

`tube_quadratic_of_fail`: let `h : FailData r s ε₀ η P D`, with classes `cls` (lines, with
their geometry) and coarse tubes `tb`, and let `S ⊆ D` be a subfamily on which the labels per
(pin, tube) and per line are balanced with ratio `K` and every line has at most half of its
labels within `c` of any of its pins. Then for every label `q₀ ∈ S`, with `m` the labels of its
pin in its tube,
`m ^ 2 ≤ 2 ⌈4 r ^ (-η)⌉₊ ^ 2 K ^ 3 (2 r ^ (-η) 52 ^ s c ^ (-s)) #(lines of S in that tube)`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_tower_balanced_refinement

theorem tube_quadratic_of_fail {r s ε₀ η c K : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : FailData r s ε₀ η P D) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hc : 0 < c) (hK : 0 < K)
    {cls tb : E2 × E2 → E2 × E2} (hcls1 : ∀ q ∈ D, ‖(cls q).2‖ = 1)
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
      (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r))
    {S : Finset (E2 × E2)} (hSD : S ⊆ D)
    (hbal : Balanced S (fun q => (q.1, tb (cls q))) K) (hclsbal : Balanced S cls K)
    (hfar : ∀ q ∈ S, 2 * ((((S.filter (fun q' => cls q' = cls q)).filter
        (fun q' => dist q'.1 q.1 < c)).card : ℝ)) ≤ (S.filter (fun q' => cls q' = cls q)).card)
    {q₀ : E2 × E2} (hq₀ : q₀ ∈ S) :
    ((S.filter (fun q => q.1 = q₀.1 ∧ tb (cls q) = tb (cls q₀))).card : ℝ) ^ 2 ≤
      2 * ((⌈4 * r ^ (-η)⌉₊ : ℕ) : ℝ) ^ 2 * K ^ 3 * (2 * r ^ (-η) * ((52 : ℝ) ^ s * c ^ (-s))) *
        ((S.filter (fun q => tb (cls q) = tb (cls q₀))).image cls).card := by
  classical
  have hr := h.r_pos
  have hμ : 0 ≤ 2 * r ^ (-η) * ((52 : ℝ) ^ s * c ^ (-s)) := by positivity
  apply tube_lines_quadratic hK hμ ⌈4 * r ^ (-η)⌉₊ hq₀
  · -- labels per (pin, tube)
    intro q hq
    have hb := hbal q₀ hq₀ q hq
    have hfib : ∀ x, leafFiber S (fun q => (q.1, tb (cls q))) x =
        S.filter (fun a => a.1 = x.1 ∧ tb (cls a) = tb (cls x)) := by
      intro x; ext a; rw [mem_leafFiber', Finset.mem_filter, Prod.mk.injEq]
    rwa [hfib, hfib] at hb
  · -- labels per line
    intro q hq q' hq'
    have hb := hclsbal q hq q' hq'
    have hfib : ∀ x, leafFiber S cls x = S.filter (fun a => cls a = cls x) := by
      intro x; ext a; rw [mem_leafFiber', Finset.mem_filter]
    rwa [hfib, hfib] at hb
  · -- labels per (pin, line)
    intro x ℓ
    have h1 := pin_class_labels h hs0 hs1 hcls1 hgeo hSD x ℓ
    have h2 : ((S.filter (fun q => q.1 = x ∧ cls q = ℓ)).card : ℝ) ≤
        ((⌈4 * r ^ (-η)⌉₊ : ℕ) : ℝ) := h1.trans (Nat.le_ceil _)
    exact_mod_cast h2
  · exact hfar
  · -- far pins lie on few lines of `q₀.1`
    intro x hx
    have hq₀D := hSD hq₀
    have hpP : q₀.1 ∈ P := (h.D_mem q₀ hq₀D).1
    set A := S.filter (fun q => q.1 = q₀.1 ∧ tb (cls q) = tb (cls q₀)) with hA
    have hAD : A ⊆ D := fun q hq => hSD (Finset.mem_filter.mp hq).1
    have hAp : ∀ q ∈ A, q.1 = q₀.1 := fun q hq => (Finset.mem_filter.mp hq).2.1
    have hmono : (A.image cls).filter (fun ℓ => ∃ q' ∈ S, q'.1 = x ∧ cls q' = ℓ) ⊆
        (A.image cls).filter (fun ℓ => ∃ q' ∈ D, q'.1 = x ∧ cls q' = ℓ) := by
      intro ℓ hℓ
      obtain ⟨hℓA, q', hq'S, hq'x, hq'c⟩ := Finset.mem_filter.mp hℓ
      exact Finset.mem_filter.mpr ⟨hℓA, q', hSD hq'S, hq'x, hq'c⟩
    have hcard := (by exact_mod_cast Finset.card_le_card hmono :
      (((A.image cls).filter (fun ℓ => ∃ q' ∈ S, q'.1 = x ∧ cls q' = ℓ)).card : ℝ) ≤
        (((A.image cls).filter (fun ℓ => ∃ q' ∈ D, q'.1 = x ∧ cls q' = ℓ)).card : ℝ))
    by_cases hxP : x ∈ P
    · have hxp : x ≠ q₀.1 := by
        intro hxe
        rw [hxe, dist_self] at hx
        linarith
      have hm := far_pin_multiplicity h hgeo hAD hpP hAp hxP hxp
      have hd : (dist x q₀.1) ^ (-s) ≤ c ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos hc hx (by linarith)
      have hX : 0 ≤ 2 * r ^ (-η) := by positivity
      have h52 : 0 ≤ (52 : ℝ) ^ s := by positivity
      calc _ ≤ _ := hcard
        _ ≤ 2 * r ^ (-η) * ((52 : ℝ) ^ s * (dist x q₀.1) ^ (-s)) := hm
        _ ≤ 2 * r ^ (-η) * ((52 : ℝ) ^ s * c ^ (-s)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd h52) hX
    · -- no label has its pin at `x`
      have hempty : (A.image cls).filter (fun ℓ => ∃ q' ∈ D, q'.1 = x ∧ cls q' = ℓ) = ∅ := by
        apply Finset.filter_false_of_mem
        rintro ℓ - ⟨q', hq'D, hq'x, -⟩
        exact hxP (hq'x ▸ (h.D_mem q' hq'D).1)
      rw [hempty, Finset.card_empty, Nat.cast_zero] at hcard
      exact hcard.trans hμ

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_tower_balanced_refinement

attribute [local instance] Classical.propDecidable

/-- One pin per occupied `ρ`-cell: if every cell holds between `ν` and `Kν` pins of a set
`Q ⊆ P` with `#(P ∩ B(x,t)) ≤ A t` for `t ≥ ρ`, the representatives are normalized
1-Frostman at scale `ρ`: `#(reps in B(x,t)) #Q ≤ 3 A K t #reps` for `t ≥ ρ`. -/
theorem cell_reps_frostman {ρ A ν K : ℝ} (hρ : 0 < ρ) (hν : 0 < ν) (hK : 0 ≤ K) {P Q : Finset E2}
    (hQP : Q ⊆ P)
    (hPball : ∀ (x : E2) (t : ℝ), ρ ≤ t → ((P.filter (fun z => dist z x ≤ t)).card : ℝ) ≤ A * t)
    (hcell_low : ∀ p ∈ Q, ν ≤ ((Q.filter (fun z => cellOf ρ z = cellOf ρ p)).card : ℝ))
    (hcell_up : ∀ p ∈ Q, ((Q.filter (fun z => cellOf ρ z = cellOf ρ p)).card : ℝ) ≤ K * ν)
    (rep : ℤ × ℤ → E2) (hrep : ∀ c ∈ Q.image (cellOf ρ), rep c ∈ Q ∧ cellOf ρ (rep c) = c)
    (x : E2) (t : ℝ) (ht : ρ ≤ t) :
    ((((Q.image (cellOf ρ)).image rep).filter (fun z => z ∈ Metric.closedBall x t)).card : ℝ) *
        Q.card ≤ 3 * A * K * t * ((Q.image (cellOf ρ)).image rep).card := by
  classical
  set C := Q.image (cellOf ρ) with hC
  set Y := C.image rep with hY
  -- the representatives are distinct for distinct cells
  have hrepinj : Set.InjOn rep C := by
    intro c hc c' hc' h
    rw [← (hrep c hc).2, ← (hrep c' hc').2, h]
  have hYcard : Y.card = C.card := Finset.card_image_of_injOn hrepinj
  -- #Q ≤ K ν #cells
  have hQup : (Q.card : ℝ) ≤ K * ν * C.card := by
    have hsum : (Q.card : ℝ) = ∑ c ∈ C, ((Q.filter (fun z => cellOf ρ z = c)).card : ℝ) := by
      have := Finset.card_eq_sum_card_fiberwise (f := cellOf ρ) (s := Q) (t := C)
        (fun z hz => Finset.mem_image.mpr ⟨z, hz, rfl⟩)
      rw [this]; push_cast; rfl
    rw [hsum]
    calc ∑ c ∈ C, ((Q.filter (fun z => cellOf ρ z = c)).card : ℝ) ≤ ∑ _c ∈ C, K * ν := by
          apply Finset.sum_le_sum
          intro c hc
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
          exact hcell_up p hp
      _ = K * ν * C.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  -- the cells of the representatives in the ball are disjoint and full
  set W := Y.filter (fun z => z ∈ Metric.closedBall x t) with hW
  have hWcells : (W.card : ℝ) * ν ≤ A * (3 * t) := by
    -- pins of those cells lie within 3t of x
    set U := Q.filter (fun z => ∃ y ∈ W, cellOf ρ z = cellOf ρ y) with hU
    have hUcount : (W.card : ℝ) * ν ≤ U.card := by
      have hsum : (U.card : ℝ) ≥ ∑ y ∈ W, ((Q.filter (fun z => cellOf ρ z = cellOf ρ y)).card : ℝ) := by
        have hdisj : (W : Set E2).PairwiseDisjoint (fun y => Q.filter (fun z => cellOf ρ z = cellOf ρ y)) := by
          intro y hy y' hy' hne
          simp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro z hz hz'
          have h1 := (Finset.mem_filter.mp hz).2
          have h2 := (Finset.mem_filter.mp hz').2
          apply hne
          obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hy).1
          obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hy').1
          rw [(hrep c hc).2] at h1
          rw [(hrep c' hc').2] at h2
          rw [← h1, h2]
        have hsub : W.biUnion (fun y => Q.filter (fun z => cellOf ρ z = cellOf ρ y)) ⊆ U := by
          intro z hz
          obtain ⟨y, hy, hzy⟩ := Finset.mem_biUnion.mp hz
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hzy).1, y, hy,
            (Finset.mem_filter.mp hzy).2⟩
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_biUnion hdisj] at h1
        exact_mod_cast h1
      refine le_trans ?_ hsum
      calc (W.card : ℝ) * ν = ∑ _y ∈ W, ν := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro y hy
          obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hy).1
          exact hcell_low (rep c) (hrep c hc).1
    have hUsub : U ⊆ P.filter (fun z => dist z x ≤ 3 * t) := by
      intro z hz
      obtain ⟨hzQ, y, hyW, hzy⟩ := Finset.mem_filter.mp hz
      refine Finset.mem_filter.mpr ⟨hQP hzQ, ?_⟩
      have hyx : dist y x ≤ t := Metric.mem_closedBall.mp (Finset.mem_filter.mp hyW).2
      have hzy' : dist z y ≤ 2 * ρ := dist_le_of_cellOf_eq hρ hzy
      calc dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
        _ ≤ 2 * ρ + t := add_le_add hzy' hyx
        _ ≤ 3 * t := by linarith
    have h1 := Finset.card_le_card hUsub
    have h2 := hPball x (3 * t) (by linarith)
    have h3 : (U.card : ℝ) ≤ A * (3 * t) := (by exact_mod_cast h1 : (U.card : ℝ) ≤ _).trans h2
    linarith
  -- combine: W ν ≤ 3At and Q ≤ K ν C
  rw [hYcard]
  have hW0 : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
  calc (W.card : ℝ) * Q.card ≤ W.card * (K * ν * C.card) := mul_le_mul_of_nonneg_left hQup hW0
    _ = (W.card * ν) * (K * C.card) := by ring
    _ ≤ (A * (3 * t)) * (K * C.card) :=
        mul_le_mul_of_nonneg_right hWcells (mul_nonneg hK (Nat.cast_nonneg _))
    _ = 3 * A * K * t * C.card := by ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_tower_balanced_refinement

attribute [local instance] Classical.propDecidable

/-- The coarse tubes met by the pins of the cell of `x`. -/
noncomputable def cellTubes (ρ : ℝ) (S : Finset (E2 × E2)) (cls tb : E2 × E2 → E2 × E2)
    (x : E2) : Finset (E2 × E2) :=
  (S.filter (fun q => cellOf ρ q.1 = cellOf ρ x)).image (fun q => tb (cls q))

/-- The coarse tubes met by the pin `p`. -/
noncomputable def pinTubes (S : Finset (E2 × E2)) (cls tb : E2 × E2 → E2 × E2) (p : E2) :
    Finset (E2 × E2) :=
  (S.filter (fun q => q.1 = p)).image (fun q => tb (cls q))

/-- The bush of a pin is at most (its tubes) × (the largest labels per (pin, tube)). -/
theorem bush_le_pinTubes {S : Finset (E2 × E2)} {cls tb : E2 × E2 → E2 × E2} {M : ℝ}
    (p : E2)
    (hM : ∀ q ∈ S, q.1 = p →
      ((S.filter (fun a => a.1 = p ∧ tb (cls a) = tb (cls q))).card : ℝ) ≤ M) :
    ((bushOf S p).card : ℝ) ≤ (pinTubes S cls tb p).card * M := by
  classical
  rw [card_bushOf]
  have hsum : (((S.filter (fun q => q.1 = p)).card : ℝ)) =
      ∑ j ∈ pinTubes S cls tb p,
        (((S.filter (fun q => q.1 = p)).filter (fun q => tb (cls q) = j)).card : ℝ) := by
    have := Finset.card_eq_sum_card_fiberwise (f := fun q => tb (cls q))
      (s := S.filter (fun q => q.1 = p)) (t := pinTubes S cls tb p)
      (fun q hq => Finset.mem_image.mpr ⟨q, hq, rfl⟩)
    rw [this]; push_cast; rfl
  rw [hsum]
  calc ∑ j ∈ pinTubes S cls tb p,
        (((S.filter (fun q => q.1 = p)).filter (fun q => tb (cls q) = j)).card : ℝ)
      ≤ ∑ _j ∈ pinTubes S cls tb p, M := by
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
        have hqS := (Finset.mem_filter.mp hq).1
        have hqp := (Finset.mem_filter.mp hq).2
        have heq : (S.filter (fun q' => q'.1 = p)).filter (fun q' => tb (cls q') = tb (cls q)) =
            S.filter (fun a => a.1 = p ∧ tb (cls a) = tb (cls q)) := by
          ext a; simp only [Finset.mem_filter]; tauto
        rw [heq]
        exact hM q hqS hqp
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_tower_balanced_refinement
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Regularity

attribute [local instance] Classical.propDecidable

/-- The per-tube constant of `tube_quadratic_of_fail`. -/
noncomputable def tubeConst (r s η c K : ℝ) : ℝ :=
  2 * ((⌈4 * r ^ (-η)⌉₊ : ℕ) : ℝ) ^ 2 * K ^ 3 * (2 * r ^ (-η) * ((52 : ℝ) ^ s * c ^ (-s)))

/-- The coarse Cauchy--Schwarz constant (width `28 ρ`, separation `ρ`, Frostman constant `CY`). -/
noncomputable def cellConst (ρ CY : ℝ) (KY : ℕ) : ℝ :=
  128000 * (64 * (28 * ρ) / ρ + 2) * (36 * (28 * ρ) / ρ + 2) * CY *
    (1 + Real.log (1 / (28 * ρ))) * ((KY : ℝ) + 1) ^ 2

theorem tubeConst_nonneg {r s η c K : ℝ} (hr : 0 < r) (hc : 0 < c) (hK : 0 ≤ K) :
    0 ≤ tubeConst r s η c K := by
  unfold tubeConst; positivity

/-- Pins of a cell are balanced (ratio `K ^ 3`) when labels per cell and bushes are. -/
theorem cell_pins_balanced {ρ K : ℝ} {S : Finset (E2 × E2)} (hK : 0 ≤ K)
    (hbfst : Balanced S Prod.fst K) (hbcell : Balanced S (fun q => cellOf ρ q.1) K)
    {q q' : E2 × E2} (hq : q ∈ S) (hq' : q' ∈ S) :
    ((cellPins ρ (S.image Prod.fst) q.1).card : ℝ) ≤
      K ^ 3 * (cellPins ρ (S.image Prod.fst) q'.1).card := by
  classical
  set Q := S.image Prod.fst with hQ
  have hSQ : ∀ a ∈ S, a.1 ∈ Q := fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hp : q.1 ∈ Q := hSQ q hq
  have hbush : ∀ x ∈ Q, ∀ y ∈ Q, ((bushOf S x).card : ℝ) ≤ K * (bushOf S y).card :=
    fun x hx y hy => bush_le_of_balanced hbfst hx hy
  have hb0 := hbcell q hq q' hq'
  have hfib : ∀ y, leafFiber S (fun a => cellOf ρ a.1) y =
      S.filter (fun a => cellOf ρ a.1 = cellOf ρ y.1) := by
    intro y; ext a; rw [mem_leafFiber', Finset.mem_filter]
  rw [hfib, hfib, cell_labels_eq_sum ρ hSQ, cell_labels_eq_sum ρ hSQ] at hb0
  set b := ((bushOf S q.1).card : ℝ) with hb
  have hlow : ∀ x ∈ Q, b ≤ K * (bushOf S x).card := fun x hx => hbush q.1 hp x hx
  have hup : ∀ x ∈ Q, ((bushOf S x).card : ℝ) ≤ K * b := fun x hx => hbush x hx q.1 hp
  have hcp : ∀ x ∈ cellPins ρ Q q.1, x ∈ Q := fun x hx => (Finset.mem_filter.mp hx).1
  have hcp' : ∀ x ∈ cellPins ρ Q q'.1, x ∈ Q := fun x hx => (Finset.mem_filter.mp hx).1
  have hA : ((cellPins ρ Q q.1).card : ℝ) * b ≤
      K * ∑ x ∈ cellPins ρ Q q.1, ((bushOf S x).card : ℝ) := by
    rw [Finset.mul_sum]
    calc ((cellPins ρ Q q.1).card : ℝ) * b = ∑ _x ∈ cellPins ρ Q q.1, b := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun x hx => hlow x (hcp x hx))
  have hB : ∑ x ∈ cellPins ρ Q q'.1, ((bushOf S x).card : ℝ) ≤
      ((cellPins ρ Q q'.1).card : ℝ) * (K * b) := by
    calc ∑ x ∈ cellPins ρ Q q'.1, ((bushOf S x).card : ℝ)
        ≤ ∑ _x ∈ cellPins ρ Q q'.1, K * b := Finset.sum_le_sum (fun x hx => hup x (hcp' x hx))
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hbpos : 0 < b := by
    have hmem : q.2 ∈ bushOf S q.1 := mem_bushOf.mpr (by simpa using hq)
    have := Finset.card_pos.mpr ⟨q.2, hmem⟩
    rw [hb]; exact_mod_cast this
  have key : ((cellPins ρ Q q.1).card : ℝ) * b ≤
      (K ^ 3 * (cellPins ρ Q q'.1).card) * b := by
    calc ((cellPins ρ Q q.1).card : ℝ) * b
        ≤ K * ∑ x ∈ cellPins ρ Q q.1, ((bushOf S x).card : ℝ) := hA
      _ ≤ K * (K * ∑ x ∈ cellPins ρ Q q'.1, ((bushOf S x).card : ℝ)) :=
          mul_le_mul_of_nonneg_left hb0 hK
      _ ≤ K * (K * (((cellPins ρ Q q'.1).card : ℝ) * (K * b))) := by
          apply mul_le_mul_of_nonneg_left _ hK
          exact mul_le_mul_of_nonneg_left hB hK
      _ = _ := by ring
  exact le_of_mul_le_mul_right key hbpos

/-- Tubes per cell are balanced (ratio `K ^ 2`) when labels per cell and per (cell, tube) are. -/
theorem cell_tubes_balanced {ρ K : ℝ} {S : Finset (E2 × E2)} {cls tb : E2 × E2 → E2 × E2}
    (hK : 0 ≤ K) (hbcell : Balanced S (fun q => cellOf ρ q.1) K)
    (hbct : Balanced S (fun q => (cellOf ρ q.1, tb (cls q))) K)
    {q q' : E2 × E2} (hq : q ∈ S) (hq' : q' ∈ S) :
    ((cellTubes ρ S cls tb q.1).card : ℝ) ≤ K ^ 2 * (cellTubes ρ S cls tb q'.1).card := by
  classical
  set φ : E2 × E2 → (ℤ × ℤ) × (E2 × E2) := fun a => (cellOf ρ a.1, tb (cls a)) with hφ
  have hb := balanced_image S φ Prod.fst hK hbct hbcell
  have hcard : ∀ a ∈ S, (leafFiber (S.image φ) Prod.fst (φ a)).card =
      (cellTubes ρ S cls tb a.1).card := by
    intro a _
    have himg : (leafFiber (S.image φ) Prod.fst (φ a)).image Prod.snd = cellTubes ρ S cls tb a.1 := by
      ext j
      simp only [Finset.mem_image, mem_leafFiber', cellTubes, Finset.mem_filter, hφ]
      constructor
      · rintro ⟨x, ⟨⟨b, hb, rfl⟩, hbc⟩, rfl⟩
        exact ⟨b, ⟨hb, hbc⟩, rfl⟩
      · rintro ⟨b, ⟨hb, hbc⟩, rfl⟩
        exact ⟨(cellOf ρ b.1, tb (cls b)), ⟨⟨b, hb, rfl⟩, hbc⟩, rfl⟩
    rw [← himg, Finset.card_image_of_injOn]
    intro x hx y hy hxy
    have hx' := (mem_leafFiber'.mp hx).2
    have hy' := (mem_leafFiber'.mp hy).2
    exact Prod.ext (hx'.trans hy'.symm) hxy
  have h1 := hb (φ q) (Finset.mem_image.mpr ⟨q, hq, rfl⟩) (φ q') (Finset.mem_image.mpr ⟨q', hq', rfl⟩)
  rw [hcard q hq, hcard q' hq'] at h1
  exact h1

/-- Pure arithmetic of the shared-tubes bound. -/
theorem shared_tubes_arith {X Pt m K C₁ Cq J T R : ℝ} (hK : 0 < K) (hR : 0 < R)
    (hC₁ : 0 ≤ C₁) (hT : 0 ≤ T)
    (hX2 : X ^ 2 ≤ K ^ 4 * (C₁ * T)) (hT2 : T * m ^ 2 ≤ K ^ 2 * (Cq * J))
    (hrb : R ≤ Pt * (K * m)) :
    X ^ 2 * R ^ 2 ≤ K ^ 8 * C₁ * Cq * J * Pt ^ 2 := by
  have hX0 : 0 ≤ X ^ 2 := sq_nonneg X
  have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
  have hK4 : 0 ≤ K ^ 4 := by positivity
  have hrb2 : R ^ 2 ≤ Pt ^ 2 * K ^ 2 * m ^ 2 := by
    have := pow_le_pow_left₀ hR.le hrb 2
    calc R ^ 2 ≤ (Pt * (K * m)) ^ 2 := this
      _ = Pt ^ 2 * K ^ 2 * m ^ 2 := by ring
  have hXm : X ^ 2 * m ^ 2 ≤ K ^ 6 * C₁ * Cq * J := by
    calc X ^ 2 * m ^ 2 ≤ K ^ 4 * (C₁ * T) * m ^ 2 :=
          mul_le_mul_of_nonneg_right hX2 (sq_nonneg m)
      _ = K ^ 4 * C₁ * (T * m ^ 2) := by ring
      _ ≤ K ^ 4 * C₁ * (K ^ 2 * (Cq * J)) :=
          mul_le_mul_of_nonneg_left hT2 (mul_nonneg hK4 hC₁)
      _ = K ^ 6 * C₁ * Cq * J := by ring
  calc X ^ 2 * R ^ 2 ≤ X ^ 2 * (Pt ^ 2 * K ^ 2 * m ^ 2) := mul_le_mul_of_nonneg_left hrb2 hX0
    _ = (X ^ 2 * m ^ 2) * (K ^ 2 * Pt ^ 2) := by ring
    _ ≤ (K ^ 6 * C₁ * Cq * J) * (K ^ 2 * Pt ^ 2) :=
        mul_le_mul_of_nonneg_right hXm (mul_nonneg hK2 (sq_nonneg Pt))
    _ = K ^ 8 * C₁ * Cq * J * Pt ^ 2 := by ring

/-- (a)-(c): the occupied tubes. With `m` the labels of `q`'s pin in `q`'s tube,
`#T (m / K) ^ 2 ≤ tubeConst #J₀`. -/
theorem shared_tubes_count {r s ε₀ η c K : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : FailData r s ε₀ η P D) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hc : 0 < c) (hK : 0 < K)
    {cls tb : E2 × E2 → E2 × E2} {J₀ : Finset (E2 × E2)}
    (hclsJ : ∀ q ∈ D, cls q ∈ J₀) (hJ₀D : J₀ ⊆ D)
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
      (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r))
    {S : Finset (E2 × E2)} (hSD : S ⊆ D)
    (hbcls : Balanced S cls K) (hbpt : Balanced S (fun q => (q.1, tb (cls q))) K)
    (hfar : ∀ q ∈ S, 2 * ((((S.filter (fun q' => cls q' = cls q)).filter
        (fun q' => dist q'.1 q.1 < c)).card : ℝ)) ≤ (S.filter (fun q' => cls q' = cls q)).card)
    {q : E2 × E2} (hq : q ∈ S) :
    ((S.image (fun a => tb (cls a))).card : ℝ) *
        (((S.filter (fun a => a.1 = q.1 ∧ tb (cls a) = tb (cls q))).card : ℝ) / K) ^ 2 ≤
      tubeConst r s η c K * J₀.card := by
  classical
  have hr := h.r_pos
  have hcls1 : ∀ a ∈ D, ‖(cls a).2‖ = 1 := fun a ha => (h.D_mem _ (hJ₀D (hclsJ a ha))).2
  have hlabfib : ∀ x, leafFiber S (fun a => (a.1, tb (cls a))) x =
      S.filter (fun a => a.1 = x.1 ∧ tb (cls a) = tb (cls x)) := by
    intro x; ext a; rw [mem_leafFiber', Finset.mem_filter, Prod.mk.injEq]
  have hCq0 : 0 ≤ tubeConst r s η c K := tubeConst_nonneg hr hc hK.le
  have hquad : ∀ q₀ ∈ S,
      (((S.filter (fun a => a.1 = q.1 ∧ tb (cls a) = tb (cls q))).card : ℝ) / K) ^ 2 ≤
      tubeConst r s η c K * ((S.filter (fun a => tb (cls a) = tb (cls q₀))).image cls).card := by
    intro q₀ hq₀
    have h1 := tube_quadratic_of_fail h hs0 hs1 hc hK hcls1 hgeo hSD hbpt hbcls hfar hq₀
    have hb := hbpt q hq q₀ hq₀
    rw [hlabfib, hlabfib] at hb
    have h2 : ((S.filter (fun a => a.1 = q.1 ∧ tb (cls a) = tb (cls q))).card : ℝ) / K ≤
        ((S.filter (fun a => a.1 = q₀.1 ∧ tb (cls a) = tb (cls q₀))).card : ℝ) := by
      rw [div_le_iff₀ hK, mul_comm]; exact hb
    have hm0 : 0 ≤ ((S.filter (fun a => a.1 = q.1 ∧ tb (cls a) = tb (cls q))).card : ℝ) / K :=
      div_nonneg (Nat.cast_nonneg _) hK.le
    exact (pow_le_pow_left₀ hm0 h2 2).trans h1
  have hTcount := tube_count hCq0 hquad
  have himgJ : ((S.image cls).card : ℝ) ≤ J₀.card := by
    have : S.image cls ⊆ J₀ := by
      intro ℓ hℓ
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hℓ
      exact hclsJ a (hSD ha)
    exact_mod_cast Finset.card_le_card this
  exact hTcount.trans (mul_le_mul_of_nonneg_left himgJ hCq0)

/-- (f): the bush of `q`'s pin is at most its tubes times `K m`. -/
theorem shared_tubes_pin {K : ℝ} {cls tb : E2 × E2 → E2 × E2} {S : Finset (E2 × E2)}
    (hbpt : Balanced S (fun q => (q.1, tb (cls q))) K) {q : E2 × E2} (hq : q ∈ S) :
    ((bushOf S q.1).card : ℝ) ≤ (pinTubes S cls tb q.1).card *
      (K * ((S.filter (fun a => a.1 = q.1 ∧ tb (cls a) = tb (cls q))).card : ℝ)) := by
  classical
  have hlabfib : ∀ x, leafFiber S (fun a => (a.1, tb (cls a))) x =
      S.filter (fun a => a.1 = x.1 ∧ tb (cls a) = tb (cls x)) := by
    intro x; ext a; rw [mem_leafFiber', Finset.mem_filter, Prod.mk.injEq]
  apply bush_le_pinTubes
  intro q₂ hq₂ hq₂p
  have hb := hbpt q₂ hq₂ q hq
  rw [hlabfib, hlabfib, hq₂p] at hb
  exact hb

theorem cellConst_nonneg {ρ CY : ℝ} (hρ : 0 < ρ) (hρ2 : 28 * ρ ≤ 1 / 2) (hCY : 0 ≤ CY)
    (KY : ℕ) : 0 ≤ cellConst ρ CY KY := by
  unfold cellConst
  have hlog : 0 ≤ Real.log (1 / (28 * ρ)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by linarith)]
    linarith
  have h1 : (0 : ℝ) ≤ 64 * (28 * ρ) / ρ + 2 := by
    have : 0 ≤ 64 * (28 * ρ) / ρ := div_nonneg (by linarith) hρ.le
    linarith
  have h2 : (0 : ℝ) ≤ 36 * (28 * ρ) / ρ + 2 := by
    have : 0 ≤ 36 * (28 * ρ) / ρ := div_nonneg (by linarith) hρ.le
    linarith
  have h3 : (0 : ℝ) ≤ 1 + Real.log (1 / (28 * ρ)) := by linarith
  have h4 : (0 : ℝ) ≤ ((KY : ℝ) + 1) ^ 2 := sq_nonneg _
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) h2) hCY) h3) h4

/-- (d)-(e): coarse Cauchy--Schwarz with one pin per cell. -/
theorem shared_tubes_cs {r s ε₀ η η' K ρ : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : FailData r s ε₀ η P D) (hK : 1 ≤ K) (hrρ : r ≤ ρ) (hρ2 : 28 * ρ ≤ 1 / 2)
    {cls tb : E2 × E2 → E2 × E2} {J₀ J₁ : Finset (E2 × E2)}
    (hclsJ : ∀ q ∈ D, cls q ∈ J₀) (hJ₀D : J₀ ⊆ D)
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
      (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r))
    (hJ₁ : J₁ ⊆ J₀) (hJ₁sep : ∀ x ∈ J₁, ∀ y ∈ J₁, x ≠ y → StripSep ρ x y)
    (htbJ : ∀ ℓ ∈ J₀, tb ℓ ∈ J₁)
    (htbgeo : ∀ ℓ ∈ J₀, |inner ℝ (ℓ.1 - (tb ℓ).1) (tb ℓ).2| < 9 * ρ ∧
      (dist ℓ.2 (tb ℓ).2 < ρ ∨ dist ℓ.2 (-(tb ℓ).2) < ρ))
    {S : Finset (E2 × E2)} (hSD : S ⊆ D) (hS : FailData r s ε₀ η' (S.image Prod.fst) S)
    (hbfst : Balanced S Prod.fst K) (hbcell : Balanced S (fun q => cellOf ρ q.1) K)
    (hbct : Balanced S (fun q => (cellOf ρ q.1, tb (cls q))) K)
    (KY : ℕ) (hKY : ((S.image Prod.fst).card : ℝ) ≤ 2 ^ KY)
    {q q' : E2 × E2} (hq : q ∈ S) (hq' : q' ∈ S) :
    (((cellTubes ρ S cls tb q'.1).card : ℝ) / K ^ 2) ^ 2 ≤
      cellConst ρ (3 * (r ^ (-η) / r) * K ^ 6 / ((S.image Prod.fst).card : ℝ)) KY *
        (S.image (fun a => tb (cls a))).card := by
  classical
  have hr := h.r_pos
  have hρ : 0 < ρ := hr.trans_le hrρ
  have hK0 : 0 ≤ K := by linarith
  have hKpos : 0 < K := by linarith
  have hQP : S.image Prod.fst ⊆ P := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact (h.D_mem a (hSD ha)).1
  have hSQ : ∀ a ∈ S, a.1 ∈ S.image Prod.fst := fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hcls1 : ∀ a ∈ D, ‖(cls a).2‖ = 1 := fun a ha => (h.D_mem _ (hJ₀D (hclsJ a ha))).2
  -- one pin per cell
  have hrep_ex : ∀ cc : ℤ × ℤ, ∃ y : E2,
      cc ∈ (S.image Prod.fst).image (cellOf ρ) → y ∈ S.image Prod.fst ∧ cellOf ρ y = cc := by
    intro cc
    by_cases hcc : cc ∈ (S.image Prod.fst).image (cellOf ρ)
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hcc
      exact ⟨y, fun _ => ⟨hy, rfl⟩⟩
    · exact ⟨0, fun h' => absurd h' hcc⟩
  choose rep hrep using hrep_ex
  have hYQ : ((S.image Prod.fst).image (cellOf ρ)).image rep ⊆ S.image Prod.fst := by
    intro y hy
    obtain ⟨cc, hcc, rfl⟩ := Finset.mem_image.mp hy
    exact (hrep cc hcc).1
  -- cell regularity
  have hc0 : (0 : ℝ) < ((cellPins ρ (S.image Prod.fst) q.1).card : ℝ) := by
    have hmem : q.1 ∈ cellPins ρ (S.image Prod.fst) q.1 := Finset.mem_filter.mpr ⟨hSQ q hq, rfl⟩
    exact_mod_cast Finset.card_pos.mpr ⟨q.1, hmem⟩
  have hK3 : (0 : ℝ) < K ^ 3 := pow_pos hKpos 3
  have hν0 : 0 < ((cellPins ρ (S.image Prod.fst) q.1).card : ℝ) / K ^ 3 := div_pos hc0 hK3
  have hcell_low : ∀ p ∈ S.image Prod.fst, ((cellPins ρ (S.image Prod.fst) q.1).card : ℝ) / K ^ 3 ≤
      (((S.image Prod.fst).filter (fun z => cellOf ρ z = cellOf ρ p)).card : ℝ) := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    have := cell_pins_balanced hK0 hbfst hbcell hq ha
    rw [div_le_iff₀ hK3, mul_comm]
    exact this
  have hcell_up : ∀ p ∈ S.image Prod.fst,
      (((S.image Prod.fst).filter (fun z => cellOf ρ z = cellOf ρ p)).card : ℝ) ≤
        K ^ 6 * (((cellPins ρ (S.image Prod.fst) q.1).card : ℝ) / K ^ 3) := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    have := cell_pins_balanced hK0 hbfst hbcell ha hq
    have heq : K ^ 6 * (((cellPins ρ (S.image Prod.fst) q.1).card : ℝ) / K ^ 3) =
        K ^ 3 * ((cellPins ρ (S.image Prod.fst) q.1).card : ℝ) := by
      field_simp
    rw [heq]
    exact this
  have hPball : ∀ (x : E2) (t : ℝ), ρ ≤ t →
      ((P.filter (fun z => dist z x ≤ t)).card : ℝ) ≤ (r ^ (-η) / r) * t := by
    intro x t ht
    have := h.P_kt x t (hrρ.trans ht)
    calc _ ≤ r ^ (-η) * (t / r) := this
      _ = (r ^ (-η) / r) * t := by ring
  have hQpos : (0 : ℝ) < ((S.image Prod.fst).card : ℝ) := by
    obtain ⟨a, ha⟩ := hS.P_ne
    exact_mod_cast Finset.card_pos.mpr ⟨a, ha⟩
  have hA0 : 0 ≤ r ^ (-η) / r := div_nonneg (Real.rpow_nonneg hr.le _) hr.le
  have hK6 : 0 ≤ K ^ 6 := pow_nonneg hK0 6
  have hCY0 : 0 ≤ 3 * (r ^ (-η) / r) * K ^ 6 / ((S.image Prod.fst).card : ℝ) :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA0) hK6) hQpos.le
  have hYfr : ∀ (x : E2) (t : ℝ), ρ ≤ t →
      (((((S.image Prod.fst).image (cellOf ρ)).image rep).filter
          (fun z => z ∈ Metric.closedBall x t)).card : ℝ) ≤
        (3 * (r ^ (-η) / r) * K ^ 6 / ((S.image Prod.fst).card : ℝ)) * t *
          (((S.image Prod.fst).image (cellOf ρ)).image rep).card := by
    intro x t ht
    have h1 := cell_reps_frostman hρ hν0 hK6 hQP hPball hcell_low hcell_up rep
      (fun cc hcc => hrep cc hcc) x t ht
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hQpos]
    calc _ ≤ 3 * (r ^ (-η) / r) * K ^ 6 * t *
          ((((S.image Prod.fst).image (cellOf ρ)).image rep).card : ℝ) := h1
      _ = _ := by ring
  have hYne : (((S.image Prod.fst).image (cellOf ρ)).image rep).Nonempty := by
    obtain ⟨a, ha⟩ := hS.P_ne
    exact ⟨rep (cellOf ρ a), Finset.mem_image.mpr ⟨cellOf ρ a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, rfl⟩⟩
  have hY4 : ∀ y ∈ ((S.image Prod.fst).image (cellOf ρ)).image rep, ‖y‖ ≤ 4 :=
    fun y hy => h.P_norm _ (hQP (hYQ hy))
  have hTJ₁ : S.image (fun a => tb (cls a)) ⊆ J₁ := by
    intro j hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
    exact htbJ _ (hclsJ a (hSD ha))
  have hTprop : ∀ j ∈ S.image (fun a => tb (cls a)), ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1 := by
    intro j hj
    have hjD := hJ₀D (hJ₁ (hTJ₁ hj))
    exact ⟨h.P_norm _ (h.D_mem j hjD).1, (h.D_mem j hjD).2⟩
  have hYcard : (((((S.image Prod.fst).image (cellOf ρ)).image rep).card : ℕ) : ℝ) ≤ 2 ^ KY :=
    (by exact_mod_cast Finset.card_le_card hYQ :
      (((((S.image Prod.fst).image (cellOf ρ)).image rep).card : ℕ) : ℝ) ≤
        ((S.image Prod.fst).card : ℝ)).trans hKY
  have hB0 : 0 ≤ ((cellTubes ρ S cls tb q'.1).card : ℝ) / K ^ 2 :=
    div_nonneg (Nat.cast_nonneg _) (pow_nonneg hK0 2)
  have hinc : ∀ y ∈ ((S.image Prod.fst).image (cellOf ρ)).image rep,
      ((cellTubes ρ S cls tb q'.1).card : ℝ) / K ^ 2 ≤
        (((S.image (fun a => tb (cls a))).filter
          (fun j => |inner ℝ (y - j.1) j.2| < 28 * ρ)).card : ℝ) := by
    intro y hy
    obtain ⟨cc, hcc, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hyQ, hyc⟩ := hrep cc hcc
    obtain ⟨a, ha, hay⟩ := Finset.mem_image.mp hyQ
    have hsub : cellTubes ρ S cls tb (rep cc) ⊆
        (S.image (fun a => tb (cls a))).filter (fun j => |inner ℝ (rep cc - j.1) j.2| < 28 * ρ) := by
      intro j hj
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨hbS, hbc⟩ := Finset.mem_filter.mp hb
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨b, hbS, rfl⟩, ?_⟩
      have hbD := hSD hbS
      have hℓJ := hclsJ b hbD
      have hj1 : ‖(tb (cls b)).2‖ = 1 := (h.D_mem _ (hJ₀D (hJ₁ (htbJ _ hℓJ)))).2
      have hnear := pin_near_tube (h.P_norm _ (h.D_mem b hbD).1)
        (h.P_norm _ (h.D_mem _ (hJ₀D hℓJ)).1) (hcls1 b hbD) hj1
        (hgeo b hbD).1 (htbgeo _ hℓJ).1 (htbgeo _ hℓJ).2
      have hdist : dist (rep cc) b.1 ≤ 2 * ρ := dist_le_of_cellOf_eq hρ hbc.symm
      have hsplit : inner ℝ (rep cc - (tb (cls b)).1) (tb (cls b)).2 =
          inner ℝ (rep cc - b.1) (tb (cls b)).2 + inner ℝ (b.1 - (tb (cls b)).1) (tb (cls b)).2 := by
        rw [← inner_add_left]; congr 1; abel
      have hfirst : |inner ℝ (rep cc - b.1) (tb (cls b)).2| ≤ 2 * ρ := by
        calc |inner ℝ (rep cc - b.1) (tb (cls b)).2| ≤ ‖rep cc - b.1‖ * ‖(tb (cls b)).2‖ :=
              abs_real_inner_le_norm _ _
          _ = dist (rep cc) b.1 := by rw [hj1, mul_one, dist_eq_norm]
          _ ≤ 2 * ρ := hdist
      rw [hsplit]
      calc |inner ℝ (rep cc - b.1) (tb (cls b)).2 + inner ℝ (b.1 - (tb (cls b)).1) (tb (cls b)).2|
          ≤ |inner ℝ (rep cc - b.1) (tb (cls b)).2| + |inner ℝ (b.1 - (tb (cls b)).1) (tb (cls b)).2| :=
            abs_add_le _ _
        _ < 2 * ρ + (9 * r + 17 * ρ) := by linarith
        _ ≤ 28 * ρ := by linarith
    have hbal := cell_tubes_balanced hK0 hbcell hbct hq' ha
    rw [hay] at hbal
    have h2 : ((cellTubes ρ S cls tb (rep cc)).card : ℝ) ≤
        (((S.image (fun a => tb (cls a))).filter
          (fun j => |inner ℝ (rep cc - j.1) j.2| < 28 * ρ)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    rw [div_le_iff₀ (pow_pos hKpos 2)]
    calc ((cellTubes ρ S cls tb q'.1).card : ℝ) ≤ K ^ 2 * (cellTubes ρ S cls tb (rep cc)).card := hbal
      _ ≤ K ^ 2 * (((S.image (fun a => tb (cls a))).filter
            (fun j => |inner ℝ (rep cc - j.1) j.2| < 28 * ρ)).card : ℝ) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hK0 2)
      _ = _ := by ring
  have hρw : ρ ≤ 28 * ρ := by linarith
  have hCS := cell_tubes_bound hρ hρw hρ2 hCY0 hB0 _ hYne hY4 hYfr _ hTprop
    (fun x hx y hy hne => hJ₁sep x (hTJ₁ hx) y (hTJ₁ hy) hne) KY hYcard hinc
  calc _ ≤ _ := hCS
    _ = _ := by unfold cellConst; ring

/-- **Shared coarse tubes.** In a regularized failed bush estimate, the coarse tubes met by
the pins of a `ρ`-cell number at most `X` times those met by any single pin, where
`X ^ 2 = K ^ 8 cellConst tubeConst #J₀ r ^ (2 (s - η'))` (`≈ r ^ (-O(ε))` since
`#J₀ < r ^ (-2 s - ε₀)`). Stated without division:
`#cellTubes ^ 2 (r ^ (η' - s)) ^ 2 ≤ K ^ 8 cellConst tubeConst #J₀ #pinTubes ^ 2`. -/
theorem shared_tubes {r s ε₀ η η' c K ρ : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : FailData r s ε₀ η P D) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hc : 0 < c) (hK : 1 ≤ K)
    (hrρ : r ≤ ρ) (hρ2 : 28 * ρ ≤ 1 / 2)
    {cls tb : E2 × E2 → E2 × E2} {J₀ J₁ : Finset (E2 × E2)}
    (hclsJ : ∀ q ∈ D, cls q ∈ J₀) (hJ₀D : J₀ ⊆ D)
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
      (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r))
    (hJ₁ : J₁ ⊆ J₀) (hJ₁sep : ∀ x ∈ J₁, ∀ y ∈ J₁, x ≠ y → StripSep ρ x y)
    (htbJ : ∀ ℓ ∈ J₀, tb ℓ ∈ J₁)
    (htbgeo : ∀ ℓ ∈ J₀, |inner ℝ (ℓ.1 - (tb ℓ).1) (tb ℓ).2| < 9 * ρ ∧
      (dist ℓ.2 (tb ℓ).2 < ρ ∨ dist ℓ.2 (-(tb ℓ).2) < ρ))
    {S : Finset (E2 × E2)} (hSD : S ⊆ D) (hS : FailData r s ε₀ η' (S.image Prod.fst) S)
    (hbfst : Balanced S Prod.fst K) (hbcls : Balanced S cls K)
    (hbpt : Balanced S (fun q => (q.1, tb (cls q))) K)
    (hbcell : Balanced S (fun q => cellOf ρ q.1) K)
    (hbct : Balanced S (fun q => (cellOf ρ q.1, tb (cls q))) K)
    (hfar : ∀ q ∈ S, 2 * ((((S.filter (fun q' => cls q' = cls q)).filter
        (fun q' => dist q'.1 q.1 < c)).card : ℝ)) ≤ (S.filter (fun q' => cls q' = cls q)).card)
    (KY : ℕ) (hKY : ((S.image Prod.fst).card : ℝ) ≤ 2 ^ KY)
    {q q' : E2 × E2} (hq : q ∈ S) (hq' : q' ∈ S) :
    ((cellTubes ρ S cls tb q'.1).card : ℝ) ^ 2 * (r ^ (η' - s)) ^ 2 ≤
      K ^ 8 * cellConst ρ (3 * (r ^ (-η) / r) * K ^ 6 / ((S.image Prod.fst).card : ℝ)) KY *
        tubeConst r s η c K * J₀.card * ((pinTubes S cls tb q.1).card : ℝ) ^ 2 := by
  have hr := h.r_pos
  have hρ : 0 < ρ := hr.trans_le hrρ
  have hKpos : 0 < K := by linarith
  have hcs := shared_tubes_cs h hK hrρ hρ2 hclsJ hJ₀D hgeo hJ₁ hJ₁sep htbJ htbgeo hSD hS
    hbfst hbcell hbct KY hKY hq hq'
  have hcount := shared_tubes_count h hs0 hs1 hc hKpos hclsJ hJ₀D hgeo hSD hbcls hbpt hfar hq
  have hpin := shared_tubes_pin hbpt hq
  have hbush : r ^ (η' - s) ≤ ((bushOf S q.1).card : ℝ) :=
    hS.D_card q.1 (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  have hQpos : (0 : ℝ) < ((S.image Prod.fst).card : ℝ) := by
    obtain ⟨a, ha⟩ := hS.P_ne
    exact_mod_cast Finset.card_pos.mpr ⟨a, ha⟩
  have hCY0 : 0 ≤ 3 * (r ^ (-η) / r) * K ^ 6 / ((S.image Prod.fst).card : ℝ) :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (div_nonneg (Real.rpow_nonneg hr.le _) hr.le)) (pow_nonneg hKpos.le 6)) hQpos.le
  have hC₁0 := cellConst_nonneg hρ hρ2 hCY0 KY
  have hX2 : ((cellTubes ρ S cls tb q'.1).card : ℝ) ^ 2 ≤
      K ^ 4 * (cellConst ρ (3 * (r ^ (-η) / r) * K ^ 6 / ((S.image Prod.fst).card : ℝ)) KY *
        (S.image (fun a => tb (cls a))).card) := by
    have hK4 : (0 : ℝ) < K ^ 4 := pow_pos hKpos 4
    have heq : (((cellTubes ρ S cls tb q'.1).card : ℝ) / K ^ 2) ^ 2 =
        ((cellTubes ρ S cls tb q'.1).card : ℝ) ^ 2 / K ^ 4 := by
      rw [div_pow, ← pow_mul]
    rw [heq, div_le_iff₀ hK4, mul_comm] at hcs
    exact hcs
  have hT2 : ((S.image (fun a => tb (cls a))).card : ℝ) *
      ((S.filter (fun a => a.1 = q.1 ∧ tb (cls a) = tb (cls q))).card : ℝ) ^ 2 ≤
      K ^ 2 * (tubeConst r s η c K * J₀.card) := by
    have hK2 : (0 : ℝ) < K ^ 2 := pow_pos hKpos 2
    have heq : ((S.image (fun a => tb (cls a))).card : ℝ) *
        (((S.filter (fun a => a.1 = q.1 ∧ tb (cls a) = tb (cls q))).card : ℝ) / K) ^ 2 =
        (((S.image (fun a => tb (cls a))).card : ℝ) *
          ((S.filter (fun a => a.1 = q.1 ∧ tb (cls a) = tb (cls q))).card : ℝ) ^ 2) / K ^ 2 := by
      rw [div_pow, mul_div_assoc]
    rw [heq, div_le_iff₀ hK2, mul_comm (tubeConst r s η c K * _)] at hcount
    exact hcount
  exact shared_tubes_arith hKpos (Real.rpow_pos_of_pos hr _) hC₁0 (Nat.cast_nonneg _) hX2 hT2
    (hbush.trans hpin)

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
