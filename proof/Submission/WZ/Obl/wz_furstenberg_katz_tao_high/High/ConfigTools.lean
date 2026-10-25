-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.ConfigTools.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0675 High/ConfigTools.lean (b19b589).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.Leaves
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.LinePins
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.SharedArcs
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.Regularize

/-!
# Tools for building a `HighConfig`

* `FailData.mono_eta`: `FailData` is monotone in `η` (for `r ≤ 1`);
* `lines_exist`: a maximal `StripSep r`-separated family `J₀ ⊆ D` with its class map
  (x0538's `cls_exists`, keeping the separation of `J₀`);
* `Balanced.mono`, `card_le_balanced`, `classSize_mul_le`: balance compares class sizes with
  the average;
* `prune_card`, `FailData.prune`: removing a set `Bad` of labels and then the pins that lost
  more than half of their bush keeps `|S| / 2 - |Bad|` labels and the failure;
* `ceil_logb_le`: `C (⌈log₂ (8 / r)⌉ + 1) ≤ r ^ (-δ)` for small `r`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_tower_balanced_refinement

noncomputable section

theorem FailData.mono_eta {r s ε₀ η η' : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : FailData r s ε₀ η P D) (hηη : η ≤ η') (hr1 : r ≤ 1) : FailData r s ε₀ η' P D := by
  have hr := h.r_pos
  refine ⟨hr, h.P_ne, h.P_norm, h.P_sep, ?_, ?_, h.D_mem, ?_, h.D_sep, ?_, h.few_lines⟩
  · exact (Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)).trans h.P_card
  · intro x ρ hρ
    refine (h.P_kt x ρ hρ).trans ?_
    have hρr : 0 ≤ ρ / r := div_nonneg (hr.le.trans hρ) hr.le
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)) hρr
  · intro p hp
    exact (Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)).trans (h.D_card p hp)
  · intro p hp u hu ρ hρ
    refine (h.D_kt p hp u hu ρ hρ).trans ?_
    have hρr : 0 ≤ (ρ / r) ^ s := Real.rpow_nonneg (div_nonneg (hr.le.trans hρ) hr.le) _
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)) hρr

/-- The lines: a maximal `StripSep r`-separated `J₀ ⊆ D` and a class map with the 9r/r
geometry (x0538's `cls_exists`, keeping the separation). -/
theorem lines_exist {r s ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : FailData r s ε₀ η P D) :
    ∃ (J₀ : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2),
      J₀ ⊆ D ∧ (∀ x ∈ J₀, ∀ y ∈ J₀, x ≠ y → StripSep r x y) ∧ (∀ q ∈ D, cls q ∈ J₀) ∧
      (∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
        (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r)) := by
  obtain ⟨J, hJD, hJpair, hJmax⟩ := exists_maximal_pairwise D (StripSep r)
  have hch : ∀ q : E2 × E2, ∃ j : E2 × E2,
      q ∈ D → j ∈ J ∧ (q = j ∨ ¬ StripSep r q j ∨ ¬ StripSep r j q) := by
    intro q
    by_cases hq : q ∈ D
    · by_cases hqJ : q ∈ J
      · exact ⟨q, fun _ => ⟨hqJ, Or.inl rfl⟩⟩
      · obtain ⟨j, hj, hj'⟩ := hJmax q hq hqJ
        exact ⟨j, fun _ => ⟨hj, Or.inr hj'⟩⟩
    · exact ⟨q, fun h' => absurd h' hq⟩
  choose cls hcls using hch
  refine ⟨J, cls, hJD, hJpair, fun q hq => (hcls q hq).1, ?_⟩
  intro q hq
  have hj := hcls q hq
  have hq4 : ‖q.1‖ ≤ 4 := h.P_norm _ (h.D_mem q hq).1
  have hj4 : ‖(cls q).1‖ ≤ 4 := h.P_norm _ (h.D_mem _ (hJD hj.1)).1
  exact near_of_not_stripSep hq4 hj4 hj.2 h.r_pos

theorem Balanced.mono {α β : Type*} [DecidableEq α] {S : Finset α} {f : α → β} {K K' : ℝ}
    (h : Balanced S f K) (hK : K ≤ K') : Balanced S f K' := by
  intro i hi i' hi'
  exact (h i hi i' hi').trans (mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg _))

/-- Balance: `|S| ≤ K · #classes · (size of any class)`. -/
theorem card_le_balanced {S : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2} {K : ℝ}
    (hbal : Balanced S cls K) {q : E2 × E2} (hq : q ∈ S) :
    (S.card : ℝ) ≤ K * (S.image cls).card * (classSize S cls q : ℝ) := by
  classical
  have hsum : (S.card : ℝ) = ∑ ℓ ∈ S.image cls, ((S.filter (fun q' => cls q' = ℓ)).card : ℝ) := by
    have := Finset.card_eq_sum_card_fiberwise (f := cls) (s := S) (t := S.image cls)
      (fun q' hq' => Finset.mem_image_of_mem cls hq')
    rw [this]; push_cast; rfl
  rw [hsum]
  have hfib : ∀ ℓ ∈ S.image cls,
      ((S.filter (fun q' => cls q' = ℓ)).card : ℝ) ≤ K * (classSize S cls q : ℝ) := by
    intro ℓ hℓ
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hℓ
    have hb := hbal q' hq' q hq
    have e1 : leafFiber S cls q' = S.filter (fun a => cls a = cls q') := by
      ext a; rw [mem_leafFiber', Finset.mem_filter]
    have e2 : leafFiber S cls q = S.filter (fun a => cls a = cls q) := by
      ext a; rw [mem_leafFiber', Finset.mem_filter]
    rw [e1, e2] at hb
    unfold classSize
    exact hb
  calc ∑ ℓ ∈ S.image cls, ((S.filter (fun q' => cls q' = ℓ)).card : ℝ)
      ≤ ∑ _ℓ ∈ S.image cls, K * (classSize S cls q : ℝ) := Finset.sum_le_sum hfib
    _ = K * (S.image cls).card * (classSize S cls q : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- Balance: `(size of any class) · #classes ≤ K |S|`. -/
theorem classSize_mul_le {S : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2} {K : ℝ}
    (hbal : Balanced S cls K) {q : E2 × E2} (hq : q ∈ S) :
    (classSize S cls q : ℝ) * (S.image cls).card ≤ K * S.card := by
  classical
  have hsum : (S.card : ℝ) = ∑ ℓ ∈ S.image cls, ((S.filter (fun q' => cls q' = ℓ)).card : ℝ) := by
    have := Finset.card_eq_sum_card_fiberwise (f := cls) (s := S) (t := S.image cls)
      (fun q' hq' => Finset.mem_image_of_mem cls hq')
    rw [this]; push_cast; rfl
  have hfib : ∀ ℓ ∈ S.image cls,
      (classSize S cls q : ℝ) ≤ K * ((S.filter (fun q' => cls q' = ℓ)).card : ℝ) := by
    intro ℓ hℓ
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hℓ
    have hb := hbal q hq q' hq'
    have e1 : leafFiber S cls q' = S.filter (fun a => cls a = cls q') := by
      ext a; rw [mem_leafFiber', Finset.mem_filter]
    have e2 : leafFiber S cls q = S.filter (fun a => cls a = cls q) := by
      ext a; rw [mem_leafFiber', Finset.mem_filter]
    rw [e1, e2] at hb
    unfold classSize
    exact hb
  calc (classSize S cls q : ℝ) * (S.image cls).card
      = ∑ _ℓ ∈ S.image cls, (classSize S cls q : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ ℓ ∈ S.image cls, K * ((S.filter (fun q' => cls q' = ℓ)).card : ℝ) :=
        Finset.sum_le_sum hfib
    _ = K * S.card := by rw [← Finset.mul_sum, ← hsum]

/-- The pins kept after removing `Bad`: those that keep at least half of their bush. -/
def keptPins (S Bad : Finset (E2 × E2)) : Finset E2 :=
  (S.image Prod.fst).filter (fun p =>
    (S.filter (fun q => q.1 = p)).card ≤ 2 * ((S \ Bad).filter (fun q => q.1 = p)).card)

/-- The labels kept after removing `Bad` and the pins that lost more than half their bush. -/
def keptLabels (S Bad : Finset (E2 × E2)) : Finset (E2 × E2) :=
  (S \ Bad).filter (fun q => q.1 ∈ keptPins S Bad)

theorem keptLabels_subset (S Bad : Finset (E2 × E2)) : keptLabels S Bad ⊆ S :=
  fun _ hq => (Finset.mem_sdiff.mp (Finset.mem_filter.mp hq).1).1

theorem not_mem_bad_of_kept {S Bad : Finset (E2 × E2)} {q : E2 × E2}
    (hq : q ∈ keptLabels S Bad) : q ∉ Bad :=
  (Finset.mem_sdiff.mp (Finset.mem_filter.mp hq).1).2

/-- `|S| ≤ 2 |kept labels| + 2 |Bad|`. -/
theorem prune_card (S Bad : Finset (E2 × E2)) (hBad : Bad ⊆ S) :
    (S.card : ℝ) ≤ 2 * (keptLabels S Bad).card + 2 * Bad.card := by
  classical
  set P := S.image Prod.fst with hP
  have fib : ∀ T : Finset (E2 × E2), T ⊆ S →
      (T.card : ℝ) = ∑ p ∈ P, ((T.filter (fun q => q.1 = p)).card : ℝ) := by
    intro T hT
    have := Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := T) (t := P)
      (fun q hq => Finset.mem_image_of_mem Prod.fst (hT hq))
    rw [this]; push_cast; rfl
  have hS2 : S \ Bad ⊆ S := Finset.sdiff_subset
  have hsplit : ∀ p, ((S.filter (fun q => q.1 = p)).card : ℕ) =
      ((S \ Bad).filter (fun q => q.1 = p)).card + (Bad.filter (fun q => q.1 = p)).card := by
    intro p
    have heq : (S \ Bad).filter (fun q => q.1 = p) =
        S.filter (fun q => q.1 = p) \ Bad.filter (fun q => q.1 = p) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      tauto
    rw [heq, Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ hBad)]
    have := Finset.card_le_card (Finset.filter_subset_filter (fun q : E2 × E2 => q.1 = p) hBad)
    omega
  have hpt : ∀ p ∈ P, ((S.filter (fun q => q.1 = p)).card : ℝ) ≤
      2 * (((keptLabels S Bad).filter (fun q => q.1 = p)).card : ℝ) +
        2 * ((Bad.filter (fun q => q.1 = p)).card : ℝ) := by
    intro p hp
    by_cases hk : p ∈ keptPins S Bad
    · have hfil : (keptLabels S Bad).filter (fun q => q.1 = p) =
          (S \ Bad).filter (fun q => q.1 = p) := by
        ext q
        simp only [keptLabels, Finset.mem_filter]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by rw [h3]; exact hk⟩, h3⟩
      rw [hfil]
      have h1 := (Finset.mem_filter.mp hk).2
      have h1' : ((S.filter (fun q => q.1 = p)).card : ℝ) ≤
          2 * (((S \ Bad).filter (fun q => q.1 = p)).card : ℝ) := by exact_mod_cast h1
      have h2 : (0 : ℝ) ≤ ((Bad.filter (fun q => q.1 = p)).card : ℝ) := Nat.cast_nonneg _
      linarith
    · have h1 : ¬ ((S.filter (fun q => q.1 = p)).card ≤
          2 * ((S \ Bad).filter (fun q => q.1 = p)).card) := by
        intro hle; exact hk (Finset.mem_filter.mpr ⟨hp, hle⟩)
      have h2 := hsplit p
      have h3 : ((S.filter (fun q => q.1 = p)).card : ℕ) ≤
          2 * (Bad.filter (fun q => q.1 = p)).card := by omega
      have h3' : ((S.filter (fun q => q.1 = p)).card : ℝ) ≤
          2 * ((Bad.filter (fun q => q.1 = p)).card : ℝ) := by exact_mod_cast h3
      have h4 : (0 : ℝ) ≤ (((keptLabels S Bad).filter (fun q => q.1 = p)).card : ℝ) :=
        Nat.cast_nonneg _
      linarith
  rw [fib S le_rfl, fib (keptLabels S Bad) (keptLabels_subset S Bad), fib Bad hBad,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum hpt

/-- A kept pin keeps at least half of its bush. -/
theorem kept_bush {S Bad : Finset (E2 × E2)} {p : E2}
    (hp : p ∈ (keptLabels S Bad).image Prod.fst) :
    ((bushOf S p).card : ℝ) ≤ 2 * ((bushOf (keptLabels S Bad) p).card : ℝ) := by
  classical
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  have hk : q.1 ∈ keptPins S Bad := (Finset.mem_filter.mp hq).2
  have h1 := (Finset.mem_filter.mp hk).2
  have hfil : (keptLabels S Bad).filter (fun q' => q'.1 = q.1) =
      (S \ Bad).filter (fun q' => q'.1 = q.1) := by
    ext q'
    simp only [keptLabels, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by rw [h3]; exact hk⟩, h3⟩
  rw [card_bushOf, card_bushOf, hfil]
  exact_mod_cast h1

/-- The failure survives pruning, with a worse `η'`, given the pin count and the bush
lower bound of the pruned family. -/
theorem FailData.prune {r s ε₀ η η' : ℝ} {S S' : Finset (E2 × E2)}
    (h : FailData r s ε₀ η (S.image Prod.fst) S) (hsub : S' ⊆ S) (hne : S'.Nonempty)
    (hηη : η ≤ η') (hr1 : r ≤ 1)
    (hcard : r ^ (η' - 1) ≤ ((S'.image Prod.fst).card : ℝ))
    (hbush : ∀ p ∈ S'.image Prod.fst, r ^ (η' - s) ≤ ((bushOf S' p).card : ℝ)) :
    FailData r s ε₀ η' (S'.image Prod.fst) S' := by
  have hr := h.r_pos
  have hPsub : S'.image Prod.fst ⊆ S.image Prod.fst := Finset.image_subset_image hsub
  refine ⟨hr, hne.image _, fun p hp => h.P_norm p (hPsub hp),
    fun p hp p' hp' hne' => h.P_sep p (hPsub hp) p' (hPsub hp') hne', hcard, ?_, ?_, hbush,
    fun p e e' he he' hne' => h.D_sep p e e' (hsub he) (hsub he') hne', ?_, ?_⟩
  · intro x ρ hρ
    have h1 := h.P_kt x ρ hρ
    have h2 : ((S'.image Prod.fst).filter (fun p => dist p x ≤ ρ)).card ≤
        ((S.image Prod.fst).filter (fun p => dist p x ≤ ρ)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ hPsub)
    have hρr : 0 ≤ ρ / r := div_nonneg (hr.le.trans hρ) hr.le
    calc (((S'.image Prod.fst).filter (fun p => dist p x ≤ ρ)).card : ℝ)
        ≤ ((S.image Prod.fst).filter (fun p => dist p x ≤ ρ)).card := by exact_mod_cast h2
      _ ≤ r ^ (-η) * (ρ / r) := h1
      _ ≤ r ^ (-η') * (ρ / r) := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)) hρr
  · intro q hq
    exact ⟨Finset.mem_image_of_mem _ hq, (h.D_mem q (hsub hq)).2⟩
  · intro p hp u hu ρ hρ
    have h1 := h.D_kt p (hPsub hp) u hu ρ hρ
    have hb : bushOf S' p ⊆ bushOf S p := by
      intro e he
      exact mem_bushOf.mpr (hsub (mem_bushOf.mp he))
    have h2 := Finset.card_le_card (Finset.filter_subset_filter (fun e => dist e u ≤ ρ) hb)
    have hρr : 0 ≤ (ρ / r) ^ s := Real.rpow_nonneg (div_nonneg (hr.le.trans hρ) hr.le) _
    calc (((bushOf S' p).filter (fun e => dist e u ≤ ρ)).card : ℝ)
        ≤ ((bushOf S p).filter (fun e => dist e u ≤ ρ)).card := by exact_mod_cast h2
      _ ≤ r ^ (-η) * (ρ / r) ^ s := h1
      _ ≤ r ^ (-η') * (ρ / r) ^ s := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)) hρr
  · intro J hJ hsep
    exact h.few_lines J (hJ.trans hsub) hsep

/-- `C (⌈log₂ (8 / r)⌉ + 1) ≤ r ^ (-δ)` for small `r`. -/
theorem ceil_logb_le {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ r : ℝ, 0 < r → r ≤ r₁ →
      C * ((⌈Real.logb 2 (8 / r)⌉₊ : ℝ) + 1) ≤ r ^ (-δ) := by
  set C' : ℝ := 8 / ((δ / 2) * Real.log 2) + 2 with hC'
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC'0 : 0 < C' := by positivity
  obtain ⟨r₁, hr₁, hsmall⟩ := WangZahlLot.Obl.wz_slab_local_linearity.exists_small_rpow
    (a := δ / 2) (B := 1 / (C * C')) (by positivity) (by positivity)
  refine ⟨min r₁ 1, lt_min hr₁ one_pos, ?_⟩
  intro r hr hrr
  have hr1 : r ≤ 1 := hrr.trans (min_le_right _ _)
  have hrs := hsmall r hr (hrr.trans (min_le_left _ _))
  have hhalf : 1 ≤ r ^ (-(δ / 2)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by linarith)
  -- log (8 / r) ≤ (8 / r) ^ (δ/2) / (δ/2) ≤ 8 r ^ (-δ/2) / (δ/2)
  have h8r : 0 ≤ 8 / r := by positivity
  have hlog := Real.log_le_rpow_div h8r (by positivity : 0 < δ / 2)
  have hpow : (8 / r) ^ (δ / 2) ≤ 8 * r ^ (-(δ / 2)) := by
    rw [Real.div_rpow (by norm_num) hr.le, Real.rpow_neg hr.le, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc (8 : ℝ) ^ (δ / 2) ≤ 8 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 8 := Real.rpow_one 8
  have hlogb : Real.logb 2 (8 / r) ≤ 8 / ((δ / 2) * Real.log 2) * r ^ (-(δ / 2)) := by
    unfold Real.logb
    rw [div_le_iff₀ hlog2]
    have h1 : Real.log (8 / r) ≤ 8 * r ^ (-(δ / 2)) / (δ / 2) :=
      hlog.trans (div_le_div_of_nonneg_right hpow (by positivity))
    calc Real.log (8 / r) ≤ 8 * r ^ (-(δ / 2)) / (δ / 2) := h1
      _ = 8 / ((δ / 2) * Real.log 2) * r ^ (-(δ / 2)) * Real.log 2 := by
          field_simp
  have hceil : (⌈Real.logb 2 (8 / r)⌉₊ : ℝ) + 1 ≤ C' * r ^ (-(δ / 2)) := by
    have hlb0 : 0 ≤ Real.logb 2 (8 / r) := by
      apply Real.logb_nonneg (by norm_num)
      rw [le_div_iff₀ hr]; linarith
    have h1 := Nat.ceil_lt_add_one hlb0
    rw [hC']
    nlinarith
  -- C C' r^(-δ/2) ≤ r^(-δ) since r^(δ/2) ≤ 1 / (C C')
  have hsplit : r ^ (-δ) = r ^ (-(δ / 2)) * r ^ (-(δ / 2)) := by
    rw [← Real.rpow_add hr]; ring_nf
  have hinv : C * C' ≤ r ^ (-(δ / 2)) := by
    rw [Real.rpow_neg hr.le]
    rw [le_inv_comm₀ (by positivity) (Real.rpow_pos_of_pos hr _)]
    rw [one_div] at hrs
    exact hrs
  calc C * ((⌈Real.logb 2 (8 / r)⌉₊ : ℝ) + 1) ≤ C * (C' * r ^ (-(δ / 2))) :=
        mul_le_mul_of_nonneg_left hceil hC.le
    _ = (C * C') * r ^ (-(δ / 2)) := by ring
    _ ≤ r ^ (-(δ / 2)) * r ^ (-(δ / 2)) :=
        mul_le_mul_of_nonneg_right hinv (Real.rpow_pos_of_pos hr _).le
    _ = r ^ (-δ) := hsplit.symm

end

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
