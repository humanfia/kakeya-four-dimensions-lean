-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.Regularize.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o222/x0722 High/Regularize.lean (064b94b).
-- Adapted from local obligation o157, branch x0675, commit c7aca52cd124.
-- Source: High/Regularize.lean. Own namespaces renamed; shared definitions imported from accepted o213.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.FailData

/-!
# Regularizing a failed bush estimate along finitely many partitions

`FailData.regularize`: given `FailData r s ε₀ η P D` and a bounded number of arbitrary
partition maps `f i : E2 × E2 → Y i` of the labels (for instance cells of the pins, arcs
of the normals or assigned lines, at any fixed scales), there is `S ⊆ D` with
`|S| ≥ r ^ ε |D|` on which every `f i` and the bush map `Prod.fst` are balanced with
ratio `r ^ (-ε)`, and `S` (over its own pins) is again `FailData`, with `η` replaced by
`3 η + 2 ε`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale
open WangZahlLot.Obl.wz_tower_balanced_refinement

/-- The codomains of a family of maps, with `E2` (for `Prod.fst`) adjoined at `none`. -/
def withFst {I : Type} (Y : I → Type) : Option I → Type := fun o => Option.elim o E2 Y

noncomputable scoped instance withFst.decEq {I : Type} (Y : I → Type) [∀ i, DecidableEq (Y i)] :
    ∀ o, DecidableEq (withFst Y o)
  | none => inferInstanceAs (DecidableEq E2)
  | some i => inferInstanceAs (DecidableEq (Y i))

/-- The family of maps with `Prod.fst` adjoined at `none`. -/
def addFst {I : Type} {Y : I → Type} (f : ∀ i, E2 × E2 → Y i) :
    ∀ o, E2 × E2 → withFst Y o
  | none => Prod.fst
  | some i => f i

/-- Fibers of `Prod.fst` are bushes. -/
theorem leafFiber_fst_card (S : Finset (E2 × E2)) (q : E2 × E2) :
    (leafFiber S Prod.fst q).card = (bushOf S q.1).card := by
  classical
  rw [card_bushOf]
  congr 1
  ext a
  simp [leafFiber]

/-- A balanced bush map compares any two bushes. -/
theorem bush_le_of_balanced {S : Finset (E2 × E2)} {K : ℝ}
    (hbal : Balanced S Prod.fst K) {p p' : E2} (hp : p ∈ S.image Prod.fst)
    (hp' : p' ∈ S.image Prod.fst) :
    ((bushOf S p).card : ℝ) ≤ K * (bushOf S p').card := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hp'
  have h := hbal q hq q' hq'
  rwa [leafFiber_fst_card, leafFiber_fst_card] at h

theorem FailData.regularize (s ε : ℝ) (_hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hε : 0 < ε) (B : ℕ) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 / 2 ∧ ∀ r ε₀ η : ℝ, r ≤ r₀ → 0 ≤ η → η ≤ 1 →
      ∀ (P : Finset E2) (D : Finset (E2 × E2)), FailData r s ε₀ η P D →
      ∀ {I : Type} [Fintype I] [DecidableEq I] {Y : I → Type} [∀ i, DecidableEq (Y i)],
        Fintype.card I ≤ B → ∀ f : ∀ i, E2 × E2 → Y i,
        ∃ S ⊆ D, r ^ ε * (D.card : ℝ) ≤ S.card ∧
          FailData r s ε₀ (3 * η + 2 * ε) (S.image Prod.fst) S ∧
          Balanced S Prod.fst (r ^ (-ε)) ∧ ∀ i, Balanced S (f i) (r ^ (-ε)) := by
  classical
  obtain ⟨δ₀, hδ₀, hδ₀1, hreg⟩ := regularize_finite_partitions_power ε hε (B + 1)
  obtain ⟨r₁, hr₁, hr₁spec⟩ := WangZahlLot.Obl.wz_slab_local_linearity.exists_small_rpow
    (a := ε) (B := 1 / 2) hε (by norm_num)
  refine ⟨min (min δ₀ r₁) (1 / 2), lt_min (lt_min hδ₀ hr₁) (by norm_num),
    min_le_right _ _, ?_⟩
  intro r ε₀ η hrr₀ hη0 hη1 P D h I _ _ Y _ hIB f
  have hr : 0 < r := h.r_pos
  have hrδ : r ≤ δ₀ := hrr₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hrr₁ : r ≤ r₁ := hrr₀.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrhalf : r ≤ 1 / 2 := hrr₀.trans (min_le_right _ _)
  have hr1 : r ≤ 1 := by linarith
  have hrε : r ^ ε ≤ 1 / 2 := hr₁spec r hr hrr₁
  -- sizes of `D`
  have hbushD : ∀ p ∈ P, ((bushOf D p).card : ℝ) ≤ r ^ (-η) * (2 / r) ^ s :=
    fun p hp => h.bush_le (by linarith) hp
  have hDsum := card_eq_sum_bushOf (fun q hq => (h.D_mem q hq).1)
  have hPcard := h.P_card_le (by linarith)
  have hrη : r ^ (-η) ≤ r⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  have h2rs : (2 / r) ^ s ≤ 2 / r :=
    Real.rpow_le_self_of_one_le (by rw [le_div_iff₀ hr]; linarith) hs1
  have hDle : (D.card : ℝ) ≤ r ^ (-7 : ℝ) := by
    have h1 : (D.card : ℝ) ≤ P.card * (r ^ (-η) * (2 / r) ^ s) := by
      rw [hDsum]
      calc ∑ p ∈ P, ((bushOf D p).card : ℝ) ≤ ∑ _p ∈ P, r ^ (-η) * (2 / r) ^ s :=
            Finset.sum_le_sum hbushD
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have h2 : (P.card : ℝ) * (r ^ (-η) * (2 / r) ^ s) ≤ (r⁻¹ * (4 / r)) * (r⁻¹ * (2 / r)) := by
      apply mul_le_mul (hPcard.trans (mul_le_mul_of_nonneg_right hrη (by positivity)))
        (mul_le_mul hrη h2rs (by positivity) (by positivity)) (by positivity) (by positivity)
    have h3 : (r⁻¹ * (4 / r)) * (r⁻¹ * (2 / r)) = 8 * r⁻¹ ^ 4 := by
      field_simp; ring
    have h4 : (8 : ℝ) * r⁻¹ ^ 4 ≤ r ^ (-7 : ℝ) := by
      have hr3 : r ^ 3 ≤ 1 / 8 := by
        calc r ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ hr.le hrhalf 3
          _ = 1 / 8 := by norm_num
      have h7 : r ^ (-7 : ℝ) = r⁻¹ ^ 7 := by
        rw [Real.rpow_neg hr.le, inv_pow]
        norm_num
      rw [h7]
      have hri : (1 : ℝ) ≤ r⁻¹ := one_le_inv_iff₀.mpr ⟨hr, hr1⟩
      have : r⁻¹ ^ 7 = r⁻¹ ^ 4 * (r⁻¹) ^ 3 := by ring
      rw [this]
      have h8 : (8 : ℝ) ≤ r⁻¹ ^ 3 := by
        rw [inv_pow, le_inv_comm₀ (by norm_num) (by positivity)]
        linarith
      nlinarith [pow_pos (inv_pos.mpr hr) 4]
    linarith
  have hDne : D.Nonempty := by
    obtain ⟨p, hp⟩ := h.P_ne
    have hb := h.D_card p hp
    have hpos : (0 : ℝ) < ((bushOf D p).card : ℝ) :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos hr _) hb
    obtain ⟨e, he⟩ := Finset.card_pos.mp (by exact_mod_cast hpos)
    exact ⟨(p, e), mem_bushOf.mp he⟩
  -- regularize
  have hcard : Fintype.card (Option I) ≤ B + 1 := by
    rw [Fintype.card_option]; omega
  obtain ⟨S, hSD, hSne, hmass, hbal⟩ :=
    hreg r hr hrδ (α := E2 × E2) (I := Option I) (Y := withFst Y) hcard D hDne hDle (addFst f)
  have hbalfst : Balanced S Prod.fst (r ^ (-ε)) := hbal none
  refine ⟨S, hSD, hmass, ?_, hbalfst, fun i => hbal (some i)⟩
  -- the regularized family is again `FailData`
  set Q := S.image Prod.fst with hQ
  have hQP : Q ⊆ P := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact (h.D_mem q (hSD hq)).1
  have hQne : Q.Nonempty := hSne.image _
  have hη' : η ≤ 3 * η + 2 * ε := by linarith
  have hrpow_mono : ∀ a b : ℝ, a ≤ b → r ^ b ≤ r ^ a :=
    fun a b hab => Real.rpow_le_rpow_of_exponent_ge hr hr1 hab
  have hSsum := card_eq_sum_bushOf (P := Q) (D := S)
    (fun q hq => Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  have hPlow : r ^ (η - s) * (P.card : ℝ) ≤ D.card := by
    rw [hDsum]
    calc r ^ (η - s) * (P.card : ℝ) = ∑ _p ∈ P, r ^ (η - s) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun p hp => h.D_card p hp)
  have hQcardP : (Q.card : ℝ) ≤ P.card := by exact_mod_cast Finset.card_le_card hQP
  have hQpos : (0 : ℝ) < Q.card := by exact_mod_cast hQne.card_pos
  -- every bush of `S` is large
  have hbushS : ∀ p ∈ Q, r ^ (2 * ε + η - s) ≤ ((bushOf S p).card : ℝ) := by
    intro p hp
    have hsum_le : (S.card : ℝ) ≤ Q.card * (r ^ (-ε) * (bushOf S p).card) := by
      rw [hSsum]
      calc ∑ p' ∈ Q, ((bushOf S p').card : ℝ) ≤ ∑ _p' ∈ Q, r ^ (-ε) * (bushOf S p).card :=
            Finset.sum_le_sum (fun p' hp' => bush_le_of_balanced hbalfst hp' hp)
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hchain : r ^ ε * (r ^ (η - s) * (P.card : ℝ)) ≤ Q.card * (r ^ (-ε) * (bushOf S p).card) :=
      (mul_le_mul_of_nonneg_left hPlow (Real.rpow_nonneg hr.le _)).trans (hmass.trans hsum_le)
    have hrε2 : r ^ ε * r ^ ε = r ^ (2 * ε) := by rw [← Real.rpow_add hr]; ring_nf
    have hrεinv : r ^ ε * r ^ (-ε) = 1 := by rw [← Real.rpow_add hr]; simp
    have hkey : r ^ (2 * ε) * r ^ (η - s) * (P.card : ℝ) ≤ Q.card * (bushOf S p).card := by
      have := mul_le_mul_of_nonneg_left hchain (Real.rpow_nonneg hr.le ε)
      calc r ^ (2 * ε) * r ^ (η - s) * (P.card : ℝ)
          = r ^ ε * (r ^ ε * (r ^ (η - s) * (P.card : ℝ))) := by rw [← hrε2]; ring
        _ ≤ r ^ ε * (Q.card * (r ^ (-ε) * (bushOf S p).card)) := this
        _ = (r ^ ε * r ^ (-ε)) * (Q.card * (bushOf S p).card) := by ring
        _ = Q.card * (bushOf S p).card := by rw [hrεinv, one_mul]
    have hsplit : r ^ (2 * ε + η - s) = r ^ (2 * ε) * r ^ (η - s) := by
      rw [← Real.rpow_add hr]; ring_nf
    rw [hsplit]
    have hPpos : (0 : ℝ) < P.card := lt_of_lt_of_le hQpos hQcardP
    have : r ^ (2 * ε) * r ^ (η - s) * (Q.card : ℝ) ≤ Q.card * (bushOf S p).card := by
      calc r ^ (2 * ε) * r ^ (η - s) * (Q.card : ℝ)
          ≤ r ^ (2 * ε) * r ^ (η - s) * (P.card : ℝ) :=
            mul_le_mul_of_nonneg_left hQcardP (by positivity)
        _ ≤ _ := hkey
    nlinarith [this, hQpos]
  refine ⟨hr, hQne, fun p hp => h.P_norm p (hQP hp),
    fun p hp p' hp' hne => h.P_sep p (hQP hp) p' (hQP hp') hne, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- number of pins
    have hbushSle : ∀ p ∈ Q, ((bushOf S p).card : ℝ) ≤ r ^ (-η) * (2 / r) ^ s := by
      intro p hp
      have hsub : bushOf S p ⊆ bushOf D p := by
        intro e he
        exact mem_bushOf.mpr (hSD (mem_bushOf.mp he))
      exact (by exact_mod_cast Finset.card_le_card hsub : ((bushOf S p).card : ℝ) ≤ _).trans
        (hbushD p (hQP hp))
    have hSle : (S.card : ℝ) ≤ Q.card * (r ^ (-η) * (2 / r) ^ s) := by
      rw [hSsum]
      calc ∑ p ∈ Q, ((bushOf S p).card : ℝ) ≤ ∑ _p ∈ Q, r ^ (-η) * (2 / r) ^ s :=
            Finset.sum_le_sum hbushSle
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have h2s : (2 / r) ^ s = 2 ^ s * r ^ (-s) := by
      rw [Real.div_rpow (by norm_num) hr.le, Real.rpow_neg hr.le]; ring
    have h2s2 : (2 : ℝ) ^ s ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) hs1
    have hlow : r ^ ε * (r ^ (η - s) * r ^ (η - 1)) ≤ Q.card * (r ^ (-η) * (2 * r ^ (-s))) := by
      calc r ^ ε * (r ^ (η - s) * r ^ (η - 1))
          ≤ r ^ ε * (r ^ (η - s) * P.card) := by
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hr.le _)
            exact mul_le_mul_of_nonneg_left h.P_card (Real.rpow_nonneg hr.le _)
        _ ≤ r ^ ε * D.card := mul_le_mul_of_nonneg_left hPlow (Real.rpow_nonneg hr.le _)
        _ ≤ S.card := hmass
        _ ≤ Q.card * (r ^ (-η) * (2 / r) ^ s) := hSle
        _ ≤ Q.card * (r ^ (-η) * (2 * r ^ (-s))) := by
            rw [h2s]
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hr.le _)
            exact mul_le_mul_of_nonneg_right h2s2 (Real.rpow_nonneg hr.le _)
    -- rearrange: Q ≥ r^(ε + 3η - 1) / 2 ≥ r^(2ε + 3η - 1)
    have hA : r ^ ε * (r ^ (η - s) * r ^ (η - 1)) =
        (r ^ (ε + 3 * η - 1)) * (r ^ (-η) * r ^ (-s)) := by
      rw [← Real.rpow_add hr, ← Real.rpow_add hr, ← Real.rpow_add hr, ← Real.rpow_add hr]
      ring_nf
    rw [hA] at hlow
    have hpos : 0 < r ^ (-η) * r ^ (-s) := by positivity
    have hQge : r ^ (ε + 3 * η - 1) ≤ 2 * Q.card := by
      have : r ^ (ε + 3 * η - 1) * (r ^ (-η) * r ^ (-s)) ≤
          (2 * Q.card) * (r ^ (-η) * r ^ (-s)) := by nlinarith [hlow]
      exact le_of_mul_le_mul_right this hpos
    have hsplit : r ^ (3 * η + 2 * ε - 1) = r ^ ε * r ^ (ε + 3 * η - 1) := by
      rw [← Real.rpow_add hr]; ring_nf
    rw [hsplit]
    have hnn : 0 ≤ r ^ (ε + 3 * η - 1) := Real.rpow_nonneg hr.le _
    nlinarith [hrε, hQge, hnn]
  · -- Katz--Tao bound for the pins
    intro x ρ hρ
    have hsub : Q.filter (fun p => dist p x ≤ ρ) ⊆ P.filter (fun p => dist p x ≤ ρ) :=
      Finset.filter_subset_filter _ hQP
    have h1 := (by exact_mod_cast Finset.card_le_card hsub :
      ((Q.filter (fun p => dist p x ≤ ρ)).card : ℝ) ≤ (P.filter (fun p => dist p x ≤ ρ)).card)
    have hρr : 0 ≤ ρ / r := div_nonneg (hr.le.trans hρ) hr.le
    calc _ ≤ _ := h1
      _ ≤ r ^ (-η) * (ρ / r) := h.P_kt x ρ hρ
      _ ≤ r ^ (-(3 * η + 2 * ε)) * (ρ / r) :=
        mul_le_mul_of_nonneg_right (hrpow_mono _ _ (by linarith)) hρr
  · intro q hq
    exact ⟨Finset.mem_image.mpr ⟨q, hq, rfl⟩, (h.D_mem q (hSD hq)).2⟩
  · intro p hp
    exact (hrpow_mono _ _ (by linarith)).trans (hbushS p hp)
  · intro p e e' he he' hne
    exact h.D_sep p e e' (hSD he) (hSD he') hne
  · intro p hp u hu ρ hρ
    have hsub : (bushOf S p).filter (fun e => dist e u ≤ ρ) ⊆
        (bushOf D p).filter (fun e => dist e u ≤ ρ) := by
      apply Finset.filter_subset_filter
      intro e he
      exact mem_bushOf.mpr (hSD (mem_bushOf.mp he))
    have h1 := (by exact_mod_cast Finset.card_le_card hsub :
      (((bushOf S p).filter (fun e => dist e u ≤ ρ)).card : ℝ) ≤
        ((bushOf D p).filter (fun e => dist e u ≤ ρ)).card)
    have hρr : 0 ≤ (ρ / r) ^ s := Real.rpow_nonneg (div_nonneg (hr.le.trans hρ) hr.le) _
    calc _ ≤ _ := h1
      _ ≤ r ^ (-η) * (ρ / r) ^ s := h.D_kt p (hQP hp) u hu ρ hρ
      _ ≤ r ^ (-(3 * η + 2 * ε)) * (ρ / r) ^ s :=
        mul_le_mul_of_nonneg_right (hrpow_mono _ _ (by linarith)) hρr
  · intro J hJ hsep
    exact h.few_lines J (hJ.trans hSD) hsep

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
