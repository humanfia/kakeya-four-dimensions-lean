-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.Config.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0675 High/Config.lean (b19b589).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.ConfigTools

/-!
# The configuration leaf

`configLeaf`: `ConfigLeaf s` for `0 < s < 1`. From a failed configuration `(P, D)`:

1. the lines `J₀` and the class map `cls` (`lines_exist`), and the tubes at every palette
   scale (`exists_coarse_tubes`);
2. a first regularization balances the classes (`S₁ ⊆ D`);
3. the labels whose line has too many pins near them at some dyadic scale are few (Markov
   over the scales, x0672's `bad_labels_weight_le` with the energy bound `fcls_upper`):
   `|Bad| ≤ |S₁| / 4`; they are removed together with the pins that lost more than half of
   their bush (`keptLabels`, `FailData.prune`);
4. a second regularization balances every palette map (`cfgMaps`), giving `S₃`.

The pins of a line of `S₃` are `(1 - s)`-Frostman because they are so in `S₁` and the class
sizes of `S₁` and `S₃` are comparable by the two balances (`near_le_of_good`).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_tower_balanced_refinement

noncomputable section

/-! ### The maps balanced by the final regularization -/

/-- Codomains of the configuration maps. -/
def cfgY (n : ℕ) : Fin 12 × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) → Type :=
  fun i => ![E2 × E2, ℤ × ℤ, ℤ × ℤ, E2 × E2, E2 × (ℤ × ℤ), E2 × (E2 × E2),
    (ℤ × ℤ) × (E2 × E2), (ℤ × ℤ) × (ℤ × ℤ), (ℤ × ℤ) × (E2 × E2), E2 × E2, E2 × (E2 × E2),
    (ℤ × ℤ) × (E2 × E2)] i.1

/-- The configuration maps: class, cell, arc, tube, (pin, arc), (pin, tube), (cell, class),
(cell, arc), (cell, tube), composed tube, (pin, composed tube), (cell, composed tube), at all
palette scales. -/
def cfgMaps (r : ℝ) (n : ℕ) (cls : E2 × E2 → E2 × E2) (tb : ℕ → E2 × E2 → E2 × E2) :
    ∀ i : Fin 12 × Fin (n + 1) × Fin (n + 1) × Fin (n + 1), E2 × E2 → cfgY n i
  | ⟨0, _, _, _⟩ => fun q => cls q
  | ⟨1, i, _, _⟩ => fun q => cellOf (palScale r n i) q.1
  | ⟨2, _, j, _⟩ => fun q => arcOf (palScale r n j) q.2
  | ⟨3, _, j, _⟩ => fun q => tb j (cls q)
  | ⟨4, _, j, _⟩ => fun q => (q.1, arcOf (palScale r n j) q.2)
  | ⟨5, _, j, _⟩ => fun q => (q.1, tb j (cls q))
  | ⟨6, i, _, _⟩ => fun q => (cellOf (palScale r n i) q.1, cls q)
  | ⟨7, i, j, _⟩ => fun q => (cellOf (palScale r n i) q.1, arcOf (palScale r n j) q.2)
  | ⟨8, i, j, _⟩ => fun q => (cellOf (palScale r n i) q.1, tb j (cls q))
  | ⟨9, h, a, _⟩ => fun q => tb h (tb a (cls q))
  | ⟨10, h, a, _⟩ => fun q => (q.1, tb h (tb a (cls q)))
  | ⟨11, h, a, i⟩ => fun q => (cellOf (palScale r n i) q.1, tb h (tb a (cls q)))

noncomputable scoped instance cfgY.decEq {n : ℕ} : ∀ i, DecidableEq (cfgY n i)
  | ⟨0, _, _, _⟩ => inferInstanceAs (DecidableEq (E2 × E2))
  | ⟨1, _, _, _⟩ => inferInstanceAs (DecidableEq (ℤ × ℤ))
  | ⟨2, _, _, _⟩ => inferInstanceAs (DecidableEq (ℤ × ℤ))
  | ⟨3, _, _, _⟩ => inferInstanceAs (DecidableEq (E2 × E2))
  | ⟨4, _, _, _⟩ => inferInstanceAs (DecidableEq (E2 × (ℤ × ℤ)))
  | ⟨5, _, _, _⟩ => inferInstanceAs (DecidableEq (E2 × (E2 × E2)))
  | ⟨6, _, _, _⟩ => inferInstanceAs (DecidableEq ((ℤ × ℤ) × (E2 × E2)))
  | ⟨7, _, _, _⟩ => inferInstanceAs (DecidableEq ((ℤ × ℤ) × (ℤ × ℤ)))
  | ⟨8, _, _, _⟩ => inferInstanceAs (DecidableEq ((ℤ × ℤ) × (E2 × E2)))
  | ⟨9, _, _, _⟩ => inferInstanceAs (DecidableEq (E2 × E2))
  | ⟨10, _, _, _⟩ => inferInstanceAs (DecidableEq (E2 × (E2 × E2)))
  | ⟨11, _, _, _⟩ => inferInstanceAs (DecidableEq ((ℤ × ℤ) × (E2 × E2)))

/-! ### Bad labels -/

/-- The labels whose class has more than `Bt (r 2 ^ k) ^ (1 - s)` times its size within
`r 2 ^ k` of their point, at some `k ≤ K₀`. -/
def badLabels (S : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2) (r s Bt : ℝ) (K₀ : ℕ) :
    Finset (E2 × E2) :=
  S.filter (fun q => ∃ k ≤ K₀, Bt * (r * 2 ^ k) ^ (1 - s) * (classSize S cls q : ℝ) <
    ((nearClass S cls q (r * 2 ^ k)).card : ℝ))

theorem badLabels_card {r s ε₀ η K Bt : ℝ} {P : Finset E2} {D S₁ : Finset (E2 × E2)}
    (h : FailData r s ε₀ η P D) (hs0 : 0 ≤ s) (hs1 : s < 1) (hr : r ≤ 1 / 100) (hη : 0 < η)
    {cls : E2 × E2 → E2 × E2}
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
      (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r))
    (hS₁ : S₁ ⊆ D) (hbal : Balanced S₁ cls K) (hK : 0 ≤ K) (hBt : 0 < Bt) (K₀ : ℕ) :
    ((badLabels S₁ cls r s Bt K₀).card : ℝ) * S₁.card ≤
      (K₀ + 1) * (10 ^ 4 / (1 - (1 / 2 : ℝ) ^ (1 - s)) * r ^ (-2 - 4 * η)) / Bt *
        (K * (S₁.image cls).card) := by
  have hr0 := h.r_pos
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 10 ^ 4 / (1 - (1 / 2 : ℝ) ^ (1 - s)) * r ^ (-2 - 4 * η) :=
    ⟨_, rfl⟩
  rw [← hA]
  have hT : ∀ k : ℕ, 0 < Bt * (r * 2 ^ k) ^ (1 - s) := fun k => by positivity
  have hS4 : ∀ q ∈ S₁, ‖q.1‖ ≤ 4 := fun q hq => h.P_norm _ (h.D_mem q (hS₁ hq)).1
  have hgeo' : ∀ q ∈ S₁, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
      (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r) := fun q hq => hgeo q (hS₁ hq)
  have henergy : ∀ k ≤ K₀, (((sameClass S₁ cls).filter
      (fun qq => dist qq.1.1 qq.2.1 < r * 2 ^ k)).card : ℝ) ≤ A * (r * 2 ^ k) ^ (1 - s) := by
    intro k _
    have hk : r ≤ r * 2 ^ k := by
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      nlinarith
    rw [hA]
    apply fcls_upper h hs0 hs1 hr hη hk
    intro qq hqq
    obtain ⟨h1, h2, h3, h4, h5⟩ := cls_mem_pairs hS4 hgeo' hqq
    exact ⟨hS₁ h1, hS₁ h2, h3, h4, h5⟩
  have hw := bad_labels_weight_le S₁ cls (r := r) K₀ (fun k => A * (r * 2 ^ k) ^ (1 - s))
    (fun k => Bt * (r * 2 ^ k) ^ (1 - s)) hT henergy
  have hterm : ∀ k : ℕ, A * (r * 2 ^ k) ^ (1 - s) / (Bt * (r * 2 ^ k) ^ (1 - s)) = A / Bt := by
    intro k
    have hpos : 0 < (r * 2 ^ k) ^ (1 - s) := by positivity
    field_simp
  have hsum : ∑ k ∈ Finset.range (K₀ + 1), A * (r * 2 ^ k) ^ (1 - s) /
      (Bt * (r * 2 ^ k) ^ (1 - s)) = (K₀ + 1) * (A / Bt) := by
    rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    push_cast; ring
  have hw' : ∑ q ∈ badLabels S₁ cls r s Bt K₀, (classSize S₁ cls q : ℝ) ≤
      (K₀ + 1) * (A / Bt) := by
    rw [← hsum]
    exact hw
  -- each bad label has class size at least `|S₁| / (K #classes)`
  have hlow : ∀ q ∈ badLabels S₁ cls r s Bt K₀,
      (S₁.card : ℝ) ≤ K * (S₁.image cls).card * (classSize S₁ cls q : ℝ) :=
    fun q hq => card_le_balanced hbal (Finset.mem_filter.mp hq).1
  calc ((badLabels S₁ cls r s Bt K₀).card : ℝ) * S₁.card
      = ∑ _q ∈ badLabels S₁ cls r s Bt K₀, (S₁.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ q ∈ badLabels S₁ cls r s Bt K₀, K * (S₁.image cls).card * (classSize S₁ cls q : ℝ) :=
        Finset.sum_le_sum hlow
    _ = K * (S₁.image cls).card * ∑ q ∈ badLabels S₁ cls r s Bt K₀, (classSize S₁ cls q : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ K * (S₁.image cls).card * ((K₀ + 1) * (A / Bt)) := by
        apply mul_le_mul_of_nonneg_left hw'
        positivity
    _ = (K₀ + 1) * A / Bt * (K * (S₁.image cls).card) := by ring

/-! ### The Frostman bound of the pins of a line -/

theorem near_le_of_good {r s κ Bt X K₁ K₃ c : ℝ} {S₁ S₃ : Finset (E2 × E2)}
    {cls : E2 × E2 → E2 × E2} {K₀ : ℕ} {q : E2 × E2}
    (hr : 0 < r) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hS₃ : S₃ ⊆ S₁) (hq : q ∈ S₃)
    (hgood : ∀ k ≤ K₀, ((nearClass S₁ cls q (r * 2 ^ k)).card : ℝ) ≤
      Bt * (r * 2 ^ k) ^ (1 - s) * (classSize S₁ cls q : ℝ))
    (hK₀ : Real.logb 2 (8 / r) ≤ K₀)
    (hcls1 : (classSize S₁ cls q : ℝ) * (S₁.image cls).card ≤ K₁ * S₁.card)
    (hcls3 : (S₃.card : ℝ) ≤ K₃ * (S₃.image cls).card * (classSize S₃ cls q : ℝ))
    (hsize : (S₁.card : ℝ) ≤ X * S₃.card)
    (hBt : 0 ≤ Bt) (hX : 0 ≤ X) (hK₁ : 0 ≤ K₁) (hK₃ : 0 ≤ K₃)
    (hconst : 2 * Bt * K₁ * X * K₃ ≤ r ^ (-κ)) (hκ1 : 1 ≤ r ^ (-κ)) (hc : r ≤ c) :
    (((S₃.filter (fun q' => cls q' = cls q)).filter (fun q' => dist q'.1 q.1 < c)).card : ℝ) ≤
      r ^ (-κ) * c ^ (1 - s) * (S₃.filter (fun q' => cls q' = cls q)).card := by
  have hc0 : 0 < c := hr.trans_le hc
  have hcl0 : (0 : ℝ) ≤ (S₃.filter (fun q' => cls q' = cls q)).card := Nat.cast_nonneg _
  have hsub : ((S₃.filter (fun q' => cls q' = cls q)).filter (fun q' => dist q'.1 q.1 < c)) ⊆
      S₃.filter (fun q' => cls q' = cls q) := Finset.filter_subset _ _
  have hle := Finset.card_le_card hsub
  rcases le_or_gt 1 c with hc1 | hc1
  · -- `c ≥ 1`: trivial
    have h1 : 1 ≤ c ^ (1 - s) := Real.one_le_rpow hc1 (by linarith)
    have h2 : 1 ≤ r ^ (-κ) * c ^ (1 - s) := by nlinarith
    calc ((((S₃.filter (fun q' => cls q' = cls q)).filter
            (fun q' => dist q'.1 q.1 < c)).card : ℝ))
        ≤ (S₃.filter (fun q' => cls q' = cls q)).card := by exact_mod_cast hle
      _ = 1 * (S₃.filter (fun q' => cls q' = cls q)).card := by ring
      _ ≤ r ^ (-κ) * c ^ (1 - s) * (S₃.filter (fun q' => cls q' = cls q)).card :=
          mul_le_mul_of_nonneg_right h2 hcl0
  · -- `r ≤ c < 1`: the dyadic scale `r 2 ^ k ∈ [c, 2 c)`
    have hcr : 0 < c / r := div_pos hc0 hr
    have hlb0 : 0 ≤ Real.logb 2 (c / r) := by
      apply Real.logb_nonneg (by norm_num)
      rw [le_div_iff₀ hr]; linarith
    set k := ⌈Real.logb 2 (c / r)⌉₊ with hk
    have hkK : k ≤ K₀ := by
      apply Nat.ceil_le.mpr
      refine le_trans ?_ hK₀
      apply Real.logb_le_logb_of_le (by norm_num) hcr
      exact div_le_div_of_nonneg_right (by linarith) hr.le
    have h2k : (2 : ℝ) ^ (k : ℝ) = 2 ^ k := Real.rpow_natCast 2 k
    have hup : c ≤ r * 2 ^ k := by
      have h1 : c / r = 2 ^ (Real.logb 2 (c / r)) :=
        (Real.rpow_logb (by norm_num) (by norm_num) hcr).symm
      have h2 : (2 : ℝ) ^ (Real.logb 2 (c / r)) ≤ 2 ^ (k : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
      rw [h2k] at h2
      have h3 : c / r ≤ 2 ^ k := h1 ▸ h2
      rw [div_le_iff₀ hr] at h3
      linarith
    have hdown : r * 2 ^ k ≤ 2 * c := by
      have h1 : (k : ℝ) < Real.logb 2 (c / r) + 1 := Nat.ceil_lt_add_one hlb0
      have h2 : (2 : ℝ) ^ (k : ℝ) ≤ 2 ^ (Real.logb 2 (c / r) + 1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h1.le
      rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hcr,
        Real.rpow_one, h2k] at h2
      have h3 : r * 2 ^ k ≤ r * (c / r * 2) := mul_le_mul_of_nonneg_left h2 hr.le
      have h4 : r * (c / r * 2) = 2 * c := by field_simp
      linarith
    -- the near pins of `S₃` are near pins of `S₁` at the scale `r 2 ^ k`
    have hsub2 : ((S₃.filter (fun q' => cls q' = cls q)).filter
        (fun q' => dist q'.1 q.1 < c)) ⊆ nearClass S₁ cls q (r * 2 ^ k) := by
      intro q' hq'
      simp only [Finset.mem_filter] at hq'
      simp only [nearClass, Finset.mem_filter]
      refine ⟨hS₃ hq'.1.1, hq'.1.2, ?_⟩
      rw [dist_comm]
      linarith [hq'.2]
    have hnear0 : ((((S₃.filter (fun q' => cls q' = cls q)).filter
        (fun q' => dist q'.1 q.1 < c)).card : ℝ)) ≤ (nearClass S₁ cls q (r * 2 ^ k)).card := by
      exact_mod_cast Finset.card_le_card hsub2
    have hnear := hnear0.trans (hgood k hkK)
    -- `(r 2 ^ k) ^ (1 - s) ≤ 2 c ^ (1 - s)`
    have hpow : (r * 2 ^ k) ^ (1 - s) ≤ 2 * c ^ (1 - s) := by
      have h1 : (r * 2 ^ k) ^ (1 - s) ≤ (2 * c) ^ (1 - s) :=
        Real.rpow_le_rpow (by positivity) hdown (by linarith)
      rw [Real.mul_rpow (by norm_num) hc0.le] at h1
      have h2 : (2 : ℝ) ^ (1 - s) ≤ 2 := by
        calc (2 : ℝ) ^ (1 - s) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 2 := Real.rpow_one 2
      have h3 : 0 ≤ c ^ (1 - s) := Real.rpow_nonneg hc0.le _
      nlinarith
    -- class sizes: `classSize S₁ ≤ K₁ X K₃ classSize S₃`
    have hq1 : q ∈ S₁ := hS₃ hq
    have hN1 : (0 : ℝ) < (S₁.image cls).card := by
      exact_mod_cast Finset.card_pos.mpr ⟨cls q, Finset.mem_image_of_mem cls hq1⟩
    have hN31 : ((S₃.image cls).card : ℝ) ≤ (S₁.image cls).card := by
      exact_mod_cast Finset.card_le_card (Finset.image_subset_image hS₃)
    have hc3 : (0 : ℝ) ≤ (classSize S₃ cls q : ℝ) := Nat.cast_nonneg _
    have hclass : (classSize S₁ cls q : ℝ) ≤ K₁ * X * K₃ * (classSize S₃ cls q : ℝ) := by
      have h1 : (classSize S₁ cls q : ℝ) * (S₁.image cls).card ≤
          K₁ * X * K₃ * (classSize S₃ cls q : ℝ) * (S₁.image cls).card := by
        calc (classSize S₁ cls q : ℝ) * (S₁.image cls).card ≤ K₁ * S₁.card := hcls1
          _ ≤ K₁ * (X * S₃.card) := mul_le_mul_of_nonneg_left hsize hK₁
          _ ≤ K₁ * (X * (K₃ * (S₃.image cls).card * (classSize S₃ cls q : ℝ))) := by
              apply mul_le_mul_of_nonneg_left _ hK₁
              exact mul_le_mul_of_nonneg_left hcls3 hX
          _ ≤ K₁ * (X * (K₃ * (S₁.image cls).card * (classSize S₃ cls q : ℝ))) := by
              apply mul_le_mul_of_nonneg_left _ hK₁
              apply mul_le_mul_of_nonneg_left _ hX
              apply mul_le_mul_of_nonneg_right _ hc3
              exact mul_le_mul_of_nonneg_left hN31 hK₃
          _ = K₁ * X * K₃ * (classSize S₃ cls q : ℝ) * (S₁.image cls).card := by ring
      exact le_of_mul_le_mul_right h1 hN1
    have hcs3 : (classSize S₃ cls q : ℝ) = (S₃.filter (fun q' => cls q' = cls q)).card := rfl
    have hc1s : 0 ≤ c ^ (1 - s) := Real.rpow_nonneg hc0.le _
    calc ((((S₃.filter (fun q' => cls q' = cls q)).filter
            (fun q' => dist q'.1 q.1 < c)).card : ℝ))
        ≤ Bt * (r * 2 ^ k) ^ (1 - s) * (classSize S₁ cls q : ℝ) := hnear
      _ ≤ Bt * (2 * c ^ (1 - s)) * (K₁ * X * K₃ * (classSize S₃ cls q : ℝ)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hpow hBt) hclass (Nat.cast_nonneg _)
          positivity
      _ = (2 * Bt * K₁ * X * K₃) * c ^ (1 - s) * (classSize S₃ cls q : ℝ) := by ring
      _ ≤ r ^ (-κ) * c ^ (1 - s) * (classSize S₃ cls q : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hc3
          exact mul_le_mul_of_nonneg_right hconst hc1s
      _ = r ^ (-κ) * c ^ (1 - s) * (S₃.filter (fun q' => cls q' = cls q)).card := by rw [hcs3]

end

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
