-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.Classes.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_intermediate_twist_normalization.FarRows
import Submission.WZ.Obl.wz_intermediate_twist_normalization.NormTube

/-!
# Classes of tubes

With `b = 100 / c²`, a tube belongs to the class `(⌊icX / b⌋, ⌊slX / b⌋)`. The enlarged class
`clSet k` of an index `k` consists of the tubes whose index differs from `k` by at most `2` in
the first and `1` in the second coordinate; its tubes lie within `300 / c²` and `200 / c²` of
the reference line `clα k + clβ k z`.

Two tubes whose slopes differ by less than `b` and whose twisted centres come close
(`Z2` nonempty) lie in a common enlarged class (`mem_clSet_of_near`), and each tube belongs to
at most `15` enlarged classes (`sum_card_clSet_le`).
-/

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_small_twist_projection_estimate (Space tube SlopeN lineAt Xc slX icX
  Zset Zset_sub abs_slX_le)

/-- The class index of a tube. -/
noncomputable def clIdx (c : ℝ) (x v : Space) : ℤ × ℤ :=
  (⌊icX c x v / (100 / c ^ 2)⌋, ⌊slX c v / (100 / c ^ 2)⌋)

/-- The enlarged class of an index. -/
noncomputable def clSet {n : ℕ} (c : ℝ) (x v : Fin n → Space) (k : ℤ × ℤ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => |(clIdx c (x j) (v j)).1 - k.1| ≤ 2 ∧
    |(clIdx c (x j) (v j)).2 - k.2| ≤ 1)

/-- The reference intercept of an index. -/
noncomputable def clα (c : ℝ) (k : ℤ × ℤ) : ℝ := ((k.1 : ℝ) + 1 / 2) * (100 / c ^ 2)

/-- The reference slope of an index. -/
noncomputable def clβ (c : ℝ) (k : ℤ × ℤ) : ℝ := ((k.2 : ℝ) + 1 / 2) * (100 / c ^ 2)

/-- Floors of nearby reals are close. -/
theorem abs_floor_sub_le {a a' : ℝ} {N : ℤ} (h : |a - a'| ≤ N) : |⌊a⌋ - ⌊a'⌋| ≤ N := by
  have h1 := Int.floor_le a
  have h2 := Int.lt_floor_add_one a
  have h3 := Int.floor_le a'
  have h4 := Int.lt_floor_add_one a'
  obtain ⟨hl, hu⟩ := abs_le.mp h
  have e1 : ((⌊a⌋ - ⌊a'⌋ : ℤ) : ℝ) < N + 1 := by push_cast; linarith
  have e2 : -(N + 1 : ℝ) < ((⌊a⌋ - ⌊a'⌋ : ℤ) : ℝ) := by push_cast; linarith
  have e1' : ⌊a⌋ - ⌊a'⌋ < N + 1 := by exact_mod_cast e1
  have e2' : -(N + 1) < ⌊a⌋ - ⌊a'⌋ := by exact_mod_cast e2
  rw [abs_le]
  constructor <;> omega

theorem b_pos {c : ℝ} (hc : 100 < |c|) : 0 < 100 / c ^ 2 := by
  have : c ≠ 0 := by intro h; rw [h, abs_zero] at hc; linarith
  positivity

/-- The tubes of an enlarged class lie close to its reference line. -/
theorem clSet_bounds {n : ℕ} {c : ℝ} (hc : 100 < |c|) {x v : Fin n → Space} {k : ℤ × ℤ}
    {j : Fin n} (hj : j ∈ clSet c x v k) :
    |icX c (x j) (v j) - clα c k| ≤ 300 / c ^ 2 ∧ |slX c (v j) - clβ c k| ≤ 200 / c ^ 2 := by
  have hb := b_pos hc
  set b := 100 / c ^ 2 with hbdef
  rw [clSet, Finset.mem_filter] at hj
  obtain ⟨-, h1, h2⟩ := hj
  simp only [clIdx] at h1 h2
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  have f1 := Int.floor_le (icX c (x j) (v j) / b)
  have f2 := Int.lt_floor_add_one (icX c (x j) (v j) / b)
  have f3 := Int.floor_le (slX c (v j) / b)
  have f4 := Int.lt_floor_add_one (slX c (v j) / b)
  have k1 : ((⌊icX c (x j) (v j) / b⌋ : ℤ) : ℝ) ≤ k.1 + 2 := by exact_mod_cast (by linarith : _)
  have k2 : (k.1 : ℝ) - 2 ≤ ((⌊icX c (x j) (v j) / b⌋ : ℤ) : ℝ) := by
    exact_mod_cast (by linarith : _)
  have k3 : ((⌊slX c (v j) / b⌋ : ℤ) : ℝ) ≤ k.2 + 1 := by exact_mod_cast (by linarith : _)
  have k4 : (k.2 : ℝ) - 1 ≤ ((⌊slX c (v j) / b⌋ : ℤ) : ℝ) := by exact_mod_cast (by linarith : _)
  have ei : icX c (x j) (v j) = (icX c (x j) (v j) / b) * b := by field_simp
  have es : slX c (v j) = (slX c (v j) / b) * b := by field_simp
  constructor
  · rw [clα, ← hbdef, abs_le]
    have : (300 : ℝ) / c ^ 2 = 3 * b := by rw [hbdef]; ring
    rw [this]
    constructor <;> nlinarith
  · rw [clβ, ← hbdef, abs_le]
    have : (200 : ℝ) / c ^ 2 = 2 * b := by rw [hbdef]; ring
    rw [this]
    constructor <;> nlinarith

theorem mem_clSet_self {n : ℕ} (c : ℝ) (x v : Fin n → Space) (j : Fin n) :
    j ∈ clSet c x v (clIdx c (x j) (v j)) := by
  rw [clSet, Finset.mem_filter]
  simp

/-- The reference slope of the class of a transverse tube is at most `3`. -/
theorem abs_clβ_le {c : ℝ} (hc : 100 < |c|) {x v : Space} (hv : ‖v‖ = 1)
    (hv2 : (1 / 2 : ℝ) ≤ |v 2|) : |clβ c (clIdx c x v)| ≤ 3 := by
  have hb := b_pos hc
  have hc2 : (10000 : ℝ) < c ^ 2 := by
    have := pow_lt_pow_left₀ hc (by norm_num) (two_ne_zero)
    rw [sq_abs] at this; linarith
  have hb1 : 100 / c ^ 2 ≤ 1 / 100 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set b := 100 / c ^ 2 with hbdef
  have hs := abs_slX_le hc hv hv2
  have f3 := Int.floor_le (slX c v / b)
  have f4 := Int.lt_floor_add_one (slX c v / b)
  have es : slX c v = (slX c v / b) * b := by field_simp
  simp only [clβ, clIdx]
  rw [← hbdef]
  have hβ : |((⌊slX c v / b⌋ : ℤ) + 1 / 2 : ℝ) * b - slX c v| ≤ b := by
    rw [abs_le]; constructor <;> nlinarith
  calc |((⌊slX c v / b⌋ : ℤ) + 1 / 2 : ℝ) * b| ≤
        |((⌊slX c v / b⌋ : ℤ) + 1 / 2 : ℝ) * b - slX c v| + |slX c v| := by
        have := abs_add_le (((⌊slX c v / b⌋ : ℤ) + 1 / 2 : ℝ) * b - slX c v) (slX c v)
        rwa [sub_add_cancel] at this
    _ ≤ b + 5 / 2 := by linarith
    _ ≤ 3 := by linarith

/-- **Near pairs share an enlarged class.** -/
theorem mem_clSet_of_near {δ : ℝ} (hδ : 0 < δ) {f : ℝ → ℝ} (hf : SlopeN f)
    (hc : 100 < |f 0|) (hδc : δ * (f 0) ^ 2 ≤ 1) {n : ℕ} {x v : Fin n → Space}
    (hv : ∀ i, ‖v i‖ = 1) (hv2 : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|)
    (hT : ∀ i, tube δ (x i) (v i) ⊆ ball 0 1) {i j : Fin n}
    (hne : (Z2 f δ (x i) (v i) (x j) (v j)).Nonempty)
    (hnear : |slX (f 0) (v i) - slX (f 0) (v j)| < 100 / (f 0) ^ 2) :
    j ∈ clSet (f 0) x v (clIdx (f 0) (x i) (v i)) := by
  set c := f 0 with hcdef
  have hb := b_pos hc
  set b := 100 / c ^ 2 with hbdef
  have hc2 : 0 < c ^ 2 := by
    have : c ≠ 0 := by intro h; rw [h, abs_zero] at hc; linarith
    positivity
  have hrc : 1 ≤ (1 / c ^ 2) * c ^ 2 := by rw [one_div, inv_mul_cancel₀ hc2.ne']
  have hδr : δ ≤ 1 / c ^ 2 := by rw [le_div_iff₀ hc2]; linarith
  obtain ⟨z0, hz0⟩ := hne
  have hZ := Z2_subset_Zset hδ hδr hf hc hrc (hv i) (hv2 i) (hT i) (hv j) (hv2 j) (hT j) hz0
  obtain ⟨hzI, hzX⟩ := hZ
  rw [Zset_sub] at hzX
  have hz1 : |z0| ≤ 1 := abs_le.mpr hzI
  have hicX : |icX c (x i) (v i) - icX c (x j) (v j)| < 2 * b := by
    have h1 : |(slX c (v i) - slX c (v j)) * z0| ≤ |slX c (v i) - slX c (v j)| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hz1
    have h2 := abs_sub (icX c (x i) (v i) - icX c (x j) (v j) +
      (slX c (v i) - slX c (v j)) * z0) ((slX c (v i) - slX c (v j)) * z0)
    rw [add_sub_cancel_right] at h2
    have h3 : 27 * (1 / c ^ 2) = 27 / 100 * b := by rw [hbdef]; ring
    rw [h3] at hzX
    linarith
  rw [clSet, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · simp only [clIdx]
    rw [abs_sub_comm]
    apply abs_floor_sub_le
    rw [← sub_div, abs_div, abs_of_pos hb, div_le_iff₀ hb]
    push_cast
    linarith
  · simp only [clIdx]
    rw [abs_sub_comm]
    apply abs_floor_sub_le
    rw [← sub_div, abs_div, abs_of_pos hb, div_le_iff₀ hb]
    push_cast
    linarith

/-- Each tube belongs to at most `15` enlarged classes. -/
theorem card_clSet_filter_le {n : ℕ} (c : ℝ) (x v : Fin n → Space) (S : Finset (ℤ × ℤ))
    (j : Fin n) : (S.filter (fun k => j ∈ clSet c x v k)).card ≤ 15 := by
  set κ := clIdx c (x j) (v j)
  have hsub : S.filter (fun k => j ∈ clSet c x v k) ⊆
      Finset.Icc (κ.1 - 2) (κ.1 + 2) ×ˢ Finset.Icc (κ.2 - 1) (κ.2 + 1) := by
    intro k hk
    rw [Finset.mem_filter, clSet, Finset.mem_filter] at hk
    obtain ⟨-, -, h1, h2⟩ := hk
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    have h1' := abs_le.mp h1
    have h2' := abs_le.mp h2
    refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  calc (S.filter (fun k => j ∈ clSet c x v k)).card
      ≤ (Finset.Icc (κ.1 - 2) (κ.1 + 2) ×ˢ Finset.Icc (κ.2 - 1) (κ.2 + 1)).card :=
        Finset.card_le_card hsub
    _ = 15 := by
        rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
        have e1 : κ.1 + 2 + 1 - (κ.1 - 2) = 5 := by ring
        have e2 : κ.2 + 1 + 1 - (κ.2 - 1) = 3 := by ring
        rw [e1, e2]
        rfl

/-- The enlarged classes cover each tube at most `15` times. -/
theorem sum_card_clSet_le {n : ℕ} (c : ℝ) (x v : Fin n → Space) (S : Finset (ℤ × ℤ)) :
    ∑ k ∈ S, ((clSet c x v k).card : ℝ) ≤ 15 * n := by
  classical
  have h : ∑ k ∈ S, (clSet c x v k).card =
      ∑ j : Fin n, (S.filter (fun k => j ∈ clSet c x v k)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [clSet]
    simp only [Finset.sum_filter, Finset.mem_filter, Finset.mem_univ, true_and]
  have h2 : ∑ j : Fin n, (S.filter (fun k => j ∈ clSet c x v k)).card ≤ 15 * n := by
    calc ∑ j : Fin n, (S.filter (fun k => j ∈ clSet c x v k)).card
        ≤ ∑ _j : Fin n, 15 := Finset.sum_le_sum fun j _ => card_clSet_filter_le c x v S j
      _ = 15 * n := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
          mul_comm]
  have h3 : (∑ k ∈ S, (clSet c x v k).card : ℕ) ≤ 15 * n := h ▸ h2
  exact_mod_cast h3

end WangZahlLot.Obl.wz_intermediate_twist_normalization
