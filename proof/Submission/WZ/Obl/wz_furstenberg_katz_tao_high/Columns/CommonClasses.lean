-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns.CommonClasses.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.ClassPairs

/-!
# Common line classes of two pins, at a general bush exponent

The accepted `ClassPairs` module of o213 bounds the number of line classes containing two
given pins for `1/2`-Katz–Tao bushes.  Here the same geometry is used with bushes that are
Katz–Tao with an arbitrary exponent `s ≥ 0` and constant `K`:

* `shared_normals_two_caps`: the normals at `p` of the labels whose class also contains a pin
  `p'` at distance `d ≥ 40 r` lie in the two caps of radius `91 r / d` around `± e₁`
  (exponent free);
* `common_classes_le_rpow`: for any two pins, the number of common classes is at most
  `2 K (91 / max (dist p p') (40 r)) ^ s`.

These are the pair bounds behind the cell energy of `Columns/CellEnergy.lean`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

/-- The shared normals of two pins at distance `d ≥ 40 r` lie in two caps of radius
`91 r / d` around a unit vector and its opposite. -/
theorem shared_normals_two_caps {r : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4)
    {D J₀ : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2}
    (hcls : ∀ q ∈ D, cls q ∈ J₀ ∧ (q = cls q ∨ ¬ StripSep r q (cls q) ∨ ¬ StripSep r (cls q) q))
    (hJ₀ : J₀ ⊆ D) (hnorm : ∀ q ∈ D, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1)
    {p p' : E2} (hp4 : ‖p‖ ≤ 4) (hp'4 : ‖p'‖ ≤ 4) (hfar : 40 * r ≤ dist p p') :
    ∃ e₁ : E2, ‖e₁‖ = 1 ∧ sharedNormals D cls p p' ⊆
      ((bushOf D p).filter (fun e => dist e e₁ ≤ 91 * r / dist p p')) ∪
        ((bushOf D p).filter (fun e => dist e (-e₁) ≤ 91 * r / dist p p')) := by
  classical
  set d' := dist p p' with hd'
  have hd'pos : 0 < d' := lt_of_lt_of_le (by positivity) hfar
  have hd'8 : d' ≤ 8 := by
    rw [hd', dist_eq_norm]
    calc ‖p - p'‖ ≤ ‖p‖ + ‖p'‖ := norm_sub_le _ _
      _ ≤ 8 := by linarith
  by_cases hE : sharedNormals D cls p p' = ∅
  · obtain ⟨u, hu⟩ : ∃ u : E2, ‖u‖ = 1 := exists_norm_eq E2 zero_le_one
    exact ⟨u, hu, by rw [hE]; exact Finset.empty_subset _⟩
  obtain ⟨e₁, he₁⟩ := Finset.nonempty_iff_ne_empty.mpr hE
  have he₁u : ‖e₁‖ = 1 := (hnorm _ (mem_bushOf.mp (Finset.mem_filter.mp he₁).1)).2
  refine ⟨e₁, he₁u, ?_⟩
  set ρ := 91 * r / d' with hρ
  intro e he
  have heu : ‖e‖ = 1 := (hnorm _ (mem_bushOf.mp (Finset.mem_filter.mp he).1)).2
  have hb : e ∈ bushOf D p := (Finset.mem_filter.mp he).1
  have h1 := shared_inner_lt hr hcls hJ₀ hnorm he
  have h2 := shared_inner_lt hr hcls hJ₀ hnorm he₁
  have hvlen : d' ≤ ‖p - p'‖ := by rw [hd', dist_eq_norm]
  have hsmall : ((18 * r + d' * r) / d') ^ 2 ≤ 1 / 2 := by
    have hq : (18 * r + d' * r) / d' ≤ 7 / 10 := by
      rw [div_le_iff₀ hd'pos]; nlinarith
    have hq0 : 0 ≤ (18 * r + d' * r) / d' := by positivity
    nlinarith
  rw [← hd'] at h1 h2
  have hcl := normals_close_of_long_vector hd'pos heu he₁u hvlen h1 h2 hsmall hsmall
  have hbound : 3 * (((18 * r + d' * r) + (18 * r + d' * r)) / d') ^ 2 ≤ ρ ^ 2 := by
    have hdr : d' * r ≤ 8 * r := by nlinarith
    have ha0 : 0 ≤ (18 * r + d' * r) + (18 * r + d' * r) := by positivity
    have ha1 : (18 * r + d' * r) + (18 * r + d' * r) ≤ 52 * r := by linarith
    have hsq : ((18 * r + d' * r) + (18 * r + d' * r)) ^ 2 ≤ (52 * r) ^ 2 :=
      pow_le_pow_left₀ ha0 ha1 2
    have hnum : 3 * ((18 * r + d' * r) + (18 * r + d' * r)) ^ 2 ≤ (91 * r) ^ 2 := by
      nlinarith
    rw [hρ, div_pow, div_pow, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hnum (by positivity)
  have hρ0 : 0 ≤ ρ := by positivity
  rcases hcl with h | h
  · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hb, ?_⟩)
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (e - e₁), sq_nonneg (‖e - e₁‖ - ρ)]
  · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hb, ?_⟩)
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (e - -e₁), sq_nonneg (‖e - -e₁‖ - ρ)]

/-- The number of common classes of two far pins, for `(K, s)`-Katz–Tao bushes. -/
theorem shared_card_far_rpow {r s K : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4)
    {D J₀ : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2}
    (hcls : ∀ q ∈ D, cls q ∈ J₀ ∧ (q = cls q ∨ ¬ StripSep r q (cls q) ∨ ¬ StripSep r (cls q) q))
    (hJ₀ : J₀ ⊆ D) (hnorm : ∀ q ∈ D, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1)
    {P : Finset E2}
    (hDkt : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      (((bushOf D p).filter (fun e => dist e u ≤ ρ)).card : ℝ) ≤ K * (ρ / r) ^ s)
    {p p' : E2} (hp : p ∈ P) (hp4 : ‖p‖ ≤ 4) (hp'4 : ‖p'‖ ≤ 4) (hfar : 40 * r ≤ dist p p') :
    ((sharedNormals D cls p p').card : ℝ) ≤ 2 * (K * (91 / dist p p') ^ s) := by
  classical
  obtain ⟨e₁, he₁u, hcover⟩ := shared_normals_two_caps hr hr4 hcls hJ₀ hnorm hp4 hp'4 hfar
  set d' := dist p p' with hd'
  have hd'pos : 0 < d' := lt_of_lt_of_le (by positivity) hfar
  have hd'8 : d' ≤ 8 := by
    rw [hd', dist_eq_norm]
    calc ‖p - p'‖ ≤ ‖p‖ + ‖p'‖ := norm_sub_le _ _
      _ ≤ 8 := by linarith
  have hρr : r ≤ 91 * r / d' := by
    rw [le_div_iff₀ hd'pos]; nlinarith
  have hneg : ‖-e₁‖ = 1 := by rw [norm_neg, he₁u]
  have e1 : (91 * r / d') / r = 91 / d' := by field_simp
  calc ((sharedNormals D cls p p').card : ℝ)
      ≤ (((bushOf D p).filter (fun e => dist e e₁ ≤ 91 * r / d')) ∪
          ((bushOf D p).filter (fun e => dist e (-e₁) ≤ 91 * r / d'))).card := by
        exact_mod_cast Finset.card_le_card hcover
    _ ≤ (((bushOf D p).filter (fun e => dist e e₁ ≤ 91 * r / d')).card : ℝ) +
          (((bushOf D p).filter (fun e => dist e (-e₁) ≤ 91 * r / d')).card : ℝ) := by
        exact_mod_cast Finset.card_union_le _ _
    _ ≤ K * ((91 * r / d') / r) ^ s + K * ((91 * r / d') / r) ^ s :=
        add_le_add (hDkt p hp e₁ he₁u _ hρr) (hDkt p hp (-e₁) hneg _ hρr)
    _ = 2 * (K * (91 / d') ^ s) := by rw [e1]; ring

/-- **Common classes of two pins** at a general bush exponent: for every pin `p` of `P` and
every `p'` of norm at most `4`, at most `2 K (91 / max (dist p p') (40 r)) ^ s` classes contain
both. -/
theorem common_classes_le_rpow {r s K : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4) (hs : 0 ≤ s)
    {D J₀ : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2}
    (hcls : ∀ q ∈ D, cls q ∈ J₀ ∧ (q = cls q ∨ ¬ StripSep r q (cls q) ∨ ¬ StripSep r (cls q) q))
    (hJ₀ : J₀ ⊆ D) (hnorm : ∀ q ∈ D, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1)
    {P : Finset E2}
    (hDkt : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      (((bushOf D p).filter (fun e => dist e u ≤ ρ)).card : ℝ) ≤ K * (ρ / r) ^ s)
    {p p' : E2} (hp : p ∈ P) (hp4 : ‖p‖ ≤ 4) (hp'4 : ‖p'‖ ≤ 4) :
    ((J₀.filter (fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j)).card : ℝ) ≤
      2 * K * (91 / max (dist p p') (40 * r)) ^ s := by
  classical
  have hc := common_classes_le_shared D J₀ cls p p'
  have hcR : ((J₀.filter (fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j)).card : ℝ) ≤
      ((sharedNormals D cls p p').card : ℝ) := by exact_mod_cast hc
  refine hcR.trans ?_
  by_cases hfar : 40 * r ≤ dist p p'
  · have h := shared_card_far_rpow hr hr4 hcls hJ₀ hnorm hDkt hp hp4 hp'4 hfar
    rw [max_eq_left hfar]
    linarith
  · push Not at hfar
    obtain ⟨u, hu⟩ : ∃ u : E2, ‖u‖ = 1 := exists_norm_eq E2 zero_le_one
    have hall : sharedNormals D cls p p' ⊆ (bushOf D p).filter (fun e => dist e u ≤ 2) := by
      intro e he
      have hb : e ∈ bushOf D p := (Finset.mem_filter.mp he).1
      have heu : ‖e‖ = 1 := (hnorm _ (mem_bushOf.mp hb)).2
      refine Finset.mem_filter.mpr ⟨hb, ?_⟩
      rw [dist_eq_norm]
      calc ‖e - u‖ ≤ ‖e‖ + ‖u‖ := norm_sub_le _ _
        _ = 2 := by rw [heu, hu]; norm_num
    have hkt := hDkt p hp u hu 2 (by linarith)
    have hc1 : ((sharedNormals D cls p p').card : ℝ) ≤
        (((bushOf D p).filter (fun e => dist e u ≤ 2)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hall
    have hK : 0 ≤ K := by
      have h0 : (0 : ℝ) ≤ (((bushOf D p).filter (fun e => dist e u ≤ 2)).card : ℝ) :=
        Nat.cast_nonneg _
      have hpos : 0 < (2 / r) ^ s := Real.rpow_pos_of_pos (by positivity) s
      by_contra hneg
      push Not at hneg
      have : K * (2 / r) ^ s < 0 := mul_neg_of_neg_of_pos hneg hpos
      linarith
    rw [max_eq_right hfar.le]
    have hmono : (2 / r) ^ s ≤ (91 / (40 * r)) ^ s := by
      apply Real.rpow_le_rpow (by positivity) _ hs
      rw [div_le_div_iff₀ hr (by positivity)]
      nlinarith
    calc ((sharedNormals D cls p p').card : ℝ) ≤ K * (2 / r) ^ s := hc1.trans hkt
      _ ≤ K * (91 / (40 * r)) ^ s := mul_le_mul_of_nonneg_left hmono hK
      _ ≤ 2 * K * (91 / (40 * r)) ^ s := by
          have : 0 ≤ K * (91 / (40 * r)) ^ s :=
            mul_nonneg hK (Real.rpow_nonneg (by positivity) s)
          linarith

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

/-- **Common classes for an arbitrary cap bound.**  If every cap of radius `ρ ≥ r` of a bush of
`P` holds at most `Bd ρ` normals, with `Bd` monotone on `[r, ∞)`, then two pins of norm at most
`4` share at most `2 Bd (91 r / max (dist p p') (40 r))` classes. -/
theorem common_classes_le_capBound {r : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4)
    {D J₀ : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2}
    (hcls : ∀ q ∈ D, cls q ∈ J₀ ∧ (q = cls q ∨ ¬ StripSep r q (cls q) ∨ ¬ StripSep r (cls q) q))
    (hJ₀ : J₀ ⊆ D) (hnorm : ∀ q ∈ D, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1)
    {P : Finset E2} (Bd : ℝ → ℝ) (hBd : ∀ ρ ρ', r ≤ ρ → ρ ≤ ρ' → Bd ρ ≤ Bd ρ')
    (hcap : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      (((bushOf D p).filter (fun e => dist e u ≤ ρ)).card : ℝ) ≤ Bd ρ)
    {p p' : E2} (hp : p ∈ P) (hp4 : ‖p‖ ≤ 4) (hp'4 : ‖p'‖ ≤ 4) :
    ((J₀.filter (fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j)).card : ℝ) ≤
      2 * Bd (91 * r / max (dist p p') (40 * r)) := by
  classical
  have hc := common_classes_le_shared D J₀ cls p p'
  have hcR : ((J₀.filter (fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j)).card : ℝ) ≤
      ((sharedNormals D cls p p').card : ℝ) := by exact_mod_cast hc
  refine hcR.trans ?_
  have hBd0 : ∀ ρ, r ≤ ρ → 0 ≤ Bd ρ := by
    intro ρ hρ
    obtain ⟨u, hu⟩ : ∃ u : E2, ‖u‖ = 1 := exists_norm_eq E2 zero_le_one
    exact le_trans (Nat.cast_nonneg _) (hcap p hp u hu ρ hρ)
  by_cases hfar : 40 * r ≤ dist p p'
  · obtain ⟨e₁, he₁u, hcover⟩ := shared_normals_two_caps hr hr4 hcls hJ₀ hnorm hp4 hp'4 hfar
    have hd'pos : 0 < dist p p' := lt_of_lt_of_le (by positivity) hfar
    have hd'8 : dist p p' ≤ 8 := by
      rw [dist_eq_norm]
      calc ‖p - p'‖ ≤ ‖p‖ + ‖p'‖ := norm_sub_le _ _
        _ ≤ 8 := by linarith
    have hρr : r ≤ 91 * r / dist p p' := by
      rw [le_div_iff₀ hd'pos]; nlinarith
    have hneg : ‖-e₁‖ = 1 := by rw [norm_neg, he₁u]
    rw [max_eq_left hfar]
    calc ((sharedNormals D cls p p').card : ℝ)
        ≤ (((bushOf D p).filter (fun e => dist e e₁ ≤ 91 * r / dist p p')) ∪
            ((bushOf D p).filter (fun e => dist e (-e₁) ≤ 91 * r / dist p p'))).card := by
          exact_mod_cast Finset.card_le_card hcover
      _ ≤ (((bushOf D p).filter (fun e => dist e e₁ ≤ 91 * r / dist p p')).card : ℝ) +
            (((bushOf D p).filter (fun e => dist e (-e₁) ≤ 91 * r / dist p p')).card : ℝ) := by
          exact_mod_cast Finset.card_union_le _ _
      _ ≤ Bd (91 * r / dist p p') + Bd (91 * r / dist p p') :=
          add_le_add (hcap p hp e₁ he₁u _ hρr) (hcap p hp (-e₁) hneg _ hρr)
      _ = 2 * Bd (91 * r / dist p p') := by ring
  · push Not at hfar
    obtain ⟨u, hu⟩ : ∃ u : E2, ‖u‖ = 1 := exists_norm_eq E2 zero_le_one
    have hall : sharedNormals D cls p p' ⊆ (bushOf D p).filter (fun e => dist e u ≤ 2) := by
      intro e he
      have hb : e ∈ bushOf D p := (Finset.mem_filter.mp he).1
      have heu : ‖e‖ = 1 := (hnorm _ (mem_bushOf.mp hb)).2
      refine Finset.mem_filter.mpr ⟨hb, ?_⟩
      rw [dist_eq_norm]
      calc ‖e - u‖ ≤ ‖e‖ + ‖u‖ := norm_sub_le _ _
        _ = 2 := by rw [heu, hu]; norm_num
    have hc1 : ((sharedNormals D cls p p').card : ℝ) ≤
        (((bushOf D p).filter (fun e => dist e u ≤ 2)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hall
    rw [max_eq_right hfar.le]
    have h91 : 91 * r / (40 * r) = 91 / 40 := by field_simp
    rw [h91]
    have hmono : Bd 2 ≤ Bd (91 / 40) := hBd 2 (91 / 40) (by linarith) (by norm_num)
    have h2 : 0 ≤ Bd (91 / 40) := hBd0 _ (by linarith)
    calc ((sharedNormals D cls p p').card : ℝ) ≤ Bd 2 := hc1.trans (hcap p hp u hu 2 (by linarith))
      _ ≤ Bd (91 / 40) := hmono
      _ ≤ 2 * Bd (91 / 40) := by linarith

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns
