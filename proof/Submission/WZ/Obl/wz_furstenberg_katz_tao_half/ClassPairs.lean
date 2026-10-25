-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.ClassPairs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.HalfExt.Defs

/-!
# Pairs of pins in common line classes

Let `cls` assign to every label of `D` a class in `J₀` from which it is not separated.
`class_pair_bound`: summed over the classes `j`, the number of pairs of pins of `j` at distance
at most `d` is at most `1100 r ^ (-3 η) r⁻¹ (d / r) ^ (1/2)`, for `r ≤ d` (the `1/2`-Katz–Tao
bushes and `1`-Katz–Tao pins of `HalfData`).

Two pins at distance `d'` lie in a common class only through labels `(p, e)` whose normals
are within `91 r / d'` of one direction up to sign (`normals_close_of_long_vector`), so by the
bush bound in at most `2 r ^ (-η) (91 / d') ^ (1/2)` classes; a layer-cake sum over dyadic
shells, with the point bound, gives the `d ^ (1/2)` growth.

This is the `L²` input of the two-ends step (`two_ends_frostman`) in the `s = 1/2` extraction.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

open scoped BigOperators

/-- The pins of the class `j`. -/
noncomputable def pinsOf (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2) (j : E2 × E2) :
    Finset E2 :=
  (D.filter (fun q => cls q = j)).image Prod.fst

theorem mem_pinsOf {D : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2} {j : E2 × E2} {p : E2} :
    p ∈ pinsOf D cls j ↔ ∃ e, (p, e) ∈ D ∧ cls (p, e) = j := by
  classical
  unfold pinsOf
  constructor
  · intro h
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h
    exact ⟨q.2, by simpa using (Finset.mem_filter.mp hq).1, by simpa using (Finset.mem_filter.mp hq).2⟩
  · rintro ⟨e, he, hc⟩
    exact Finset.mem_image.mpr ⟨(p, e), Finset.mem_filter.mpr ⟨he, hc⟩, rfl⟩

/-- The normals at `p` of the labels whose class also contains `p'`. -/
noncomputable def sharedNormals (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2) (p p' : E2) :
    Finset E2 :=
  (bushOf D p).filter (fun e => p' ∈ pinsOf D cls (cls (p, e)))

theorem common_classes_le_shared (D J₀ : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
    (p p' : E2) :
    (J₀.filter (fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j)).card ≤
      (sharedNormals D cls p p').card := by
  classical
  have hsub : J₀.filter (fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j) ⊆
      (sharedNormals D cls p p').image (fun e => cls (p, e)) := by
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    obtain ⟨e, he, hce⟩ := mem_pinsOf.mp hj'.1
    refine Finset.mem_image.mpr ⟨e, ?_, hce⟩
    refine Finset.mem_filter.mpr ⟨mem_bushOf.mpr he, ?_⟩
    rw [hce]; exact hj'.2
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- A shared normal is nearly orthogonal to `p - p'`. -/
theorem shared_inner_lt {r : ℝ} (hr : 0 < r) {D J₀ : Finset (E2 × E2)}
    {cls : E2 × E2 → E2 × E2}
    (hcls : ∀ q ∈ D, cls q ∈ J₀ ∧ (q = cls q ∨ ¬ StripSep r q (cls q) ∨ ¬ StripSep r (cls q) q))
    (hJ₀ : J₀ ⊆ D) (hnorm : ∀ q ∈ D, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1)
    {p p' e : E2} (he : e ∈ sharedNormals D cls p p') :
    |inner ℝ (p - p') e| < 18 * r + dist p p' * r := by
  classical
  have he' := Finset.mem_filter.mp he
  have hpe : (p, e) ∈ D := mem_bushOf.mp he'.1
  obtain ⟨e', hpe', hce'⟩ := mem_pinsOf.mp he'.2
  set j := cls (p, e) with hj
  have hjD : j ∈ D := hJ₀ (hcls _ hpe).1
  have hj4 : ‖j.1‖ ≤ 4 := (hnorm j hjD).1
  have h1 := near_of_not_stripSep (q := (p, e)) (j := j) (hnorm _ hpe).1 hj4 (hcls _ hpe).2 hr
  have hc2 := (hcls _ hpe').2
  rw [hce'] at hc2
  have h2 := near_of_not_stripSep (q := (p', e')) (j := j) (hnorm _ hpe').1 hj4 hc2 hr
  have hv : |inner ℝ (p - p') j.2| < 18 * r := by
    have : inner ℝ (p - p') j.2 = inner ℝ (p - j.1) j.2 - inner ℝ (p' - j.1) j.2 := by
      rw [← inner_sub_left]; congr 1; abel
    rw [this]
    calc |inner ℝ (p - j.1) j.2 - inner ℝ (p' - j.1) j.2|
        ≤ |inner ℝ (p - j.1) j.2| + |inner ℝ (p' - j.1) j.2| := abs_sub _ _
      _ < 9 * r + 9 * r := add_lt_add h1.1 h2.1
      _ = 18 * r := by ring
  have hdist : ‖p - p'‖ = dist p p' := (dist_eq_norm p p').symm
  rcases h1.2 with hc | hc
  · have hsplit : inner ℝ (p - p') e = inner ℝ (p - p') j.2 + inner ℝ (p - p') (e - j.2) := by
      rw [← inner_add_right]; congr 1; abel
    have hcs : |inner ℝ (p - p') (e - j.2)| ≤ dist p p' * r := by
      calc |inner ℝ (p - p') (e - j.2)| ≤ ‖p - p'‖ * ‖e - j.2‖ := abs_real_inner_le_norm _ _
        _ ≤ dist p p' * r := by
          rw [hdist, ← dist_eq_norm]
          exact mul_le_mul_of_nonneg_left hc.le dist_nonneg
    rw [hsplit]
    calc |inner ℝ (p - p') j.2 + inner ℝ (p - p') (e - j.2)|
        ≤ |inner ℝ (p - p') j.2| + |inner ℝ (p - p') (e - j.2)| := abs_add_le _ _
      _ < 18 * r + dist p p' * r := by linarith
  · have hsplit : inner ℝ (p - p') e =
        -inner ℝ (p - p') j.2 + inner ℝ (p - p') (e - -j.2) := by
      rw [inner_sub_right, inner_neg_right]; ring
    have hcs : |inner ℝ (p - p') (e - -j.2)| ≤ dist p p' * r := by
      calc |inner ℝ (p - p') (e - -j.2)| ≤ ‖p - p'‖ * ‖e - -j.2‖ := abs_real_inner_le_norm _ _
        _ ≤ dist p p' * r := by
          rw [hdist, ← dist_eq_norm]
          exact mul_le_mul_of_nonneg_left hc.le dist_nonneg
    rw [hsplit]
    calc |-inner ℝ (p - p') j.2 + inner ℝ (p - p') (e - -j.2)|
        ≤ |-inner ℝ (p - p') j.2| + |inner ℝ (p - p') (e - -j.2)| := abs_add_le _ _
      _ < 18 * r + dist p p' * r := by rw [abs_neg]; linarith

/-- The bush bound applied to the shared normals of two pins `40 r` apart or more. -/
theorem shared_card_far {r η : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4) {D J₀ : Finset (E2 × E2)}
    {cls : E2 × E2 → E2 × E2}
    (hcls : ∀ q ∈ D, cls q ∈ J₀ ∧ (q = cls q ∨ ¬ StripSep r q (cls q) ∨ ¬ StripSep r (cls q) q))
    (hJ₀ : J₀ ⊆ D) (hnorm : ∀ q ∈ D, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1)
    {P : Finset E2}
    (hDkt : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      (((bushOf D p).filter (fun e => dist e u ≤ ρ)).card : ℝ) ≤ r ^ (-η) * (ρ / r) ^ (1 / 2 : ℝ))
    {p p' : E2} (hp : p ∈ P) (hp4 : ‖p‖ ≤ 4) (hp'4 : ‖p'‖ ≤ 4) (hfar : 40 * r ≤ dist p p') :
    ((sharedNormals D cls p p').card : ℝ) ≤
      2 * (r ^ (-η) * ((91 * r / dist p p') / r) ^ (1 / 2 : ℝ)) := by
  classical
  set d' := dist p p' with hd'
  have hd'pos : 0 < d' := lt_of_lt_of_le (by positivity) hfar
  have hd'8 : d' ≤ 8 := by
    rw [hd', dist_eq_norm]
    calc ‖p - p'‖ ≤ ‖p‖ + ‖p'‖ := norm_sub_le _ _
      _ ≤ 8 := by linarith
  by_cases hE : sharedNormals D cls p p' = ∅
  · rw [hE, Finset.card_empty, Nat.cast_zero]
    have : 0 ≤ r ^ (-η) * ((91 * r / d') / r) ^ (1 / 2 : ℝ) := by positivity
    linarith
  obtain ⟨e₁, he₁⟩ := Finset.nonempty_iff_ne_empty.mpr hE
  have he₁u : ‖e₁‖ = 1 := (hnorm _ (mem_bushOf.mp (Finset.mem_filter.mp he₁).1)).2
  set ρ := 91 * r / d' with hρ
  have hρr : r ≤ ρ := by
    rw [hρ, le_div_iff₀ hd'pos]; nlinarith
  -- every shared normal is within ρ of ± e₁
  have hcover : sharedNormals D cls p p' ⊆
      ((bushOf D p).filter (fun e => dist e e₁ ≤ ρ)) ∪
        ((bushOf D p).filter (fun e => dist e (-e₁) ≤ ρ)) := by
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
    rcases hcl with h | h
    · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hb, ?_⟩)
      rw [dist_eq_norm]
      nlinarith [norm_nonneg (e - e₁), sq_nonneg (‖e - e₁‖ - ρ)]
    · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hb, ?_⟩)
      rw [dist_eq_norm]
      nlinarith [norm_nonneg (e - -e₁), sq_nonneg (‖e - -e₁‖ - ρ)]
  have hneg : ‖-e₁‖ = 1 := by rw [norm_neg, he₁u]
  calc ((sharedNormals D cls p p').card : ℝ)
      ≤ (((bushOf D p).filter (fun e => dist e e₁ ≤ ρ)) ∪
          ((bushOf D p).filter (fun e => dist e (-e₁) ≤ ρ))).card := by
        exact_mod_cast Finset.card_le_card hcover
    _ ≤ (((bushOf D p).filter (fun e => dist e e₁ ≤ ρ)).card : ℝ) +
          (((bushOf D p).filter (fun e => dist e (-e₁) ≤ ρ)).card : ℝ) := by
        exact_mod_cast Finset.card_union_le _ _
    _ ≤ r ^ (-η) * (ρ / r) ^ (1 / 2 : ℝ) + r ^ (-η) * (ρ / r) ^ (1 / 2 : ℝ) :=
        add_le_add (hDkt p hp e₁ he₁u ρ hρr) (hDkt p hp (-e₁) hneg ρ hρr)
    _ = 2 * (r ^ (-η) * (ρ / r) ^ (1 / 2 : ℝ)) := by ring

/-- A uniform bound on the number of common classes of two pins. -/
theorem common_classes_bound {r η : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4)
    {D J₀ : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2}
    (hcls : ∀ q ∈ D, cls q ∈ J₀ ∧ (q = cls q ∨ ¬ StripSep r q (cls q) ∨ ¬ StripSep r (cls q) q))
    (hJ₀ : J₀ ⊆ D) (hnorm : ∀ q ∈ D, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1)
    {P : Finset E2}
    (hDkt : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      (((bushOf D p).filter (fun e => dist e u ≤ ρ)).card : ℝ) ≤ r ^ (-η) * (ρ / r) ^ (1 / 2 : ℝ))
    {p p' : E2} (hp : p ∈ P) (hp4 : ‖p‖ ≤ 4) (hp'4 : ‖p'‖ ≤ 4) :
    ((J₀.filter (fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j)).card : ℝ) ≤
      2 * r ^ (-η) * Real.sqrt 91 / Real.sqrt (max (dist p p') r) := by
  classical
  have hmr : r ≤ max (dist p p') r := le_max_right _ _
  have hmpos : 0 < max (dist p p') r := hr.trans_le hmr
  have hc := common_classes_le_shared D J₀ cls p p'
  have hcR : ((J₀.filter (fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j)).card : ℝ) ≤
      ((sharedNormals D cls p p').card : ℝ) := by exact_mod_cast hc
  refine hcR.trans ?_
  have hsqrt_eq : ∀ x : ℝ, 0 ≤ x → x ^ (1 / 2 : ℝ) = Real.sqrt x := fun x hx => by
    rw [Real.sqrt_eq_rpow]
  by_cases hfar : 40 * r ≤ dist p p'
  · have h := shared_card_far hr hr4 hcls hJ₀ hnorm hDkt hp hp4 hp'4 hfar
    have hmax : max (dist p p') r = dist p p' := max_eq_left (by linarith)
    rw [hmax]
    have hdpos : 0 < dist p p' := lt_of_lt_of_le (by positivity) hfar
    have e1 : (91 * r / dist p p') / r = 91 / dist p p' := by field_simp
    rw [e1, hsqrt_eq _ (by positivity), Real.sqrt_div' 91 hdpos.le] at h
    calc ((sharedNormals D cls p p').card : ℝ) ≤ 2 * (r ^ (-η) * (Real.sqrt 91 / Real.sqrt (dist p p'))) := h
      _ = _ := by ring
  · -- close pins: all bush elements
    push Not at hfar
    obtain ⟨u, hu⟩ : ∃ u : E2, ‖u‖ = 1 := by
      obtain ⟨u, hu⟩ := exists_norm_eq E2 (zero_le_one)
      exact ⟨u, hu⟩
    have hall : sharedNormals D cls p p' ⊆ (bushOf D p).filter (fun e => dist e u ≤ 2) := by
      intro e he
      have hb : e ∈ bushOf D p := (Finset.mem_filter.mp he).1
      have heu : ‖e‖ = 1 := (hnorm _ (mem_bushOf.mp hb)).2
      refine Finset.mem_filter.mpr ⟨hb, ?_⟩
      rw [dist_eq_norm]
      calc ‖e - u‖ ≤ ‖e‖ + ‖u‖ := norm_sub_le _ _
        _ = 2 := by rw [heu, hu]; norm_num
    have h2 : (2 : ℝ) ≥ r := by linarith
    have hkt := hDkt p hp u hu 2 h2
    have hc1 : ((sharedNormals D cls p p').card : ℝ) ≤
        (((bushOf D p).filter (fun e => dist e u ≤ 2)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hall
    have hcard : ((sharedNormals D cls p p').card : ℝ) ≤ r ^ (-η) * (2 / r) ^ (1 / 2 : ℝ) :=
      hc1.trans hkt
    refine hcard.trans ?_
    rw [hsqrt_eq _ (by positivity), Real.sqrt_div' 2 hr.le]
    have hm40 : max (dist p p') r ≤ 40 * r := max_le hfar.le (by linarith)
    have hsq : Real.sqrt (max (dist p p') r) ≤ Real.sqrt 40 * Real.sqrt r := by
      rw [← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt hm40
    have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
    have hsm : 0 < Real.sqrt (max (dist p p') r) := Real.sqrt_pos.mpr hmpos
    have h91 : Real.sqrt 2 * Real.sqrt 40 ≤ 2 * Real.sqrt 91 := by
      rw [← Real.sqrt_mul (by norm_num)]
      have : Real.sqrt (2 * 40) ≤ Real.sqrt 91 := Real.sqrt_le_sqrt (by norm_num)
      have h0 : 0 ≤ Real.sqrt 91 := Real.sqrt_nonneg _
      linarith
    have hrη : 0 ≤ r ^ (-η) := Real.rpow_nonneg hr.le _
    rw [← mul_div_assoc, div_le_div_iff₀ hsr hsm]
    calc r ^ (-η) * Real.sqrt 2 * Real.sqrt (max (dist p p') r)
        ≤ r ^ (-η) * Real.sqrt 2 * (Real.sqrt 40 * Real.sqrt r) := by
          gcongr
      _ = r ^ (-η) * (Real.sqrt 2 * Real.sqrt 40) * Real.sqrt r := by ring
      _ ≤ r ^ (-η) * (2 * Real.sqrt 91) * Real.sqrt r := by gcongr
      _ = 2 * r ^ (-η) * Real.sqrt 91 * Real.sqrt r := by ring

/-- Layer-cake bound: with the point bound `#(S ∩ B(p, ρ)) ≤ C ρ / r`, the sum of
`max (dist p q) r ^ (-1/2)` over the points `q` within `d` of `p` is at most `8 C √d / r`. -/
theorem layer_cake_inv_sqrt {r d C : ℝ} (hr : 0 < r) (hd : r ≤ d) (hC : 0 ≤ C)
    (S : Finset E2) (p : E2)
    (hS : ∀ ρ : ℝ, r ≤ ρ → ((S.filter (fun q => dist q p ≤ ρ)).card : ℝ) ≤ C * (ρ / r)) :
    ∑ q ∈ S.filter (fun q => dist p q ≤ d), 1 / Real.sqrt (max (dist p q) r) ≤
      8 * C * Real.sqrt d / r := by
  classical
  have hex : ∃ K : ℕ, d ≤ r * 2 ^ (K + 1) := by
    obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (d / r) (by norm_num : (1 : ℝ) < 2)
    refine ⟨K, ?_⟩
    rw [div_lt_iff₀ hr] at hK
    have : (2 : ℝ) ^ K ≤ 2 ^ (K + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ K)
    nlinarith
  set K := Nat.find hex with hKdef
  have hK : d ≤ r * 2 ^ (K + 1) := Nat.find_spec hex
  -- the number of dyadic scales is controlled by `d / r`
  have hK2 : (2 : ℝ) ^ (K + 1) ≤ 2 * d / r := by
    rw [le_div_iff₀ hr]
    by_cases hK0 : K = 0
    · rw [hK0]; norm_num; linarith
    · have hmin := Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero hK0) one_pos)
      rw [← hKdef] at hmin
      push Not at hmin
      have e : K - 1 + 1 = K := Nat.sub_add_cancel (Nat.pos_of_ne_zero hK0)
      rw [e] at hmin
      have : (2 : ℝ) ^ (K + 1) = 2 * 2 ^ K := by rw [pow_succ]; ring
      rw [this]; nlinarith
  -- pointwise layer-cake
  have hpt : ∀ q ∈ S.filter (fun q => dist p q ≤ d),
      1 / Real.sqrt (max (dist p q) r) ≤
        ∑ k ∈ Finset.range (K + 1),
          (if dist q p ≤ r * 2 ^ (k + 1) then 1 / Real.sqrt (r * 2 ^ k) else 0) := by
    intro q hq
    have hqd : dist p q ≤ d := (Finset.mem_filter.mp hq).2
    have hexq : ∃ k : ℕ, dist p q ≤ r * 2 ^ (k + 1) := ⟨K, hqd.trans hK⟩
    set k₀ := Nat.find hexq with hk₀def
    have hk₀ : dist p q ≤ r * 2 ^ (k₀ + 1) := Nat.find_spec hexq
    have hk₀K : k₀ ≤ K := Nat.find_min' hexq (hqd.trans hK)
    have hlow : r * 2 ^ k₀ ≤ max (dist p q) r := by
      by_cases h0 : k₀ = 0
      · rw [h0, pow_zero, mul_one]; exact le_max_right _ _
      · have hmin := Nat.find_min hexq (Nat.sub_lt (Nat.pos_of_ne_zero h0) one_pos)
        rw [← hk₀def] at hmin
        push Not at hmin
        have e : k₀ - 1 + 1 = k₀ := Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)
        rw [e] at hmin
        exact hmin.le.trans (le_max_left _ _)
    have hpos : 0 < r * 2 ^ k₀ := by positivity
    have hterm : 1 / Real.sqrt (max (dist p q) r) ≤ 1 / Real.sqrt (r * 2 ^ k₀) := by
      apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr hpos)
      exact Real.sqrt_le_sqrt hlow
    refine hterm.trans ?_
    have hmem : k₀ ∈ Finset.range (K + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hk₀K)
    have hcond : dist q p ≤ r * 2 ^ (k₀ + 1) := by rw [dist_comm]; exact hk₀
    have hsingle := Finset.single_le_sum (f := fun k =>
        (if dist q p ≤ r * 2 ^ (k + 1) then 1 / Real.sqrt (r * 2 ^ k) else 0))
      (fun k _ => by
        split_ifs
        · positivity
        · exact le_refl _) hmem
    simp only [hcond, ite_true] at hsingle
    exact hsingle
  calc ∑ q ∈ S.filter (fun q => dist p q ≤ d), 1 / Real.sqrt (max (dist p q) r)
      ≤ ∑ q ∈ S.filter (fun q => dist p q ≤ d), ∑ k ∈ Finset.range (K + 1),
          (if dist q p ≤ r * 2 ^ (k + 1) then 1 / Real.sqrt (r * 2 ^ k) else 0) :=
        Finset.sum_le_sum hpt
    _ = ∑ k ∈ Finset.range (K + 1), ∑ q ∈ S.filter (fun q => dist p q ≤ d),
          (if dist q p ≤ r * 2 ^ (k + 1) then 1 / Real.sqrt (r * 2 ^ k) else 0) :=
        Finset.sum_comm
    _ ≤ ∑ k ∈ Finset.range (K + 1), 2 * C / Real.sqrt r * Real.sqrt 2 ^ k := by
        apply Finset.sum_le_sum
        intro k _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        have hcnt : (((S.filter (fun q => dist p q ≤ d)).filter
            (fun q => dist q p ≤ r * 2 ^ (k + 1))).card : ℝ) ≤ C * (r * 2 ^ (k + 1) / r) := by
          refine le_trans ?_ (hS _ (by
            have : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
            nlinarith))
          exact_mod_cast Finset.card_le_card (fun q hq =>
            Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1,
              (Finset.mem_filter.mp hq).2⟩)
        have hsq : Real.sqrt (r * 2 ^ k) = Real.sqrt r * Real.sqrt 2 ^ k := by
          rw [Real.sqrt_mul hr.le, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
            ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
            ← Real.rpow_mul (by norm_num)]
          ring_nf
        have hs2 : Real.sqrt 2 ^ k * Real.sqrt 2 ^ k = 2 ^ k := by
          rw [← mul_pow, Real.mul_self_sqrt (by norm_num)]
        have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
        have hs2k : 0 < Real.sqrt 2 ^ k := by positivity
        rw [hsq]
        calc (((S.filter (fun q => dist p q ≤ d)).filter
              (fun q => dist q p ≤ r * 2 ^ (k + 1))).card : ℝ) *
              (1 / (Real.sqrt r * Real.sqrt 2 ^ k))
            ≤ C * (r * 2 ^ (k + 1) / r) * (1 / (Real.sqrt r * Real.sqrt 2 ^ k)) := by
              gcongr
          _ = 2 * C / Real.sqrt r * Real.sqrt 2 ^ k := by
              have e1 : r * 2 ^ (k + 1) / r = 2 * 2 ^ k := by
                field_simp; ring
              rw [e1, ← hs2]
              field_simp
    _ = 2 * C / Real.sqrt r * ∑ k ∈ Finset.range (K + 1), Real.sqrt 2 ^ k := by
        rw [Finset.mul_sum]
    _ ≤ 2 * C / Real.sqrt r * (Real.sqrt 2 ^ (K + 1) * (Real.sqrt 2 + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hs1 : 1 < Real.sqrt 2 := by
          rw [show (1 : ℝ) = Real.sqrt 1 by simp]
          exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
        have hgeom := geom_sum_eq (x := Real.sqrt 2) (ne_of_gt hs1) (K + 1)
        rw [hgeom]
        rw [div_le_iff₀ (by linarith)]
        have hpos : 0 ≤ Real.sqrt 2 ^ (K + 1) := by positivity
        have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
        nlinarith
    _ ≤ 8 * C * Real.sqrt d / r := by
        have hsK : Real.sqrt 2 ^ (K + 1) ≤ Real.sqrt (2 * d / r) := by
          have : Real.sqrt 2 ^ (K + 1) = Real.sqrt (2 ^ (K + 1)) := by
            rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
              ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
            ring_nf
          rw [this]
          exact Real.sqrt_le_sqrt hK2
        have hsd : Real.sqrt (2 * d / r) = Real.sqrt 2 * Real.sqrt d / Real.sqrt r := by
          rw [Real.sqrt_div' _ hr.le, Real.sqrt_mul (by norm_num)]
        rw [hsd] at hsK
        have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
        have hrr : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr.le
        have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
        have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
        have hs2' : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
        have hsdpos : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
        calc 2 * C / Real.sqrt r * (Real.sqrt 2 ^ (K + 1) * (Real.sqrt 2 + 1))
            ≤ 2 * C / Real.sqrt r * (Real.sqrt 2 * Real.sqrt d / Real.sqrt r * (Real.sqrt 2 + 1)) := by
              gcongr
          _ = 2 * C * Real.sqrt d * (Real.sqrt 2 * (Real.sqrt 2 + 1)) / (Real.sqrt r * Real.sqrt r) := by
              field_simp
          _ = 2 * C * Real.sqrt d * (2 + Real.sqrt 2) / r := by
              have e : Real.sqrt 2 * (Real.sqrt 2 + 1) = 2 + Real.sqrt 2 := by
                rw [mul_add, h2, mul_one]
              rw [hrr, e]
          _ ≤ 8 * C * Real.sqrt d / r := by
              apply div_le_div_of_nonneg_right _ hr.le
              have : 0 ≤ C * Real.sqrt d := by positivity
              nlinarith

/-- **The class pair bound.** -/
theorem class_pair_bound {r η d : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4) (hd : r ≤ d)
    {P : Finset E2} {D J₀ : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2}
    (hP4 : ∀ p ∈ P, ‖p‖ ≤ 4)
    (hPkt : ∀ (x : E2) (ρ : ℝ), r ≤ ρ →
      ((P.filter (fun p => dist p x ≤ ρ)).card : ℝ) ≤ r ^ (-η) * (ρ / r))
    (hDmem : ∀ q ∈ D, q.1 ∈ P ∧ ‖q.2‖ = 1)
    (hDkt : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      (((bushOf D p).filter (fun e => dist e u ≤ ρ)).card : ℝ) ≤ r ^ (-η) * (ρ / r) ^ (1 / 2 : ℝ))
    (hcls : ∀ q ∈ D, cls q ∈ J₀ ∧ (q = cls q ∨ ¬ StripSep r q (cls q) ∨ ¬ StripSep r (cls q) q))
    (hJ₀ : J₀ ⊆ D) :
    (∑ j ∈ J₀, ((((pinsOf D cls j) ×ˢ (pinsOf D cls j)).filter
        (fun pp => dist pp.1 pp.2 ≤ d)).card : ℝ)) ≤
      128 * Real.sqrt 91 * (r ^ (-η)) ^ 3 * Real.sqrt d / r ^ 2 := by
  classical
  have hnorm : ∀ q ∈ D, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1 :=
    fun q hq => ⟨hP4 _ (hDmem q hq).1, (hDmem q hq).2⟩
  have hpins : ∀ j, pinsOf D cls j ⊆ P := by
    intro j p hp
    obtain ⟨e, he, _⟩ := mem_pinsOf.mp hp
    exact (hDmem _ he).1
  set PP := (P ×ˢ P).filter (fun pp : E2 × E2 => dist pp.1 pp.2 ≤ d) with hPP
  set m : E2 × E2 → ℕ := fun pp =>
    (J₀.filter (fun j => pp.1 ∈ pinsOf D cls j ∧ pp.2 ∈ pinsOf D cls j)).card with hm
  -- swap the sums
  have hswap : (∑ j ∈ J₀, (((pinsOf D cls j) ×ˢ (pinsOf D cls j)).filter
      (fun pp => dist pp.1 pp.2 ≤ d)).card) = ∑ pp ∈ PP, m pp := by
    have h1 : ∀ j ∈ J₀, (((pinsOf D cls j) ×ˢ (pinsOf D cls j)).filter
        (fun pp => dist pp.1 pp.2 ≤ d)).card =
        ∑ pp ∈ PP, (if pp.1 ∈ pinsOf D cls j ∧ pp.2 ∈ pinsOf D cls j then 1 else 0) := by
      intro j _
      rw [← Finset.card_filter]
      congr 1
      ext pp
      simp only [hPP, Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨⟨hpins j h1, hpins j h2⟩, h3⟩, h1, h2⟩
      · rintro ⟨⟨_, h3⟩, h1, h2⟩
        exact ⟨⟨h1, h2⟩, h3⟩
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro pp _
    simp only [hm]
    rw [Finset.card_filter]
  have hswapR : (∑ j ∈ J₀, ((((pinsOf D cls j) ×ˢ (pinsOf D cls j)).filter
      (fun pp => dist pp.1 pp.2 ≤ d)).card : ℝ)) = ∑ pp ∈ PP, (m pp : ℝ) := by
    exact_mod_cast hswap
  rw [hswapR]
  -- bound each term
  have hterm : ∀ pp ∈ PP, (m pp : ℝ) ≤
      2 * r ^ (-η) * Real.sqrt 91 / Real.sqrt (max (dist pp.1 pp.2) r) := by
    intro pp hpp
    have hpp' := Finset.mem_product.mp (Finset.mem_filter.mp hpp).1
    exact common_classes_bound hr hr4 hcls hJ₀ hnorm hDkt hpp'.1 (hP4 _ hpp'.1) (hP4 _ hpp'.2)
  refine (Finset.sum_le_sum hterm).trans ?_
  -- regroup by the first pin
  have hregroup : ∑ pp ∈ PP, 2 * r ^ (-η) * Real.sqrt 91 / Real.sqrt (max (dist pp.1 pp.2) r) =
      ∑ p ∈ P, ∑ p' ∈ P.filter (fun p' => dist p p' ≤ d),
        2 * r ^ (-η) * Real.sqrt 91 / Real.sqrt (max (dist p p') r) := by
    rw [hPP, Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_filter]
  rw [hregroup]
  have hrη : 0 ≤ r ^ (-η) := Real.rpow_nonneg hr.le _
  have hinner : ∀ p ∈ P, ∑ p' ∈ P.filter (fun p' => dist p p' ≤ d),
      2 * r ^ (-η) * Real.sqrt 91 / Real.sqrt (max (dist p p') r) ≤
        2 * r ^ (-η) * Real.sqrt 91 * (8 * r ^ (-η) * Real.sqrt d / r) := by
    intro p _
    have hlc := layer_cake_inv_sqrt hr hd hrη P p (fun ρ hρ => hPkt p ρ hρ)
    calc ∑ p' ∈ P.filter (fun p' => dist p p' ≤ d),
          2 * r ^ (-η) * Real.sqrt 91 / Real.sqrt (max (dist p p') r)
        = 2 * r ^ (-η) * Real.sqrt 91 * ∑ p' ∈ P.filter (fun p' => dist p p' ≤ d),
            1 / Real.sqrt (max (dist p p') r) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p' _
          ring
      _ ≤ 2 * r ^ (-η) * Real.sqrt 91 * (8 * r ^ (-η) * Real.sqrt d / r) :=
          mul_le_mul_of_nonneg_left hlc (by positivity)
  refine (Finset.sum_le_sum hinner).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  -- the number of pins
  have hPcard : (P.card : ℝ) ≤ r ^ (-η) * (8 / r) := by
    have h := hPkt 0 8 (by linarith)
    have hfull : P.filter (fun p => dist p 0 ≤ 8) = P := by
      apply Finset.filter_true_of_mem
      intro p hp
      rw [dist_zero_right]
      linarith [hP4 p hp]
    rwa [hfull] at h
  have hconst : 0 ≤ 2 * r ^ (-η) * Real.sqrt 91 * (8 * r ^ (-η) * Real.sqrt d / r) := by
    positivity
  calc (P.card : ℝ) * (2 * r ^ (-η) * Real.sqrt 91 * (8 * r ^ (-η) * Real.sqrt d / r))
      ≤ r ^ (-η) * (8 / r) * (2 * r ^ (-η) * Real.sqrt 91 * (8 * r ^ (-η) * Real.sqrt d / r)) :=
        mul_le_mul_of_nonneg_right hPcard hconst
    _ = 128 * Real.sqrt 91 * (r ^ (-η)) ^ 3 * Real.sqrt d / r ^ 2 := by
        field_simp
        ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
