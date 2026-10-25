import Mathlib

/-!
# Keeping a quadratic in a slit plane along a segment

If every complex root of a polynomial `q` of degree at most two stays at distance at least `ρ`
from the real segment `[0, 1]`, then one fixed rotation `λ` puts `q(s) / λ`, and all its relative
perturbations of size `≲ ρ²`, into the slit plane for every `s ∈ [0, 1]`.  Each root factor
`(s - r)` is divided by `s* - r`, where `s*` is the point of `[0, 1]` closest to `r`; the
quotients have real part at least one, and a product of at most two such numbers stays at
distance `1/2` from the negative real axis.
-/

namespace Submission.Lib.K4QuadraticSheets

open Complex

/-- A product of two numbers of real part at least one has real part at least `1/2` or
imaginary part of size at least one. -/
theorem re_or_im_of_mul_of_one_le_re {u v : ℂ} (hu : 1 ≤ u.re) (hv : 1 ≤ v.re) :
    1 / 2 ≤ (u * v).re ∨ 1 ≤ |(u * v).im| := by
  rw [mul_re, mul_im]
  by_cases h : 1 / 2 ≤ u.re * v.re - u.im * v.im
  · exact Or.inl h
  · right
    rw [not_le] at h
    have huv : 1 ≤ u.re * v.re := by nlinarith
    have hbd : 1 / 2 < u.im * v.im := by linarith
    rcases lt_or_gt_of_ne (show u.im ≠ 0 by intro h0; rw [h0] at hbd; linarith) with hb | hb
    · have hd : v.im < 0 := by
        by_contra hd
        rw [not_lt] at hd
        nlinarith
      have h1 : u.re * v.im + u.im * v.re ≤ v.im + u.im := by nlinarith
      have h2 : 1 < (v.im + u.im) ^ 2 := by nlinarith
      rw [abs_of_neg (by nlinarith)]
      nlinarith
    · have hd : 0 < v.im := by
        by_contra hd
        rw [not_lt] at hd
        nlinarith
      have h1 : v.im + u.im ≤ u.re * v.im + u.im * v.re := by nlinarith
      have h2 : 1 < (v.im + u.im) ^ 2 := by nlinarith
      rw [abs_of_pos (by nlinarith)]
      nlinarith

/-- A point within `1/2` of a number of real part at least `1/2`, or of imaginary part of size
at least one, lies in the slit plane. -/
theorem mem_slitPlane_of_near {u w : ℂ} (hu : 1 / 2 ≤ u.re ∨ 1 ≤ |u.im|)
    (hw : ‖w - u‖ < 1 / 2) : w ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  have hre : |(w - u).re| < 1 / 2 := lt_of_le_of_lt (abs_re_le_norm _) hw
  have him : |(w - u).im| < 1 / 2 := lt_of_le_of_lt (abs_im_le_norm _) hw
  rw [sub_re] at hre
  rw [sub_im] at him
  rcases hu with hu | hu
  · left
    have := (abs_lt.mp hre).1
    linarith
  · right
    intro h0
    rw [h0] at him
    have : |u.im| < 1 / 2 := by simpa [abs_sub_comm] using him
    linarith

/-- The point of `[0, 1]` closest to a complex number, as a complex number. -/
noncomputable def clampPt (r : ℂ) : ℂ := ((max 0 (min 1 r.re) : ℝ) : ℂ)

theorem clampPt_mem (r : ℂ) : max 0 (min 1 r.re) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- The key half-plane inequality for the segment `[0, 1]`. -/
theorem re_mul_conj_clamp_ge (r : ℂ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ‖clampPt r - r‖ ^ 2 ≤ (((s : ℂ) - r) * (starRingEnd ℂ) (clampPt r - r)).re := by
  set m := max 0 (min 1 r.re) with hm
  have hkey : 0 ≤ (m - r.re) * (s - m) := by
    rcases le_or_gt r.re 0 with hx | hx
    · have : m = 0 := by rw [hm]; exact max_eq_left (le_trans (min_le_right _ _) hx)
      rw [this]
      nlinarith [hs.1]
    · rcases le_or_gt r.re 1 with hx1 | hx1
      · have : m = r.re := by
          rw [hm, min_eq_right hx1, max_eq_right hx.le]
        rw [this]
        ring_nf
        exact le_refl _
      · have : m = 1 := by
          rw [hm, min_eq_left hx1.le, max_eq_right zero_le_one]
        rw [this]
        nlinarith [hs.2]
  have hnorm : ‖clampPt r - r‖ ^ 2 = (m - r.re) ^ 2 + r.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [clampPt, hm]
    ring
  rw [hnorm]
  simp only [clampPt, ← hm, mul_re, sub_re, ofReal_re, map_sub, conj_ofReal, sub_im,
    ofReal_im, conj_re, conj_im]
  nlinarith [hkey]

/-- The normalized root factor has real part at least one and bounded size. -/
theorem root_factor_bounds (r : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hfar : ∀ s ∈ Set.Icc (0 : ℝ) 1, ρ ≤ ‖(s : ℂ) - r‖) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    clampPt r - r ≠ 0 ∧ 1 ≤ (((s : ℂ) - r) / (clampPt r - r)).re ∧
      ‖((s : ℂ) - r) / (clampPt r - r)‖ ≤ 1 + 1 / ρ := by
  have hp : ρ ≤ ‖clampPt r - r‖ := hfar _ (clampPt_mem r)
  have hp0 : 0 < ‖clampPt r - r‖ := lt_of_lt_of_le hρ hp
  have hpne : clampPt r - r ≠ 0 := norm_pos_iff.mp hp0
  refine ⟨hpne, ?_, ?_⟩
  · rw [div_re]
    have h1 := re_mul_conj_clamp_ge r hs
    have hns : Complex.normSq (clampPt r - r) = ‖clampPt r - r‖ ^ 2 :=
      Complex.normSq_eq_norm_sq _
    have hexp : (((s : ℂ) - r) * (starRingEnd ℂ) (clampPt r - r)).re =
        ((s : ℂ) - r).re * (clampPt r - r).re + ((s : ℂ) - r).im * (clampPt r - r).im := by
      simp [mul_re]
      ring
    rw [hexp] at h1
    rw [← add_div, hns, le_div_iff₀ (by positivity)]
    linarith
  · rw [norm_div, div_le_iff₀ hp0]
    have hsm : ‖(s : ℂ) - clampPt r‖ ≤ 1 := by
      have hm := clampPt_mem r
      rw [clampPt, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hs.1, hs.2, hm.1, hm.2]
    calc ‖(s : ℂ) - r‖ = ‖((s : ℂ) - clampPt r) + (clampPt r - r)‖ := by ring_nf
      _ ≤ ‖(s : ℂ) - clampPt r‖ + ‖clampPt r - r‖ := norm_add_le _ _
      _ ≤ 1 + ‖clampPt r - r‖ := by linarith
      _ ≤ (1 + 1 / ρ) * ‖clampPt r - r‖ := by
        rw [add_mul, one_mul, add_comm (1 : ℝ)]
        have : 1 ≤ 1 / ρ * ‖clampPt r - r‖ := by
          rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hρ, one_mul]
          exact hp
        linarith

/-- A multiset of cardinality at most two is empty, a singleton or a pair. -/
theorem multiset_card_le_two {α : Type*} (M : Multiset α) (h : Multiset.card M ≤ 2) :
    M = 0 ∨ (∃ a, M = {a}) ∨ ∃ a b, M = {a, b} := by
  rcases Nat.lt_or_ge (Multiset.card M) 2 with h2 | h2
  · rcases Nat.lt_or_ge (Multiset.card M) 1 with h1 | h1
    · left
      exact Multiset.card_eq_zero.mp (by omega)
    · right; left
      exact Multiset.card_eq_one.mp (by omega)
  · right; right
    exact Multiset.card_eq_two.mp (by omega)

/-- **Slit-plane rotation along a segment.**  If all roots of a polynomial of degree at most
two stay `ρ`-far from `[0, 1]`, a fixed `λ ≠ 0` sends every small relative perturbation of
its values on `[0, 1]` into the slit plane. -/
theorem exists_slit_rotation (q : Polynomial ℂ) (hq : q ≠ 0) (hdeg : q.natDegree ≤ 2)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hfar : ∀ r ∈ q.roots, ∀ s ∈ Set.Icc (0 : ℝ) 1, ρ ≤ ‖(s : ℂ) - r‖) :
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ w : ℂ,
      ‖w - q.eval (s : ℂ)‖ * (2 * (1 + 1 / ρ) ^ 2) < ‖q.eval (s : ℂ)‖ →
        w / lam ∈ slitPlane := by
  classical
  have hs := IsAlgClosed.splits q
  have hcard : Multiset.card q.roots ≤ 2 := (Polynomial.card_roots' q).trans hdeg
  set p : ℂ → ℂ := fun r => clampPt r - r with hpdef
  set lam : ℂ := q.leadingCoeff * (q.roots.map p).prod with hlam
  have hlead : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  have hpne : ∀ r ∈ q.roots, p r ≠ 0 := fun r hr =>
    (root_factor_bounds r hρ (hfar r hr) (s := 0) ⟨le_refl _, zero_le_one⟩).1
  have hlam0 : lam ≠ 0 := by
    rw [hlam]
    refine mul_ne_zero hlead ?_
    apply Multiset.prod_ne_zero
    intro h0
    obtain ⟨r, hr, hr0⟩ := Multiset.mem_map.mp h0
    exact hpne r hr hr0
  refine ⟨lam, hlam0, ?_⟩
  intro s hsI w hw
  set R : ℝ := 1 + 1 / ρ with hR
  have hR1 : 1 ≤ R := by rw [hR]; have : 0 < 1 / ρ := by positivity
                         linarith
  -- the normalized product
  set u : ℂ := (q.roots.map (fun r => ((s : ℂ) - r) / p r)).prod with hu
  have hqs : q.eval (s : ℂ) = lam * u := by
    rw [hs.eval_eq_prod_roots, hlam, hu, mul_assoc]
    congr 1
    rw [← Multiset.prod_map_mul]
    congr 1
    apply Multiset.map_congr rfl
    intro r hr
    field_simp [hpne r hr]
  -- bounds on the factors
  have hfac : ∀ r ∈ q.roots, 1 ≤ (((s : ℂ) - r) / p r).re ∧ ‖((s : ℂ) - r) / p r‖ ≤ R :=
    fun r hr => (root_factor_bounds r hρ (hfar r hr) hsI).2
  -- position of the product
  have hpos : (1 / 2 ≤ u.re ∨ 1 ≤ |u.im|) ∧ ‖u‖ ≤ R ^ 2 := by
    rcases multiset_card_le_two q.roots hcard with h0 | ⟨a, ha⟩ | ⟨a, b, hab⟩
    · rw [hu, h0]
      simp only [Multiset.map_zero, Multiset.prod_zero, one_re, norm_one]
      exact ⟨Or.inl (by norm_num), by nlinarith⟩
    · have ha' := hfac a (by rw [ha]; exact Multiset.mem_singleton_self a)
      rw [hu, ha]
      simp only [Multiset.map_singleton, Multiset.prod_singleton]
      exact ⟨Or.inl (by linarith [ha'.1]), by nlinarith [ha'.2, norm_nonneg (((s : ℂ) - a) / p a)]⟩
    · have ha' := hfac a (by rw [hab]; simp)
      have hb' := hfac b (by rw [hab]; simp)
      rw [hu, hab]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
        Multiset.prod_cons, Multiset.prod_singleton]
      refine ⟨re_or_im_of_mul_of_one_le_re ha'.1 hb'.1, ?_⟩
      rw [norm_mul, sq]
      exact mul_le_mul ha'.2 hb'.2 (norm_nonneg _) (by linarith)
  -- the perturbation is small
  have hqs0 : q.eval (s : ℂ) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hw
    exact absurd hw (not_lt.mpr (by positivity))
  have hu0 : u ≠ 0 := by
    intro h0
    apply hqs0
    rw [hqs, h0, mul_zero]
  have hclose : ‖w / lam - u‖ < 1 / 2 := by
    have hwl : w / lam - u = (w - q.eval (s : ℂ)) / lam := by
      rw [hqs]
      field_simp
    rw [hwl, norm_div]
    have hlampos : 0 < ‖lam‖ := norm_pos_iff.mpr hlam0
    rw [div_lt_iff₀ hlampos]
    have hnq : ‖q.eval (s : ℂ)‖ = ‖lam‖ * ‖u‖ := by rw [hqs, norm_mul]
    rw [hnq] at hw
    have hR2 : 0 < 2 * R ^ 2 := by positivity
    have : ‖w - q.eval (s : ℂ)‖ * (2 * R ^ 2) < ‖lam‖ * R ^ 2 := by
      calc ‖w - q.eval (s : ℂ)‖ * (2 * R ^ 2) < ‖lam‖ * ‖u‖ := hw
        _ ≤ ‖lam‖ * R ^ 2 := mul_le_mul_of_nonneg_left hpos.2 hlampos.le
    nlinarith
  exact mem_slitPlane_of_near hpos.1 hclose

end Submission.Lib.K4QuadraticSheets
