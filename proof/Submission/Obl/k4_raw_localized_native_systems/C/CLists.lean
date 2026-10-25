import Submission.Obl.k4_raw_localized_native_systems.C.CChart

/-
Adapted from this LOT tree, o178, session x0596, `CLists.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# Lists and disjointness of the full-time charts

With compatibility tolerance three bin widths, a later chart is compatible with at
most `2 ⋅ 9⁴` representatives of distinct bins, so the lists of the full-time charts
are at most `2 ⋅ 9⁴` times longer than the later lists.  Full-time charts of
distinct bins have disjoint assignments.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

variable {p : Data} {k : ℕ}

/-- An injective family of integer vectors meets a box of radius `R` at most
`(2R+1)⁴` times. -/
theorem card_filter_box_le {m : ℕ} (φ : Fin m → Fin 4 → ℤ) (hφ : Function.Injective φ)
    (c : Fin 4 → ℤ) (R : ℕ) :
    (Finset.univ.filter fun i => ∀ j, |φ i j - c j| ≤ R).card ≤ (2 * R + 1) ^ 4 := by
  classical
  set S := Finset.univ.filter fun i => ∀ j, |φ i j - c j| ≤ R with hS
  have himg : S.image φ ⊆
      Fintype.piFinset (fun j : Fin 4 => Finset.Icc (c j - R) (c j + R)) := by
    intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨i, hi, rfl⟩ := hv
    rw [hS, Finset.mem_filter] at hi
    rw [Fintype.mem_piFinset]
    intro j
    have := abs_le.1 (hi.2 j)
    rw [Finset.mem_Icc]
    constructor <;> linarith [this.1, this.2]
  have hcard := Finset.card_le_card himg
  rw [Finset.card_image_of_injective _ hφ, Fintype.card_piFinset] at hcard
  have hIcc : ∀ j : Fin 4, (Finset.Icc (c j - R) (c j + R)).card = 2 * R + 1 := by
    intro j
    rw [Int.card_Icc]
    omega
  simp only [hIcc, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcard
  exact hcard

theorem floor_sub_floor_le {x y G : ℝ} (hG : 0 < G) (h : |x - y| ≤ 3 * G) :
    |⌊x / G⌋ - ⌊y / G⌋| ≤ (4 : ℤ) := by
  have h1 := Int.floor_le (x / G)
  have h2 := Int.lt_floor_add_one (x / G)
  have h3 := Int.floor_le (y / G)
  have h4 := Int.lt_floor_add_one (y / G)
  have hxy : |x / G - y / G| ≤ 3 := by
    rw [← sub_div, abs_div, abs_of_pos hG, div_le_iff₀ hG]; linarith
  have hb := abs_le.1 hxy
  have lt1 : ((⌊x / G⌋ - ⌊y / G⌋ : ℤ) : ℝ) < 4 := by push_cast; linarith
  have lt2 : (-4 : ℝ) < ((⌊x / G⌋ - ⌊y / G⌋ : ℤ) : ℝ) := by push_cast; linarith
  have i1 : ⌊x / G⌋ - ⌊y / G⌋ < 4 := by exact_mod_cast lt1
  have i2 : -4 < ⌊x / G⌋ - ⌊y / G⌋ := by exact_mod_cast lt2
  rw [abs_le]; constructor <;> omega

/-- The bin of the sign-reversed strip data. -/
def negBin (a : Atlas p k) (Kc G : ℝ) (b : Fin a.C) : Fin 4 → ℤ :=
  ![⌊-q2normal a b 0 / G⌋, ⌊-q2normal a b 1 / G⌋, ⌊-q2intercept a Kc b / G⌋,
    ⌊-q2speed a Kc b / G⌋]

theorem compat_bin_close {a : Atlas p k} {Kc G : ℝ} (hG : 0 < G) {b'' b : Fin a.C}
    (h : Compat a Kc (3 * G) b'' b) :
    (∀ j, |q2bin a Kc G b j - q2bin a Kc G b'' j| ≤ ((4 : ℕ) : ℤ)) ∨
      (∀ j, |q2bin a Kc G b j - negBin a Kc G b'' j| ≤ ((4 : ℕ) : ℤ)) := by
  rcases h with ⟨hn, hi, hs⟩ | ⟨hn, hi, hs⟩
  · left
    have h0 : |q2normal a b 0 - q2normal a b'' 0| ≤ 3 * G := by
      have := abs_coord_le_norm_fin2 (q2normal a b'' - q2normal a b) 0
      simp only [PiLp.sub_apply] at this
      rw [abs_sub_comm]; linarith
    have h1 : |q2normal a b 1 - q2normal a b'' 1| ≤ 3 * G := by
      have := abs_coord_le_norm_fin2 (q2normal a b'' - q2normal a b) 1
      simp only [PiLp.sub_apply] at this
      rw [abs_sub_comm]; linarith
    intro j
    fin_cases j <;> simp only [q2bin, Nat.cast_ofNat] <;> simp
    · exact floor_sub_floor_le hG h0
    · exact floor_sub_floor_le hG h1
    · exact floor_sub_floor_le hG (by rw [abs_sub_comm]; exact hi)
    · exact floor_sub_floor_le hG (by rw [abs_sub_comm]; exact hs)
  · right
    have h0 : |q2normal a b 0 - -q2normal a b'' 0| ≤ 3 * G := by
      have := abs_coord_le_norm_fin2 (q2normal a b'' + q2normal a b) 0
      simp only [PiLp.add_apply] at this
      rw [sub_neg_eq_add, add_comm]; linarith
    have h1 : |q2normal a b 1 - -q2normal a b'' 1| ≤ 3 * G := by
      have := abs_coord_le_norm_fin2 (q2normal a b'' + q2normal a b) 1
      simp only [PiLp.add_apply] at this
      rw [sub_neg_eq_add, add_comm]; linarith
    have hi' : |q2intercept a Kc b - -q2intercept a Kc b''| ≤ 3 * G := by
      rw [sub_neg_eq_add, add_comm]; exact hi
    have hs' : |q2speed a Kc b - -q2speed a Kc b''| ≤ 3 * G := by
      rw [sub_neg_eq_add, add_comm]; exact hs
    intro j
    fin_cases j <;> simp only [q2bin, negBin, Nat.cast_ofNat] <;> simp
    · exact floor_sub_floor_le hG h0
    · exact floor_sub_floor_le hG h1
    · exact floor_sub_floor_le hG hi'
    · exact floor_sub_floor_le hG hs'

/-- A later chart is compatible with boundedly many representatives of distinct bins. -/
theorem card_compatible_le {a : Atlas p k} (γ : Fin (p.W k)) {Kc G : ℝ} (hG : 0 < G) {m : ℕ}
    (rep : Fin m → Fin a.C) (hinj : Function.Injective fun i => q2bin a Kc G (rep i))
    (b'' : Fin a.C) :
    (Finset.univ.filter fun i => b'' ∈ compatSet a γ Kc (3 * G) (rep i)).card ≤ 2 * 9 ^ 4 := by
  classical
  have hsub : (Finset.univ.filter fun i => b'' ∈ compatSet a γ Kc (3 * G) (rep i)) ⊆
      (Finset.univ.filter fun i => ∀ j, |q2bin a Kc G (rep i) j - q2bin a Kc G b'' j| ≤
          ((4 : ℕ) : ℤ)) ∪
        (Finset.univ.filter fun i => ∀ j, |q2bin a Kc G (rep i) j - negBin a Kc G b'' j| ≤
          ((4 : ℕ) : ℤ)) := by
    intro i hi
    rw [Finset.mem_filter, mem_compatSet] at hi
    rcases compat_bin_close hG hi.2.2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  have e1 := card_filter_box_le (fun i => q2bin a Kc G (rep i)) hinj (q2bin a Kc G b'') 4
  have e2 := card_filter_box_le (fun i => q2bin a Kc G (rep i)) hinj (negBin a Kc G b'') 4
  norm_num at e1 e2 ⊢
  omega

/-- **List length of the full-time charts.** -/
theorem card_cLst_le {a : Atlas p k} (γ : Fin (p.W k)) {Kc G : ℝ} (hG : 0 < G) {m : ℕ}
    (rep : Fin m → Fin a.C) (hinj : Function.Injective fun i => q2bin a Kc G (rep i))
    (o : Observation) :
    (cLst a γ Kc (3 * G) rep o).card ≤ 2 * 9 ^ 4 * (a.lst γ o).card := by
  classical
  have hsub : cLst a γ Kc (3 * G) rep o ⊆ (a.lst γ o).biUnion
      (fun b'' => Finset.univ.filter fun i => b'' ∈ compatSet a γ Kc (3 * G) (rep i)) := by
    intro i hi
    rw [mem_cLst] at hi
    obtain ⟨b'', hb'', hc⟩ := hi
    rw [Finset.mem_biUnion]
    exact ⟨b'', hb'', Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ b'' ∈ a.lst γ o, (Finset.univ.filter fun i =>
        b'' ∈ compatSet a γ Kc (3 * G) (rep i)).card
      ≤ ∑ _b'' ∈ a.lst γ o, 2 * 9 ^ 4 :=
        Finset.sum_le_sum fun b'' _ => card_compatible_le γ hG rep hinj b''
    _ = 2 * 9 ^ 4 * (a.lst γ o).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- The lists are measurable. -/
theorem measurableSet_cLst {a : Atlas p k} (γ : Fin (p.W k)) (Kc ε : ℝ) {m : ℕ}
    (rep : Fin m → Fin a.C) (hmeas : ∀ b, MeasurableSet {o | b ∈ a.lst γ o}) (i : Fin m) :
    MeasurableSet {o | i ∈ cLst a γ Kc ε rep o} := by
  have : {o | i ∈ cLst a γ Kc ε rep o} =
      ⋃ b'' ∈ compatSet a γ Kc ε (rep i), {o | b'' ∈ a.lst γ o} := by
    ext o
    simp only [Set.mem_ofPred_eq, mem_cLst, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨b'', h1, h2⟩; exact ⟨b'', h2, h1⟩
    · rintro ⟨b'', h1, h2⟩; exact ⟨b'', h2, h1⟩
  rw [this]
  exact Finset.measurableSet_biUnion _ fun b'' _ => hmeas b''

/-- **Disjointness.** Full-time charts of distinct bins have disjoint assignments. -/
theorem cA_disjoint {a : Atlas p k}
    (hdisj : ∀ b b', b ≠ b' → a.γ b = a.γ b' → a.j b = a.j b' → Disjoint (a.A b) (a.A b'))
    (γ : Fin (p.W k)) {t₀ lam Kc G g κC : ℝ} {m : ℕ} (rep : Fin m → Fin a.C)
    (hinj : Function.Injective fun i => q2bin a Kc G (rep i)) {i i' : Fin m} (hii : i ≠ i') :
    Disjoint (cA a γ t₀ lam Kc G g κC (rep i)) (cA a γ t₀ lam Kc G g κC (rep i')) := by
  classical
  rw [Set.disjoint_left]
  intro l hl hl'
  rw [mem_cA] at hl hl'
  obtain ⟨⟨b', hb', hlA⟩, -⟩ := hl
  obtain ⟨⟨b''', hb''', hlA'⟩, -⟩ := hl'
  simp only [binMates, Finset.mem_filter, Finset.mem_univ, true_and] at hb' hb'''
  have hne : b' ≠ b''' := by
    intro h
    apply hii
    apply hinj
    simp only
    rw [← hb'.2.2.2.2.2, ← hb'''.2.2.2.2.2, h]
  have hj : a.j b' = a.j b''' := by
    apply Fin.ext
    have := hb'.2.1.symm.trans hb'''.2.1
    exact_mod_cast this
  exact Set.disjoint_left.1 (hdisj b' b''' hne (hb'.1.trans hb'''.1.symm) hj) hlA hlA'

end

end Submission.Obl.k4_raw_localized_native_systems.C
