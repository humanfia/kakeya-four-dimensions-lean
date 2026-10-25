import Mathlib

/-!
# Deterministic palette box at a common reference index (o069)

* `accuracy_eq_of_radius_eq`, `accuracy_at_reference`: on a uniquely active
  piece the accuracy exponent of the active order at the reference time is
  exactly `β v`, i.e. `l_v(z/q) = β_v`.
* `floor_mul_mem_Icc`, `pair_mem_paletteBox`, `reference_palette_mem_box`:
  refining a floor bin of scale `s` to scale `s * w` leaves at most
  `⌊w⌋₊ + 2` values per coordinate.  On an `F_z` fiber the reference palette
  therefore takes at most `(⌊N^(6/q)⌋₊ + 2)^2` values (`card_paletteBox`).
* `card_image_filter_le_of_box`: the finite-code form of this count, in the
  shape of the support hypothesis of the finite palette theorem (o038).
-/

namespace Submission.Obl.k4_matching_cofinal_palette_selection

/-! ### The accuracy exponent at the reference time -/

/-- Every order's line is below the radius (the image of `Icc 1 J` is finite). -/
theorem le_radius (J : ℕ) (β : ℕ → ℝ) (a : ℝ) {j : ℕ} (hj1 : 1 ≤ j) (hjJ : j ≤ J) :
    (a - β j) / (j : ℝ) ≤
      sSup (Set.image (fun j : ℕ => (a - β j) / (j : ℝ)) (Set.Icc 1 J)) :=
  le_csSup ((Set.finite_Icc 1 J).image _).bddAbove ⟨j, ⟨hj1, hjJ⟩, rfl⟩

/-- If `r` dominates the line `(x - b)/v` everywhere and touches it at `a ≥ 0`,
then `sup_{0 ≤ x ≤ a} (x - v r(x)) = b`. -/
theorem sSup_sub_mul_eq (r : ℝ → ℝ) (b : ℝ) (v : ℕ) (hv : 1 ≤ v) (a : ℝ) (ha : 0 ≤ a)
    (hle : ∀ x, (x - b) / (v : ℝ) ≤ r x) (heq : r a = (a - b) / (v : ℝ)) :
    sSup (Set.image (fun x : ℝ => x - (v : ℝ) * r x) (Set.Icc 0 a)) = b := by
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hv
  apply IsGreatest.csSup_eq
  refine ⟨⟨a, ⟨ha, le_rfl⟩, ?_⟩, ?_⟩
  · simp only [heq]
    field_simp
    ring
  · rintro _ ⟨x, -, rfl⟩
    have h := hle x
    rw [div_le_iff₀ hv0] at h
    have : r x * (v : ℝ) = (v : ℝ) * r x := mul_comm _ _
    linarith

/-- The accuracy of order `v` equals `β v` at any time `a ≥ 0` where the radius
is attained by the `v`-th line. -/
theorem accuracy_eq_of_radius_eq (J : ℕ) (β : ℕ → ℝ) {v : ℕ} (hv1 : 1 ≤ v) (hvJ : v ≤ J)
    {a : ℝ} (ha : 0 ≤ a)
    (hr : sSup (Set.image (fun j : ℕ => (a - β j) / (j : ℝ)) (Set.Icc 1 J)) =
      (a - β v) / (v : ℝ)) :
    sSup (Set.image (fun x : ℝ => x - (v : ℝ) *
      sSup (Set.image (fun j : ℕ => (x - β j) / (j : ℝ)) (Set.Icc 1 J))) (Set.Icc 0 a)) =
      β v :=
  sSup_sub_mul_eq (fun x => sSup (Set.image (fun j : ℕ => (x - β j) / (j : ℝ)) (Set.Icc 1 J)))
    (β v) v hv1 a ha (fun x => le_radius J β x hv1 hvJ) hr

/-- `l_v(z/q) = β_v` at the reference index of an admissible step: the
admissibility interval starts at `z/q`. -/
theorem accuracy_at_reference (J : ℕ) (β : ℕ → ℝ) (q k v zv : ℕ) (hv1 : 1 ≤ v) (hvJ : v ≤ J)
    (hzk : zv ≤ k)
    (hr : ∀ x ∈ Set.Icc ((zv : ℝ) / (q : ℝ)) (((k + 6 * (J + 1) : ℕ) : ℝ) / (q : ℝ)),
      sSup (Set.image (fun j : ℕ => (x - β j) / (j : ℝ)) (Set.Icc 1 J)) =
        (x - β v) / (v : ℝ)) :
    sSup (Set.image (fun x : ℝ => x - (v : ℝ) *
      sSup (Set.image (fun j : ℕ => (x - β j) / (j : ℝ)) (Set.Icc 1 J)))
        (Set.Icc 0 ((zv : ℝ) / (q : ℝ)))) = β v := by
  have hmem : (zv : ℝ) / (q : ℝ) ∈
      Set.Icc ((zv : ℝ) / (q : ℝ)) (((k + 6 * (J + 1) : ℕ) : ℝ) / (q : ℝ)) := by
    refine ⟨le_rfl, ?_⟩
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg q)
    exact_mod_cast (le_trans hzk (Nat.le_add_right k _))
  exact accuracy_eq_of_radius_eq J β hv1 hvJ (by positivity) (hr _ hmem)

/-! ### Refining a floor bin -/

/-- Refining a floor bin: if `⌊s * g⌋ = m` and `0 ≤ w`, then `⌊s * w * g⌋`
lies in an integer interval with `⌊w⌋₊ + 2` points determined by `m`. -/
theorem floor_mul_mem_Icc {s w g : ℝ} (hw : 0 ≤ w) {m : ℤ} (hm : ⌊s * g⌋ = m) :
    ⌊s * w * g⌋ ∈ Finset.Icc ⌊w * m⌋ (⌊w * m⌋ + (⌊w⌋₊ : ℤ) + 1) := by
  rw [Int.floor_eq_iff] at hm
  have hsw : s * w * g = w * (s * g) := by ring
  have h1 : w * m ≤ s * w * g := by
    rw [hsw]
    exact mul_le_mul_of_nonneg_left hm.1 hw
  have h2 : s * w * g ≤ w * m + w := by
    rw [hsw]
    have : w * (s * g) ≤ w * ((m : ℝ) + 1) := mul_le_mul_of_nonneg_left hm.2.le hw
    linarith
  rw [Finset.mem_Icc]
  refine ⟨Int.floor_le_floor h1, ?_⟩
  calc ⌊s * w * g⌋ ≤ ⌊w * m + w⌋ := Int.floor_le_floor h2
    _ ≤ ⌊w * m⌋ + ⌊w⌋ + 1 := by linarith [Int.le_floor_add_floor (w * (m : ℝ)) w]
    _ = ⌊w * m⌋ + (⌊w⌋₊ : ℤ) + 1 := by rw [Int.natCast_floor_eq_floor hw]

/-- The box of refined palette pairs over a coarse pair of bins `(m₁, m₂)`. -/
noncomputable def paletteBox (w : ℝ) (m₁ m₂ : ℤ) : Finset (ℤ × ℤ) :=
  Finset.Icc ⌊w * m₁⌋ (⌊w * m₁⌋ + (⌊w⌋₊ : ℤ) + 1) ×ˢ
    Finset.Icc ⌊w * m₂⌋ (⌊w * m₂⌋ + (⌊w⌋₊ : ℤ) + 1)

theorem card_paletteBox (w : ℝ) (m₁ m₂ : ℤ) :
    (paletteBox w m₁ m₂).card = (⌊w⌋₊ + 2) ^ 2 := by
  unfold paletteBox
  rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
  have h : ∀ a : ℤ, a + (⌊w⌋₊ : ℤ) + 1 + 1 - a = ((⌊w⌋₊ + 2 : ℕ) : ℤ) := by
    intro a; push_cast; ring
  rw [h, h, Int.toNat_natCast, sq]

/-- A refined palette pair lies in the box of its coarse bins. -/
theorem pair_mem_paletteBox {s w g₁ g₂ g₁' g₂' : ℝ} (hw : 0 ≤ w)
    (h₁ : ⌊s * g₁⌋ = ⌊s * g₁'⌋) (h₂ : ⌊s * g₂⌋ = ⌊s * g₂'⌋) :
    (⌊s * w * g₁'⌋, ⌊s * w * g₂'⌋) ∈ paletteBox w ⌊s * g₁⌋ ⌊s * g₂⌋ := by
  unfold paletteBox
  rw [Finset.mem_product]
  exact ⟨floor_mul_mem_Icc hw h₁.symm, floor_mul_mem_Icc hw h₂.symm⟩

/-- The reference palette of `y` lies in the palette box of `x` whenever `x`
and `y` share their record at the reference index `zv`, provided the accuracy
of order `v` at time `zv / q` is `bv`.  Here `hF` is the record identity of the
frozen record data and `c` its dyadic center map. -/
theorem reference_palette_mem_box {n₁ n₂ : ℕ} (J q zv v : ℕ) (hzq : zv ≤ q) (hvJ : v ≤ J)
    (N bv : ℝ) (hN : 0 < N)
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (h : ℕ → ℕ)
    (c : ℕ → ℝ → ℝ) (l : ℕ → ℝ → ℝ) (hl : l v ((zv : ℝ) / (q : ℝ)) = bv)
    (F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ) (S : Set ((Fin n₁ × Fin n₂) × ℝ))
    (hF : ∀ k : ℕ, k ≤ q → ∀ x ∈ S, ∀ y ∈ S, F k x = F k y ↔ ∀ v : ℕ, v ≤ k →
      Int.floor (x.2 * (2 : ℝ) ^ h v) = Int.floor (y.2 * (2 : ℝ) ^ h v) ∧
      ∀ j : ℕ, j ≤ J →
        Int.floor (N ^ (l j ((v : ℝ) / (q : ℝ))) * iteratedDeriv j (f₁ x.1.1) (c v x.2)) =
          Int.floor (N ^ (l j ((v : ℝ) / (q : ℝ))) * iteratedDeriv j (f₁ y.1.1) (c v y.2)) ∧
        Int.floor (N ^ (l j ((v : ℝ) / (q : ℝ))) * iteratedDeriv j (f₂ x.1.2) (c v x.2)) =
          Int.floor (N ^ (l j ((v : ℝ) / (q : ℝ))) * iteratedDeriv j (f₂ y.1.2) (c v y.2)))
    {x y : (Fin n₁ × Fin n₂) × ℝ} (hx : x ∈ S) (hy : y ∈ S) (hxy : F zv x = F zv y) :
    (Int.floor (N ^ (bv + 6 / (q : ℝ)) * iteratedDeriv v (f₁ y.1.1) (c zv y.2)),
      Int.floor (N ^ (bv + 6 / (q : ℝ)) * iteratedDeriv v (f₂ y.1.2) (c zv y.2))) ∈
      paletteBox (N ^ (6 / (q : ℝ)))
        (Int.floor (N ^ bv * iteratedDeriv v (f₁ x.1.1) (c zv x.2)))
        (Int.floor (N ^ bv * iteratedDeriv v (f₂ x.1.2) (c zv x.2))) := by
  obtain ⟨e₁, e₂⟩ := (((hF zv hzq x hx y hy).1 hxy) zv le_rfl).2 v hvJ
  rw [hl] at e₁ e₂
  rw [Real.rpow_add hN]
  exact pair_mem_paletteBox (Real.rpow_nonneg hN.le _) e₁ e₂

/-! ### The count in finite-code form -/

/-- Support hypothesis of the finite palette theorem from a palette box: if
every code value has a representative in `S` (recording the reference record
`Fz` and the encoded palette `P`), and palettes over an `Fz`-fiber lie in a box
of at most `K` points, then each reference fiber carries at most `K` codes'
palettes. -/
theorem card_image_filter_le_of_box {Ω : Type*} {n : ℕ} (S : Set Ω)
    (p : Fin n → ℝ) (F0 Z : Fin n → ℕ) (Fz : Ω → ℕ) (P : Ω → ℤ × ℤ)
    (box : Ω → Finset (ℤ × ℤ)) (K : ℕ)
    (hrep : ∀ b, ∃ ω ∈ S, F0 b = Fz ω ∧ Z b = Encodable.encode (P ω))
    (hbox : ∀ x ∈ S, ∀ y ∈ S, Fz x = Fz y → P y ∈ box x)
    (hcard : ∀ x, (box x).card ≤ K) (a : Fin n) :
    ((Finset.univ.filter (fun b => 0 < p b ∧ F0 b = F0 a)).image Z).card ≤ K := by
  classical
  obtain ⟨ωa, hωa, hFa, -⟩ := hrep a
  calc ((Finset.univ.filter (fun b => 0 < p b ∧ F0 b = F0 a)).image Z).card
      ≤ ((box ωa).image Encodable.encode).card := by
        apply Finset.card_le_card
        intro t ht
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ht
        obtain ⟨ωb, hωb, hFb, hZb⟩ := hrep b
        have hb' := (Finset.mem_filter.mp hb).2.2
        rw [hZb]
        apply Finset.mem_image_of_mem
        apply hbox ωa hωa ωb hωb
        rw [← hFa, ← hFb, hb']
    _ ≤ (box ωa).card := Finset.card_image_le
    _ ≤ K := hcard ωa

end Submission.Obl.k4_matching_cofinal_palette_selection
