-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.CellProofs.LinearityClasses.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.CellProofs.Covering
import Submission.WZ.Obl.wz_slab_local_linearity.CellProofs.LinearityCount

/-!
# Classes of an Assouad-type set and lattice fibres

* `card_floor_image_le_of_assouad`: values lying in a set satisfying the frozen upper covering
  condition `Assouad d α C`, inside an interval of length `R`, fall into at most
  `3 C (R / r)^α` classes `⌊v / r⌋`.
* `card_le_of_subset_Icc_int`: a finite set of integers in a real interval of length `L` has at
  most `L + 1` elements.
* `card_lattice_fibre_le`: lattice points `(i, j)` on which two transversal linear forms take
  values in short intervals are few (at most `4 / |D| + 1`, `D` the determinant).
-/

namespace WangZahlLot.Obl.wz_slab_local_linearity.CellProofs

open Finset Set Metric

/-- Index-type version of `card_image_le_of_subset_range`. -/
theorem card_image_le_of_forall_exists {α β ι : Type*} [DecidableEq β] [Fintype ι]
    (s : Finset α) (k : α → β) (c : ι → β) (h : ∀ a ∈ s, ∃ j, k a = c j) :
    #(s.image k) ≤ Fintype.card ι := by
  classical
  calc #(s.image k) ≤ #(Finset.univ.image c) := by
        apply Finset.card_le_card
        intro v hv
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨j, hj⟩ := h a ha
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj.symm⟩
    _ ≤ #(Finset.univ : Finset ι) := card_image_le
    _ = Fintype.card ι := Finset.card_univ

/-- A point of `closedBall c r` has `⌊v / r⌋` within one of `⌊c / r⌋`. -/
theorem floor_div_mem_of_mem_closedBall {r c v : ℝ} (hr : 0 < r) (hv : v ∈ closedBall c r) :
    ∃ e : Fin 3, ⌊v / r⌋ = ⌊c / r⌋ + ((e : ℤ) - 1) := by
  rw [mem_closedBall, Real.dist_eq, abs_le] at hv
  have h1 : c / r - 1 ≤ v / r := by
    rw [sub_le_iff_le_add, div_add_one hr.ne', div_le_div_iff_of_pos_right hr]; linarith
  have h2 : v / r ≤ c / r + 1 := by
    rw [div_add_one hr.ne', div_le_div_iff_of_pos_right hr]; linarith
  have hlo : ⌊c / r⌋ - 1 ≤ ⌊v / r⌋ := by
    have : ⌊c / r - 1⌋ ≤ ⌊v / r⌋ := Int.floor_le_floor h1
    rwa [Int.floor_sub_one] at this
  have hhi : ⌊v / r⌋ ≤ ⌊c / r⌋ + 1 := by
    have : ⌊v / r⌋ ≤ ⌊c / r + 1⌋ := Int.floor_le_floor h2
    rwa [Int.floor_add_one] at this
  have hcases : ⌊v / r⌋ = ⌊c / r⌋ - 1 ∨ ⌊v / r⌋ = ⌊c / r⌋ ∨ ⌊v / r⌋ = ⌊c / r⌋ + 1 := by omega
  rcases hcases with h | h | h
  · exact ⟨0, by rw [h]; norm_num; ring⟩
  · exact ⟨1, by rw [h]; norm_num⟩
  · exact ⟨2, by rw [h]; norm_num⟩

/-- **Classes of an Assouad-type set.** If the values `v a` (`a ∈ s`) lie in `B ∩ [x, x + R]`
and `B` satisfies the frozen upper covering condition at scale `d ≤ r ≤ R`, then they fall into
at most `3 C (R / r)^α` classes `⌊v / r⌋`. -/
theorem card_floor_image_le_of_assouad {α : Type*} {d α' C r R x : ℝ} {B : Set ℝ}
    (hB : Assouad d α' C B) (hdr : d ≤ r) (hrR : r ≤ R) (hr : 0 < r)
    (s : Finset α) (v : α → ℝ) (hvB : ∀ a ∈ s, v a ∈ B) (hvI : ∀ a ∈ s, v a ∈ Icc x (x + R)) :
    (#(s.image fun a => ⌊v a / r⌋) : ℝ) ≤ 3 * (C * (R / r) ^ α') := by
  classical
  obtain ⟨m, c, hcov, hm⟩ := hB r R x hdr hrR
  have hcl : ∀ a ∈ s, ∃ j : Fin m × Fin 3,
      ⌊v a / r⌋ = (fun j : Fin m × Fin 3 => ⌊c j.1 / r⌋ + ((j.2 : ℤ) - 1)) j := by
    intro a ha
    have hmem : v a ∈ B ∩ Icc x (x + R) := ⟨hvB a ha, hvI a ha⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcov hmem)
    obtain ⟨e, he⟩ := floor_div_mem_of_mem_closedBall hr hj
    exact ⟨(j, e), he⟩
  have hcard := card_image_le_of_forall_exists s (fun a => ⌊v a / r⌋) _ hcl
  simp only [Fintype.card_prod, Fintype.card_fin] at hcard
  calc (#(s.image fun a => ⌊v a / r⌋) : ℝ) ≤ ((m * 3 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = 3 * m := by push_cast; ring
    _ ≤ 3 * (C * (R / r) ^ α') := by gcongr

/-- A finite set of integers inside a real interval of length `L ≥ 0` has at most `L + 1`
elements. -/
theorem card_le_of_subset_Icc_int {a L : ℝ} (hL : 0 ≤ L) (S : Finset ℤ)
    (hS : ∀ j ∈ S, a ≤ (j : ℝ) ∧ (j : ℝ) ≤ a + L) : (#S : ℝ) ≤ L + 1 := by
  classical
  have hsub : S ⊆ Finset.Icc ⌈a⌉ ⌊a + L⌋ := by
    intro j hj
    obtain ⟨h1, h2⟩ := hS j hj
    exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr h1, Int.le_floor.mpr h2⟩
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  have hceil : (a : ℝ) ≤ ⌈a⌉ := Int.le_ceil a
  have hfloor : (⌊a + L⌋ : ℝ) ≤ a + L := Int.floor_le _
  rcases le_or_gt (⌊a + L⌋ + 1 - ⌈a⌉) 0 with h | h
  · have : (⌊a + L⌋ + 1 - ⌈a⌉).toNat = 0 := Int.toNat_eq_zero.mpr h
    rw [this] at hcard
    have : #S = 0 := by omega
    rw [this]; push_cast; linarith
  · have hnat : (((⌊a + L⌋ + 1 - ⌈a⌉).toNat : ℕ) : ℤ) = ⌊a + L⌋ + 1 - ⌈a⌉ :=
      Int.toNat_of_nonneg h.le
    have hcardR : (#S : ℝ) ≤ (((⌊a + L⌋ + 1 - ⌈a⌉).toNat : ℕ) : ℝ) := by exact_mod_cast hcard
    have : (((⌊a + L⌋ + 1 - ⌈a⌉).toNat : ℕ) : ℝ) = (⌊a + L⌋ : ℝ) + 1 - ⌈a⌉ := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hnat
      push_cast at this
      exact this
    rw [this] at hcardR
    linarith

/-- **Lattice fibres.** Lattice points `(i, j)` with `⌊i + F j⌋ = w` and
`Vx i + Vy j ∈ [c, c + 2]` number at most `4 / |Vy - F Vx| + 1`, when `|Vx| ≤ 1`. -/
theorem card_lattice_fibre_le {F Vx Vy c : ℝ} {w : ℤ} (hVx : |Vx| ≤ 1)
    (hD : 0 < |Vy - F * Vx|) (T : Finset (ℤ × ℤ))
    (hT : ∀ q ∈ T, ⌊(q.1 : ℝ) + F * q.2⌋ = w ∧
      c ≤ Vx * q.1 + Vy * q.2 ∧ Vx * q.1 + Vy * q.2 ≤ c + 2) :
    (#T : ℝ) ≤ 4 / |Vy - F * Vx| + 1 := by
  classical
  set D := Vy - F * Vx with hDdef
  -- the second coordinate determines the point
  have hinj : Set.InjOn (fun q : ℤ × ℤ => q.2) (T : Set (ℤ × ℤ)) := by
    intro q hq q' hq' hqq
    simp only at hqq
    obtain ⟨hw, -, -⟩ := hT q hq
    obtain ⟨hw', -, -⟩ := hT q' hq'
    have h1 := Int.floor_le ((q.1 : ℝ) + F * q.2)
    have h2 := Int.lt_floor_add_one ((q.1 : ℝ) + F * q.2)
    have h3 := Int.floor_le ((q'.1 : ℝ) + F * q'.2)
    have h4 := Int.lt_floor_add_one ((q'.1 : ℝ) + F * q'.2)
    rw [hw] at h1 h2
    rw [hw'] at h3 h4
    rw [hqq] at h1 h2
    have hlt1 : ((q.1 - q'.1 : ℤ) : ℝ) < 1 := by push_cast; linarith
    have hlt2 : ((q'.1 - q.1 : ℤ) : ℝ) < 1 := by push_cast; linarith
    have e1 : q.1 - q'.1 < 1 := by exact_mod_cast hlt1
    have e2 : q'.1 - q.1 < 1 := by exact_mod_cast hlt2
    exact Prod.ext (by omega) hqq
  have hcard : #(T.image fun q => q.2) = #T := card_image_of_injOn hinj
  -- the second coordinates lie in an interval of length `4 / |D|`
  have hbound : ∀ q ∈ T, |D * q.2 - (c - Vx * w + 1)| ≤ 2 := by
    intro q hq
    obtain ⟨hw, hc1, hc2⟩ := hT q hq
    have h1 := Int.floor_le ((q.1 : ℝ) + F * q.2)
    have h2 := Int.lt_floor_add_one ((q.1 : ℝ) + F * q.2)
    rw [hw] at h1 h2
    have hsplit : Vx * q.1 + Vy * q.2 = Vx * ((q.1 : ℝ) + F * q.2) + D * q.2 := by
      rw [hDdef]; ring
    have hvx : |Vx * ((q.1 : ℝ) + F * q.2) - Vx * w| ≤ 1 := by
      rw [← mul_sub, abs_mul]
      have : |(q.1 : ℝ) + F * q.2 - w| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      calc |Vx| * |(q.1 : ℝ) + F * q.2 - w| ≤ 1 * 1 := by gcongr
        _ = 1 := by norm_num
    rw [abs_le] at hvx ⊢
    constructor <;> linarith
  have hDpos : 0 < |D| := hD
  set a0 := c - Vx * w + 1
  have hmem : ∀ j : ℤ, j ∈ T.image (fun q : ℤ × ℤ => q.2) → (a0 - 2) / D ⊓ (a0 + 2) / D ≤ (j : ℝ) ∧
      (j : ℝ) ≤ (a0 - 2) / D ⊓ (a0 + 2) / D + 4 / |D| := by
    intro j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    have hb := hbound q hq
    rw [abs_le] at hb
    rcases lt_or_gt_of_ne (abs_pos.mp hDpos) with hneg | hpos
    · have habs : |D| = -D := abs_of_neg hneg
      have hmin : (a0 - 2) / D ⊓ (a0 + 2) / D = (a0 + 2) / D := by
        apply min_eq_right
        exact div_le_div_of_nonpos_of_le hneg.le (by linarith)
      rw [hmin, habs]
      constructor
      · rw [div_le_iff_of_neg hneg]; linarith
      · have : (a0 + 2) / D + 4 / -D = (a0 - 2) / D := by field_simp; ring
        rw [this, le_div_iff_of_neg hneg]; linarith
    · have habs : |D| = D := abs_of_pos hpos
      have hmin : (a0 - 2) / D ⊓ (a0 + 2) / D = (a0 - 2) / D := by
        apply min_eq_left
        exact div_le_div_of_nonneg_right (by linarith) hpos.le
      rw [hmin, habs]
      constructor
      · rw [div_le_iff₀ hpos]; linarith
      · have : (a0 - 2) / D + 4 / D = (a0 + 2) / D := by field_simp; ring
        rw [this, le_div_iff₀ hpos]; linarith
  have := card_le_of_subset_Icc_int (by positivity) (T.image fun q : ℤ × ℤ => q.2) hmem
  rw [hcard] at this
  exact this

end WangZahlLot.Obl.wz_slab_local_linearity.CellProofs
