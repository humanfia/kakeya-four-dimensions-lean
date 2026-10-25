-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab.Cells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Slab.TwoScale

/-!
# Windows covering the rows of a cell

The rows `[a, b)` of a cell (with `L ≤ b - a`) are covered by the windows of `L` consecutive rows
starting at `a + t L` (`t < (b - a) / L`) and at `b - L`. One of these windows carries at least
the average share of the mass of the rows.
-/

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab

open Set Metric MeasureTheory
open scoped ENNReal

/-- The starting rows of the windows covering `[a, b)`. -/
def windowStarts (a b : ℤ) (L : ℕ) : Finset ℤ :=
  insert (b - L) ((Finset.range ((b - a).toNat / L)).image fun t : ℕ => a + (t : ℤ) * (L : ℤ))

lemma windowStarts_card_le (a b : ℤ) (L : ℕ) :
    (windowStarts a b L).card ≤ (b - a).toNat / L + 1 := by
  unfold windowStarts
  refine (Finset.card_insert_le _ _).trans ?_
  have := Finset.card_image_le (s := Finset.range ((b - a).toNat / L))
    (f := fun t : ℕ => a + (t : ℤ) * (L : ℤ))
  rw [Finset.card_range] at this
  omega

lemma windowStarts_sub {a b : ℤ} {L : ℕ} (hL1 : 1 ≤ L) (hL : (L : ℤ) ≤ b - a) :
    ∀ m₀ ∈ windowStarts a b L, a ≤ m₀ ∧ m₀ + L ≤ b := by
  intro m₀ hm
  unfold windowStarts at hm
  rcases Finset.mem_insert.mp hm with h | h
  · subst h; omega
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
    rw [Finset.mem_range] at ht
    have hba : (0 : ℤ) ≤ b - a := le_trans (Int.natCast_nonneg L) hL
    set D := (b - a).toNat with hD
    have h1 : (D : ℤ) = b - a := Int.toNat_of_nonneg hba
    set T := D / L with hT
    have hTL : T * L ≤ D := Nat.div_mul_le_self _ _
    have ht1 : (t + 1) * L ≤ T * L := Nat.mul_le_mul_right L ht
    have h2 : ((t + 1) * L : ℕ) ≤ (D : ℕ) := ht1.trans hTL
    have h3 : (((t + 1) * L : ℕ) : ℤ) ≤ (D : ℤ) := by exact_mod_cast h2
    push_cast at h3
    have h4 : (0 : ℤ) ≤ (t : ℤ) * (L : ℤ) := by positivity
    constructor
    · linarith
    · nlinarith

lemma rows_covered {a b : ℤ} {L : ℕ} (hL1 : 1 ≤ L) (hL : (L : ℤ) ≤ b - a) :
    ∀ m ∈ Finset.Ico a b, ∃ m₀ ∈ windowStarts a b L, m ∈ Finset.Ico m₀ (m₀ + L) := by
  intro m hm
  obtain ⟨hm1, hm2⟩ := Finset.mem_Ico.mp hm
  by_cases hlast : b - L ≤ m
  · exact ⟨b - L, Finset.mem_insert_self _ _, Finset.mem_Ico.mpr ⟨hlast, by omega⟩⟩
  · push Not at hlast
    have hba : (0 : ℤ) ≤ b - a := le_trans (Int.natCast_nonneg L) hL
    set D := (b - a).toNat with hD
    have h1 : (D : ℤ) = b - a := Int.toNat_of_nonneg hba
    set T := D / L with hT
    have hTL1 : T * L ≤ D := Nat.div_mul_le_self _ _
    have hTL2 : D < T * L + L := by
      have := Nat.lt_div_mul_add (a := D) (b := L) (by omega)
      rw [hT]; exact this
    have hma : (0 : ℤ) ≤ m - a := by omega
    set d := (m - a).toNat with hd
    have h2 : (d : ℤ) = m - a := Int.toNat_of_nonneg hma
    set t := d / L with ht
    have htL1 : t * L ≤ d := Nat.div_mul_le_self _ _
    have htL2 : d < t * L + L := by
      have := Nat.lt_div_mul_add (a := d) (b := L) (by omega)
      rw [ht]; exact this
    have hdD : d + L < D := by
      have : (d : ℤ) + L < D := by rw [h1, h2]; linarith
      exact_mod_cast this
    have htT : t < T := by
      by_contra hcon
      push Not at hcon
      have : T * L ≤ t * L := Nat.mul_le_mul_right L hcon
      omega
    refine ⟨a + (t : ℤ) * (L : ℤ), Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨t, Finset.mem_range.mpr htT, rfl⟩), Finset.mem_Ico.mpr ⟨?_, ?_⟩⟩
    · have : ((t * L : ℕ) : ℤ) ≤ (d : ℤ) := by exact_mod_cast htL1
      push_cast at this; linarith
    · have : (d : ℤ) < ((t * L + L : ℕ) : ℤ) := by exact_mod_cast htL2
      push_cast at this; linarith

/-- A best window. -/
theorem exists_best_window {n : ℕ} {Y : Fin n → Set Space} (hY : ∀ i, MeasurableSet (Y i))
    {s : ℝ} (hs : 0 < s) {a b : ℤ} {L : ℕ} (hL1 : 1 ≤ L) (hL : (L : ℤ) ≤ b - a) :
    ∃ m₀ ∈ windowStarts a b L,
      heightMass Y (rowUnion s (Finset.Ico a b)) ≤
        ((windowStarts a b L).card : ℝ≥0∞) *
          heightMass Y (rowUnion s (Finset.Ico m₀ (m₀ + L))) := by
  classical
  have hne : (windowStarts a b L).Nonempty := ⟨b - L, Finset.mem_insert_self _ _⟩
  obtain ⟨m₀, hm₀, hmax⟩ := Finset.exists_max_image (windowStarts a b L)
    (fun m₀ => heightMass Y (rowUnion s (Finset.Ico m₀ (m₀ + L)))) hne
  refine ⟨m₀, hm₀, ?_⟩
  have hsub : rowUnion s (Finset.Ico a b) ⊆
      ⋃ m₁ ∈ windowStarts a b L, rowUnion s (Finset.Ico m₁ (m₁ + L)) := by
    intro z hz
    obtain ⟨m, hm, hzm⟩ := mem_iUnion₂.mp hz
    obtain ⟨m₁, hm₁, hmm₁⟩ := rows_covered hL1 hL m hm
    exact mem_iUnion₂.mpr ⟨m₁, hm₁, mem_iUnion₂.mpr ⟨m, hmm₁, hzm⟩⟩
  calc heightMass Y (rowUnion s (Finset.Ico a b))
      ≤ heightMass Y (⋃ m₁ ∈ windowStarts a b L, rowUnion s (Finset.Ico m₁ (m₁ + L))) :=
        heightMass_mono Y hsub
    _ ≤ ∑ m₁ ∈ windowStarts a b L, heightMass Y (rowUnion s (Finset.Ico m₁ (m₁ + L))) := by
        unfold heightMass
        rw [Finset.sum_comm]
        apply Finset.sum_le_sum
        intro i _
        rw [preimage_iUnion₂, inter_iUnion₂]
        exact measure_biUnion_finset_le _ _
    _ ≤ ∑ _m₁ ∈ windowStarts a b L, heightMass Y (rowUnion s (Finset.Ico m₀ (m₀ + L))) :=
        Finset.sum_le_sum fun m₁ hm₁ => hmax m₁ hm₁
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab
