import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripPieces
import Submission.Lib.K4AngularCharge.ChartCells

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory Set Submission.Lib.K4XInterface
open scoped RealInnerProductSpace

noncomputable def CoverData.midpointBins {W : ℕ} {p : PathData W} (_c : CoverData p)
    (width : ℝ) : Finset ℤ :=
  Finset.Icc ⌊-(p.κ + width) / width⌋ ⌊(p.κ + width) / width⌋

abbrev CoverData.RawStripPiece {W : ℕ} {p : PathData W} (c : CoverData p) (width : ℝ) :=
  Fin c.n × {z : ℤ // z ∈ c.midpointBins width}

abbrev CoverData.UsedStripPiece {W : ℕ} {p : PathData W} (c : CoverData p) (width : ℝ) :=
  {az : c.RawStripPiece width // (c.stripPiece width az.1 az.2.val).Nonempty}

noncomputable def CoverData.stripKey {W : ℕ} {p : PathData W} (c : CoverData p)
    (width : ℝ) (az : c.UsedStripPiece width) : Fin p.C × UnitStripCode :=
  (c.old az.val.1, c.stripRow width az.val.1, az.val.2.val)

noncomputable def CoverData.usedStripKeys {W : ℕ} {p : PathData W} (c : CoverData p)
    (width : ℝ) : Finset (Fin p.C × UnitStripCode) := by
  classical
  exact Finset.univ.image (c.stripKey width)

section
variable {W m Mp Dp Mg Dg : ℕ} {p : PathData W} {c : CoverData p}
    {ℓ Nk L κ₁ δ₀ σ d₁ ρ gain ε width : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hc : c.Valid Nk L ω ν B d₁ ρ gain m Mg Dg ε) (ht : c.time = false)
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hc ht hp

lemma CoverData.Valid.stripPiece_bin_mem (hwidth : 0 < width) (a : Fin c.n) (z : ℤ)
    (hne : (c.stripPiece width a z).Nonempty) : z ∈ c.midpointBins width := by
  have hz := abs_le.mp (hc.stripPiece_center ht hp hwidth a z hne)
  apply Finset.mem_Icc.mpr
  constructor
  · have hle : -(p.κ + width) / width ≤ (z : ℝ) :=
      (div_le_iff₀ hwidth).mpr (by linarith)
    simpa only [Int.floor_intCast] using Int.floor_mono hle
  · have hle : (z : ℝ) ≤ (p.κ + width) / width :=
      (le_div_iff₀ hwidth).mpr (by linarith)
    simpa only [Int.floor_intCast] using Int.floor_mono hle

lemma CoverData.Valid.midpointBins_count (hwidth : 0 < width) :
    ((c.midpointBins width).card : ℝ) ≤ 2 * p.κ / width + 4 := by
  have hκ : 0 ≤ p.κ := by linarith [hp.one_le_slack]
  have hbound := Submission.Lib.K4AngularCharge.card_Icc_floor_le
    (-(p.κ + width) / width) ((p.κ + width) / width)
    (by apply div_le_div_of_nonneg_right _ hwidth.le; linarith)
  apply hbound.trans_eq
  field_simp
  ring

lemma CoverData.Valid.stripPiece_coverage (hwidth : 0 < width)
    (a : Fin c.n) (l : Trajectory) (hl : l ∈ c.assigned a) :
    ∃ az : c.UsedStripPiece width, az.val.1 = a ∧
      l ∈ c.stripPiece width az.val.1 az.val.2.val := by
  let z : ℤ := ⌊inner ℝ (Matrix.toEuclideanLin (p.frame (c.old a))⁻¹
    (gy l (c.oldMidpoint a) - p.center (c.old a) - c.oldMidpoint a • p.velocity (c.old a)))
    (c.stripRepresentative width (c.old a) (c.stripRow width a)).1 / width⌋
  have hmem : l ∈ c.stripPiece width a z := ⟨hl, rfl⟩
  have hne : (c.stripPiece width a z).Nonempty := ⟨l, hmem⟩
  exact ⟨⟨(a, ⟨z, hc.stripPiece_bin_mem ht hp hwidth a z hne⟩), hne⟩, rfl, hmem⟩

lemma CoverData.Valid.all_assignments_disjoint (a a' : Fin c.n) (hne : a ≠ a')
    (hw : p.world (c.old a) = p.world (c.old a'))
    (hj : p.bin (c.old a) = p.bin (c.old a')) : Disjoint (c.assigned a) (c.assigned a') := by
  by_cases hold : c.old a = c.old a'
  · exact hc.assignments_disjoint a a' hne hold
  · exact (hp.assignment_disjoint (c.old a) (c.old a') hold
      ((hc.old_level a).trans (hc.old_level a').symm) hw hj).mono
        (hc.assigned_subset a) (hc.assigned_subset a')

lemma CoverData.Valid.stripPieces_disjoint (a a' : Fin c.n) (z z' : ℤ)
    (hne : (a, z) ≠ (a', z'))
    (hw : p.world (c.old a) = p.world (c.old a'))
    (hj : p.bin (c.old a) = p.bin (c.old a')) :
    Disjoint (c.stripPiece width a z) (c.stripPiece width a' z') := by
  by_cases haa : a = a'
  · subst a'
    have hzz : z ≠ z' := fun h => hne (Prod.ext rfl h)
    apply Set.disjoint_left.mpr
    intro l hl hl'
    let x := inner ℝ (Matrix.toEuclideanLin (p.frame (c.old a))⁻¹
      (gy l (c.oldMidpoint a) - p.center (c.old a) - c.oldMidpoint a • p.velocity (c.old a)))
      (c.stripRepresentative width (c.old a) (c.stripRow width a)).1 / width
    have hz : ⌊x⌋ = z := hl.2
    have hz' : ⌊x⌋ = z' := hl'.2
    exact hzz (hz.symm.trans hz')
  · exact (hc.all_assignments_disjoint ht hp a a' haa hw hj).mono
      inter_subset_left inter_subset_left

open Classical in
lemma CoverData.Valid.usedStripPiece_count {Mr : ℕ} (hNk : 2 ≤ Nk)
    (hwidth : 0 < width) (hκ : p.κ ≤ Nk) (hinv : width⁻¹ ≤ Nk ^ Mr) :
    (Fintype.card (c.UsedStripPiece width) : ℝ) ≤ Nk ^ (Mg + Mr + 4) := by
  classical
  have hN1 : 1 ≤ Nk := by linarith
  have hN0 : 0 ≤ Nk := by linarith
  have hratio : p.κ / width ≤ Nk ^ (Mr + 1) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Nk * Nk ^ Mr := mul_le_mul hκ hinv (by positivity) hN0
      _ = _ := by rw [pow_add, pow_one]; ring
  have hbins : ((c.midpointBins width).card : ℝ) ≤ Nk ^ (Mr + 4) := by
    apply (hc.midpointBins_count ht hp hwidth).trans
    have hX : 1 ≤ Nk ^ (Mr + 1) := one_le_pow₀ hN1
    have h6 : 6 ≤ Nk ^ 3 := by
      have h8 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hNk 3
      norm_num at h8
      linarith
    calc
      _ ≤ 2 * Nk ^ (Mr + 1) + 4 := by
        rw [mul_div_assoc]
        exact add_le_add
          (mul_le_mul_of_nonneg_left hratio (show (0 : ℝ) ≤ 2 by norm_num)) le_rfl
      _ ≤ 6 * Nk ^ (Mr + 1) := by linarith
      _ ≤ Nk ^ 3 * Nk ^ (Mr + 1) := mul_le_mul_of_nonneg_right h6 (by positivity)
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hcard : Fintype.card (c.UsedStripPiece width) ≤ c.n * (c.midpointBins width).card := by
    calc
      _ ≤ Fintype.card (c.RawStripPiece width) := Fintype.card_subtype_le _
      _ = _ := by simp [CoverData.RawStripPiece]
  calc
    _ ≤ (c.n : ℝ) * ((c.midpointBins width).card : ℝ) := by exact_mod_cast hcard
    _ ≤ Nk ^ Mg * Nk ^ (Mr + 4) :=
      mul_le_mul hc.2.2.2.2.2.1 hbins (by positivity) (by positivity)
    _ = _ := by rw [← pow_add, Nat.add_assoc]

end

end Submission.Obl.k4_finite_positive_mixed_cover_realization
