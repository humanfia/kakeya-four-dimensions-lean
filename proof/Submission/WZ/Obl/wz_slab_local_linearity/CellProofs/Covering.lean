-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.CellProofs.Covering.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
namespace WangZahlLot.Obl.wz_slab_local_linearity.CellProofs

open Set Metric

/-- The covering condition in the frozen statement. -/
def Assouad (d α C : ℝ) (B : Set ℝ) : Prop :=
  ∀ r R a : ℝ, d ≤ r → r ≤ R →
    ∃ (m : ℕ) (c : Fin m → ℝ),
      B ∩ Icc a (a + R) ⊆ ⋃ j, closedBall (c j) r ∧
        (m : ℝ) ≤ C * (R / r) ^ α

/-- The horizontal slice of the twisted projection. -/
def ProjectedSlice (f : ℝ → ℝ) (E : Set (EuclideanSpace ℝ (Fin 3)))
    (z : ℝ) : Set ℝ :=
  {u | (u, z) ∈ (fun p => (p 0 + f (p 2) * p 1, p 2)) '' E}

theorem Assouad.mono_set {d α C : ℝ} {A B : Set ℝ}
    (h : Assouad d α C B) (hAB : A ⊆ B) : Assouad d α C A := by
  intro r R a hdr hrR
  obtain ⟨m, c, hc, hm⟩ := h r R a hdr hrR
  exact ⟨m, c, (inter_subset_inter_left _ hAB).trans hc, hm⟩

theorem Assouad.mono_constant {d α C C' : ℝ} {B : Set ℝ}
    (hd : 0 < d) (h : Assouad d α C B) (hCC' : C ≤ C') : Assouad d α C' B := by
  intro r R a hdr hrR
  obtain ⟨m, c, hc, hm⟩ := h r R a hdr hrR
  refine ⟨m, c, hc, hm.trans ?_⟩
  exact mul_le_mul_of_nonneg_right hCC'
    (Real.rpow_nonneg (div_nonneg (hd.le.trans (hdr.trans hrR)) (hd.le.trans hdr)) _)

theorem projectedSlice_mono {f : ℝ → ℝ} {E F : Set (EuclideanSpace ℝ (Fin 3))}
    (hEF : E ⊆ F) (z : ℝ) : ProjectedSlice f E z ⊆ ProjectedSlice f F z :=
  fun _ hu => image_mono hEF hu

/-- A pointwise perturbation by at most the smallest scale costs a factor of six.
The two new balls over each old ball are essential: a perturbation cannot in general
be absorbed without changing the covering multiplicity. -/
theorem Assouad.perturb {d α C : ℝ} {A B : Set ℝ}
    (hd : 0 < d) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hC : 0 ≤ C)
    (hB : Assouad d α C B)
    (hAB : ∀ u ∈ A, ∃ v ∈ B, |u - v| ≤ d) :
    Assouad d α (6 * C) A := by
  intro r R a hdr hrR
  have hr : 0 < r := hd.trans_le hdr
  have hR : 0 < R := hr.trans_le hrR
  obtain ⟨m, c, hc, hm⟩ := hB r (R + 2 * d) (a - d) hdr (by linarith)
  let c' : Fin (m + m) → ℝ := Fin.append (fun j => c j - r) (fun j => c j + r)
  refine ⟨m + m, c', ?_, ?_⟩
  · rintro u ⟨hu, hua, huR⟩
    obtain ⟨v, hv, huv⟩ := hAB u hu
    have huv' := abs_le.mp huv
    have hvI : v ∈ Icc (a - d) (a - d + (R + 2 * d)) := by
      constructor <;> linarith
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hc ⟨hv, hvI⟩)
    have hj' : |v - c j| ≤ r := by simpa only [mem_closedBall, Real.dist_eq] using hj
    have huc : |u - c j| ≤ 2 * r := by
      calc |u - c j| ≤ |u - v| + |v - c j| := abs_sub_le _ _ _
        _ ≤ 2 * r := by linarith
    obtain ⟨huc0, huc1⟩ := abs_le.mp huc
    by_cases hside : u ≤ c j
    · refine mem_iUnion.mpr ⟨Fin.castAdd m j, ?_⟩
      simp only [c', Fin.append_left, mem_closedBall, Real.dist_eq, abs_le]
      constructor <;> linarith
    · refine mem_iUnion.mpr ⟨Fin.natAdd m j, ?_⟩
      simp only [c', Fin.append_right, mem_closedBall, Real.dist_eq, abs_le]
      constructor <;> linarith
  · have hratio : (R + 2 * d) / r ≤ 3 * (R / r) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by linarith) hr.le
    have hp : ((R + 2 * d) / r) ^ α ≤ 3 * (R / r) ^ α := by
      calc ((R + 2 * d) / r) ^ α
          ≤ (3 * (R / r)) ^ α := Real.rpow_le_rpow (by positivity) hratio hα0
        _ = (3 : ℝ) ^ α * (R / r) ^ α := Real.mul_rpow (by norm_num) (by positivity)
        _ ≤ 3 * (R / r) ^ α := mul_le_mul_of_nonneg_right
          (Real.rpow_le_self_of_one_le (by norm_num) hα1) (by positivity)
    have hcount := hm.trans (mul_le_mul_of_nonneg_left hp hC)
    push_cast
    nlinarith

/-- The twisted projection moves by at most the slope error inside the unit strip. -/
theorem projectedSlice_perturb {f g : ℝ → ℝ} {E F : Set (EuclideanSpace ℝ (Fin 3))}
    {d z : ℝ} (hEF : E ⊆ F) (hstrip : ∀ p ∈ E, |p 1| ≤ 1)
    (hfg : ∀ p ∈ E, |g (p 2) - f (p 2)| ≤ d) :
    ∀ u ∈ ProjectedSlice g E z, ∃ v ∈ ProjectedSlice f F z, |u - v| ≤ d := by
  rintro u ⟨p, hp, he⟩
  have hu : p 0 + g (p 2) * p 1 = u := congrArg Prod.fst he
  have hz : p 2 = z := congrArg Prod.snd he
  refine ⟨p 0 + f (p 2) * p 1, ⟨p, hEF hp, by simp only [hz]⟩, ?_⟩
  rw [← hu, show p 0 + g (p 2) * p 1 - (p 0 + f (p 2) * p 1) =
    (g (p 2) - f (p 2)) * p 1 by ring, abs_mul]
  calc |g (p 2) - f (p 2)| * |p 1| ≤ |g (p 2) - f (p 2)| * 1 :=
      mul_le_mul_of_nonneg_left (hstrip p hp) (abs_nonneg _)
    _ ≤ d := by simpa only [mul_one] using hfg p hp

theorem Assouad.projectedSlice_change {d α C z : ℝ}
    {f g : ℝ → ℝ} {E F : Set (EuclideanSpace ℝ (Fin 3))}
    (hd : 0 < d) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hC : 0 ≤ C)
    (hF : Assouad d α C (ProjectedSlice f F z))
    (hEF : E ⊆ F) (hstrip : ∀ p ∈ E, |p 1| ≤ 1)
    (hfg : ∀ p ∈ E, |g (p 2) - f (p 2)| ≤ d) :
    Assouad d α (6 * C) (ProjectedSlice g E z) :=
  hF.perturb hd hα0 hα1 hC (projectedSlice_perturb hEF hstrip hfg)

end WangZahlLot.Obl.wz_slab_local_linearity.CellProofs
