/-
Adapted from: here:o204
Original o204 sources and file-level provenance are recorded below.
-/
/- Original provenance: here:o204, session x0706, commit d013eb32;
   original file Submission/Obl/k4_uniform_sampled_isotropic_branches/AnisotropicSupport.lean. -/
import Submission.Lib.K4OriginalGeometricReference.GraphCells

/-!
Original full-prior floors cancel the determinant of a narrowed old
frame against the sum of the fine graph-box volumes. No largest-side
cube or ambient packet-count factor is used.
-/

namespace Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells

open Set

noncomputable section

/-- The exact volume cancellation, with an arbitrary old frame and
possibly varying fine times and determinants. The masses in `mass` are
earlier ORIGINAL witness masses; their full-prior floors are explicit. -/
theorem original_graph_box_volume_budget
    {I : Type*} [Fintype I]
    (boxVolume fineTime fineDet prior mass : I → ℝ)
    {N fOld fFine oldTime oldDet oldPrior Kbox Kfine Kold θ : ℝ}
    (hN : 0 < N) (ht : 0 < oldTime) (hdet : 0 < oldDet) (hθ : 0 < θ)
    (hKbox : 0 ≤ Kbox) (hKfine : 0 ≤ Kfine) (_hKold : 0 ≤ Kold)
    (htime : ∀ i, 0 ≤ fineTime i)
    (hbox : ∀ i, boxVolume i ≤ Kbox * fineTime i * fineDet i / (oldTime * oldDet))
    (hprior : ∀ i, fineDet i ≤ Kfine * N ^ fFine * prior i)
    (hfloor : ∀ i, θ * fineTime i * prior i ≤ mass i)
    (hsum : (∑ i, mass i) ≤ oldTime * oldPrior)
    (hold : oldPrior ≤ Kold * N ^ (-fOld) * oldDet) :
    (∑ i, boxVolume i) ≤ (Kbox * Kfine * Kold / θ) * N ^ (fFine - fOld) := by
  have hpoint (i : I) : boxVolume i ≤
      (Kbox * Kfine * N ^ fFine / (oldTime * oldDet * θ)) * mass i := by
    have hfl : fineTime i * prior i ≤ mass i / θ := by
      apply (le_div_iff₀ hθ).mpr
      nlinarith [hfloor i]
    calc
      boxVolume i ≤ Kbox * fineTime i * fineDet i / (oldTime * oldDet) := hbox i
      _ ≤ Kbox * fineTime i * (Kfine * N ^ fFine * prior i) / (oldTime * oldDet) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hprior i) (mul_nonneg hKbox (htime i))) (by positivity)
      _ = Kbox * Kfine * N ^ fFine / (oldTime * oldDet) * (fineTime i * prior i) := by ring
      _ ≤ Kbox * Kfine * N ^ fFine / (oldTime * oldDet) * (mass i / θ) :=
        mul_le_mul_of_nonneg_left hfl (by positivity)
      _ = _ := by ring
  have hpower : N ^ fFine * N ^ (-fOld) = N ^ (fFine - fOld) := by
    rw [← Real.rpow_add hN]
    congr 1
  calc
    (∑ i, boxVolume i) ≤ ∑ i, (Kbox * Kfine * N ^ fFine /
        (oldTime * oldDet * θ)) * mass i := Finset.sum_le_sum (fun i _ => hpoint i)
    _ = (Kbox * Kfine * N ^ fFine / (oldTime * oldDet * θ)) * ∑ i, mass i :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (Kbox * Kfine * N ^ fFine / (oldTime * oldDet * θ)) *
        (oldTime * (Kold * N ^ (-fOld) * oldDet)) := by
      apply mul_le_mul_of_nonneg_left
        (hsum.trans (mul_le_mul_of_nonneg_left hold ht.le)) (by positivity)
    _ = (Kbox * Kfine * Kold / θ) * (N ^ fFine * N ^ (-fOld)) := by
      field_simp
    _ = _ := by rw [hpower]

/-- A family of actual rectangular graph entries is charged to its SUM
of base volumes. This works for anisotropic boxes of different shapes. -/
theorem rectangular_graph_family_cover
    {I X : Type*} [Fintype I]
    (Z : X → Fin 3 → ℝ) (signal : X → ℝ)
    (A : I → Set X) (c H : I → Fin 3 → ℝ)
    {R mesh V : ℝ} (hR : 0 ≤ R) (hmesh : 0 < mesh)
    (hresolve : ∀ i j, mesh ≤ H i j)
    (hbox : ∀ i x, x ∈ A i → ∀ j, |Z x j - c i j| ≤ H i j)
    (hosc : ∀ i x, x ∈ A i → ∀ y, y ∈ A i →
      baseCode mesh (Z x) = baseCode mesh (Z y) → |signal x - signal y| ≤ R * mesh)
    (hvolume : (∑ i, ∏ j, H i j) ≤ V) :
    ∃ S : Finset (Fin 4 → ℤ),
      (S.card : ℝ) * mesh ^ 3 ≤ 216 * (2 * R + 2) * V ∧
      ∀ i x, x ∈ A i → pointCode mesh (Z x) (signal x) ∈ S := by
  classical
  choose cells hcells hcover using fun i =>
    graph_cells_rectangular_volume Z signal (A i) (c i) (H i) hR hmesh
      (hresolve i) (hbox i) (hosc i)
  let S := Finset.univ.biUnion cells
  have hcard : (S.card : ℝ) ≤ ∑ i, ((cells i).card : ℝ) := by
    exact_mod_cast Finset.card_biUnion_le
  refine ⟨S, ?_, ?_⟩
  · calc
      (S.card : ℝ) * mesh ^ 3 ≤ (∑ i, ((cells i).card : ℝ)) * mesh ^ 3 :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = ∑ i, ((cells i).card : ℝ) * mesh ^ 3 := Finset.sum_mul _ _ _
      _ ≤ ∑ i, 216 * (∏ j, H i j) * (2 * R + 2) := Finset.sum_le_sum (fun i _ => hcells i)
      _ = (216 * (2 * R + 2)) * ∑ i, ∏ j, H i j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hvolume (by positivity)
  · intro i x hx
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hcover i x hx⟩

/-- Full original entry floors and exact determinant geometry give
support dimension three plus the ORIGINAL profile slope, independently
of the accumulated narrowing of the old frame. -/
theorem original_anisotropic_graph_support
    {I X : Type*} [Fintype I]
    (Z : X → Fin 3 → ℝ) (signal : X → ℝ)
    (A : I → Set X) (c H : I → Fin 3 → ℝ)
    (fineTime fineDet prior mass : I → ℝ)
    {N fOld fFine fZero rOld rFine d error oldTime oldDet oldPrior Kbox Kfine Kold θ R mesh : ℝ}
    (hN : 1 ≤ N) (ht : 0 < oldTime) (hdet : 0 < oldDet) (hθ : 0 < θ)
    (hKbox : 0 ≤ Kbox) (hKfine : 0 ≤ Kfine) (hKold : 0 ≤ Kold)
    (htime : ∀ i, 0 ≤ fineTime i)
    (hR : 0 ≤ R) (hmesh : 0 < mesh) (hmeshN : mesh = N ^ (-(rFine - rOld)))
    (hresolve : ∀ i j, mesh ≤ H i j)
    (hbox : ∀ i x, x ∈ A i → ∀ j, |Z x j - c i j| ≤ H i j)
    (hosc : ∀ i x, x ∈ A i → ∀ y, y ∈ A i →
      baseCode mesh (Z x) = baseCode mesh (Z y) → |signal x - signal y| ≤ R * mesh)
    (hgeometry : ∀ i, (∏ j, H i j) ≤ Kbox * fineTime i * fineDet i / (oldTime * oldDet))
    (hprior : ∀ i, fineDet i ≤ Kfine * N ^ fFine * prior i)
    (hfloor : ∀ i, θ * fineTime i * prior i ≤ mass i)
    (hsum : (∑ i, mass i) ≤ oldTime * oldPrior)
    (hold : oldPrior ≤ Kold * N ^ (-fOld) * oldDet)
    (hOldProfile : |fOld - fZero - d * rOld| ≤ error)
    (hFineProfile : |fFine - fZero - d * rFine| ≤ error) :
    ∃ S : Finset (Fin 4 → ℤ),
      (S.card : ℝ) * mesh ^ (3 + d) ≤
        (216 * (2 * R + 2) * (Kbox * Kfine * Kold / θ)) * N ^ (2 * error) ∧
      ∀ i x, x ∈ A i → pointCode mesh (Z x) (signal x) ∈ S := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hvolume := original_graph_box_volume_budget (fun i => ∏ j, H i j)
    fineTime fineDet prior mass hNpos ht hdet hθ hKbox hKfine hKold htime
    hgeometry hprior hfloor hsum hold
  obtain ⟨S, hS, hcover⟩ := rectangular_graph_family_cover Z signal A c H
    hR hmesh hresolve hbox hosc hvolume
  let C := 216 * (2 * R + 2) * (Kbox * Kfine * Kold / θ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcount : (S.card : ℝ) * mesh ^ 3 ≤ C * N ^ (fFine - fOld) := by
    convert hS using 1 <;> dsimp [C] <;> ring
  have hpow : mesh ^ d = N ^ (-d * (rFine - rOld)) := by
    rw [hmeshN, ← Real.rpow_mul hNpos.le]
    congr 1
    ring
  have hsplit : mesh ^ (3 + d) = mesh ^ 3 * mesh ^ d := by
    rw [Real.rpow_add hmesh]
    norm_num
  have hexp : fFine - fOld + (-d * (rFine - rOld)) ≤ 2 * error := by
    rcases abs_le.mp hOldProfile with ⟨_, hlo⟩
    rcases abs_le.mp hFineProfile with ⟨hhi, _⟩
    rcases abs_le.mp hOldProfile with ⟨hOldLower, _⟩
    rcases abs_le.mp hFineProfile with ⟨_, hFineUpper⟩
    nlinarith
  refine ⟨S, ?_, hcover⟩
  calc
    (S.card : ℝ) * mesh ^ (3 + d) = ((S.card : ℝ) * mesh ^ 3) * mesh ^ d := by
      rw [hsplit, mul_assoc]
    _ ≤ (C * N ^ (fFine - fOld)) * mesh ^ d :=
      mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg hmesh.le _)
    _ = C * N ^ (fFine - fOld + (-d * (rFine - rOld))) := by
      rw [hpow, mul_assoc, ← Real.rpow_add hNpos]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN hexp) hC

end

end Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
