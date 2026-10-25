-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.MixedPlunnecke.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.RealPlunnecke
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.RealCover

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open scoped Pointwise

/-- A cover of a mixed sum controls the corresponding integer sumset. -/
theorem grid_mixed_sum_card_le {δ : ℝ} (hδ : 0 < δ) (A B : Finset ℝ)
    {m : ℕ} (cc : Fin m → ℝ) (hcov : Covers δ (↑(A + B) : Set ℝ) cc) :
    ((A.image (realGridIndex δ) + B.image (realGridIndex δ)).card : ℝ) ≤ 6 * (m : ℝ) := by
  classical
  have hcov' : Covers δ ((fun p : ℝ × ℝ => p.1 + p.2) '' (↑(A ×ˢ B) : Set (ℝ × ℝ))) cc := by
    rintro x ⟨p, hp, rfl⟩
    exact hcov (Finset.add_mem_add (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2)
  obtain ⟨S, hSc, hS⟩ := grid_sums_of_cover hδ (A ×ˢ B) cc hcov'
  have hsub : A.image (realGridIndex δ) + B.image (realGridIndex δ) ⊆ S := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact hS (a, b) (Finset.mem_product.mpr ⟨ha, hb⟩)
  have hc : ((A.image (realGridIndex δ) + B.image (realGridIndex δ)).card : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hc.trans hSc

/-- Plunnecke's inequality permits a different base set from the set being
iterated. The denominator is the number of occupied base grid cells. -/
theorem mixed_plunnecke_cover {δ : ℝ} (hδ : 0 < δ) (A B : Finset ℝ) (hA : A.Nonempty)
    {m : ℕ} (cc : Fin m → ℝ) (hcov : Covers δ (↑(A + B) : Set ℝ) cc) (k l : ℕ) :
    ∃ (n : ℕ) (centers : Fin n → ℝ),
      Covers (((k + l : ℕ) : ℝ) * δ) (↑(k • B - l • B) : Set ℝ) centers ∧
      (n : ℝ) ≤ (6 * (m : ℝ) / (A.image (realGridIndex δ)).card) ^ (k + l) *
        (A.image (realGridIndex δ)).card := by
  classical
  let G := A.image (realGridIndex δ)
  let H := B.image (realGridIndex δ)
  have hG : G.Nonempty := hA.image _
  have hGc : (0 : ℝ) < G.card := by exact_mod_cast Finset.card_pos.mpr hG
  have hsum := grid_mixed_sum_card_le hδ A B cc hcov
  obtain ⟨n, centers, hcover, hn⟩ := cover_of_grid_nsmul_sub_nsmul hδ B k l
  refine ⟨n, centers, hcover, ?_⟩
  rw [hn]
  have hp : ((k • H - l • H).card : ℝ) ≤
      (((G + H).card : ℝ) / (G.card : ℝ)) ^ (k + l) * (G.card : ℝ) := by
    have hh := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hG H k l
    have hh' := (NNRat.cast_le (K := ℝ)).mpr hh
    push_cast at hh'
    exact hh'
  apply hp.trans
  gcongr

/-- For a separated base, a nine-term mixed expansion has a cover at the
original radius with an absolute factor nine. -/
theorem mixed_plunnecke_nine {δ K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (A B : Finset ℝ) (hA : A.Nonempty)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b)
    {m : ℕ} (cc : Fin m → ℝ) (hcov : Covers δ (↑(A + B) : Set ℝ) cc)
    (hm : (m : ℝ) ≤ K * (A.card : ℝ)) (k l : ℕ) (hkl : k + l ≤ 9) :
    ∃ (n : ℕ) (centers : Fin n → ℝ), Covers δ (↑(k • B - l • B) : Set ℝ) centers ∧
      (n : ℝ) ≤ 9 * (6 * K) ^ (k + l) * (A.card : ℝ) := by
  classical
  obtain ⟨n, centers, hc, hn⟩ := mixed_plunnecke_cover hδ A B hA cc hcov k l
  have hcard : (A.image (realGridIndex δ)).card = A.card :=
    Finset.card_image_iff.mpr (realGridIndex_injective hδ hsep)
  rw [hcard] at hn
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hquot : 6 * (m : ℝ) / (A.card : ℝ) ≤ 6 * K := by
    apply (div_le_iff₀ hAp).mpr
    nlinarith
  have hn' : (n : ℝ) ≤ (6 * K) ^ (k + l) * (A.card : ℝ) := by
    apply hn.trans
    gcongr
  have hc' : Covers (9 * δ) (↑(k • B - l • B) : Set ℝ) centers :=
    hc.mono_radius (mul_le_mul_of_nonneg_right (by exact_mod_cast hkl) hδ.le)
  obtain ⟨centers', hc''⟩ := hc'.refine_nine
  refine ⟨n * 9, centers', hc'', ?_⟩
  push_cast
  nlinarith

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
