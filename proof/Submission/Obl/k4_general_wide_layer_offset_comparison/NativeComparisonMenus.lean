-- Adapted from this LOT tree, obligation o254, branch x0898, commit 91a4f454, file Submission/Obl/k4_general_parent_wide_layer_candidates/NativeComparisonMenus.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.TrueDomainGeometry

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.CommonDomain

open Set

noncomputable section

/-- At fixed original major bins, one true packet meets only the stated
number of small native comparison domains. No major-bin count is charged. -/
theorem true_tag_domain_menu {K Q q χ g w t₀ : ℝ}
    (hK : 1 ≤ K) (hQ : 0 < Q) (hq : 0 < q) (hqQ : q ≤ Q)
    (hχ : 0 < χ) (hg : 0 < g) (hχg : χ ≤ g) (hχQg : χ ≤ Q * g)
    (hw : 0 < w) (hwQg : w ≤ Q * g)
    (c : Fin 5 → ℝ) (hc₄ : |c 4| ≤ K) (tag : Fin 2 → ℤ) :
    ∃ S : Finset Code,
      (S.card : ℝ) ≤ 1320 * K ^ 2 * (Q / q) * (Q * g / w) ∧
      ∀ (b : Fin 6 → ℝ) (t : ℝ), t ∈ Icc (0 : ℝ) 1 → |t - t₀| ≤ Q →
        ⌊b 3 / χ⌋ = tag 0 → ⌊b 0 / χ⌋ = tag 1 →
        |rowError c b t₀| ≤ K * Q * g →
        |b 4 - c 3 - c 4 * b 3| ≤ K * g → code q χ g w b t ∈ S := by
  classical
  have hK0 : 0 ≤ K := (zero_le_one : (0 : ℝ) ≤ 1).trans hK
  obtain ⟨J, hJ, hJcover⟩ :=
    Submission.Lib.K4MovingMeshBoxes.interval_mesh_cover hq hQ.le t₀
  have hJcard : (J.card : ℝ) ≤ 6 * (Q / q) := by
    have hratio : 1 ≤ Q / q := (one_le_div hq).mpr hqQ
    rw [mul_div_assoc] at hJ
    linarith
  obtain ⟨G, hG, hGcover⟩ :=
    Submission.Lib.K4MovingMeshBoxes.interval_mesh_cover hg
      (by positivity : 0 ≤ 2 * K * g) (c 3 + c 4 * ((tag 0 : ℝ) * χ))
  have hGcard : (G.card : ℝ) ≤ 10 * K := by
    have hid : 4 * (2 * K * g) / g + 2 = 8 * K + 2 := by field_simp; ring
    rw [hid] at hG
    linarith
  obtain ⟨P, hP, hPcover⟩ := true_position_menus (t₀ := t₀)
    hK hq hqQ hχ hχQg hw hwQg c hc₄
  have hPcard (j : ℤ) : ((P j (tag 0) (tag 1)).card : ℝ) ≤ 22 * K * Q * g / w :=
    (le_div_iff₀ hw).mpr (hP j (tag 0) (tag 1))
  let Index := Σ _j : ℤ, Σ _v : ℤ, ℤ
  let raw : Finset Index := J.sigma fun j => G.sigma fun _v => P j (tag 0) (tag 1)
  let decode (i : Index) : Code := ![i.1, tag 0, tag 1, i.2.1, i.2.2]
  let S : Finset Code := raw.image decode
  refine ⟨S, ?_, ?_⟩
  · have hcard : (S.card : ℝ) ≤ raw.card := by
      exact_mod_cast (Finset.card_image_le : (raw.image decode).card ≤ raw.card)
    calc
      _ ≤ (raw.card : ℝ) := hcard
      _ = ∑ j ∈ J, ∑ _v ∈ G, ((P j (tag 0) (tag 1)).card : ℝ) := by
        simp only [Index, raw, Finset.card_sigma, Nat.cast_sum]
      _ ≤ ∑ _j ∈ J, ∑ _v ∈ G, 22 * K * Q * g / w :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun _v _ => hPcard j
      _ = (J.card : ℝ) * (G.card : ℝ) * (22 * K * Q * g / w) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ (6 * (Q / q)) * (10 * K) * (22 * K * Q * g / w) := by gcongr
      _ = _ := by ring
  · intro b t ht htt₀ hv hz hposition hslope
    have hround : |b 3 - (tag 0 : ℝ) * χ| ≤ χ := by
      simpa only [hv] using
        Submission.Lib.K4VelocityStrips.midpoint_floor_center_bound hχ (b 3)
    have hvelocity : |b 4 - (c 3 + c 4 * ((tag 0 : ℝ) * χ))| ≤ 2 * K * g := by
      have hid : b 4 - (c 3 + c 4 * ((tag 0 : ℝ) * χ)) =
          (b 4 - c 3 - c 4 * b 3) + c 4 * (b 3 - (tag 0 : ℝ) * χ) := by ring
      rw [hid]
      calc
        _ ≤ |b 4 - c 3 - c 4 * b 3| + |c 4 * (b 3 - (tag 0 : ℝ) * χ)| := abs_add_le _ _
        _ ≤ K * g + K * χ := by rw [abs_mul]; gcongr
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hχg hK0]
    have hj : ⌊t / q⌋ ∈ J := hJcover t htt₀
    have hγ : ⌊b 4 / g⌋ ∈ G := hGcover (b 4) hvelocity
    have hp : code q χ g w b t 4 ∈ P ⌊t / q⌋ (tag 0) (tag 1) := by
      simpa only [hv, hz] using hPcover b t ht htt₀ hposition hslope
    apply Finset.mem_image.mpr
    refine ⟨⟨⌊t / q⌋, ⟨⌊b 4 / g⌋, code q χ g w b t 4⟩⟩,
      Finset.mem_sigma.mpr ⟨hj, Finset.mem_sigma.mpr ⟨hγ, hp⟩⟩, ?_⟩
    ext i
    fin_cases i <;> simp [decode, code, hv, hz]

end
end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.CommonDomain
