-- Adapted from this LOT tree, obligation o254, branch x0898, commit 91a4f454, file Submission/Obl/k4_general_parent_wide_layer_candidates/NativeRefinementMenus.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.CommonDomains
import Submission.Lib.K4MovingMeshBoxes.Geometry

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.CommonDomain

open Set

noncomputable section

/-- A short original domain meets a controlled number of finer native
comparison domains, with the same original major and velocity bins. -/
theorem refinement_domain_menu {Q q χ g : ℝ} (hQ : 0 < Q) (hq : 0 < q)
    (hqQ : q ≤ Q) (hg : 0 < g) (D : Code) :
    ∃ S : Finset Code, (S.card : ℝ) ≤ 84 * (Q / q) ^ 2 ∧
      ∀ (b : Fin 6 → ℝ) (t : ℝ), code Q χ g (Q * g) b t = D →
        code q χ g (q * g) b t ∈ S := by
  classical
  have hQg : 0 < Q * g := mul_pos hQ hg
  have hqg : 0 < q * g := mul_pos hq hg
  have hratio : 1 ≤ Q / q := (one_le_div hq).mpr hqQ
  obtain ⟨J, hJ, hJcover⟩ :=
    Submission.Lib.K4MovingMeshBoxes.interval_mesh_cover hq hQ.le (timeCenter Q D)
  have hJcard : (J.card : ℝ) ≤ 6 * (Q / q) := by
    rw [mul_div_assoc] at hJ
    linarith
  let center (j : ℤ) := (D 4 : ℝ) * (Q * g) +
    ((j : ℝ) * q - timeCenter Q D) * ((D 3 : ℝ) * g)
  choose P hP hPcover using fun j : ℤ =>
    Submission.Lib.K4MovingMeshBoxes.interval_mesh_cover hqg
      (by positivity : 0 ≤ 3 * Q * g) (center j)
  have hPcard (j : ℤ) : ((P j).card : ℝ) ≤ 14 * (Q / q) := by
    have hid : 4 * (3 * Q * g) / (q * g) + 2 = 12 * (Q / q) + 2 := by
      field_simp
      ring
    have hj := hP j
    rw [hid] at hj
    linarith
  let Index := Σ _j : ℤ, ℤ
  let raw : Finset Index := J.sigma P
  let decode (i : Index) : Code := ![i.1, D 1, D 2, D 3, i.2]
  let S : Finset Code := raw.image decode
  refine ⟨S, ?_, ?_⟩
  · have hcard : (S.card : ℝ) ≤ raw.card := by
      exact_mod_cast (Finset.card_image_le : (raw.image decode).card ≤ raw.card)
    calc
      _ ≤ (raw.card : ℝ) := hcard
      _ = ∑ j ∈ J, ((P j).card : ℝ) := by
        simp only [Index, raw, Finset.card_sigma, Nat.cast_sum]
      _ ≤ ∑ _j ∈ J, 14 * (Q / q) := Finset.sum_le_sum fun j _ => hPcard j
      _ = (J.card : ℝ) * (14 * (Q / q)) := by simp
      _ ≤ (6 * (Q / q)) * (14 * (Q / q)) := by gcongr
      _ = _ := by ring
  · intro b t hD
    have hc (i : Fin 5) : code Q χ g (Q * g) b t i = D i := congrArg (fun c => c i) hD
    have htime : |t - timeCenter Q D| ≤ Q := by
      simpa only [hD] using time_error (χ := χ) (g := g) (m := Q * g) hQ b t
    have hj : ⌊t / q⌋ ∈ J := hJcover t htime
    let j : ℤ := ⌊t / q⌋
    have hshort : |t - (j : ℝ) * q| ≤ q := by
      simpa only [j, timeCenter, code, Matrix.cons_val_zero] using
        time_error (χ := χ) (g := g) (m := q * g) hq b t
    have hdistance : |(j : ℝ) * q - timeCenter Q D| ≤ 2 * Q := by
      have h := abs_sub_le ((j : ℝ) * q) t (timeCenter Q D)
      rw [abs_sub_comm ((j : ℝ) * q) t] at h
      linarith
    have hv : ⌊b 4 / g⌋ = D 3 := by simpa [code] using hc 3
    have hround : |b 4 - (D 3 : ℝ) * g| ≤ g := by
      simpa only [hv] using Submission.Lib.K4VelocityStrips.midpoint_floor_center_bound hg (b 4)
    have hleft : ⌊(b 1 + timeCenter Q D * b 4) / (Q * g)⌋ = D 4 := by
      have h := hc 4
      simpa [code, timeCenter,
        show ⌊t / Q⌋ = D 0 by simpa [code] using hc 0] using h
    have hposition : |b 1 + timeCenter Q D * b 4 - (D 4 : ℝ) * (Q * g)| ≤ Q * g := by
      simpa only [hleft] using Submission.Lib.K4VelocityStrips.midpoint_floor_center_bound
        hQg (b 1 + timeCenter Q D * b 4)
    have hnear : |b 1 + (j : ℝ) * q * b 4 - center j| ≤ 3 * Q * g := by
      have hid : b 1 + (j : ℝ) * q * b 4 - center j =
          (b 1 + timeCenter Q D * b 4 - (D 4 : ℝ) * (Q * g)) +
            ((j : ℝ) * q - timeCenter Q D) * (b 4 - (D 3 : ℝ) * g) := by
        dsimp [center]
        ring
      rw [hid]
      calc
        _ ≤ |b 1 + timeCenter Q D * b 4 - (D 4 : ℝ) * (Q * g)| +
            |((j : ℝ) * q - timeCenter Q D) * (b 4 - (D 3 : ℝ) * g)| := abs_add_le _ _
        _ ≤ Q * g + (2 * Q) * g := by rw [abs_mul]; gcongr
        _ = _ := by ring
    have hp : code q χ g (q * g) b t 4 ∈ P j := by
      simpa [code, j] using
        hPcover j (b 1 + (j : ℝ) * q * b 4) hnear
    apply Finset.mem_image.mpr
    refine ⟨⟨j, code q χ g (q * g) b t 4⟩, Finset.mem_sigma.mpr ⟨hj, hp⟩, ?_⟩
    have h₁ : ⌊b 3 / χ⌋ = D 1 := by simpa [code] using hc 1
    have h₂ : ⌊b 0 / χ⌋ = D 2 := by simpa [code] using hc 2
    ext i
    fin_cases i <;> simp [decode, code, j, h₁, h₂, hv]

end
end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.CommonDomain
