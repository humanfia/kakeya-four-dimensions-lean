-- Adapted from this LOT tree, obligation o254, branch x0898, commit 91a4f454, file Submission/Obl/k4_general_parent_wide_layer_candidates/NativeCommonNumerics.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open Filter

/-- A finer original major mesh fits the stable native common frame.
The conclusion is uniform over the actual dyadic block length. -/
theorem eventually_native_common_mesh {N M : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hM : ∀ k, 1 ≤ M k)
    (hMs : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, M k ≤ N k ^ ε)
    (C : ℕ) {κ ℓ s m : ℝ} (hgap : (κ + ℓ) * s < m) :
    ∀ᶠ k in atTop, ∀ Q : ℝ, N k ^ (-κ * s) / M k ≤ Q →
      N k ^ (-m) ≤ (Q * N k ^ (-ℓ * s)) / (10000 * M k ^ C) := by
  have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hM hMs (C + 1) (show -m < -(κ + ℓ) * s by linarith)
    (by norm_num : (0 : ℝ) ≤ 10000)
  filter_upwards [hsmall] with k hk
  intro Q hQ
  have hNp : 0 < N k := zero_lt_one.trans_le (hN k)
  have hMp : 0 < M k := zero_lt_one.trans_le (hM k)
  have hQg : N k ^ (-κ * s) * N k ^ (-ℓ * s) ≤ Q * M k * N k ^ (-ℓ * s) :=
    mul_le_mul_of_nonneg_right ((div_le_iff₀ hMp).mp hQ) (by positivity)
  have hpowers : N k ^ (-(κ + ℓ) * s) = N k ^ (-κ * s) * N k ^ (-ℓ * s) := by
    rw [← Real.rpow_add hNp]
    congr 1
    ring
  have hscaled : N k ^ (-m) * (10000 * M k ^ C) * M k ≤
      Q * N k ^ (-ℓ * s) * M k := by
    calc
      _ = 10000 * M k ^ (C + 1) * N k ^ (-m) := by ring
      _ ≤ N k ^ (-(κ + ℓ) * s) := hk.le
      _ = N k ^ (-κ * s) * N k ^ (-ℓ * s) := hpowers
      _ ≤ Q * M k * N k ^ (-ℓ * s) := hQg
      _ = _ := by ring
  apply (le_div_iff₀ (by positivity : 0 < 10000 * M k ^ C)).mpr
  exact le_of_mul_le_mul_right hscaled hMp

/-- The literal small common frame meets all elementary geometric
conditions for the native and projected source families. -/
theorem native_common_scale_bounds {M V Q g χ β : ℝ}
    (hM : 1 ≤ M) (hMV : M ≤ V) (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hg : 0 < g) (hg1 : g ≤ 1) (hχ : 0 < χ)
    (hχw : χ ≤ Q * g / (10000 * V)) (hβ : g / M ≤ β) :
    let q := Q / (10000 * V)
    let w := q * g
    0 < q ∧ 0 < w ∧ q ≤ Q ∧ q ≤ 1 ∧
      χ ≤ 1 ∧ χ ≤ g ∧ χ ≤ Q ∧ χ ≤ Q * g ∧
      w ≤ Q * g ∧ w ≤ β ∧ χ ≤ w ∧
      q ≤ V⁻¹ * Q / 10000 ∧ w ≤ V⁻¹ * (Q * g) / 10000 := by
  intro q w
  have hMp : 0 < M := zero_lt_one.trans_le hM
  have hV1 : 1 ≤ V := hM.trans hMV
  have hVp : 0 < V := zero_lt_one.trans_le hV1
  have hden : 0 < 10000 * V := by positivity
  have hq : 0 < q := div_pos hQ hden
  have hw : 0 < w := mul_pos hq hg
  have hqQ : q ≤ Q := div_le_self hQ.le (by linarith)
  have hq1 : q ≤ 1 := hqQ.trans hQ1
  have hqM : q ≤ 1 / M := by
    apply (le_div_iff₀ hMp).mpr
    change Q / (10000 * V) * M ≤ 1
    rw [div_mul_eq_mul_div, div_le_one hden]
    exact (mul_le_mul_of_nonneg_right hQ1 hMp.le).trans (by linarith)
  have hχw' : χ ≤ w := by
    simpa only [w, q, div_mul_eq_mul_div] using hχw
  have hwQg : w ≤ Q * g := mul_le_mul_of_nonneg_right hqQ hg.le
  have hwg : w ≤ g := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hq1 hg.le
  have hwQ : w ≤ Q :=
    hwQg.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hg1 hQ.le)
  have hwβ : w ≤ β := by
    apply le_trans _ hβ
    calc
      _ ≤ (1 / M) * g := mul_le_mul_of_nonneg_right hqM hg.le
      _ = _ := by ring
  have hqe : q = V⁻¹ * Q / 10000 := by dsimp [q]; field_simp
  have hwe : w = V⁻¹ * (Q * g) / 10000 := by dsimp [w, q]; field_simp
  exact ⟨hq, hw, hqQ, hq1, (hχw'.trans hwg).trans hg1,
    hχw'.trans hwg, hχw'.trans hwQ, hχw'.trans hwQg,
    hwQg, hwβ, hχw', hqe.le, hwe.le⟩

/-- One fine physical mesh resolves every coordinate of the common
frame. Only its smallest scale, the original major mesh, matters. -/
theorem native_common_mesh_resolution {N M s m u : ℝ}
    (hN : 0 < N) (hM : 1 ≤ M) (hu : N ^ (-m) ≤ u)
    (hsmall : 3 * M * N ^ (-1 : ℝ) ≤ 1) :
    (2 * M + 1) * N ^ (-(m + s + 1)) ≤ 100 * u * (N ^ (-s) / 100) := by
  have hδ : N ^ (-(m + s + 1)) = N ^ (-m) * N ^ (-s) * N ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hN, ← Real.rpow_add hN]
    congr 1
    ring
  have hM0 : 0 ≤ M := by linarith
  have ha : 0 ≤ N ^ (-s) := by positivity
  have hχ : 0 ≤ N ^ (-m) := by positivity
  calc
    _ ≤ (3 * M) * N ^ (-(m + s + 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (N ^ (-m) * N ^ (-s)) * (3 * M * N ^ (-1 : ℝ)) := by rw [hδ]; ring
    _ ≤ (N ^ (-m) * N ^ (-s)) * 1 :=
      mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ ≤ u * N ^ (-s) := by simpa only [mul_one] using mul_le_mul_of_nonneg_right hu ha
    _ = _ := by ring

theorem native_common_jitter_resolution {V a : ℝ} (hV : 0 ≤ V) (ha : 0 ≤ a) :
    2 * (4 * V) * (3 * (a / 100)) ≤ (8 * V * a) / 2 := by
  nlinarith [mul_nonneg hV ha]

end Submission.Obl.k4_general_wide_layer_offset_comparison
