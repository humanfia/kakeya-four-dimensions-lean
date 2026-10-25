-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Types
import Submission.WZ.Obl.wz_tube_packing_bound

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open MeasureTheory

lemma Admissible.mono_density {d d' δ : ℝ} {n : ℕ} {x v : Fin n → E}
    {Y : Fin n → Set E} (h : Admissible d δ n x v Y) (hd : d' ≤ d) :
    Admissible d' δ n x v Y := by
  rcases h with ⟨hn, hv, hB, hdj, hm, hY, hmass⟩
  refine ⟨hn, hv, hB, hdj, hm, hY, le_trans ?_ hmass⟩
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg n)) (sq_nonneg δ)

/-- The exponent `100` in the certificate requires no geometric extraction: it follows
from the accepted four-parameter packing bound after a uniform reduction of the cutoff. -/
lemma exists_card_cutoff : ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 100 ∧
    ∀ (δ d : ℝ) (n : ℕ) (x v : Fin n → E) (Y : Fin n → Set E),
      0 < δ → δ ≤ δ₀ → Admissible d δ n x v Y → (n : ℝ) ≤ δ ^ (-100 : ℝ) := by
  obtain ⟨C, hC, hpack⟩ := WangZahlLot.wz_tube_packing_bound
  refine ⟨min (1 / 100) (C + 1)⁻¹, lt_min (by norm_num) (by positivity),
    min_le_left _ _, ?_⟩
  intro δ d n x v Y hδ hδ₀ hA
  have hδmax : δ ≤ 1 / 100 := hδ₀.trans (min_le_left _ _)
  have hδC : δ ≤ (C + 1)⁻¹ := hδ₀.trans (min_le_right _ _)
  obtain ⟨hn, hv, hB, hdj, hm, hY, hmass⟩ := hA
  have hpack' := hpack δ hδ hδmax n x v hv hB hdj
  have hδ96 : δ ^ (96 : ℕ) ≤ δ := by
    simpa using Real.rpow_le_self_of_le_one hδ.le (show δ ≤ 1 by linarith)
      (show (1 : ℝ) ≤ 96 by norm_num)
  have hCδ : C * δ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hδC (show 0 ≤ C + 1 by positivity)
    rw [mul_inv_cancel₀ (by positivity : C + 1 ≠ 0)] at h
    nlinarith
  have hn100 : (n : ℝ) * δ ^ (100 : ℕ) ≤ 1 := by
    calc (n : ℝ) * δ ^ (100 : ℕ) = ((n : ℝ) * δ ^ 4) * δ ^ (96 : ℕ) := by ring
      _ ≤ C * δ ^ (96 : ℕ) := mul_le_mul_of_nonneg_right hpack' (by positivity)
      _ ≤ C * δ := mul_le_mul_of_nonneg_left hδ96 hC.le
      _ ≤ 1 := hCδ
  rw [Real.rpow_neg hδ.le, Real.rpow_ofNat]
  rw [← one_div]
  exact (le_div_iff₀ (by positivity : 0 < δ ^ (100 : ℕ))).mpr hn100

lemma prism_measurable (a b : ℝ) (c : E) (u : Fin 3 → E) :
    MeasurableSet (prism a b c u) := by
  have hf (k : Fin 3) : Continuous (fun p : E => |inner ℝ (u k) (p - c)|) := by
    fun_prop
  exact ((isClosed_le (hf 0) continuous_const).inter
    ((isClosed_le (hf 1) continuous_const).inter
      (isClosed_le (hf 2) continuous_const))).measurableSet

lemma prism_convex (a b : ℝ) (c : E) (u : Fin 3 → E) :
    Convex ℝ (prism a b c u) := by
  intro p hp q hq α β hα hβ hsum
  have hcoord (k : Fin 3) :
      inner ℝ (u k) (α • p + β • q - c) =
        α * inner ℝ (u k) (p - c) + β * inner ℝ (u k) (q - c) := by
    have he : α • p + β • q - c = α • (p - c) + β • (q - c) := by
      calc α • p + β • q - c = α • p + β • q - (α + β) • c := by rw [hsum, one_smul]
        _ = α • (p - c) + β • (q - c) := by module
    rw [he, inner_add_right, inner_smul_right, inner_smul_right]
  have hbound (k : Fin 3) (r : ℝ) (hp : |inner ℝ (u k) (p - c)| ≤ r)
      (hq : |inner ℝ (u k) (q - c)| ≤ r) :
      |inner ℝ (u k) (α • p + β • q - c)| ≤ r := by
    rw [hcoord]
    calc |α * inner ℝ (u k) (p - c) + β * inner ℝ (u k) (q - c)|
        ≤ |α * inner ℝ (u k) (p - c)| + |β * inner ℝ (u k) (q - c)| := abs_add_le _ _
      _ = α * |inner ℝ (u k) (p - c)| + β * |inner ℝ (u k) (q - c)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hα, abs_of_nonneg hβ]
      _ ≤ α * r + β * r := add_le_add
        (mul_le_mul_of_nonneg_left hp hα) (mul_le_mul_of_nonneg_left hq hβ)
      _ = r := by rw [← add_mul, hsum, one_mul]
  exact ⟨hbound 0 a hp.1 hq.1, hbound 1 b hp.2.1 hq.2.1,
    hbound 2 (1 / 1000) hp.2.2 hq.2.2⟩

lemma prism_mono {a a' b b' : ℝ} (ha : a ≤ a') (hb : b ≤ b') (c : E)
    (u : Fin 3 → E) : prism a b c u ⊆ prism a' b' c u := by
  intro p hp
  exact ⟨hp.1.trans ha, hp.2.1.trans hb, hp.2.2⟩

lemma center_mem_prism {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (c : E) (u : Fin 3 → E) : c ∈ prism a b c u := by
  simp [prism, ha, hb]

lemma Cells.mono {δ h h' : ℝ} {n : ℕ} {x v : Fin n → E} {Y : Fin n → Set E}
    (hδ : 0 ≤ δ) (hh' : 0 < h') (hh : h' ≤ h) (hc : Cells δ h n x v Y) :
    Cells δ h' n x v Y := by
  rcases hc with ⟨hn, hnmax, m, hm, I, f, D, a, b, c, u, H, ha, hab, hb,
    hδb, hI, hret, hD, hf, hu, hP, hT, hHmeas, hHsub, hHmass, hHreg, htrans, hslab, hdisj⟩
  refine ⟨hn, hnmax, m, hm, I, f, D, a, b, c, u, H, ha, hab, hb,
    le_trans (mul_le_mul_of_nonneg_left hh hδ) hδb, hI,
    le_trans (mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg n)) hret,
    hD, hf, hu, hP, hT, hHmeas, hHsub, ?_, ?_, ?_, ?_, hdisj⟩
  · intro j i hi
    exact (mul_le_mul_left (ENNReal.ofReal_le_ofReal hh) _).trans (hHmass j i hi)
  · intro j i hi p hp r hra hr1
    exact (mul_le_mul_left (ENNReal.ofReal_le_ofReal hh) _).trans
      (hHreg j i hi p hp r hra hr1)
  · intro j p hp
    obtain ⟨i, i', hi, hi', hpi, hpi', hangle⟩ := htrans j p hp
    exact ⟨i, i', hi, hi', hpi, hpi', hh.trans hangle⟩
  · intro j ν s r hν hr
    apply (hslab j ν s r hν hr).trans
    apply mul_le_mul_left
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hh' hh) (Nat.cast_nonneg _)

/-- For round cross sections, the escape term alone supplies pointwise transversality. -/
lemma transverse_of_le_aspect {h a b : ℝ} (hh : h ≤ a / b) {n : ℕ}
    (I : Finset (Fin n)) (u : Fin n → Fin 3 → E) (H : Fin n → Set E) :
    ∀ p : E, (∃ i, i ∈ I ∧ p ∈ H i) →
      ∃ i i', i ∈ I ∧ i' ∈ I ∧ p ∈ H i ∧ p ∈ H i' ∧
        h ≤ a / b + min ‖u i 0 - u i' 0‖ ‖u i 0 + u i' 0‖ := by
  intro p hp
  obtain ⟨i, hi, hpi⟩ := hp
  exact ⟨i, i, hi, hi, hpi, hpi,
    hh.trans (le_add_of_nonneg_right (le_min (norm_nonneg _) (norm_nonneg _)))⟩

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
