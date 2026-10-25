-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PrescribedWindows.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PrescribedWindows.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 5604560, PrescribedWindows.lean.
This is workspace collaboration code; existing local and accepted dependencies are imported. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ContainedCrossing
import Submission.WZ.Obl.wz_coarse_grains_assembly.LocalCount

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory

/-- Centres spaced along the long axis, with unchanged transverse coordinates. -/
def axialWindowCenter (c ℓ : ℝ) (z : V) (e : V ≃ₗᵢ[ℝ] V) (k : ℕ) : V :=
  z + e.symm (EuclideanSpace.single 2 (-ℓ / 2 + k * c / 16))

theorem axialWindowCenter_coord (c ℓ : ℝ) (z p : V)
    (e : V ≃ₗᵢ[ℝ] V) (k : ℕ) (i : Fin 3) :
    e (p - axialWindowCenter c ℓ z e k) i =
      e (p - z) i - if i = 2 then -ℓ / 2 + k * c / 16 else 0 := by
  rw [axialWindowCenter, show p - (z + e.symm
      (EuclideanSpace.single 2 (-ℓ / 2 + k * c / 16))) =
      (p - z) - e.symm (EuclideanSpace.single 2 (-ℓ / 2 + k * c / 16)) by abel,
    map_sub, e.apply_symm_apply]
  simp

/-- A prescribed finite axial grid covers the long prism whenever its last
centre reaches the opposite end. -/
theorem prescribed_length_core_cover_fixed {A B c ℓ : ℝ} {N : ℕ}
    (hc : 0 < c) (hN : 16 * ℓ / c ≤ N) (z : V) (e : V ≃ₗᵢ[ℝ] V) :
    P A B ℓ z e ⊆ ⋃ k : Fin (N + 1),
      P A B (c / 8) (axialWindowCenter c ℓ z e k) e := by
  intro p hp
  let t := 16 * (e (p - z) 2 + ℓ / 2) / c
  have ht : 0 ≤ t := by
    apply div_nonneg _ hc.le
    have hh := (abs_le.mp hp.2.2).1
    dsimp only [t]
    nlinarith
  have htℓ : t ≤ 16 * ℓ / c := by
    apply div_le_div_of_nonneg_right _ hc.le
    have hh := (abs_le.mp hp.2.2).2
    nlinarith
  have hk : ⌊t⌋₊ < N + 1 := by
    apply Nat.lt_succ_of_le
    exact_mod_cast (Nat.floor_le ht).trans (htℓ.trans hN)
  refine mem_iUnion.mpr ⟨⟨⌊t⌋₊, hk⟩, ?_⟩
  change |e (p - axialWindowCenter c ℓ z e ⌊t⌋₊) 0| ≤ A / 2 ∧
    |e (p - axialWindowCenter c ℓ z e ⌊t⌋₊) 1| ≤ B / 2 ∧
    |e (p - axialWindowCenter c ℓ z e ⌊t⌋₊) 2| ≤ (c / 8) / 2
  simp only [axialWindowCenter_coord, show (0 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 2 by decide, ite_false, ite_true, sub_zero]
  refine ⟨hp.1, hp.2.1, ?_⟩
  have hlo := (le_div_iff₀ hc).mp (Nat.floor_le ht)
  have hhi := (div_lt_iff₀ hc).mp (Nat.lt_floor_add_one t)
  dsimp only [t] at hlo hhi
  apply abs_le.mpr
  constructor <;> nlinarith


/-- A long prism is covered by at most `16 ℓ/c + 2` axial cores of
length `c/8`. The covering does not enlarge its transverse dimensions. -/
theorem prescribed_length_core_cover {A B c ℓ : ℝ}
    (hc : 0 < c) (hℓ : 0 ≤ ℓ) (z : V) (e : V ≃ₗᵢ[ℝ] V) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ 16 * ℓ / c + 2 ∧
      P A B ℓ z e ⊆ ⋃ k : Fin N,
        P A B (c / 8) (axialWindowCenter c ℓ z e k) e := by
  refine ⟨⌈16 * ℓ / c⌉₊ + 1, Nat.succ_pos _, ?_,
    prescribed_length_core_cover_fixed hc (Nat.le_ceil _) z e⟩
  push_cast
  linarith [Nat.ceil_lt_add_one (by positivity : 0 ≤ 16 * ℓ / c)]

/-- The outer windows have a total volume controlled independently of the
short and middle widths. -/
theorem prescribed_length_window_volume {A B c ℓ : ℝ} {N : ℕ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 < c) (hcℓ : c ≤ ℓ)
    (hN : (N : ℝ) ≤ 16 * ℓ / c + 2) (z : Fin N → V)
    (e : V ≃ₗᵢ[ℝ] V) (z₀ : V) :
    (∑ k, μ (P (128 * A) (128 * B) c (z k) e)) ≤
      O 294912 * μ (P A B ℓ z₀ e) := by
  have hℓ : 0 ≤ ℓ := (hc.trans_le hcℓ).le
  have hnℓ : (N : ℝ) * c ≤ 18 * ℓ := by
    have hh := (le_div_iff₀ hc).mp
      (show (N : ℝ) - 2 ≤ 16 * ℓ / c by linarith)
    nlinarith
  simp only [WangZahlLot.Obl.wz_coarse_grains_assembly.volume_P
    (by positivity : 0 ≤ 128 * A) (by positivity : 0 ≤ 128 * B) hc.le,
    WangZahlLot.Obl.wz_coarse_grains_assembly.volume_P hA hB hℓ]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change (N : ENNReal) * ENNReal.ofReal ((128 * A) * (128 * B) * c) ≤
    ENNReal.ofReal 294912 * ENNReal.ofReal (A * B * ℓ)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg N),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 294912)]
  apply ENNReal.ofReal_le_ofReal
  have hh := mul_le_mul_of_nonneg_left hnℓ (show 0 ≤ 16384 * A * B by positivity)
  nlinarith

/-- Seventeen residue classes separate the length-`c` outer windows.
This separation is within one containing prism and does not assert any
separation between unrelated containers. -/
theorem prescribed_length_windows_disjoint {A B c ℓ : ℝ} (hc : 0 < c)
    (z : V) (e : V ≃ₗᵢ[ℝ] V) {j k : ℕ}
    (hjk : j ≠ k) (hcolor : j % 17 = k % 17) :
    Disjoint (P A B c (axialWindowCenter c ℓ z e j) e)
      (P A B c (axialWindowCenter c ℓ z e k) e) := by
  apply Set.disjoint_left.mpr
  intro p hp hq
  have hp' := abs_le.mp hp.2.2
  have hq' := abs_le.mp hq.2.2
  simp only [axialWindowCenter_coord, ite_true] at hp' hq'
  have hsep : j + 17 ≤ k ∨ k + 17 ≤ j := by omega
  rcases hsep with hsep | hsep
  · have hs : (j : ℝ) + 17 ≤ k := by exact_mod_cast hsep
    have hh := mul_le_mul_of_nonneg_right hs hc.le
    nlinarith [hp'.1, hq'.2]
  · have hs : (k : ℝ) + 17 ≤ j := by exact_mod_cast hsep
    have hh := mul_le_mul_of_nonneg_right hs hc.le
    nlinarith [hp'.2, hq'.1]

/-- Every core meeting of an endpoint-clear fine tube crossing a contained
old grain produces exact crossing of the corresponding length-`c` window. -/
theorem prescribed_length_window_crossing {δ a b c A B ℓ : ℝ}
    {x v z z₀ p : V} (e g : V ≃ₗᵢ[ℝ] V) (k : ℕ)
    (hδ : 0 < δ) (hδA : δ ≤ A) (hAB : A ≤ B)
    (hδc : 16 * δ ≤ c) (hBc : 128 * B ≤ c) (hv : ‖v‖ = 1)
    (hsub : P a b c z e ⊆ P A B ℓ z₀ g)
    (hcross : ∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
      ∃ q ∈ T δ x v ∩ P a b c z e, e (q - z) 2 = t)
    (hp : p ∈ (T δ x v \ WangZahlLot.Obl.wz_coarse_tube_grains.RIS.tubeEnds δ c x v) ∩
      P A B (c / 8) (axialWindowCenter c ℓ z₀ g k) g) :
    (∀ q ∈ T δ x v ∩ frontier
      (P (128 * A) (128 * B) c (axialWindowCenter c ℓ z₀ g k) g),
      |g (q - axialWindowCenter c ℓ z₀ g k) 2| = c / 2) ∧
    ∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
      ∃ q ∈ T δ x v ∩ P (128 * A) (128 * B) c (axialWindowCenter c ℓ z₀ g k) g,
        g (q - axialWindowCenter c ℓ z₀ g k) 2 = t := by
  apply wider_prism_crossing_of_contained_grain e g hδ hδA hAB hδc hBc hv hsub hcross
  refine ⟨hp.1, ?_⟩
  have hA : 0 < A := hδ.trans_le hδA
  have hB : 0 < B := hA.trans_le hAB
  exact ⟨hp.2.1.trans (by linarith), hp.2.2.1.trans (by linarith), hp.2.2.2⟩

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
