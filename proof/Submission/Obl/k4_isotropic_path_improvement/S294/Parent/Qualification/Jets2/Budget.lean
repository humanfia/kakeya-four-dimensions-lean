-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.Jets2.Budget, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/Jets2/Budget.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/Jets2/Budget.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/Jets2/Budget.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Tree

set_option autoImplicit false

/-!
# The thresholds of one pair, in closed form (version 2)

Adapted from this LOT tree: o229, session x0801, branch `x0801` at `ec0250f0`, `Jets/Budget.lean`,
with the constants of the version-2 pair (`4000 K⁶` from the slab estimate, factors `2` from dot
products).

For one pair (children: list size `n`, row bound `BR`, Lipschitz constant `CJ`, scalar width `W`,
precision `w = CJ W`; parent: scalar width `W'`, Lipschitz constant `CJ'`), choose

* `X = 120000 M K⁷ nG / mD`, `Λ j = (BR + 1) X^j` (tail thresholds);
* `Y = 16000 K⁶ n nG / mD`, `Z = Y (1 + 2 M K)`, `s = w + 2 w Kg/H + 2 K H Λ M + eT Kg/H`,
  `δc j = s Z^{j+1}` (compatibility thresholds).

`pairBudget_of_small`: the `PairBudget` holds as soon as `4000 K⁶ n nG W ≤ mD/4`,
`eT Kg / H ≤ 1`, and the new-jet precision `2 w Kg/H + 2 K (H Λ m + m s Z^m)` is at most `W'`.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open PairData

noncomputable section

/-- The candidate count of the divided differences at one pair. -/
def pairNG (K BR H eT W w : ℝ) (n : ℕ) : ℕ := nGrad n W (W + H * w + errS K BR H eT)

/-- Tail growth factor. -/
def pairX (K mD : ℝ) (M nG : ℕ) : ℝ := 120000 * M * K ^ 7 * nG / mD

/-- Tail thresholds. -/
def pairLam (K BR mD : ℝ) (M nG : ℕ) (j : ℕ) : ℝ := (BR + 1) * pairX K mD M nG ^ j

/-- Compatibility factor. -/
def pairZ (K mD : ℝ) (M n nG : ℕ) : ℝ := 16000 * K ^ 6 * n * nG / mD * (1 + 2 * M * K)

/-- Compatibility base. -/
def pairS (K Kg H eT w BR mD : ℝ) (M nG : ℕ) : ℝ :=
  w + 2 * w * Kg / H + 2 * K * H * pairLam K BR mD M nG M + eT * Kg / H

/-- Compatibility thresholds. -/
def pairDc (K Kg H eT w BR mD : ℝ) (M n nG : ℕ) (j : ℕ) : ℝ :=
  pairS K Kg H eT w BR mD M nG * pairZ K mD M n nG ^ (j + 1)

theorem budget_key1 (a b c : ℝ) (hb : b ≠ 0) : c * a = b * (c * (a / b)) := by
  field_simp

theorem budget_key2 (a b : ℝ) (hb : b ≠ 0) : 4000 * b * (a / (16000 * b)) = a / 4 := by
  field_simp; ring

theorem budget_key3 (K M nG mD : ℝ) (hmD : 0 < mD) (hK : 0 < K) (hMnG : 0 < M * nG) :
    4000 * K ^ 6 * nG * (8 * M * K / (120000 * M * K ^ 7 * nG / mD)) = 4 / 15 * mD := by
  have hM : M ≠ 0 := by intro h; rw [h, zero_mul] at hMnG; exact lt_irrefl 0 hMnG
  have hnG : nG ≠ 0 := by intro h; rw [h, mul_zero] at hMnG; exact lt_irrefl 0 hMnG
  field_simp; ring

theorem pairBudget_of_small {K ζ BR H Kg eT W W' mD CJ CJ' : ℝ} {n M m : ℕ}
    (hK : 1 ≤ K) (hKg : 1 ≤ Kg) (hBR : 0 ≤ BR) (hH : 0 < H) (heT : 0 ≤ eT) (hW : 0 < W)
    (hCJ : 1 ≤ CJ) (hmD : 0 < mD) (hmD1 : mD ≤ 1) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmM : m ≤ M)
    (hζW : ζ ≤ W) (hWW' : W ≤ W') (hW'1 : W' ≤ 1) (hCJ' : CJ ≤ CJ')
    (hCJ'big : 3 + 4 * max BR (pairLam K BR mD M (pairNG K BR H eT W (CJ * W) n) m) +
      2 * (m + 1) * max BR (pairLam K BR mD M (pairNG K BR H eT W (CJ * W) n) m) ≤ CJ')
    (hS1 : 4000 * K ^ 6 * n * (pairNG K BR H eT W (CJ * W) n) * W ≤ mD / 4)
    (hS2 : eT * Kg / H ≤ 1)
    (hS3 : 2 * (CJ * W) * Kg / H +
      2 * K * (H * pairLam K BR mD M (pairNG K BR H eT W (CJ * W) n) m +
      m * pairDc K Kg H eT (CJ * W) BR mD M n (pairNG K BR H eT W (CJ * W) n) (m - 1)) ≤ W') :
    PairBudget K ζ BR H Kg eT W (CJ * W) W' (CJ' * W') mD CJ' n m
      (pairLam K BR mD M (pairNG K BR H eT W (CJ * W) n))
      (pairDc K Kg H eT (CJ * W) BR mD M n (pairNG K BR H eT W (CJ * W) n)) := by
  set w := CJ * W with hw
  set nG := pairNG K BR H eT W w n with hnG
  have hK0 : 0 ≤ K := by linarith
  have hw0 : 0 < w := by positivity
  have hnG1 : 1 ≤ nG := le_trans hn (le_nGrad hn)
  have hnGr : (1 : ℝ) ≤ nG := by exact_mod_cast hnG1
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast (hm.trans hmM)
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmMr : (m : ℝ) ≤ M := by exact_mod_cast hmM
  set X := pairX K mD M nG with hX
  have hX1 : 1 ≤ X := by
    rw [hX, pairX, le_div_iff₀ hmD]
    have h6 : 1 ≤ K ^ 7 := one_le_pow₀ hK
    have h1 : (1 : ℝ) ≤ (M : ℝ) * K ^ 7 := one_le_mul_of_one_le_of_one_le hMr h6
    have h2 : (1 : ℝ) ≤ (M : ℝ) * K ^ 7 * nG := one_le_mul_of_one_le_of_one_le h1 hnGr
    have e : 120000 * (M : ℝ) * K ^ 7 * nG = 120000 * ((M : ℝ) * K ^ 7 * nG) := by ring
    rw [e]; linarith
  set Lam := pairLam K BR mD M nG with hLam
  have hLam_pos : ∀ j, 0 < Lam j := fun j => by simp only [hLam, pairLam]; positivity
  have hLam_ge : ∀ j, BR + 1 ≤ Lam j := fun j => by
    simp only [hLam, pairLam]
    exact le_mul_of_one_le_right (by linarith) (one_le_pow₀ hX1)
  have hLam_mono : ∀ j j', j ≤ j' → Lam j ≤ Lam j' := fun j j' hjj => by
    simp only [hLam, pairLam]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 hjj) (by linarith)
  set Z := pairZ K mD M n nG with hZ
  have hY1 : 1 ≤ 16000 * K ^ 6 * n * nG / mD := by
    rw [le_div_iff₀ hmD]
    have : 1 ≤ K ^ 6 := one_le_pow₀ hK
    nlinarith [mul_le_mul hnr hnGr zero_le_one (by linarith)]
  have hZ1 : 1 ≤ Z := by
    rw [hZ, pairZ]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ M) hK0]
  set s := pairS K Kg H eT w BR mD M nG with hs
  have hs0 : 0 ≤ s := by
    simp only [hs, pairS]
    have := hLam_pos M
    positivity
  set δc := pairDc K Kg H eT w BR mD M n nG with hδc
  have hδc_eq : ∀ j, δc j = s * Z ^ (j + 1) := fun j => rfl
  have hnGdef : nGrad n W (W + H * w + errS K BR H eT) = nG := rfl
  have hspos : 0 < s := by
    simp only [hs, pairS]
    have := hLam_pos M
    positivity
  have hLj_succ : ∀ j, Lam (j + 1) = X * Lam j := fun j => by
    simp only [hLam, pairLam, pow_succ]; ring
  have hZdef : Z = 16000 * K ^ 6 * n * nG / mD * (1 + 2 * M * K) := by rw [hZ, pairZ]
  have hXdef : X = 120000 * M * K ^ 7 * nG / mD := by rw [hX, pairX]
  have hsLam : w + 2 * w * Kg / H + 2 * K * H * Lam M + eT * Kg / H = s := by rw [hs, pairS]
  clear_value δc s Z Lam X nG w
  refine {
    hζq := hζW, hqW := hWW', hW1 := hW'1, hnL := hn, hδL := hw0.le
    hw := mul_pos (by linarith) (by linarith [hW, hWW'])
    b0 := ?_, bpos := hLam_pos, b1 := ?_, c0 := ?_, cpos := ?_, c1 := ?_, newP := ?_
    oldP := ?_, hCJ := hCJ'big, hwCJ := le_rfl }
  · -- b0
    calc BR + eT * Kg / H ≤ BR + 1 := by linarith
      _ ≤ Lam 0 := hLam_ge 0
  · -- b1
    intro j hj1 hjm
    rw [hnGdef]
    have hLprev := hLam_ge (j - 1)
    have hLj : Lam j = X * Lam (j - 1) := by
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; exact hLj_succ j'
    have hwKg : 2 * w * Kg / H ≤ 1 := by
      have h1 : 0 ≤ 2 * K * (H * Lam m + m * δc (m - 1)) := by
        have := hLam_pos m; rw [hδc_eq]; positivity
      linarith
    have hjr : (j : ℝ) ≤ M := by exact_mod_cast hjm.trans hmM
    have hnum : 2 * w * Kg / H + (3 * K + 2 * BR * K + 2 * j * Lam (j - 1) * K) ≤
        8 * M * K * Lam (j - 1) := by
      have hL1 : 1 ≤ Lam (j - 1) := by linarith only [hLprev, hBR]
      have hBRL : BR ≤ Lam (j - 1) := by linarith only [hLprev]
      set L := Lam (j - 1)
      have hL0 : 0 ≤ L := by linarith only [hL1]
      have a1 : 2 * w * Kg / H ≤ K * L := le_trans hwKg (one_le_mul_of_one_le_of_one_le hK hL1)
      have a2 : 3 * K ≤ 3 * K * L := le_mul_of_one_le_right (by linarith only [hK]) hL1
      have a3 : BR * K ≤ L * K := mul_le_mul_of_nonneg_right hBRL hK0
      have a4 : (j : ℝ) * (L * K) ≤ M * (L * K) :=
        mul_le_mul_of_nonneg_right hjr (mul_nonneg hL0 hK0)
      have a5 : 1 * (6 * (K * L)) ≤ M * (6 * (K * L)) :=
        mul_le_mul_of_nonneg_right hMr (by positivity)
      have e1 : 2 * (j : ℝ) * L * K = 2 * ((j : ℝ) * (L * K)) := by ring
      have e2 : 8 * M * K * L = 2 * (M * (K * L)) + M * (6 * (K * L)) := by ring
      have e3 : L * K = K * L := by ring
      rw [e1, e2]
      rw [e3] at a3 a4
      linarith only [a1, a2, a3, a4, a5]
    have hfrac : (2 * w * Kg / H + (3 * K + 2 * BR * K + 2 * j * Lam (j - 1) * K)) / Lam j ≤
        8 * M * K / X := by
      rw [hLj, div_le_div_iff₀ (mul_pos (by linarith) (hLam_pos _)) (by linarith)]
      calc (2 * w * Kg / H + (3 * K + 2 * BR * K + 2 * j * Lam (j - 1) * K)) * X
          ≤ (8 * M * K * Lam (j - 1)) * X := mul_le_mul_of_nonneg_right hnum (by linarith)
        _ = 8 * M * K * (X * Lam (j - 1)) := by ring
    have hXval : 4000 * K ^ 6 * nG * (8 * M * K / X) = 4 / 15 * mD := by
      rw [hXdef]; exact budget_key3 _ _ _ _ (by linarith) (by positivity) (by positivity)
    have hnGW : 4000 * K ^ 6 * nG * W ≤ mD / 4 := by
      calc 4000 * K ^ 6 * nG * W ≤ n * (4000 * K ^ 6 * nG * W) :=
            le_mul_of_one_le_left (by positivity) hnr
        _ = 4000 * K ^ 6 * n * nG * W := by ring
        _ ≤ mD / 4 := hS1
    calc 4000 * K ^ 6 * (nG : ℝ) *
          ((2 * w * Kg / H + (3 * K + 2 * BR * K + 2 * j * Lam (j - 1) * K)) / Lam j + W)
        = 4000 * K ^ 6 * nG *
            ((2 * w * Kg / H + (3 * K + 2 * BR * K + 2 * j * Lam (j - 1) * K)) / Lam j)
          + 4000 * K ^ 6 * nG * W := by ring
      _ ≤ 4000 * K ^ 6 * nG * (8 * M * K / X) + mD / 4 := by gcongr
      _ = 4 / 15 * mD + mD / 4 := by rw [hXval]
      _ < mD := by linarith
  · -- c0
    rw [hδc_eq, zero_add, pow_one]
    have hsge : eT * Kg / H ≤ s := by
      rw [← hsLam]
      have := hLam_pos M
      have : 0 ≤ w + 2 * w * Kg / H + 2 * K * H * Lam M := by positivity
      linarith
    calc eT * Kg / H ≤ s := hsge
      _ ≤ s * Z := le_mul_of_one_le_right hs0 hZ1
  · -- cpos
    intro j
    rw [hδc_eq]
    positivity
  · -- c1
    intro j hj1 hjm
    rw [hnGdef]
    have hjr : (j : ℝ) ≤ M := by exact_mod_cast (by omega : j ≤ M)
    have hnum : 2 * w * Kg / H + w + 2 * K * (H * Lam j + j * δc (j - 1)) ≤
        s * (1 + 2 * M * K) * Z ^ j := by
      have hLjM : Lam j ≤ Lam M := hLam_mono j M (by omega)
      rw [hδc_eq, Nat.sub_add_cancel hj1]
      have hZj : 1 ≤ Z ^ j := one_le_pow₀ hZ1
      have h1 : w + 2 * w * Kg / H + 2 * K * H * Lam j ≤ s := by
        rw [← hsLam]
        have : 2 * K * H * Lam j ≤ 2 * K * H * Lam M := by gcongr
        have : 0 ≤ eT * Kg / H := by positivity
        linarith
      have h2 : 2 * K * (j * (s * Z ^ j)) ≤ 2 * M * K * s * Z ^ j := by
        have hX0 : 0 ≤ K * (s * Z ^ j) := by positivity
        calc 2 * K * (j * (s * Z ^ j)) = 2 * (j * (K * (s * Z ^ j))) := by ring
          _ ≤ 2 * (M * (K * (s * Z ^ j))) := by gcongr
          _ = 2 * M * K * s * Z ^ j := by ring
      calc 2 * w * Kg / H + w + 2 * K * (H * Lam j + j * (s * Z ^ j))
          = (w + 2 * w * Kg / H + 2 * K * H * Lam j) + 2 * K * (j * (s * Z ^ j)) := by ring
        _ ≤ s * Z ^ j + 2 * M * K * s * Z ^ j :=
            add_le_add (h1.trans (le_mul_of_one_le_right hs0 hZj)) h2
        _ = s * (1 + 2 * M * K) * Z ^ j := by ring
    have hδcj : δc j = s * Z ^ j * (16000 * K ^ 6 * n * nG / mD * (1 + 2 * M * K)) := by
      rw [hδc_eq, pow_succ, hZdef]; ring
    have hfrac : (2 * w * Kg / H + w + 2 * K * (H * Lam j + j * δc (j - 1))) / δc j ≤
        mD / (16000 * K ^ 6 * n * nG) := by
      rw [div_le_div_iff₀ (by rw [hδcj]; positivity) (by positivity), hδcj]
      have hZj : 0 < Z ^ j := by positivity
      calc (2 * w * Kg / H + w + 2 * K * (H * Lam j + j * δc (j - 1))) *
            (16000 * K ^ 6 * n * nG)
          ≤ s * (1 + 2 * M * K) * Z ^ j * (16000 * K ^ 6 * n * nG) := by gcongr
        _ = mD * (s * Z ^ j * (16000 * K ^ 6 * n * nG / mD * (1 + 2 * M * K))) := by
            have := budget_key1 (16000 * K ^ 6 * n * nG) mD (s * (1 + 2 * M * K) * Z ^ j)
              hmD.ne'
            rw [this]; ring
    have hval : 4000 * K ^ 6 * ((nG * n : ℕ) : ℝ) * (mD / (16000 * K ^ 6 * n * nG)) =
        mD / 4 := by
      have hb : K ^ 6 * (n : ℝ) * nG ≠ 0 := by positivity
      have := budget_key2 mD _ hb
      push_cast
      calc 4000 * K ^ 6 * ((nG : ℝ) * n) * (mD / (16000 * K ^ 6 * n * nG))
          = 4000 * (K ^ 6 * n * nG) * (mD / (16000 * (K ^ 6 * n * nG))) := by ring
        _ = mD / 4 := this
    calc 4000 * K ^ 6 * ((nG * n : ℕ) : ℝ) *
          ((2 * w * Kg / H + w + 2 * K * (H * Lam j + j * δc (j - 1))) / δc j + W)
        = 4000 * K ^ 6 * ((nG * n : ℕ) : ℝ) *
            ((2 * w * Kg / H + w + 2 * K * (H * Lam j + j * δc (j - 1))) / δc j) +
          4000 * K ^ 6 * n * nG * W := by push_cast; ring
      _ ≤ 4000 * K ^ 6 * ((nG * n : ℕ) : ℝ) * (mD / (16000 * K ^ 6 * n * nG)) + mD / 4 := by
          gcongr
      _ = mD / 4 + mD / 4 := by rw [hval]
      _ < mD := by linarith
  · -- newP
    calc 2 * w * Kg / H + 2 * K * (H * Lam m + m * δc (m - 1)) ≤ W' := hS3
      _ ≤ CJ' * W' := le_mul_of_one_le_left (hW.le.trans hWW') (hCJ.trans hCJ')
  · -- oldP
    calc w = CJ * W := hw
      _ ≤ CJ' * W' := mul_le_mul hCJ' hWW' hW.le (by linarith)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
