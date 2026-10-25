import Submission.Obl.k4_matching_homogeneous_records.Counting
import Submission.Obl.k4_matching_homogeneous_records.GapTransport

namespace Submission.Obl.k4_matching_homogeneous_records

open Set

lemma floor_sub_bound (x y : ℝ) : |((Int.floor x - Int.floor y : ℤ) : ℝ)| ≤ |x - y| + 1 := by
  have hx := Int.floor_le x
  have hx' := Int.lt_floor_add_one x
  have hy := Int.floor_le y
  have hy' := Int.lt_floor_add_one y
  push_cast
  rw [abs_le]
  constructor <;> linarith [le_abs_self (x - y), neg_abs_le (x - y)]

noncomputable def offsetCutoff (J : ℕ) (N η : ℝ) : ℕ :=
  ⌈((2 * (J + 2) : ℕ) : ℝ) * N ^ η + 1⌉₊

lemma offsetCutoff_bound {J : ℕ} {N η : ℝ} (hN : 1 ≤ N) (hη : 0 ≤ η) :
    ((2 * offsetCutoff J N η + 1 : ℕ) : ℝ) ≤
      ((4 * (J + 2) + 5 : ℕ) : ℝ) * N ^ η := by
  have hp := Real.one_le_rpow hN hη
  have hh := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ ((2 * (J + 2) : ℕ) : ℝ) * N ^ η + 1 by positivity)).le
  change ((offsetCutoff J N η : ℕ) : ℝ) ≤ _ at hh
  push_cast at hh ⊢
  nlinarith

lemma gap_jetOffset_mem {D J q : ℕ} {β : ℕ → ℝ} {N η : ℝ}
    (hDJ : D ≤ J) (hz : ∃ i, 1 ≤ i ∧ i ≤ D ∧ β i = 0)
    (hN : 1 ≤ N) (hq : 1 ≤ q)
    {n₁ n₂ : ℕ} (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (hf : ∀ i, ContDiffOn ℝ (J + 1) (f₁ i) (Ioo (-1 : ℝ) 2))
    (hg : ∀ i, ContDiffOn ℝ (J + 1) (f₂ i) (Ioo (-1 : ℝ) 2))
    (hfb : ∀ i j, j ≤ J + 1 → ∀ x ∈ Icc (0 : ℝ) 1, |iteratedDeriv j (f₁ i) x| ≤ N ^ η)
    (hgb : ∀ i j, j ≤ J + 1 → ∀ x ∈ Icc (0 : ℝ) 1, |iteratedDeriv j (f₂ i) x| ≤ N ^ η)
    (p : (Fin n₁ × Fin n₂) × ℝ)
    (hp : p.2 ∈ Ico (0 : ℝ) 1 ∧ |f₁ p.1.1 p.2 - f₂ p.1.2 p.2| ≤ N ^ (-1 + η) ∧
      ∀ j, 1 ≤ j → j ≤ J →
        |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2| ≤ N ^ (-β j + η))
    (v j : ℕ) (hv : v ≤ q) (hj : j ≤ J) :
    jetOffset f₁ f₂
      (fun k => dyadicHeight N (radius J β ((k : ℝ) / q)))
      (fun k j => N ^ accuracy J β j ((k : ℝ) / q)) v j p ∈
        Finset.Icc (-(offsetCutoff J N η : ℤ)) (offsetCutoff J N η : ℤ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have ha : (v : ℝ) / q ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · exact (div_le_one hqR).2 (by exact_mod_cast hv)
  let a := (v : ℝ) / q
  let h := dyadicHeight N (radius J β a)
  let c := dyadicCenter h p.2
  have hNp : 0 < N := by linarith
  have hb := (dyadicHeight_bounds hN (radius_nonneg hDJ hz ha.1)).1
  have hdist : |c - p.2| ≤ N ^ (-radius J β a) := by
    have hh := (dyadicCenter_dist h p.2).trans (inv_anti₀
      (Real.rpow_pos_of_pos hNp _) hb)
    simpa [c, h, Real.rpow_neg hNp.le] using hh
  have ht : p.2 ∈ Icc (0 : ℝ) 1 := ⟨hp.1.1, hp.1.2.le⟩
  have hgap (i : ℕ) (hi : i ≤ J) :
      |iteratedDeriv i (f₁ p.1.1) p.2 - iteratedDeriv i (f₂ p.1.2) p.2| ≤
        N ^ (-gapExponent β i + η) := by
    by_cases hi0 : i = 0
    · simpa [hi0, gapExponent] using hp.2.1
    · simpa only [gapExponent, ite_eq_right hi0] using hp.2.2 i (by omega) hi
  have htrans := jet_gap_transport hDJ hz hN ha hj (hf p.1.1) (hg p.1.2)
    (hfb p.1.1) (hgb p.1.2) ht (dyadicCenter_mem hp.1) hdist hgap
  let w := N ^ accuracy J β j a
  have hw : 0 < w := Real.rpow_pos_of_pos hNp _
  have he : w * (((2 * (J + 2) : ℕ) : ℝ) * N ^ (η - accuracy J β j a)) =
      ((2 * (J + 2) : ℕ) : ℝ) * N ^ η := by
    dsimp [w]
    calc
      _ = ((2 * (J + 2) : ℕ) : ℝ) *
          (N ^ accuracy J β j a * N ^ (η - accuracy J β j a)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hNp]
        congr 2
        ring
  have hscale : |w * iteratedDeriv j (f₂ p.1.2) c - w * iteratedDeriv j (f₁ p.1.1) c| ≤
      ((2 * (J + 2) : ℕ) : ℝ) * N ^ η := by
    rw [← mul_sub, abs_mul, abs_of_pos hw, abs_sub_comm]
    have htrans' : |iteratedDeriv j (f₁ p.1.1) c - iteratedDeriv j (f₂ p.1.2) c| ≤
        ((2 * (J + 2) : ℕ) : ℝ) * N ^ (η - accuracy J β j a) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using htrans
    exact (mul_le_mul_of_nonneg_left htrans' hw.le).trans_eq he
  have hfloor : |((Int.floor (w * iteratedDeriv j (f₂ p.1.2) c) -
      Int.floor (w * iteratedDeriv j (f₁ p.1.1) c) : ℤ) : ℝ)| ≤
      ((2 * (J + 2) : ℕ) : ℝ) * N ^ η + 1 := by
    have hf := floor_sub_bound (w * iteratedDeriv j (f₂ p.1.2) c)
      (w * iteratedDeriv j (f₁ p.1.1) c)
    linarith
  have hh := hfloor.trans (Nat.le_ceil (((2 * (J + 2) : ℕ) : ℝ) * N ^ η + 1))
  have hh' : |jetOffset f₁ f₂
      (fun k => dyadicHeight N (radius J β ((k : ℝ) / q)))
      (fun k j => N ^ accuracy J β j ((k : ℝ) / q)) v j p| ≤ (offsetCutoff J N η : ℤ) := by
    exact_mod_cast hh
  simpa only [Finset.mem_Icc] using abs_le.mp hh'

end Submission.Obl.k4_matching_homogeneous_records
