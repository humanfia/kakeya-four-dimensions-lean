import Submission.Obl.k4_matching_homogeneous_records.Radius
import Submission.Obl.k4_matching_homogeneous_records.Transport

namespace Submission.Obl.k4_matching_homogeneous_records

open Set

noncomputable def gapExponent (β : ℕ → ℝ) (j : ℕ) : ℝ := if j = 0 then 1 else β j

lemma accuracy_transport_exponent {J j k : ℕ} {β : ℕ → ℝ} {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hjk : j + k ≤ J) :
    accuracy J β j a ≤ gapExponent β (j + k) + (k : ℝ) * radius J β a := by
  by_cases h : j + k = 0
  · have hj : j = 0 := by omega
    have hk : k = 0 := by omega
    subst j; subst k
    simpa [gapExponent, accuracy_zero_order ha.1] using ha.2
  · simpa only [gapExponent, ite_eq_right h] using accuracy_translate (β := β) ha.1 (by omega) hjk

lemma weighted_rpow_bound {N B η r L : ℝ} (hN : 1 ≤ N) (k : ℕ)
    (hL : L ≤ B + (k : ℝ) * r) :
    N ^ (-B + η) * (N ^ (-r)) ^ k ≤ N ^ (η - L) := by
  have hp : 0 < N := by linarith
  rw [← Real.rpow_mul_natCast hp.le, ← Real.rpow_add hp]
  apply Real.rpow_le_rpow_of_exponent_le hN
  nlinarith

lemma jet_gap_transport {D J j : ℕ} {β : ℕ → ℝ} {N η a t s : ℝ}
    (hDJ : D ≤ J) (hz : ∃ i, 1 ≤ i ∧ i ≤ D ∧ β i = 0)
    (hN : 1 ≤ N) (ha : a ∈ Icc (0 : ℝ) 1) (hj : j ≤ J)
    {f g : ℝ → ℝ}
    (hf : ContDiffOn ℝ (J + 1) f (Ioo (-1 : ℝ) 2))
    (hg : ContDiffOn ℝ (J + 1) g (Ioo (-1 : ℝ) 2))
    (hfb : ∀ i, i ≤ J + 1 → ∀ x ∈ Icc (0 : ℝ) 1, |iteratedDeriv i f x| ≤ N ^ η)
    (hgb : ∀ i, i ≤ J + 1 → ∀ x ∈ Icc (0 : ℝ) 1, |iteratedDeriv i g x| ≤ N ^ η)
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1)
    (hst : |s - t| ≤ N ^ (-radius J β a))
    (hgap : ∀ i, i ≤ J →
      |iteratedDeriv i f t - iteratedDeriv i g t| ≤ N ^ (-gapExponent β i + η)) :
    |iteratedDeriv j f s - iteratedDeriv j g s| ≤
      (2 * (J + 2 : ℕ)) * N ^ (η - accuracy J β j a) := by
  have hNp : 0 < N := by linarith
  let n := J + 1 - j
  let δ := N ^ (-radius J β a)
  let A := 2 * N ^ (η - accuracy J β j a)
  have hδ : 0 < δ := Real.rpow_pos_of_pos hNp _
  have hn : j + n = J + 1 := by dsimp [n]; omega
  have hrem : accuracy J β j a ≤ (n : ℝ) * radius J β a := by
    have h := accuracy_remainder hDJ hz ha.1 hj
    have hnR : (n : ℝ) = (J : ℝ) + 1 - j := by
      have hnR : (j : ℝ) + n = (J : ℝ) + 1 := by exact_mod_cast hn
      linarith
    simpa [hnR, Nat.cast_add, Nat.cast_one] using h
  have htop (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      |iteratedDeriv (j + n) f x - iteratedDeriv (j + n) g x| * δ ^ n ≤ A := by
    have hh : |iteratedDeriv (j + n) f x - iteratedDeriv (j + n) g x| ≤ 2 * N ^ η := by
      calc
        _ ≤ |iteratedDeriv (j + n) f x| + |iteratedDeriv (j + n) g x| := abs_sub _ _
        _ ≤ 2 * N ^ η := by linarith [hfb (j + n) hn.le x hx, hgb (j + n) hn.le x hx]
    calc
      _ ≤ (2 * N ^ η) * δ ^ n := mul_le_mul_of_nonneg_right hh (by positivity)
      _ = 2 * (N ^ (-0 + η) * (N ^ (-radius J β a)) ^ n) := by dsimp [δ]; simp only [neg_zero, zero_add]; ring
      _ ≤ A := mul_le_mul_of_nonneg_left
        (weighted_rpow_bound hN n (by simpa using hrem)) (by norm_num)
  have hinit (k : ℕ) (hk : k ≤ n) :
      |iteratedDeriv (j + k) f t - iteratedDeriv (j + k) g t| * δ ^ k ≤ A := by
    by_cases hkn : k = n
    · subst k; exact htop t ht
    have hjk : j + k ≤ J := by omega
    calc
      _ ≤ N ^ (-gapExponent β (j + k) + η) * δ ^ k :=
        mul_le_mul_of_nonneg_right (hgap (j + k) hjk) (by positivity)
      _ ≤ N ^ (η - accuracy J β j a) :=
        weighted_rpow_bound hN k (accuracy_transport_exponent ha hjk)
      _ ≤ A := by dsimp [A]; nlinarith [Real.rpow_nonneg hNp.le (η - accuracy J β j a)]
  have hb := derivativeChain_bound n
    (fun k x => iteratedDeriv (j + k) f x - iteratedDeriv (j + k) g x)
    hδ (by dsimp [A]; positivity) ht hs hst
    (fun k hk x hx => by
      have hx' : x ∈ Ioo (-1 : ℝ) 2 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have hjk : j + k < J + 1 := by omega
      have h1 := hasDerivAt_iteratedDeriv isOpen_Ioo hf hjk hx'
      have h2 := hasDerivAt_iteratedDeriv isOpen_Ioo hg hjk hx'
      convert h1.sub h2 using 1)
    hinit htop
  simp only [Nat.add_zero] at hb
  have hnJ : n + 1 ≤ J + 2 := by dsimp [n]; omega
  have hnJR : ((n + 1 : ℕ) : ℝ) ≤ (J + 2 : ℕ) := by exact_mod_cast hnJ
  calc
    _ ≤ (n + 1 : ℕ) * A := hb
    _ ≤ (J + 2 : ℕ) * A := mul_le_mul_of_nonneg_right hnJR (by dsimp [A]; positivity)
    _ = _ := by dsimp [A]; push_cast; ring

end Submission.Obl.k4_matching_homogeneous_records
