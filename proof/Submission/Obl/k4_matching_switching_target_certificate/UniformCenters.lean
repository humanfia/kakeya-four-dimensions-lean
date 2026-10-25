-- Adapted from this LOT tree, o080/x0305, Submission/Obl/k4_matching_geometric_path_cover/UniformCenters.lean.
import Submission.Obl.k4_matching_switching_target_certificate.Endpoint
import Submission.Obl.k4_matching_switching_target_certificate.Jitter

/-!
# One center variation bound for all starts

The initial reference jets are bounded uniformly over the source events. Together
with the bounded floor-bin coefficients this gives a finite Lipschitz constant for
all `tcen` functions on the normalized unit interval. No subpower estimate on this
constant is needed: it is used only to choose the common positive jitter radius.

Written for o080 by session x0305.
-/

noncomputable section

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set

lemma abs_taylorSum_le_count (c : ℕ → ℝ) (n : ℕ) {x₀ t M : ℝ}
    (hM : 0 ≤ M) (hc : ∀ i, i < n → |c i| ≤ M) (ht : |t - x₀| ≤ 1) :
    |∑ i ∈ Finset.range n, c i * (t - x₀) ^ i / (i.factorial : ℝ)| ≤ n * M := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i ∈ Finset.range n,
      |c i * (t - x₀) ^ i / (i.factorial : ℝ)| ≤ M := by
    intro i hi
    rw [abs_div, abs_mul, abs_pow, Nat.abs_cast]
    have hf : (1 : ℝ) ≤ (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i
    calc |c i| * |t - x₀| ^ i / (i.factorial : ℝ)
        ≤ |c i| * |t - x₀| ^ i := div_le_self (by positivity) hf
      _ ≤ M * 1 := mul_le_mul (hc i (Finset.mem_range.mp hi))
          (pow_le_one₀ (abs_nonneg _) ht) (by positivity) hM
      _ = M := mul_one _
  simpa using Finset.sum_le_sum hterm

/-- A bound for the normalized initial jets, uniform over all starts. -/
def initialJetBound (J m : ℕ) (β : ℕ → ℝ) (N ε : ℝ) (h : ℕ → ℕ) (k : ℕ) : ℝ :=
  (∑ i ∈ Finset.range m, N ^ β m * (lamk h k ^ m)⁻¹ * lamk h k ^ i) *
    (((J : ℝ) + 2) * N ^ ε)

lemma initialJetBound_nonneg (J m : ℕ) (β : ℕ → ℝ) {N ε : ℝ}
    (hN : 0 < N) (h : ℕ → ℕ) (k : ℕ) : 0 ≤ initialJetBound J m β N ε h k := by
  unfold initialJetBound lamk
  positivity

namespace Det

variable {n₁ n₂ J : ℕ} {β : ℕ → ℝ} {γ : ℝ} {q k m z : ℕ} {N ε : ℝ}
  {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ} {h : ℕ → ℕ}
  {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}

variable (H : Det J β γ q k m z N ε f₁ f₂ h F S)
include H

lemma jet0_abs_le {a : (Fin n₁ × Fin n₂) × ℝ} (ha : a ∈ S) {i : ℕ} (hi : i < m) :
    |jet0 J β m N f₁ h k a i| ≤ initialJetBound J m β N ε h k := by
  have hN0 := H.N_pos
  have hta := dcenter_mem_Icc h k (H.hS a ha).1
  have ht := H.time_mem ha
  have hlam := lamk_pos h k
  have htime : dcenter h k a.2 + lamk h k * ntime h k a a.2 = a.2 := by
    unfold ntime
    field_simp
    ring
  have hU : dcenter h k a.2 + lamk h k * ntime h k a a.2 ∈ Ioo (-1 : ℝ) 2 := by
    rw [htime]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hiJ : i ≤ J + 1 := by have := H.hmJ; omega
  have hdist : |a.2 - dcenter h k a.2| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2, hta.1, hta.2]
  have hpoly : |iteratedDeriv i (taylorPoly J (cref f₁ h k a) (dcenter h k a.2)) a.2| ≤
      ((J : ℝ) + 1) * N ^ ε := by
    rw [iteratedDeriv_taylorPoly J _ _ hiJ]
    have hsum := abs_taylorSum_le_count (fun j => cref f₁ h k a (i + j))
      (J + 1 - i) (H.Npow_pos ε).le (fun j hj => ?_) hdist
    · refine hsum.trans ?_
      apply mul_le_mul_of_nonneg_right _ (H.Npow_pos ε).le
      exact_mod_cast Nat.sub_le (J + 1) i
    · exact H.hB₁ a.1.1 (i + j) (by omega) _ hta
  unfold jet0 nArm
  rw [iteratedDeriv_normArm isOpen_Ioo (H.hf₁ a.1.1) (contDiff_taylorPoly J _ _)
    _ _ _ _ hiJ hU, htime, abs_mul, abs_of_nonneg (by positivity)]
  have hgap : |iteratedDeriv i (f₁ a.1.1) a.2 -
      iteratedDeriv i (taylorPoly J (cref f₁ h k a) (dcenter h k a.2)) a.2| ≤
      ((J : ℝ) + 2) * N ^ ε := by
    have h1 := abs_sub (iteratedDeriv i (f₁ a.1.1) a.2)
      (iteratedDeriv i (taylorPoly J (cref f₁ h k a) (dcenter h k a.2)) a.2)
    linarith [H.hB₁ a.1.1 i hiJ a.2 ht]
  refine (mul_le_mul_of_nonneg_left hgap (by positivity)).trans ?_
  unfold initialJetBound
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact Finset.single_le_sum (f := fun j => N ^ β m * (lamk h k ^ m)⁻¹ * lamk h k ^ j)
    (fun j hj => by positivity) (Finset.mem_range.mpr hi)

end Det

end Submission.Obl.k4_matching_switching_target_certificate

namespace Submission.Obl.k4_matching_switching_target_certificate

/-- A common bound for every coefficient reconstructed from a final bin. -/
def binCoefficientBound (J : ℕ) (β : ℕ → ℝ) (q k : ℕ) (N ε : ℝ) : ℝ :=
  N ^ ε + ∑ i ∈ Finset.range (J + 1),
    N ^ (-jetAccuracy (jetRadius J β) i (((k + 1 : ℕ) : ℝ) / (q : ℝ)))

/-- The bound is allowed to depend on the fixed data and scale. -/
def centerSlope (J m : ℕ) (β : ℕ → ℝ) (q k : ℕ) (N ε : ℝ) (h : ℕ → ℕ)
    (j : Fin m) : ℝ :=
  let i := m - 1 - (j : ℕ)
  let n := J + 1 - i
  let B := binCoefficientBound J β q k N ε
  let M := initialJetBound J m β N ε h k
  N ^ β m * (lamk h k ^ m)⁻¹ * lamk h k ^ i *
      ((n : ℝ) * (B * ((n : ℝ) * 4 ^ n)) + (n : ℝ) * (N ^ ε * ((n : ℝ) * 4 ^ n))) * lamk h k +
    (((j : ℕ) : ℝ) + 1) * (M * ((((j : ℕ) : ℝ) + 1) * 2 ^ ((j : ℕ) + 1)))

namespace Det

open Set

variable {n₁ n₂ J : ℕ} {β : ℕ → ℝ} {γ : ℝ} {q k m z : ℕ} {N ε : ℝ}
  {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ} {h : ℕ → ℕ}
  {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}

variable (H : Det J β γ q k m z N ε f₁ f₂ h F S)
include H

lemma bin_coefficient_abs_le {y : (Fin n₁ × Fin n₂) × ℝ} (hy : y ∈ S)
    (κ : Bool) {i : ℕ} (hi : i ≤ J) :
    |((finBins J β q k N f₁ f₂ h y κ i : ℤ) : ℝ) /
        N ^ jetAccuracy (jetRadius J β) i (((k + 1 : ℕ) : ℝ) / (q : ℝ))| ≤
      binCoefficientBound J β q k N ε := by
  have ht := dcenter_mem_Icc h (k + 1) (H.hS y hy).1
  have hnear := abs_sub_floor_rpow_le (N := N)
    (l := jetAccuracy (jetRadius J β) i (((k + 1 : ℕ) : ℝ) / (q : ℝ)))
    (y := iteratedDeriv i (arm f₁ f₂ κ y) (dcenter h (k + 1) y.2)) H.N_pos
  change |iteratedDeriv i (arm f₁ f₂ κ y) (dcenter h (k + 1) y.2) -
    ((finBins J β q k N f₁ f₂ h y κ i : ℤ) : ℝ) /
      N ^ jetAccuracy (jetRadius J β) i (((k + 1 : ℕ) : ℝ) / (q : ℝ))| ≤ _ at hnear
  have hb := H.arm_bound κ y (by omega : i ≤ J + 1) _ ht
  have hsum : N ^ (-jetAccuracy (jetRadius J β) i (((k + 1 : ℕ) : ℝ) / (q : ℝ))) ≤
      ∑ j ∈ Finset.range (J + 1),
        N ^ (-jetAccuracy (jetRadius J β) j (((k + 1 : ℕ) : ℝ) / (q : ℝ))) :=
    Finset.single_le_sum
      (f := fun j => N ^ (-jetAccuracy (jetRadius J β) j (((k + 1 : ℕ) : ℝ) / (q : ℝ))))
      (fun j hj => (H.Npow_pos _).le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  have htri := abs_sub_le
    (((finBins J β q k N f₁ f₂ h y κ i : ℤ) : ℝ) /
      N ^ jetAccuracy (jetRadius J β) i (((k + 1 : ℕ) : ℝ) / (q : ℝ)))
    (iteratedDeriv i (arm f₁ f₂ κ y) (dcenter h (k + 1) y.2)) 0
  rw [sub_zero, sub_zero, abs_sub_comm] at htri
  unfold binCoefficientBound
  linarith

lemma tcen_sub_le {a y : (Fin n₁ × Fin n₂) × ℝ} (ha : a ∈ S) (hy : y ∈ S)
    (κ : Bool) (j : Fin m) {s t : ℝ} (hs : |s| ≤ 1) (ht : |t| ≤ 1) :
    |tcen J β q k m N f₁ f₂ h a y κ j s - tcen J β q k m N f₁ f₂ h a y κ j t| ≤
      centerSlope J m β q k N ε h j * |s - t| := by
  have hN0 := H.N_pos
  let i := m - 1 - (j : ℕ)
  let n := J + 1 - i
  let ta := dcenter h k a.2
  let tc := dcenter h (k + 1) y.2
  let lam := lamk h k
  let A := N ^ β m * (lam ^ m)⁻¹ * lam ^ i
  let B := binCoefficientBound J β q k N ε
  let M := initialJetBound J m β N ε h k
  have hj := j.isLt
  have hiJ : i ≤ J + 1 := by dsimp [i]; have := H.hmJ; omega
  have hta : ta ∈ Icc (0 : ℝ) 1 := dcenter_mem_Icc h k (H.hS a ha).1
  have htc : tc ∈ Icc (0 : ℝ) 1 := dcenter_mem_Icc h (k + 1) (H.hS y hy).1
  have hlam0 : 0 < lam := lamk_pos h k
  have hlam1 : lam ≤ 1 := by
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hB0 : 0 ≤ B := by dsimp [B, binCoefficientBound]; positivity
  have hM0 : 0 ≤ M := initialJetBound_nonneg J m β H.N_pos h k
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hdist (v : ℝ) (hv : |v| ≤ 1) (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
      |ta + lam * v - b| ≤ 4 := by
    have hv' := abs_le.mp hv
    have hm : |lam * v| ≤ 1 := by
      rw [abs_mul, abs_of_pos hlam0]
      exact (mul_le_mul_of_nonneg_left hv hlam0.le).trans (by simpa using hlam1)
    have hm' := abs_le.mp hm
    rw [abs_le]
    constructor <;> linarith [hta.1, hta.2, hb.1, hb.2, hm'.1, hm'.2]
  have harg : |(ta + lam * s) - (ta + lam * t)| = lam * |s - t| := by
    rw [show (ta + lam * s) - (ta + lam * t) = lam * (s - t) by ring,
      abs_mul, abs_of_pos hlam0]
  have hbin := taylorSum_sub_le
    (fun v => ((finBins J β q k N f₁ f₂ h y κ (i + v) : ℤ) : ℝ) /
      N ^ jetAccuracy (jetRadius J β) (i + v) (((k + 1 : ℕ) : ℝ) / (q : ℝ)))
    n hB0 (fun v hv => H.bin_coefficient_abs_le hy κ (by dsimp [n] at hv; omega))
    (by norm_num : (1 : ℝ) ≤ 4) (hdist s hs tc htc) (hdist t ht tc htc)
  rw [harg] at hbin
  change |binJet J β N (((k + 1 : ℕ) : ℝ) / (q : ℝ))
      (finBins J β q k N f₁ f₂ h y κ) tc i (ta + lam * s) -
      binJet J β N (((k + 1 : ℕ) : ℝ) / (q : ℝ))
      (finBins J β q k N f₁ f₂ h y κ) tc i (ta + lam * t)| ≤ _ at hbin
  have hpoly := taylorSum_sub_le (fun v => cref f₁ h k a (i + v)) n
    (H.Npow_pos ε).le
    (fun v hv => H.hB₁ a.1.1 (i + v) (by dsimp [n] at hv; omega) _ hta)
    (by norm_num : (1 : ℝ) ≤ 4) (hdist s hs ta hta) (hdist t ht ta hta)
  rw [harg] at hpoly
  rw [← iteratedDeriv_taylorPoly J _ _ hiJ (ta + lam * s),
    ← iteratedDeriv_taylorPoly J _ _ hiJ (ta + lam * t)] at hpoly
  have hs0 : |ntime h k a a.2| ≤ 1 / 2 := by
    have hh := abs_sub_dcenter_of_floor_eq (h := h) (v := k) (s := a.2) (t := a.2) rfl
    rw [ntime, abs_div, abs_of_pos (lamk_pos h k), div_le_iff₀ (lamk_pos h k)]
    simpa [lamk, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh
  have hfreeArg (v : ℝ) (hv : |v| ≤ 1) : |v - ntime h k a a.2| ≤ 2 := by
    have := abs_sub v (ntime h k a a.2)
    linarith
  have hfree := taylorSum_sub_le (fun v => jet0 J β m N f₁ h k a (m - 1 - (j : ℕ) + v))
    ((j : ℕ) + 1) hM0 (fun v hv => H.jet0_abs_le ha (by omega))
    (by norm_num : (1 : ℝ) ≤ 2) (hfreeArg s hs) (hfreeArg t ht)
  change |freeJet m (jet0 J β m N f₁ h k a) (ntime h k a a.2) s j -
      freeJet m (jet0 J β m N f₁ h k a) (ntime h k a a.2) t j| ≤ _ at hfree
  let bs := binJet J β N (((k + 1 : ℕ) : ℝ) / (q : ℝ))
    (finBins J β q k N f₁ f₂ h y κ) tc i (ta + lam * s)
  let bt := binJet J β N (((k + 1 : ℕ) : ℝ) / (q : ℝ))
    (finBins J β q k N f₁ f₂ h y κ) tc i (ta + lam * t)
  let ps := iteratedDeriv i (taylorPoly J (cref f₁ h k a) ta) (ta + lam * s)
  let pt := iteratedDeriv i (taylorPoly J (cref f₁ h k a) ta) (ta + lam * t)
  let fs := freeJet m (jet0 J β m N f₁ h k a) (ntime h k a a.2) s j
  let ft := freeJet m (jet0 J β m N f₁ h k a) (ntime h k a a.2) t j
  have heq : tcen J β q k m N f₁ f₂ h a y κ j s - tcen J β q k m N f₁ f₂ h a y κ j t =
      A * ((bs - bt) - (ps - pt)) - (fs - ft) := by
    dsimp [tcen, A, bs, bt, ps, pt, fs, ft, ta, tc, lam, i]
    ring
  rw [heq]
  calc _ ≤ A * (|bs - bt| + |ps - pt|) + |fs - ft| := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_of_nonneg hA0]
        exact add_le_add (mul_le_mul_of_nonneg_left (abs_sub _ _) hA0) le_rfl
    _ ≤ A * (((n : ℝ) * (B * ((n : ℝ) * 4 ^ n))) * (lam * |s - t|) +
        ((n : ℝ) * (N ^ ε * ((n : ℝ) * 4 ^ n))) * (lam * |s - t|)) +
        (((j : ℕ) + 1 : ℕ) : ℝ) * (M * ((((j : ℕ) + 1 : ℕ) : ℝ) * 2 ^ ((j : ℕ) + 1))) * |s - t| := by
      exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add hbin hpoly) hA0) hfree
    _ = _ := by simp only [centerSlope, A, B, M, n, i, lam, Nat.cast_add, Nat.cast_one]; ring

/-- One finite variation bound for all starts and all final records. -/
theorem exists_tcen_lipschitz : ∃ L : ℝ, 0 ≤ L ∧
    ∀ a ∈ S, ∀ y ∈ S, ∀ κ j, ∀ s t : ℝ, |s| ≤ 1 → |t| ≤ 1 →
      |tcen J β q k m N f₁ f₂ h a y κ j s - tcen J β q k m N f₁ f₂ h a y κ j t| ≤
        L * |s - t| := by
  have hN0 := H.N_pos
  let L := ∑ j : Fin m, centerSlope J m β q k N ε h j
  have hnonneg (j : Fin m) : 0 ≤ centerSlope J m β q k N ε h j := by
    unfold centerSlope binCoefficientBound initialJetBound lamk
    positivity
  refine ⟨L, Finset.sum_nonneg (fun j hj => hnonneg j), ?_⟩
  intro a ha y hy κ j s t hs ht
  refine (H.tcen_sub_le ha hy κ j hs ht).trans ?_
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j hj => hnonneg j) (Finset.mem_univ j)) (abs_nonneg _)

end Det

end Submission.Obl.k4_matching_switching_target_certificate
