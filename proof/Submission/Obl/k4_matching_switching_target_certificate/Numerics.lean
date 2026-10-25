-- Adapted from this LOT tree, o080/x0272 commit 4d767e4, Submission/Obl/k4_matching_geometric_path_cover/Numerics.lean.
import Submission.Obl.k4_matching_switching_target_certificate.PathNeighbors

noncomputable section

namespace Submission.Obl.k4_matching_switching_target_certificate

open Filter Topology
open Submission.Obl.k4_matching_homogeneous_records (offsetCutoff offsetCutoff_bound)

-- Adapted within this LOT tree from o040, session x0115, commit 561995983838,
-- Submission/Obl/k4_matching_refinement_exponent/Asymptotic.lean.
lemma uniform_subpower_bound (C c η : ℝ) (hc : 0 ≤ c) (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ R : ℝ, 2 ≤ R ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ N : ℝ, R ≤ N → C * N ^ (c * ε) ≤ N ^ η := by
  let ε₀ := η / (2 * (c + 1))
  have hden : 0 < 2 * (c + 1) := by positivity
  have hε₀ : 0 < ε₀ := div_pos hη hden
  have hεeq : ε₀ * (2 * (c + 1)) = η := div_mul_cancel₀ _ hden.ne'
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop (by positivity : 0 < η / 2)).eventually (eventually_ge_atTop C))
  refine ⟨ε₀, hε₀, max 2 R, le_max_left _ _, ?_⟩
  intro ε hε hεle N hN
  have hN1 : 1 ≤ N := le_trans (by norm_num) ((le_max_left 2 R).trans hN)
  have hN0 : 0 < N := by linarith
  have hC : C ≤ N ^ (η / 2) := hR N ((le_max_right _ _).trans hN)
  have hmul := mul_le_mul_of_nonneg_left hεle hc
  have hexp : c * ε ≤ η / 2 := by nlinarith
  calc
    C * N ^ (c * ε) ≤ N ^ (η / 2) * N ^ (c * ε) := by gcongr
    _ ≤ N ^ (η / 2) * N ^ (η / 2) := by gcongr
    _ = N ^ η := by rw [← Real.rpow_add hN0]; congr 1; ring

/-- A convenient constant bounding both the integer box and the controls. -/
def coarseLossBase (J m : ℕ) : ℝ :=
  4 * ((m : ℝ) + 1) * (((4 * (J + 2) + 5 : ℕ) : ℝ)) + 10

def coarseLossDegree (J k : ℕ) : ℕ := 2 * (k + 1) * (J + 1)

lemma coarseLossBase_nonneg (J m : ℕ) : 0 ≤ coarseLossBase J m := by
  unfold coarseLossBase
  positivity

lemma neighbor_radius_bounds (J m : ℕ) {N ε : ℝ} (hN : 1 ≤ N) (hε : 0 ≤ ε) :
    ((2 * neighborRadius J m N ε + 1 : ℕ) : ℝ) ≤ coarseLossBase J m * N ^ ε ∧
      (neighborRadius J m N ε : ℝ) + 2 + 5 * N ^ ε ≤ coarseLossBase J m * N ^ ε := by
  have hNe : 1 ≤ N ^ ε := Real.one_le_rpow hN hε
  have hoff := offsetCutoff_bound (J := J) hN hε
  have hoff0 : (0 : ℝ) ≤ offsetCutoff J N ε := by positivity
  have hoff' : (offsetCutoff J N ε : ℝ) ≤ ((4 * (J + 2) + 5 : ℕ) : ℝ) * N ^ ε := by
    push_cast at hoff ⊢
    linarith
  have hG : (neighborRadius J m N ε : ℝ) ≤
      2 * ((m : ℝ) + 1) * ((4 * (J + 2) + 5 : ℕ) : ℝ) * N ^ ε := by
    unfold neighborRadius
    push_cast at hoff' ⊢
    nlinarith [mul_le_mul_of_nonneg_left hoff' (by positivity : 0 ≤ 2 * ((m : ℝ) + 1))]
  have hprod : 0 ≤ ((m : ℝ) + 1) * ((4 * (J + 2) + 5 : ℕ) : ℝ) := by positivity
  constructor
  · push_cast
    unfold coarseLossBase
    nlinarith
  · unfold coarseLossBase
    nlinarith [mul_nonneg hprod (by linarith : 0 ≤ N ^ ε)]

def coverDegree (J k m : ℕ) : ℝ := (coarseLossDegree J k : ℝ) + (m : ℝ) + 2

def coverCoeff (J k m : ℕ) (C : ℝ) : ℝ :=
  4 + coarseLossBase J m + (coarseLossBase J m) ^ coarseLossDegree J k +
    C * (coarseLossBase J m) ^ coarseLossDegree J k

/-- One uniform loss absorbs the record count, control bound and target volume. -/
def coverScale (J k m : ℕ) (C N ε : ℝ) : ℝ :=
  coverCoeff J k m C * N ^ (coverDegree J k m * ε)

lemma coverDegree_ge_one (J k m : ℕ) : 1 ≤ coverDegree J k m := by
  unfold coverDegree
  linarith [(Nat.cast_nonneg (coarseLossDegree J k) : (0 : ℝ) ≤ coarseLossDegree J k), (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

lemma coverCoeff_bounds (J k m : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    4 ≤ coverCoeff J k m C ∧ coarseLossBase J m ≤ coverCoeff J k m C ∧
      (coarseLossBase J m) ^ coarseLossDegree J k ≤ coverCoeff J k m C ∧
      C * (coarseLossBase J m) ^ coarseLossDegree J k ≤ coverCoeff J k m C := by
  have hB := coarseLossBase_nonneg J m
  have hP : 0 ≤ (coarseLossBase J m) ^ coarseLossDegree J k := pow_nonneg hB _
  have hCP : 0 ≤ C * (coarseLossBase J m) ^ coarseLossDegree J k := mul_nonneg hC hP
  unfold coverCoeff
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma le_coverScale (J k m : ℕ) {C N ε B s : ℝ} (hC : 0 ≤ C)
    (hN : 1 ≤ N) (hε : 0 ≤ ε) (hB : B ≤ coverCoeff J k m C) (hs : s ≤ coverDegree J k m) :
    B * N ^ (s * ε) ≤ coverScale J k m C N ε := by
  have hcoeff : 0 ≤ coverCoeff J k m C := by linarith [(coverCoeff_bounds J k m hC).1]
  exact (mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg (by linarith) _)).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN
      (mul_le_mul_of_nonneg_right hs hε)) hcoeff)

lemma coverScale_ge_two (J k m : ℕ) {C N ε : ℝ} (hC : 0 ≤ C) (hN : 1 ≤ N) (hε : 0 ≤ ε) :
    2 ≤ coverScale J k m C N ε := by
  have hB : (2 : ℝ) ≤ coverCoeff J k m C := by linarith [(coverCoeff_bounds J k m hC).1]
  have hd : (0 : ℝ) ≤ coverDegree J k m := by linarith [coverDegree_ge_one J k m]
  simpa only [zero_mul, Real.rpow_zero, mul_one] using le_coverScale J k m hC hN hε hB hd

lemma four_rpow_le_coverScale (J k m : ℕ) {C N ε : ℝ}
    (hC : 0 ≤ C) (hN : 1 ≤ N) (hε : 0 ≤ ε) :
    4 * N ^ ε ≤ coverScale J k m C N ε := by
  simpa only [one_mul] using le_coverScale J k m hC hN hε
    (coverCoeff_bounds J k m hC).1 (coverDegree_ge_one J k m)

lemma controls_le_coverScale (J k m : ℕ) {C N ε : ℝ}
    (hC : 0 ≤ C) (hN : 1 ≤ N) (hε : 0 ≤ ε) :
    (neighborRadius J m N ε : ℝ) + 2 + 5 * N ^ ε ≤ coverScale J k m C N ε := by
  refine (neighbor_radius_bounds J m hN hε).2.trans ?_
  simpa only [one_mul] using le_coverScale J k m hC hN hε
    (coverCoeff_bounds J k m hC).2.1 (coverDegree_ge_one J k m)

lemma record_power_eq (J k m : ℕ) {N ε : ℝ} (hN : 0 < N) :
    (coarseLossBase J m * N ^ ε) ^ coarseLossDegree J k =
      coarseLossBase J m ^ coarseLossDegree J k * N ^ ((coarseLossDegree J k : ℝ) * ε) := by
  have hp : (N ^ ε) ^ coarseLossDegree J k = N ^ ((coarseLossDegree J k : ℝ) * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    congr 1
    ring
  rw [mul_pow, hp]

lemma record_count_le_coverScale (J k m : ℕ) {C N ε : ℝ}
    (hC : 0 ≤ C) (hN : 1 ≤ N) (hε : 0 ≤ ε) :
    (((2 * neighborRadius J m N ε + 1 : ℕ) ^ coarseLossDegree J k : ℕ) : ℝ) ≤
      coverScale J k m C N ε := by
  have hN0 : 0 < N := by linarith
  calc _ ≤ (coarseLossBase J m * N ^ ε) ^ coarseLossDegree J k := by
        rw [Nat.cast_pow]
        exact pow_le_pow_left₀ (by positivity) (neighbor_radius_bounds J m hN hε).1 _
    _ = _ := record_power_eq J k m hN0
    _ ≤ _ := le_coverScale J k m hC hN hε (coverCoeff_bounds J k m hC).2.2.1
      (by unfold coverDegree; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])

lemma target_loss_le_coverScale (J k m : ℕ) {C N ε a : ℝ}
    (hC : 0 ≤ C) (hN : 1 ≤ N) (hε : 0 ≤ ε)
    (ha : a ≤ (((2 * neighborRadius J m N ε + 1 : ℕ) ^ coarseLossDegree J k : ℕ) : ℝ)) :
    C * a * N ^ (((m : ℝ) + 2) * ε) ≤ coverScale J k m C N ε := by
  have hN0 : 0 < N := by linarith
  have hcount : a ≤ coarseLossBase J m ^ coarseLossDegree J k *
      N ^ ((coarseLossDegree J k : ℝ) * ε) := by
    rw [← record_power_eq J k m hN0]
    refine ha.trans ?_
    rw [Nat.cast_pow]
    exact pow_le_pow_left₀ (by positivity) (neighbor_radius_bounds J m hN hε).1 _
  calc _ ≤ C * (coarseLossBase J m ^ coarseLossDegree J k *
          N ^ ((coarseLossDegree J k : ℝ) * ε)) * N ^ (((m : ℝ) + 2) * ε) := by gcongr
    _ = (C * coarseLossBase J m ^ coarseLossDegree J k) * N ^ (coverDegree J k m * ε) := by
      rw [mul_assoc C, mul_assoc C, mul_assoc _ (N ^ _), ← Real.rpow_add hN0]
      unfold coverDegree
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (coverCoeff_bounds J k m hC).2.2.2 (by positivity)

lemma cover_parameters (J k m q : ℕ) (hq : 1 ≤ q) (C η : ℝ) (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ R : ℝ, 2 ≤ R ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ N : ℝ, R ≤ N →
        ε ≤ 1 / (q : ℝ) ∧ 32 ≤ N ^ (1 / (q : ℝ)) ∧ coverScale J k m C N ε ≤ N ^ η := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  obtain ⟨e, he, R, hR, hb⟩ := uniform_subpower_bound (coverCoeff J k m C)
    (coverDegree J k m) η (by linarith [coverDegree_ge_one J k m]) hη
  refine ⟨min e (1 / (q : ℝ)), lt_min he (by positivity), max R ((32 : ℝ) ^ q),
    hR.trans (le_max_left _ _), ?_⟩
  intro ε hε hε₀ N hN
  exact ⟨hε₀.trans (min_le_right _ _),
    root_large_of_scale hq ((le_max_right _ _).trans hN),
    hb ε hε (hε₀.trans (min_le_left _ _)) N ((le_max_left _ _).trans hN)⟩

end Submission.Obl.k4_matching_switching_target_certificate
