-- Adapted from this LOT tree, o070/x0236 commit 12c7648, Endpoint.lean.
import Mathlib
import Submission.Obl.k4_matching_switching_target_certificate.Path

/-!
# The endpoint of an alternating path lies in the tube of its final record

For a start `a = E 0`, normalize time by the coarse interval: `ntime t = (t - ta) / lam`
with `ta = dcenter h k a.2`, `lam = 2^(-h k)`, and normalize the arms by the order-`J`
Taylor polynomial of the reference arm `f₁ a.1.1` at `ta` and the scale `N^(β m)`.

`Det.path_endpoint`: for every alternating path from `a` and any controls `u p` that
approximate the normalized top derivatives `N^(β m) (φ_p^(m)(ta) - cref m)` within `e₀`,
the endpoint polynomial of the frozen statement at (final time, switch times) is within an
explicit error of `tcen`, a center computed from the start and from the level-`(k+1)`
bins of the final arm only (`binJet` of x0118), minus the free evolution of the reference
arm.

Written for o070 by session x0236.
-/

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set

variable {n₁ n₂ : ℕ}

/-- The reference jets of a start: the jets of `f₁ a.1.1` at its coarse center. -/
noncomputable def cref (f₁ : Fin n₁ → ℝ → ℝ) (h : ℕ → ℕ) (k : ℕ)
    (a : (Fin n₁ × Fin n₂) × ℝ) : ℕ → ℝ :=
  fun i => iteratedDeriv i (f₁ a.1.1) (dcenter h k a.2)

/-- Normalized time relative to the coarse interval of a start. -/
noncomputable def ntime (h : ℕ → ℕ) (k : ℕ) (a : (Fin n₁ × Fin n₂) × ℝ) (t : ℝ) : ℝ :=
  (t - dcenter h k a.2) / lamk h k

/-- The normalized arm relative to a start. -/
noncomputable def nArm (J : ℕ) (β : ℕ → ℝ) (m : ℕ) (N : ℝ) (f₁ : Fin n₁ → ℝ → ℝ)
    (h : ℕ → ℕ) (k : ℕ) (a : (Fin n₁ × Fin n₂) × ℝ) (φ : ℝ → ℝ) : ℝ → ℝ :=
  normArm φ (taylorPoly J (cref f₁ h k a) (dcenter h k a.2)) (dcenter h k a.2) (lamk h k)
    (N ^ β m) m

/-- The normalized initial jets of the reference arm at the start time. -/
noncomputable def jet0 (J : ℕ) (β : ℕ → ℝ) (m : ℕ) (N : ℝ) (f₁ : Fin n₁ → ℝ → ℝ)
    (h : ℕ → ℕ) (k : ℕ) (a : (Fin n₁ × Fin n₂) × ℝ) : ℕ → ℝ :=
  fun i => iteratedDeriv i (nArm J β m N f₁ h k a (f₁ a.1.1)) (ntime h k a a.2)

/-- The level-`(k+1)` bins of the colour-`κ` arm of `y` at its level-`(k+1)` center. -/
noncomputable def finBins (J : ℕ) (β : ℕ → ℝ) (q k : ℕ) (N : ℝ) (f₁ : Fin n₁ → ℝ → ℝ)
    (f₂ : Fin n₂ → ℝ → ℝ) (h : ℕ → ℕ) (y : (Fin n₁ × Fin n₂) × ℝ) (κ : Bool) : ℕ → ℤ :=
  fun i => Int.floor (N ^ jetAccuracy (jetRadius J β) i (((k + 1 : ℕ) : ℝ) / (q : ℝ)) *
    iteratedDeriv i (arm f₁ f₂ κ y) (dcenter h (k + 1) y.2))

/-- The center of the target tube of a final event `y` with final colour `κ`, relative to
the start `a`, at normalized time `σ`, in the reverse jet order of the endpoint map. -/
noncomputable def tcen (J : ℕ) (β : ℕ → ℝ) (q k m : ℕ) (N : ℝ) (f₁ : Fin n₁ → ℝ → ℝ)
    (f₂ : Fin n₂ → ℝ → ℝ) (h : ℕ → ℕ) (a y : (Fin n₁ × Fin n₂) × ℝ) (κ : Bool)
    (j : Fin m) (σ : ℝ) : ℝ :=
  N ^ β m * (lamk h k ^ m)⁻¹ * lamk h k ^ (m - 1 - (j : ℕ)) *
      (binJet J β N (((k + 1 : ℕ) : ℝ) / (q : ℝ)) (finBins J β q k N f₁ f₂ h y κ)
          (dcenter h (k + 1) y.2) (m - 1 - (j : ℕ)) (dcenter h k a.2 + lamk h k * σ) -
        iteratedDeriv (m - 1 - (j : ℕ)) (taylorPoly J (cref f₁ h k a) (dcenter h k a.2))
          (dcenter h k a.2 + lamk h k * σ)) -
    freeJet m (jet0 J β m N f₁ h k a) (ntime h k a a.2) σ j

lemma continuous_tcen (J : ℕ) (β : ℕ → ℝ) (q k m : ℕ) (N : ℝ) (f₁ : Fin n₁ → ℝ → ℝ)
    (f₂ : Fin n₂ → ℝ → ℝ) (h : ℕ → ℕ) (a y : (Fin n₁ × Fin n₂) × ℝ) (κ : Bool) (j : Fin m) :
    Continuous (tcen J β q k m N f₁ f₂ h a y κ j) := by
  unfold tcen freeJet
  have h1 : Continuous fun σ : ℝ => binJet J β N (((k + 1 : ℕ) : ℝ) / (q : ℝ))
      (finBins J β q k N f₁ f₂ h y κ) (dcenter h (k + 1) y.2) (m - 1 - (j : ℕ))
      (dcenter h k a.2 + lamk h k * σ) :=
    (continuous_binJet _ _ _ _ _ _ _).comp (by fun_prop)
  have h2 : Continuous fun σ : ℝ => iteratedDeriv (m - 1 - (j : ℕ))
      (taylorPoly J (cref f₁ h k a) (dcenter h k a.2)) (dcenter h k a.2 + lamk h k * σ) :=
    ((contDiff_taylorPoly J (cref f₁ h k a) (dcenter h k a.2)).continuous_iteratedDeriv _
      (by exact_mod_cast le_top)).comp (by fun_prop)
  fun_prop

/-- The difference of two free evolutions is controlled by the difference of the initial
jets. -/
lemma abs_freeJet_sub_le {m : ℕ} (c c' : ℕ → ℝ) (s₀ σ : ℝ) (hσ : |σ - s₀| ≤ 1) {δ : ℝ}
    (hδ : ∀ i, i < m → |c i - c' i| ≤ δ) (j : Fin m) :
    |freeJet m c s₀ σ j - freeJet m c' s₀ σ j| ≤ 3 * δ := by
  have hj := j.isLt
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ 0 (by omega))
  unfold freeJet
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i ∈ Finset.range ((j : ℕ) + 1),
      |c (m - 1 - (j : ℕ) + i) * (σ - s₀) ^ i / (i.factorial : ℝ) -
        c' (m - 1 - (j : ℕ) + i) * (σ - s₀) ^ i / (i.factorial : ℝ)| ≤
        δ * (1 / (i.factorial : ℝ)) := by
    intro i hi
    have hi' : m - 1 - (j : ℕ) + i < m := by have := Finset.mem_range.mp hi; omega
    rw [← sub_div, ← sub_mul, abs_div, abs_mul, abs_pow, Nat.abs_cast]
    have hp : |σ - s₀| ^ i ≤ 1 := pow_le_one₀ (abs_nonneg _) hσ
    have hf : (0 : ℝ) < (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i
    rw [div_le_iff₀ hf]
    field_simp
    calc |c (m - 1 - (j : ℕ) + i) - c' (m - 1 - (j : ℕ) + i)| * |σ - s₀| ^ i
        ≤ δ * 1 := mul_le_mul (hδ _ hi') hp (by positivity) hδ0
      _ = δ := mul_one δ
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have he : ∑ i ∈ Finset.range ((j : ℕ) + 1), 1 / (i.factorial : ℝ) ≤ 3 := by
    have h1 := Real.sum_le_exp_of_nonneg (x := 1) (by norm_num) ((j : ℕ) + 1)
    have h2 := Real.exp_one_lt_d9
    simp only [one_pow] at h1
    linarith
  nlinarith

lemma dleft_nonneg (h : ℕ → ℕ) (v : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ dleft h v t := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ h v := by positivity
  rw [dleft]
  exact div_nonneg (by exact_mod_cast Int.floor_nonneg.mpr (mul_nonneg ht h2.le)) h2.le

lemma dleft_add_le_one (h : ℕ → ℕ) (v : ℕ) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    dleft h v t + ((2 : ℝ) ^ h v)⁻¹ ≤ 1 := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ h v := by positivity
  have hc := dcenter_mem_Icc h v ht
  have hlt : t * (2 : ℝ) ^ h v < (2 : ℝ) ^ h v := by nlinarith [ht.2]
  have h2int : ((2 : ℝ) ^ h v) = (((2 : ℤ) ^ h v : ℤ) : ℝ) := by push_cast; ring
  have hfl : Int.floor (t * (2 : ℝ) ^ h v) < (2 : ℤ) ^ h v := by
    rw [Int.floor_lt, ← h2int]; exact hlt
  have hfl' : ((Int.floor (t * (2 : ℝ) ^ h v) : ℝ)) + 1 ≤ (2 : ℝ) ^ h v := by
    rw [h2int]; exact_mod_cast hfl
  rw [dleft, div_add' _ _ _ h2.ne', div_le_one h2]
  field_simp
  linarith

namespace Det

variable {J : ℕ} {β : ℕ → ℝ} {γ : ℝ} {q k m z : ℕ} {N ε : ℝ}
  {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ} {h : ℕ → ℕ}
  {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}

variable (H : Det J β γ q k m z N ε f₁ f₂ h F S)
include H

/-- The radius is active at every level of the admissible window. -/
lemma active_at {v : ℕ} (hzv : z ≤ v) (hv : v ≤ k + 6 * (J + 1)) :
    jetRadius J β ((v : ℝ) / q) = ((v : ℝ) / q - β m) / (m : ℝ) :=
  (H.hadm _ (H.level_mem hzv hv)).1

/-- On the admissible window, low accuracies grow linearly. -/
lemma accuracy_sub {v₁ v₂ : ℕ} (hz1 : z ≤ v₁) (h12 : v₁ ≤ v₂) (h2 : v₂ ≤ k + 6 * (J + 1))
    {j : ℕ} (hj : j ≤ m) :
    jetAccuracy (jetRadius J β) j ((v₂ : ℝ) / q) - jetAccuracy (jetRadius J β) j ((v₁ : ℝ) / q)
      = ((v₂ : ℝ) / q - (v₁ : ℝ) / q) * (1 - (j : ℝ) / (m : ℝ)) :=
  jetAccuracy_sub_at_active H.hJ β (H.level_nonneg _) (H.level_nonneg _) H.hm H.hmJ hj
    (H.active_at hz1 (h12.trans h2)) (H.active_at (hz1.trans h12) h2)

/-- The low accuracies gain at least `6/q` between the coarse and the fine level. -/
lemma accuracy_gain_fine {j : ℕ} (hj : j < m) :
    jetAccuracy (jetRadius J β) j ((k : ℝ) / q) -
        jetAccuracy (jetRadius J β) j (((k + 6 * (J + 1) : ℕ) : ℝ) / q) ≤ -(6 / (q : ℝ)) := by
  have h := H.accuracy_sub H.hzk (Nat.le_add_right k (6 * (J + 1))) le_rfl hj.le
  have hq := H.q_pos
  have hm : (0 : ℝ) < m := by exact_mod_cast H.hm
  have hmJ : (m : ℝ) ≤ J := by exact_mod_cast H.hmJ
  have hjm : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
  have hdiff : (((k + 6 * (J + 1) : ℕ) : ℝ) / q - (k : ℝ) / q) = 6 * ((J : ℝ) + 1) / q := by
    push_cast; field_simp; ring
  rw [hdiff] at h
  have h1 : 1 - (j : ℝ) / m ≥ 1 / m := by
    rw [ge_iff_le, div_le_iff₀ hm, sub_mul, div_mul_cancel₀ _ hm.ne']; linarith
  have h2 : 6 * ((J : ℝ) + 1) / q * (1 - (j : ℝ) / m) ≥ 6 / q := by
    calc 6 * ((J : ℝ) + 1) / q * (1 - (j : ℝ) / m) ≥ 6 * ((J : ℝ) + 1) / q * (1 / m) := by
          gcongr
      _ = 6 / q * (((J : ℝ) + 1) / m) := by ring
      _ ≥ 6 / q * 1 := by
          gcongr
          rw [le_div_iff₀ hm]; linarith
      _ = 6 / q := mul_one _
  linarith

/-- The low accuracies gain exactly `(j+1)/(m q)` from the coarse to the child level, in the
reverse jet order. -/
lemma accuracy_gain_child (j : Fin m) :
    jetAccuracy (jetRadius J β) (m - 1 - (j : ℕ)) ((k : ℝ) / q) -
        jetAccuracy (jetRadius J β) (m - 1 - (j : ℕ)) (((k + 1 : ℕ) : ℝ) / q) =
      -((((j : ℕ) : ℝ) + 1) / (m : ℝ) / (q : ℝ)) := by
  have hj := j.isLt
  have h := H.accuracy_sub H.hzk (Nat.le_succ k) (by omega) (j := m - 1 - (j : ℕ)) (by omega)
  have hq := H.q_pos
  have hm : (0 : ℝ) < m := by exact_mod_cast H.hm
  have hcast : ((m - 1 - (j : ℕ) : ℕ) : ℝ) = (m : ℝ) - 1 - (j : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcast] at h
  have hdiff : (((k + 1 : ℕ) : ℝ) / q - (k : ℝ) / q) = 1 / q := by push_cast; field_simp; ring
  rw [hdiff] at h
  have : (1 / (q : ℝ)) * (1 - ((m : ℝ) - 1 - (j : ℝ)) / m) = ((j : ℝ) + 1) / m / q := by
    field_simp; ring
  linarith

set_option maxHeartbeats 2000000 in
/-- **The endpoint of an alternating path.** -/
theorem path_endpoint {E W : ℕ → (Fin n₁ × Fin n₂) × ℝ} {κ : ℕ → Bool}
    (hP : IsPath F S f₁ f₂ h k (6 * (J + 1)) m E W κ) (u : ℕ → ℝ) {e₀ : ℝ} (he₀ : 0 ≤ e₀)
    (hu : ∀ p, p ≤ m → |N ^ β m * (iteratedDeriv m (arm f₁ f₂ (κ p) (W p))
        (dcenter h k (E 0).2) - cref f₁ h k (E 0) m) - u p| ≤ e₀)
    (j : Fin m) :
    |(endpointMap m (fun p => u p) (ntime h k (E 0) (E 0).2)
          (ntime h k (E 0) (E (m + 1)).2, fun p => ntime h k (E 0) (E ((p : ℕ) + 1)).2)).2 j -
        tcen J β q k m N f₁ f₂ h (E 0) (E (m + 1)) (κ m) j (ntime h k (E 0) (E (m + 1)).2)| ≤
      9 ^ (m + 1) * (8 * (2 ^ m * (3 * (((m : ℝ) + 1) * (5 * N ^ ε + 1)) + 2 * N ^ ε) *
          N ^ (-(6 / (q : ℝ)))) +
        2 ^ m * (e₀ + (3 * (((m : ℝ) + 1) * (5 * N ^ ε + 1)) + N ^ ε) * N ^ (-γ))) +
      2 ^ m * (3 + 2 * N ^ ε) * N ^ (-((((j : ℕ) : ℝ) + 1) / (m : ℝ) / (q : ℝ))) +
      3 * (2 ^ m * (3 * (5 * N ^ ε + 1) + 2 * N ^ ε) * N ^ (-(6 / (q : ℝ)))) := by
  obtain ⟨k₀, hk₀, hk₀J, hβk₀⟩ := H.exists_zero
  obtain ⟨hfE, hfW⟩ := H.path_floor hP
  obtain ⟨hcE, hcW⟩ := H.path_coarse hP
  have hN0 := H.N_pos
  have hNε := H.Npow_pos ε
  set a : (Fin n₁ × Fin n₂) × ℝ := E 0 with ha_def
  have ha : a ∈ S := hP.memE 0 (by omega)
  have haI := (H.hS a ha).1
  set lam := lamk h k with hlam
  have hlam0 : 0 < lam := lamk_pos h k
  set lo := dleft h k a.2 with hlo_def
  set hi := lo + lam with hhi_def
  set ta := dcenter h k a.2 with hta_def
  have hctr : (lo + hi) / 2 = ta := by
    rw [hhi_def, hta_def, dcenter_eq, hlo_def, hlam, lamk]; ring
  have hwid : hi - lo = lam := by rw [hhi_def]; ring
  set la : ℝ := (k : ℝ) / q with hla
  set lf : ℝ := ((k + 6 * (J + 1) : ℕ) : ℝ) / q with hlf
  set lc : ℝ := ((k + 1 : ℕ) : ℝ) / q with hlc
  have hla0 : 0 ≤ la := H.level_nonneg k
  have hlf0 : 0 ≤ lf := H.level_nonneg _
  have hlc0 : 0 ≤ lc := H.level_nonneg _
  have hadm_a := H.hadm la (H.level_mem H.hzk (Nat.le_add_right k _))
  have hact : jetRadius J β la = (la - β m) / (m : ℝ) := hadm_a.1
  have hγ1 : γ ≤ ((J : ℝ) + 1 - (m : ℝ)) * jetRadius J β la -
      jetAccuracy (jetRadius J β) m la := hadm_a.2.2.1 m H.hmJ
  have hγ2 := hadm_a.2.2.2
  have hκ : ∀ j : ℕ, j < m →
      jetAccuracy (jetRadius J β) j la - jetAccuracy (jetRadius J β) j lf ≤ -(6 / (q : ℝ)) :=
    fun j hj => H.accuracy_gain_fine hj
  have hlo0 : 0 ≤ lo := dleft_nonneg h k haI.1
  have hhi1 : hi ≤ 1 := dleft_add_le_one h k haI
  have hlen : N ^ (-jetRadius J β la) / 2 ≤ hi - lo := by rw [hwid]; exact H.le_inv_pow H.k_le_q
  have hlen' : hi - lo ≤ N ^ (-jetRadius J β la) := by rw [hwid]; exact H.inv_pow_le H.k_le_q
  set φ : ℕ → ℝ → ℝ := fun p => arm f₁ f₂ (κ p) (W p) with hφ_def
  set K : ℝ := ((m : ℝ) + 1) * (5 * N ^ ε + 1) with hK_def
  have hK0 : 0 ≤ K := by positivity
  set c : ℕ → ℝ := cref f₁ h k a with hc_def
  -- coarse neighbours
  have hc : ∀ p, p ≤ m → ∀ i, i ≤ J → |iteratedDeriv i (φ p) ((lo + hi) / 2) - c i| ≤
      K * N ^ (-jetAccuracy (jetRadius J β) i la) := by
    intro p hp i hi'
    rw [hctr]
    have h1 := hcW p hp (κ p) i hi'
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (H.Npow_pos _).le)
    have hpm : (p : ℝ) ≤ m := by exact_mod_cast hp
    nlinarith
  -- times in the coarse interval
  set t : ℕ → ℝ := fun p => (E p).2 with ht_def
  have ht : ∀ p, p ≤ m + 1 → t p ∈ Icc lo hi := by
    intro p hp
    have hd : dleft h k (E p).2 = lo := dleft_congr (hfE p hp)
    constructor
    · rw [← hd]; exact dleft_le h k _
    · rw [hhi_def, ← hd, hlam, lamk]; exact (lt_dleft_add h k _).le
  -- fine switches
  set cf : ℕ → ℝ := fun p => dcenter h (k + 6 * (J + 1)) (E p).2 with hcf_def
  have hcf : ∀ p, 1 ≤ p → p ≤ m → cf p ∈ Icc (0 : ℝ) 1 ∧
      |t p - cf p| ≤ N ^ (-jetRadius J β lf) ∧
      ∀ i, i ≤ J → |iteratedDeriv i (φ p) (cf p) - iteratedDeriv i (φ (p - 1)) (cf p)| ≤
        K * N ^ (-jetAccuracy (jetRadius J β) i lf) := by
    intro p hp1 hpm
    have hEp := hP.memE p (by omega)
    refine ⟨dcenter_mem_Icc h _ (H.hS _ hEp).1, ?_, ?_⟩
    · rw [abs_sub_comm]
      refine (abs_dcenter_sub_le h _ _).trans ?_
      have := H.inv_pow_le H.kC_le_q
      have h0 : (0 : ℝ) ≤ ((2 : ℝ) ^ h (k + 6 * (J + 1)))⁻¹ := by positivity
      linarith
    · intro i hi'
      refine (H.path_switch hP hp1 hpm hi').trans
        (mul_le_mul_of_nonneg_right ?_ (H.Npow_pos _).le)
      have : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      nlinarith
  -- controls
  have hu' : ∀ p, p ≤ m →
      |N ^ β m * (iteratedDeriv m (φ p) ((lo + hi) / 2) - c m) - u p| ≤ e₀ := by
    intro p hp; rw [hctr]; exact hu p hp
  have hφs : ∀ p, p ≤ m → ContDiffOn ℝ (J + 1 : ℕ) (φ p) (Ioo (-1 : ℝ) 2) :=
    fun p _ => H.arm_smooth _ _
  have hφB : ∀ p, p ≤ m → ∀ s ∈ Icc (0 : ℝ) 1, |iteratedDeriv (J + 1) (φ p) s| ≤ N ^ ε :=
    fun p _ => H.arm_top _ _
  have hmain := switching_endpoint H.hJ hk₀ hk₀J hβk₀ H.hm H.hmJ H.hN hK0 he₀ hla0 hlf0 hact
    hγ1 hγ2 hκ hlo0 hhi1 hlen hlen' φ hφs hφB c hc t ht cf hcf u hu' j
  rw [hctr, hwid] at hmain
  -- the final target
  set i : ℕ := m - 1 - (j : ℕ) with hi_def
  have him : i < m := by have := j.isLt; omega
  have hEf := hP.memE (m + 1) le_rfl
  have hφm : φ m = arm f₁ f₂ (κ m) (E (m + 1)) := (hP.arm_eq m le_rfl).symm
  set tc := dcenter h (k + 1) (E (m + 1)).2 with htc_def
  have htc01 : tc ∈ Icc (0 : ℝ) 1 := dcenter_mem_Icc h _ (H.hS _ hEf).1
  have htf01 : (E (m + 1)).2 ∈ Icc (0 : ℝ) 1 := H.time_mem hEf
  have hk1q : k + 1 ≤ q := by have := H.hkq; omega
  have hdist : |(E (m + 1)).2 - tc| ≤ N ^ (-jetRadius J β lc) := by
    rw [abs_sub_comm]
    refine (abs_dcenter_sub_le h _ _).trans ?_
    have := H.inv_pow_le hk1q
    have h0 : (0 : ℝ) ≤ ((2 : ℝ) ^ h (k + 1))⁻¹ := by positivity
    linarith
  have hfin := final_jet_near_binJet H.hJ hk₀ hk₀J hβk₀ H.hm H.hmJ H.hN hla0 hlc0 hact hlen
    (H.arm_smooth (κ m) (E (m + 1))) (H.arm_top (κ m) (E (m + 1))) c htc01 htf01 hdist him
  rw [hctr, hwid] at hfin
  -- the start comparison of the free evolutions
  have hsI : ∀ p, p ≤ m + 1 → |ntime h k a (E p).2| ≤ 1 / 2 := by
    intro p hp
    have h1 := ht p hp
    unfold ntime
    rw [abs_div, abs_of_pos hlam0, div_le_iff₀ hlam0, abs_le]
    rw [← hta_def, ← hctr]
    constructor <;> nlinarith [h1.1, h1.2]
  have hfree : ∀ σ : ℝ, |σ - ntime h k a a.2| ≤ 1 →
      |freeJet m (fun i => iteratedDeriv i (normArm (φ 0)
          (taylorPoly J c ta) ta lam (N ^ β m) m) ((t 0 - ta) / lam)) ((t 0 - ta) / lam) σ j -
        freeJet m (jet0 J β m N f₁ h k a) (ntime h k a a.2) σ j| ≤
      3 * (2 ^ m * (3 * (5 * N ^ ε + 1) + 2 * N ^ ε) * N ^ (-(6 / (q : ℝ)))) := by
    intro σ hσ
    have hmJ' := H.hmJ
    have ht0 : (t 0 - ta) / lam = ntime h k a a.2 := rfl
    rw [ht0]
    refine abs_freeJet_sub_le _ _ _ σ hσ (fun i' hi' => ?_) j
    have hU : IsOpen (Ioo (-1 : ℝ) 2) := isOpen_Ioo
    have hsU : ta + lam * ntime h k a a.2 ∈ Ioo (-1 : ℝ) 2 := by
      have : ta + lam * ntime h k a a.2 = a.2 := by
        unfold ntime; rw [← hta_def, ← hlam]; field_simp; ring
      rw [this]
      exact ⟨by linarith [haI.1], by linarith [haI.2]⟩
    have hgap := normArm_gap hU (hφs 0 (by omega)) (H.hf₁ a.1.1)
      (contDiff_taylorPoly J c ta) ta lam (N ^ β m) m (by omega : i' ≤ J + 1) hsU
    have hts : ta + lam * ntime h k a a.2 = a.2 := by
      unfold ntime; rw [← hta_def, ← hlam]; field_simp; ring
    rw [hts] at hgap
    unfold jet0 nArm
    rw [← hc_def, ← hta_def, ← hlam, hgap, abs_mul]
    have hscale := scale_factor_le (N := N) (lam := lam) (βm := β m)
      (ra := jetRadius J β la) (lja := jetAccuracy (jetRadius J β) i' la) H.hN
      (by rw [← hwid]; exact hlen) hi'.le
      (jetAccuracy_eq_beta_add H.hJ β hla0 H.hm H.hmJ hi'.le hact)
    have hpos : 0 ≤ N ^ β m * (lam ^ m)⁻¹ * lam ^ i' := by positivity
    rw [abs_of_nonneg hpos]
    have hst := H.path_start hP (i := i') (by omega)
    calc N ^ β m * (lam ^ m)⁻¹ * lam ^ i' *
          |iteratedDeriv i' (φ 0) a.2 - iteratedDeriv i' (f₁ a.1.1) a.2|
        ≤ (2 ^ m * N ^ jetAccuracy (jetRadius J β) i' la) *
          ((3 * (5 * N ^ ε + 1) + 2 * N ^ ε) * N ^ (-jetAccuracy (jetRadius J β) i' lf)) :=
          mul_le_mul hscale hst (abs_nonneg _) (by positivity)
      _ = 2 ^ m * (3 * (5 * N ^ ε + 1) + 2 * N ^ ε) *
          N ^ (jetAccuracy (jetRadius J β) i' la - jetAccuracy (jetRadius J β) i' lf) := by
          rw [sub_eq_add_neg, Real.rpow_add hN0]; ring
      _ ≤ 2 ^ m * (3 * (5 * N ^ ε + 1) + 2 * N ^ ε) * N ^ (-(6 / (q : ℝ))) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le H.hN (hκ i' hi'))
            (by positivity)
  -- assemble
  have hσf : |ntime h k a (E (m + 1)).2 - ntime h k a a.2| ≤ 1 := by
    have h1 := hsI (m + 1) le_rfl
    have h0 := hsI 0 (by omega)
    rw [ha_def] at h0 ⊢
    calc _ ≤ |ntime h k a (E (m + 1)).2| + |ntime h k (E 0) (E 0).2| := abs_sub _ _
      _ ≤ 1 / 2 + 1 / 2 := add_le_add h1 h0
      _ = 1 := by norm_num
  have hF := hfree _ hσf
  have hgainc := H.accuracy_gain_child j
  have htsf : ta + lam * ntime h k a (E (m + 1)).2 = (E (m + 1)).2 := by
    unfold ntime; rw [← hta_def, ← hlam]; field_simp; ring
  -- rewrite everything in the start normalization
  have e1 : (t (m + 1) - ta) / lam = ntime h k a (E (m + 1)).2 := rfl
  have e0 : (t 0 - ta) / lam = ntime h k a a.2 := rfl
  have e2 : (fun p : Fin m => (t ((p : ℕ) + 1) - ta) / lam) =
      fun p : Fin m => ntime h k a (E ((p : ℕ) + 1)).2 := rfl
  rw [e1, e0, e2] at hmain
  rw [e1] at hfin
  rw [hgainc] at hfin
  -- the tcen identity
  have htcen : tcen J β q k m N f₁ f₂ h a (E (m + 1)) (κ m) j (ntime h k a (E (m + 1)).2) =
      N ^ β m * (lam ^ m)⁻¹ * lam ^ i *
        (binJet J β N lc (finBins J β q k N f₁ f₂ h (E (m + 1)) (κ m)) tc i (E (m + 1)).2 -
          iteratedDeriv i (taylorPoly J c ta) (E (m + 1)).2) -
      freeJet m (jet0 J β m N f₁ h k a) (ntime h k a a.2) (ntime h k a (E (m + 1)).2) j := by
    unfold tcen
    rw [← hlam, ← hta_def, htsf]
  rw [htcen]
  set X := (endpointMap m (fun p => u p) (ntime h k a a.2)
      (ntime h k a (E (m + 1)).2, fun p : Fin m => ntime h k a (E ((p : ℕ) + 1)).2)).2 j
  set Y := iteratedDeriv i (nArm J β m N f₁ h k a (arm f₁ f₂ (κ m) (E (m + 1))))
      (ntime h k a (E (m + 1)).2)
  set B := N ^ β m * (lam ^ m)⁻¹ * lam ^ i *
      (binJet J β N lc (finBins J β q k N f₁ f₂ h (E (m + 1)) (κ m)) tc i (E (m + 1)).2 -
        iteratedDeriv i (taylorPoly J c ta) (E (m + 1)).2)
  set F0 := freeJet m (fun i => iteratedDeriv i (normArm (φ 0)
      (taylorPoly J c ta) ta lam (N ^ β m) m) (ntime h k a a.2)) (ntime h k a a.2)
      (ntime h k a (E (m + 1)).2) j
  set Fr := freeJet m (jet0 J β m N f₁ h k a) (ntime h k a a.2) (ntime h k a (E (m + 1)).2) j
  have hmain' : |Y - F0 - X| ≤ 9 ^ (m + 1) * (8 * (2 ^ m * (3 * K + 2 * N ^ ε) *
      N ^ (-(6 / (q : ℝ)))) + 2 ^ m * (e₀ + (3 * K + N ^ ε) * N ^ (-γ))) := by
    rw [hφm] at hmain; exact hmain
  have hfin' : |Y - B| ≤ 2 ^ m * (3 + 2 * N ^ ε) *
      N ^ (-((((j : ℕ) : ℝ) + 1) / (m : ℝ) / (q : ℝ))) := hfin
  have hF' : |F0 - Fr| ≤
      3 * (2 ^ m * (3 * (5 * N ^ ε + 1) + 2 * N ^ ε) * N ^ (-(6 / (q : ℝ)))) := hF
  calc |X - (B - Fr)| = |(Y - B) - (Y - F0 - X) - (F0 - Fr)| := by ring_nf
    _ ≤ |Y - B| + |Y - F0 - X| + |F0 - Fr| := by
        have := abs_sub (Y - B - (Y - F0 - X)) (F0 - Fr)
        have := abs_sub (Y - B) (Y - F0 - X)
        linarith
    _ ≤ _ := by
        have := add_le_add (add_le_add hfin' hmain') hF'
        linarith

end Det

end Submission.Obl.k4_matching_switching_target_certificate
