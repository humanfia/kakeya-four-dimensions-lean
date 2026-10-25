import Mathlib
import Submission.Obl.k4_matching_homogeneous_records.Encoding
import Submission.Obl.k4_matching_switching_target_certificate.SwitchingEndpoint

/-!
# The deterministic setting of one admissible step

`Det` bundles the hypotheses of o070 that the deterministic part of the switching
argument uses: the two lists of arms, their smoothness and derivative bounds, the event
gaps on `S`, the dyadic depths, the record equivalence, and the admissibility of the
step `k` with active order `m` and palette reference `z`. The radius and accuracy are
x0118's `jetRadius J β` and `jetAccuracy (jetRadius J β)`, which are definitionally the
frozen `r` and `l`.

Written for o070 by session x0236.
-/

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set

/-- The dyadic center at level `v` (the frozen `c`). -/
noncomputable def dcenter (h : ℕ → ℕ) (v : ℕ) (t : ℝ) : ℝ :=
  ((Int.floor (t * (2 : ℝ) ^ h v) : ℝ) + 1 / 2) / (2 : ℝ) ^ h v

/-- The left end of the dyadic interval at level `v`. -/
noncomputable def dleft (h : ℕ → ℕ) (v : ℕ) (t : ℝ) : ℝ :=
  (Int.floor (t * (2 : ℝ) ^ h v) : ℝ) / (2 : ℝ) ^ h v

variable {n₁ n₂ : ℕ}

/-- The arm of colour `κ` of an event: `false` is the first list, `true` the second. -/
def arm (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (κ : Bool)
    (e : (Fin n₁ × Fin n₂) × ℝ) : ℝ → ℝ :=
  if κ then f₂ e.1.2 else f₁ e.1.1

@[simp] lemma arm_false (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (e : (Fin n₁ × Fin n₂) × ℝ) : arm f₁ f₂ false e = f₁ e.1.1 := rfl

@[simp] lemma arm_true (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (e : (Fin n₁ × Fin n₂) × ℝ) : arm f₁ f₂ true e = f₂ e.1.2 := rfl

/-- The deterministic hypotheses of o070 at one admissible step. -/
structure Det (J : ℕ) (β : ℕ → ℝ) (γ : ℝ) (q k m z : ℕ) (N ε : ℝ)
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (h : ℕ → ℕ)
    (F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ) (S : Set ((Fin n₁ × Fin n₂) × ℝ)) : Prop where
  hJ : 1 ≤ J
  hβ : ∀ j : ℕ, 1 ≤ j → j ≤ J → 0 ≤ β j ∧ β j ≤ 2
  hzero : ∃ j : ℕ, 1 ≤ j ∧ j ≤ J ∧ β j = 0
  hγ : 0 < γ
  hq : 1 ≤ q
  hγq : 4 ≤ γ * (q : ℝ)
  hkq : k + 6 * (J + 1) ≤ q
  hm : 1 ≤ m
  hmJ : m ≤ J
  hβm : β m < 2
  hzk : z ≤ k
  hγz : γ ≤ (z : ℝ) / (q : ℝ)
  hadm : ∀ x ∈ Icc ((z : ℝ) / (q : ℝ)) (((k + 6 * (J + 1) : ℕ) : ℝ) / (q : ℝ)),
    jetRadius J β x = (x - β m) / (m : ℝ) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ J → j ≠ m → (x - β j) / (j : ℝ) < jetRadius J β x) ∧
    (∀ j : ℕ, j ≤ J →
      γ ≤ ((J : ℝ) + 1 - (j : ℝ)) * jetRadius J β x - jetAccuracy (jetRadius J β) j x) ∧
    (∀ i : ℕ, 1 ≤ i → m + i ≤ J →
      γ ≤ jetAccuracy (jetRadius J β) (m + i) x + (i : ℝ) * jetRadius J β x - β m)
  hN : 1 ≤ N
  hε : 0 < ε
  hf₁ : ∀ i, ContDiffOn ℝ (J + 1 : ℕ) (f₁ i) (Ioo (-1 : ℝ) 2)
  hf₂ : ∀ i, ContDiffOn ℝ (J + 1 : ℕ) (f₂ i) (Ioo (-1 : ℝ) 2)
  hB₁ : ∀ (i : Fin n₁) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Icc (0 : ℝ) 1,
    |iteratedDeriv j (f₁ i) t| ≤ N ^ ε
  hB₂ : ∀ (i : Fin n₂) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Icc (0 : ℝ) 1,
    |iteratedDeriv j (f₂ i) t| ≤ N ^ ε
  hS : ∀ p ∈ S, p.2 ∈ Ico (0 : ℝ) 1 ∧ |f₁ p.1.1 p.2 - f₂ p.1.2 p.2| ≤ N ^ (-1 + ε) ∧
    ∀ j : ℕ, 1 ≤ j → j ≤ J →
      |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2| ≤ N ^ (-β j + ε) ∧
      (β j < 2 → N ^ (-β j - ε) ≤
        |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2|)
  hmono : ∀ a b : ℕ, a ≤ b → b ≤ q → h a ≤ h b
  hdepth : ∀ k' : ℕ, k' ≤ q → N ^ (jetRadius J β ((k' : ℝ) / (q : ℝ))) ≤ (2 : ℝ) ^ h k' ∧
    (2 : ℝ) ^ h k' ≤ 2 * N ^ (jetRadius J β ((k' : ℝ) / (q : ℝ)))
  hrec : ∀ k' : ℕ, k' ≤ q → ∀ x ∈ S, ∀ y ∈ S, F k' x = F k' y ↔ ∀ v : ℕ, v ≤ k' →
    Int.floor (x.2 * (2 : ℝ) ^ h v) = Int.floor (y.2 * (2 : ℝ) ^ h v) ∧
    ∀ j : ℕ, j ≤ J →
      Int.floor (N ^ (jetAccuracy (jetRadius J β) j ((v : ℝ) / (q : ℝ))) *
          iteratedDeriv j (f₁ x.1.1) (dcenter h v x.2)) =
        Int.floor (N ^ (jetAccuracy (jetRadius J β) j ((v : ℝ) / (q : ℝ))) *
          iteratedDeriv j (f₁ y.1.1) (dcenter h v y.2)) ∧
      Int.floor (N ^ (jetAccuracy (jetRadius J β) j ((v : ℝ) / (q : ℝ))) *
          iteratedDeriv j (f₂ x.1.2) (dcenter h v x.2)) =
        Int.floor (N ^ (jetAccuracy (jetRadius J β) j ((v : ℝ) / (q : ℝ))) *
          iteratedDeriv j (f₂ y.1.2) (dcenter h v y.2))

namespace Det

variable {J : ℕ} {β : ℕ → ℝ} {γ : ℝ} {q k m z : ℕ} {N ε : ℝ}
  {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ} {h : ℕ → ℕ}
  {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}

variable (H : Det J β γ q k m z N ε f₁ f₂ h F S)
include H

lemma N_pos : 0 < N := lt_of_lt_of_le one_pos H.hN

lemma q_pos : (0 : ℝ) < q := by exact_mod_cast H.hq

lemma Npow_pos (x : ℝ) : 0 < N ^ x := Real.rpow_pos_of_pos H.N_pos x

lemma Nε_ge_one : 1 ≤ N ^ ε := Real.one_le_rpow H.hN H.hε.le

lemma arm_smooth (κ : Bool) (e : (Fin n₁ × Fin n₂) × ℝ) :
    ContDiffOn ℝ (J + 1 : ℕ) (arm f₁ f₂ κ e) (Ioo (-1 : ℝ) 2) := by
  cases κ
  · exact H.hf₁ _
  · exact H.hf₂ _

lemma arm_bound (κ : Bool) (e : (Fin n₁ × Fin n₂) × ℝ) {j : ℕ} (hj : j ≤ J + 1) :
    ∀ t ∈ Icc (0 : ℝ) 1, |iteratedDeriv j (arm f₁ f₂ κ e) t| ≤ N ^ ε := by
  cases κ
  · exact H.hB₁ _ j hj
  · exact H.hB₂ _ j hj

lemma arm_top (κ : Bool) (e : (Fin n₁ × Fin n₂) × ℝ) :
    ∀ t ∈ Icc (0 : ℝ) 1, |iteratedDeriv (J + 1) (arm f₁ f₂ κ e) t| ≤ N ^ ε :=
  H.arm_bound κ e le_rfl

/-- A zero exponent among the first `J` orders. -/
lemma exists_zero : ∃ k₀ : ℕ, 1 ≤ k₀ ∧ k₀ ≤ J ∧ β k₀ = 0 := H.hzero

lemma time_mem {p : (Fin n₁ × Fin n₂) × ℝ} (hp : p ∈ S) : p.2 ∈ Icc (0 : ℝ) 1 :=
  Ico_subset_Icc_self (H.hS p hp).1


/-- The level fractions of the step lie in the admissible window. -/
lemma level_mem {v : ℕ} (hzv : z ≤ v) (hv : v ≤ k + 6 * (J + 1)) :
    (v : ℝ) / q ∈ Icc ((z : ℝ) / (q : ℝ)) (((k + 6 * (J + 1) : ℕ) : ℝ) / (q : ℝ)) := by
  have hq := H.q_pos
  constructor
  · exact div_le_div_of_nonneg_right (by exact_mod_cast hzv) hq.le
  · exact div_le_div_of_nonneg_right (by exact_mod_cast hv) hq.le

lemma level_nonneg (v : ℕ) : (0 : ℝ) ≤ (v : ℝ) / q := div_nonneg (Nat.cast_nonneg v) H.q_pos.le

lemma level_le_one {v : ℕ} (hv : v ≤ q) : (v : ℝ) / q ≤ 1 := by
  rw [div_le_one H.q_pos]; exact_mod_cast hv

/-- The interval length `2^(-h v)` at a level is comparable to `N^(-r(v/q))`. -/
lemma inv_pow_le {v : ℕ} (hv : v ≤ q) :
    ((2 : ℝ) ^ h v)⁻¹ ≤ N ^ (-jetRadius J β ((v : ℝ) / q)) := by
  rw [Real.rpow_neg H.N_pos.le]
  exact inv_anti₀ (H.Npow_pos _) (H.hdepth v hv).1

lemma le_inv_pow {v : ℕ} (hv : v ≤ q) :
    N ^ (-jetRadius J β ((v : ℝ) / q)) / 2 ≤ ((2 : ℝ) ^ h v)⁻¹ := by
  rw [Real.rpow_neg H.N_pos.le, div_eq_mul_inv, ← mul_inv]
  refine inv_anti₀ (by positivity) ?_
  linarith [(H.hdepth v hv).2]

end Det

/-! ### Dyadic intervals -/

lemma dleft_le (h : ℕ → ℕ) (v : ℕ) (t : ℝ) : dleft h v t ≤ t := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ h v := by positivity
  rw [dleft, div_le_iff₀ h2]
  exact Int.floor_le _

lemma lt_dleft_add (h : ℕ → ℕ) (v : ℕ) (t : ℝ) : t < dleft h v t + ((2 : ℝ) ^ h v)⁻¹ := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ h v := by positivity
  rw [dleft, div_add' _ _ _ h2.ne', lt_div_iff₀ h2]
  have := Int.lt_floor_add_one (t * (2 : ℝ) ^ h v)
  field_simp
  linarith

lemma dcenter_eq (h : ℕ → ℕ) (v : ℕ) (t : ℝ) :
    dcenter h v t = dleft h v t + ((2 : ℝ) ^ h v)⁻¹ / 2 := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ h v := by positivity
  rw [dcenter, dleft]
  field_simp

/-- A time is within half an interval length of its dyadic center. -/
lemma abs_dcenter_sub_le (h : ℕ → ℕ) (v : ℕ) (t : ℝ) :
    |dcenter h v t - t| ≤ ((2 : ℝ) ^ h v)⁻¹ / 2 := by
  have h1 := dleft_le h v t
  have h2 := lt_dleft_add h v t
  rw [dcenter_eq, abs_le]
  constructor <;> linarith

lemma dcenter_congr {h : ℕ → ℕ} {v : ℕ} {s t : ℝ}
    (hst : Int.floor (s * (2 : ℝ) ^ h v) = Int.floor (t * (2 : ℝ) ^ h v)) :
    dcenter h v s = dcenter h v t := by
  rw [dcenter, dcenter, hst]

lemma dleft_congr {h : ℕ → ℕ} {v : ℕ} {s t : ℝ}
    (hst : Int.floor (s * (2 : ℝ) ^ h v) = Int.floor (t * (2 : ℝ) ^ h v)) :
    dleft h v s = dleft h v t := by
  rw [dleft, dleft, hst]

/-- A time in `[0, 1)` has its dyadic center in `[0, 1]`. -/
lemma dcenter_mem_Icc (h : ℕ → ℕ) (v : ℕ) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    dcenter h v t ∈ Icc (0 : ℝ) 1 :=
  Submission.Obl.k4_matching_homogeneous_records.dyadicCenter_mem ht

/-- Dyadic intervals are nested: equal intervals at a deeper level give equal intervals at a
coarser one. -/
lemma floor_eq_of_floor_eq_of_le {H H' : ℕ} (hH : H' ≤ H) {s t : ℝ}
    (hst : Int.floor (s * (2 : ℝ) ^ H) = Int.floor (t * (2 : ℝ) ^ H)) :
    Int.floor (s * (2 : ℝ) ^ H') = Int.floor (t * (2 : ℝ) ^ H') :=
  Submission.Obl.k4_matching_homogeneous_records.floor_dyadic_eq_of_finer_eq hH hst

lemma Det.floor_eq_of_le {J : ℕ} {β : ℕ → ℝ} {γ : ℝ} {q k m z : ℕ} {N ε : ℝ}
    {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ} {h : ℕ → ℕ}
    {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}
    (H : Det J β γ q k m z N ε f₁ f₂ h F S) {a b : ℕ} (hab : a ≤ b) (hbq : b ≤ q) {s t : ℝ}
    (hst : Int.floor (s * (2 : ℝ) ^ h b) = Int.floor (t * (2 : ℝ) ^ h b)) :
    Int.floor (s * (2 : ℝ) ^ h a) = Int.floor (t * (2 : ℝ) ^ h a) :=
  floor_eq_of_floor_eq_of_le (H.hmono a b hab hbq) hst

/-- A time in the dyadic interval of `s` at a deeper level lies within half a coarse
interval of the coarse center of `s`. -/
lemma abs_sub_dcenter_of_floor_eq {h : ℕ → ℕ} {v : ℕ} {s t : ℝ}
    (hst : Int.floor (s * (2 : ℝ) ^ h v) = Int.floor (t * (2 : ℝ) ^ h v)) :
    |t - dcenter h v s| ≤ ((2 : ℝ) ^ h v)⁻¹ / 2 := by
  rw [dcenter_congr hst, abs_sub_comm]
  exact abs_dcenter_sub_le h v t

end Submission.Obl.k4_matching_switching_target_certificate
