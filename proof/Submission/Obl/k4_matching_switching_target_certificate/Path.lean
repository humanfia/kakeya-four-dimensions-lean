-- Adapted from this LOT tree, o070/x0236 commit 12c7648, Path.lean.
import Mathlib
import Submission.Obl.k4_matching_switching_target_certificate.Records

/-!
# Alternating paths of events: coarse chain and fine switches

A path of the switching experiment from a start `a ∈ S`: events `E 0 = a, E 1, …, E (m+1)`
and refreshed events `W 0, …, W m`, colours `κ p`, where `W p` has the fine record of
`E p`, and `E (p+1)` shares the colour-`κ p` arm and the coarse interval of `W p`. The arm
traversed on leg `p` is `arm (κ p) (W p)`.

We show: every event stays in the coarse interval of the start; every traversed arm is a
coarse neighbour of the reference arm `f₁ a.1.1` at the coarse center; consecutive arms
are close at the fine center of the switching event.

Written for o070 by session x0236.
-/

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set

variable {n₁ n₂ : ℕ}

/-- The level-`k` interval length `2^(-h k)`. -/
noncomputable def lamk (h : ℕ → ℕ) (k : ℕ) : ℝ := ((2 : ℝ) ^ h k)⁻¹

lemma lamk_pos (h : ℕ → ℕ) (k : ℕ) : 0 < lamk h k := by unfold lamk; positivity

/-- The alternating-path relation of the switching experiment. -/
structure IsPath (F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ) (S : Set ((Fin n₁ × Fin n₂) × ℝ))
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (h : ℕ → ℕ) (k C m : ℕ)
    (E W : ℕ → (Fin n₁ × Fin n₂) × ℝ) (κ : ℕ → Bool) : Prop where
  memE : ∀ p, p ≤ m + 1 → E p ∈ S
  memW : ∀ p, p ≤ m → W p ∈ S
  fine : ∀ p, p ≤ m → F (k + C) (W p) = F (k + C) (E p)
  arm_eq : ∀ p, p ≤ m → arm f₁ f₂ (κ p) (E (p + 1)) = arm f₁ f₂ (κ p) (W p)
  ival : ∀ p, p ≤ m →
    Int.floor ((W p).2 * (2 : ℝ) ^ h k) = Int.floor ((E (p + 1)).2 * (2 : ℝ) ^ h k)

namespace Det

variable {J : ℕ} {β : ℕ → ℝ} {γ : ℝ} {q k m z : ℕ} {N ε : ℝ}
  {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ} {h : ℕ → ℕ}
  {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}

variable (H : Det J β γ q k m z N ε f₁ f₂ h F S)
include H

lemma k_le_q : k ≤ q := by have := H.hkq; omega

lemma kC_le_q : k + 6 * (J + 1) ≤ q := H.hkq


/-- Along a path, every event lies in the coarse interval of the start. -/
lemma path_floor {E W : ℕ → (Fin n₁ × Fin n₂) × ℝ} {κ : ℕ → Bool}
    (hP : IsPath F S f₁ f₂ h k (6 * (J + 1)) m E W κ) :
    (∀ p, p ≤ m + 1 →
      Int.floor ((E p).2 * (2 : ℝ) ^ h k) = Int.floor ((E 0).2 * (2 : ℝ) ^ h k)) ∧
    (∀ p, p ≤ m →
      Int.floor ((W p).2 * (2 : ℝ) ^ h k) = Int.floor ((E 0).2 * (2 : ℝ) ^ h k)) := by
  have hW : ∀ p, p ≤ m → Int.floor ((W p).2 * (2 : ℝ) ^ h k) =
      Int.floor ((E p).2 * (2 : ℝ) ^ h k) := fun p hp =>
    H.rec_floor H.kC_le_q (hP.memW p hp) (hP.memE p (by omega)) (hP.fine p hp) (Nat.le_add_right k (6 * (J + 1)))
  have hE : ∀ p, p ≤ m + 1 →
      Int.floor ((E p).2 * (2 : ℝ) ^ h k) = Int.floor ((E 0).2 * (2 : ℝ) ^ h k) := by
    intro p
    induction p with
    | zero => intro _; rfl
    | succ p ih =>
      intro hp
      rw [← hP.ival p (by omega), hW p (by omega), ih (by omega)]
  exact ⟨hE, fun p hp => (hW p hp).trans (hE p (by omega))⟩

/-- Coarse neighbours: both arms of every event of the path have jets at the coarse
center within `D N^(-l_i(a))` of the reference arm `f₁ (E 0).1.1`. -/
lemma path_coarse {E W : ℕ → (Fin n₁ × Fin n₂) × ℝ} {κ : ℕ → Bool}
    (hP : IsPath F S f₁ f₂ h k (6 * (J + 1)) m E W κ) :
    (∀ p, p ≤ m + 1 → ∀ (κ' : Bool) (i : ℕ), i ≤ J →
      |iteratedDeriv i (arm f₁ f₂ κ' (E p)) (dcenter h k (E 0).2) -
          iteratedDeriv i (f₁ (E 0).1.1) (dcenter h k (E 0).2)| ≤
        ((p : ℝ) * (5 * N ^ ε + 1) + 5 * N ^ ε) *
          N ^ (-jetAccuracy (jetRadius J β) i ((k : ℝ) / (q : ℝ)))) ∧
    (∀ p, p ≤ m → ∀ (κ' : Bool) (i : ℕ), i ≤ J →
      |iteratedDeriv i (arm f₁ f₂ κ' (W p)) (dcenter h k (E 0).2) -
          iteratedDeriv i (f₁ (E 0).1.1) (dcenter h k (E 0).2)| ≤
        ((p : ℝ) * (5 * N ^ ε + 1) + 5 * N ^ ε + 1) *
          N ^ (-jetAccuracy (jetRadius J β) i ((k : ℝ) / (q : ℝ)))) := by
  obtain ⟨hfE, hfW⟩ := H.path_floor hP
  set ta := dcenter h k (E 0).2 with hta
  set L : ℕ → ℝ := fun i => N ^ (-jetAccuracy (jetRadius J β) i ((k : ℝ) / (q : ℝ))) with hL
  have hNε := H.Npow_pos ε
  -- centers agree along the path
  have hcE : ∀ p, p ≤ m + 1 → dcenter h k (E p).2 = ta := fun p hp =>
    (dcenter_congr (hfE p hp)).trans rfl
  have hcW : ∀ p, p ≤ m → dcenter h k (W p).2 = ta := fun p hp =>
    (dcenter_congr (hfW p hp)).trans rfl
  -- the refresh step
  have stepW : ∀ p, p ≤ m → ∀ (κ' : Bool) (i : ℕ), i ≤ J →
      |iteratedDeriv i (arm f₁ f₂ κ' (W p)) ta - iteratedDeriv i (arm f₁ f₂ κ' (E p)) ta| ≤
        L i := by
    intro p hp κ' i hi
    have := H.rec_close H.kC_le_q (hP.memW p hp) (hP.memE p (by omega)) (hP.fine p hp)
      (Nat.le_add_right k (6 * (J + 1))) hi κ'
    rwa [hcW p hp] at this
  -- the two arms of one event
  have twoArms : ∀ p, p ≤ m + 1 → ∀ (κ' κ'' : Bool) (i : ℕ), i ≤ J →
      |iteratedDeriv i (arm f₁ f₂ κ' (E p)) ta - iteratedDeriv i (arm f₁ f₂ κ'' (E p)) ta| ≤
        5 * N ^ ε * L i := by
    intro p hp κ' κ'' i hi
    have := H.arms_close_center (hP.memE p hp) H.k_le_q κ' κ'' hi
    rwa [hcE p hp] at this
  have hE : ∀ p, p ≤ m + 1 → ∀ (κ' : Bool) (i : ℕ), i ≤ J →
      |iteratedDeriv i (arm f₁ f₂ κ' (E p)) ta - iteratedDeriv i (f₁ (E 0).1.1) ta| ≤
        ((p : ℝ) * (5 * N ^ ε + 1) + 5 * N ^ ε) * L i := by
    intro p
    induction p with
    | zero =>
      intro _ κ' i hi
      have := twoArms 0 (by omega) κ' false i hi
      simp only [arm_false, Nat.cast_zero, zero_mul, zero_add] at this ⊢
      exact this
    | succ p ih =>
      intro hp κ' i hi
      have hL0 : 0 ≤ L i := (H.Npow_pos _).le
      have h1 := twoArms (p + 1) hp κ' (κ p) i hi
      rw [hP.arm_eq p (by omega)] at h1
      have h2 := stepW p (by omega) (κ p) i hi
      have h3 := ih (by omega) (κ p) i hi
      calc |iteratedDeriv i (arm f₁ f₂ κ' (E (p + 1))) ta - iteratedDeriv i (f₁ (E 0).1.1) ta|
          ≤ |iteratedDeriv i (arm f₁ f₂ κ' (E (p + 1))) ta -
              iteratedDeriv i (arm f₁ f₂ (κ p) (W p)) ta| +
            |iteratedDeriv i (arm f₁ f₂ (κ p) (W p)) ta -
              iteratedDeriv i (arm f₁ f₂ (κ p) (E p)) ta| +
            |iteratedDeriv i (arm f₁ f₂ (κ p) (E p)) ta -
              iteratedDeriv i (f₁ (E 0).1.1) ta| := by
            have := abs_sub_le (iteratedDeriv i (arm f₁ f₂ κ' (E (p + 1))) ta)
              (iteratedDeriv i (arm f₁ f₂ (κ p) (E p)) ta) (iteratedDeriv i (f₁ (E 0).1.1) ta)
            have := abs_sub_le (iteratedDeriv i (arm f₁ f₂ κ' (E (p + 1))) ta)
              (iteratedDeriv i (arm f₁ f₂ (κ p) (W p)) ta)
              (iteratedDeriv i (arm f₁ f₂ (κ p) (E p)) ta)
            linarith
        _ ≤ 5 * N ^ ε * L i + L i + ((p : ℝ) * (5 * N ^ ε + 1) + 5 * N ^ ε) * L i := by
            gcongr
        _ = (((p + 1 : ℕ) : ℝ) * (5 * N ^ ε + 1) + 5 * N ^ ε) * L i := by push_cast; ring
  refine ⟨hE, ?_⟩
  intro p hp κ' i hi
  have h2 := stepW p hp κ' i hi
  have h3 := hE p (by omega) κ' i hi
  calc |iteratedDeriv i (arm f₁ f₂ κ' (W p)) ta - iteratedDeriv i (f₁ (E 0).1.1) ta|
      ≤ |iteratedDeriv i (arm f₁ f₂ κ' (W p)) ta - iteratedDeriv i (arm f₁ f₂ κ' (E p)) ta| +
        |iteratedDeriv i (arm f₁ f₂ κ' (E p)) ta - iteratedDeriv i (f₁ (E 0).1.1) ta| :=
        abs_sub_le _ _ _
    _ ≤ L i + ((p : ℝ) * (5 * N ^ ε + 1) + 5 * N ^ ε) * L i := add_le_add h2 h3
    _ = ((p : ℝ) * (5 * N ^ ε + 1) + 5 * N ^ ε + 1) * L i := by ring

/-- Fine switches: at the fine center of `E p` (`1 ≤ p ≤ m`), the arm of leg `p` and the
arm of leg `p - 1` are `(5 N^ε + 1) N^(-l_i(f))`-close. -/
lemma path_switch {E W : ℕ → (Fin n₁ × Fin n₂) × ℝ} {κ : ℕ → Bool}
    (hP : IsPath F S f₁ f₂ h k (6 * (J + 1)) m E W κ) {p : ℕ} (hp1 : 1 ≤ p) (hpm : p ≤ m)
    {i : ℕ} (hi : i ≤ J) :
    |iteratedDeriv i (arm f₁ f₂ (κ p) (W p)) (dcenter h (k + 6 * (J + 1)) (E p).2) -
        iteratedDeriv i (arm f₁ f₂ (κ (p - 1)) (W (p - 1)))
          (dcenter h (k + 6 * (J + 1)) (E p).2)| ≤
      (5 * N ^ ε + 1) *
        N ^ (-jetAccuracy (jetRadius J β) i (((k + 6 * (J + 1) : ℕ) : ℝ) / (q : ℝ))) := by
  have hp' : p - 1 + 1 = p := by omega
  have harm := hP.arm_eq (p - 1) (by omega)
  rw [hp'] at harm
  rw [← harm]
  set cf := dcenter h (k + 6 * (J + 1)) (E p).2
  have h1 := H.rec_close H.kC_le_q (hP.memE p (by omega)) (hP.memW p hpm) (hP.fine p hpm).symm
    le_rfl hi (κ p)
  have h2 := H.arms_close_center (hP.memE p (by omega)) H.kC_le_q (κ p) (κ (p - 1)) hi
  calc |iteratedDeriv i (arm f₁ f₂ (κ p) (W p)) cf -
        iteratedDeriv i (arm f₁ f₂ (κ (p - 1)) (E p)) cf|
      ≤ |iteratedDeriv i (arm f₁ f₂ (κ p) (W p)) cf -
          iteratedDeriv i (arm f₁ f₂ (κ p) (E p)) cf| +
        |iteratedDeriv i (arm f₁ f₂ (κ p) (E p)) cf -
          iteratedDeriv i (arm f₁ f₂ (κ (p - 1)) (E p)) cf| := abs_sub_le _ _ _
    _ ≤ N ^ (-jetAccuracy (jetRadius J β) i (((k + 6 * (J + 1) : ℕ) : ℝ) / (q : ℝ))) +
        5 * N ^ ε *
          N ^ (-jetAccuracy (jetRadius J β) i (((k + 6 * (J + 1) : ℕ) : ℝ) / (q : ℝ))) := by
        refine add_le_add ?_ h2
        rw [abs_sub_comm]; exact h1
    _ = _ := by ring

/-- The first refreshed arm is close to the reference arm at the start time. -/
lemma path_start {E W : ℕ → (Fin n₁ × Fin n₂) × ℝ} {κ : ℕ → Bool}
    (hP : IsPath F S f₁ f₂ h k (6 * (J + 1)) m E W κ) {i : ℕ} (hi : i ≤ J) :
    |iteratedDeriv i (arm f₁ f₂ (κ 0) (W 0)) (E 0).2 - iteratedDeriv i (f₁ (E 0).1.1) (E 0).2|
      ≤ (3 * (5 * N ^ ε + 1) + 2 * N ^ ε) *
        N ^ (-jetAccuracy (jetRadius J β) i (((k + 6 * (J + 1) : ℕ) : ℝ) / (q : ℝ))) := by
  obtain ⟨k₀, hk₀, hk₀J, hβk₀⟩ := H.exists_zero
  have hE0 := hP.memE 0 (by omega)
  have hW0 := hP.memW 0 (by omega)
  set f := (((k + 6 * (J + 1) : ℕ) : ℝ) / (q : ℝ)) with hf
  set cf := dcenter h (k + 6 * (J + 1)) (E 0).2 with hcf
  -- closeness at the fine center
  have hgap : ∀ i' : ℕ, i' ≤ J →
      |iteratedDeriv i' (arm f₁ f₂ (κ 0) (W 0)) cf - iteratedDeriv i' (f₁ (E 0).1.1) cf| ≤
        (5 * N ^ ε + 1) * N ^ (-jetAccuracy (jetRadius J β) i' f) := by
    intro i' hi'
    have h1 := H.rec_close H.kC_le_q hE0 hW0 (hP.fine 0 (by omega)).symm le_rfl hi' (κ 0)
    have h2 := H.arms_close_center hE0 H.kC_le_q (κ 0) false hi'
    simp only [arm_false] at h2
    calc |iteratedDeriv i' (arm f₁ f₂ (κ 0) (W 0)) cf - iteratedDeriv i' (f₁ (E 0).1.1) cf|
        ≤ |iteratedDeriv i' (arm f₁ f₂ (κ 0) (W 0)) cf -
            iteratedDeriv i' (arm f₁ f₂ (κ 0) (E 0)) cf| +
          |iteratedDeriv i' (arm f₁ f₂ (κ 0) (E 0)) cf - iteratedDeriv i' (f₁ (E 0).1.1) cf| :=
          abs_sub_le _ _ _
      _ ≤ N ^ (-jetAccuracy (jetRadius J β) i' f) +
          5 * N ^ ε * N ^ (-jetAccuracy (jetRadius J β) i' f) := by
          refine add_le_add ?_ h2
          rw [abs_sub_comm]; exact h1
      _ = _ := by ring
  have hcf01 : cf ∈ Icc (0 : ℝ) 1 := dcenter_mem_Icc h _ (H.hS _ hE0).1
  have ht01 : (E 0).2 ∈ Icc (0 : ℝ) 1 := H.time_mem hE0
  have hdist : |(E 0).2 - cf| ≤ N ^ (-jetRadius J β f) := by
    rw [abs_sub_comm]
    refine (abs_dcenter_sub_le h _ _).trans ?_
    have := H.inv_pow_le H.kC_le_q
    have h0 : (0 : ℝ) ≤ ((2 : ℝ) ^ h (k + 6 * (J + 1)))⁻¹ := by positivity
    linarith
  have hNε := H.Npow_pos ε
  exact gap_translate_at_level H.hJ hk₀ hk₀J hβk₀ H.hN (by positivity) (H.arm_smooth _ _)
    (H.hf₁ _) (H.arm_top _ _) (H.hB₁ _ (J + 1) le_rfl) (H.level_nonneg _) hcf01 ht01 hgap
    hdist hi

end Det

end Submission.Obl.k4_matching_switching_target_certificate
