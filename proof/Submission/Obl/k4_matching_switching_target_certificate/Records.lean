import Mathlib
import Submission.Obl.k4_matching_switching_target_certificate.Setup

/-!
# Consequences of the record equivalence

Events of `S` with equal level-`k'` records have equal dyadic intervals and equal arm
bins at every level `v ≤ k'`, hence arm jets within `N^(-l_j(v/q))` at the common
center; the two arms of one event of `S` are `5 N^ε N^(-l_j(v/q))`-close near its time.

Written for o070 by session x0236.
-/

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set

variable {n₁ n₂ : ℕ}

namespace Det

variable {J : ℕ} {β : ℕ → ℝ} {γ : ℝ} {q k m z : ℕ} {N ε : ℝ}
  {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ} {h : ℕ → ℕ}
  {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}

variable (H : Det J β γ q k m z N ε f₁ f₂ h F S)
include H

/-- The bin of the colour-`κ` arm of `x` at level `v` and order `j`. -/
noncomputable def bin (J : ℕ) (β : ℕ → ℝ) (q : ℕ) (N : ℝ) (f₁ : Fin n₁ → ℝ → ℝ)
    (f₂ : Fin n₂ → ℝ → ℝ) (h : ℕ → ℕ) (v j : ℕ) (κ : Bool) (x : (Fin n₁ × Fin n₂) × ℝ) : ℤ :=
  Int.floor (N ^ (jetAccuracy (jetRadius J β) j ((v : ℝ) / (q : ℝ))) *
    iteratedDeriv j (arm f₁ f₂ κ x) (dcenter h v x.2))

/-- Equal records give equal intervals. -/
lemma rec_floor {k' : ℕ} (hk' : k' ≤ q) {x y : (Fin n₁ × Fin n₂) × ℝ} (hx : x ∈ S)
    (hy : y ∈ S) (hxy : F k' x = F k' y) {v : ℕ} (hv : v ≤ k') :
    Int.floor (x.2 * (2 : ℝ) ^ h v) = Int.floor (y.2 * (2 : ℝ) ^ h v) :=
  ((H.hrec k' hk' x hx y hy).mp hxy v hv).1

/-- Equal records give equal bins of both arms at every earlier level. -/
lemma rec_bin {k' : ℕ} (hk' : k' ≤ q) {x y : (Fin n₁ × Fin n₂) × ℝ} (hx : x ∈ S)
    (hy : y ∈ S) (hxy : F k' x = F k' y) {v : ℕ} (hv : v ≤ k') {j : ℕ} (hj : j ≤ J)
    (κ : Bool) : bin J β q N f₁ f₂ h v j κ x = bin J β q N f₁ f₂ h v j κ y := by
  have h1 := ((H.hrec k' hk' x hx y hy).mp hxy v hv).2 j hj
  cases κ
  · exact h1.1
  · exact h1.2

/-- Equal records give arm jets within `N^(-l_j(v/q))` at the common center. -/
lemma rec_close {k' : ℕ} (hk' : k' ≤ q) {x y : (Fin n₁ × Fin n₂) × ℝ} (hx : x ∈ S)
    (hy : y ∈ S) (hxy : F k' x = F k' y) {v : ℕ} (hv : v ≤ k') {j : ℕ} (hj : j ≤ J)
    (κ : Bool) :
    |iteratedDeriv j (arm f₁ f₂ κ x) (dcenter h v x.2) -
        iteratedDeriv j (arm f₁ f₂ κ y) (dcenter h v x.2)| ≤
      N ^ (-jetAccuracy (jetRadius J β) j ((v : ℝ) / (q : ℝ))) := by
  have hb := H.rec_bin hk' hx hy hxy hv hj κ
  have hc : dcenter h v x.2 = dcenter h v y.2 := dcenter_congr (H.rec_floor hk' hx hy hxy hv)
  unfold bin at hb
  rw [← hc] at hb
  exact abs_sub_le_of_floor_rpow_eq H.N_pos hb

/-- A record at a deeper level determines the record at a coarser level. -/
lemma rec_mono {a b : ℕ} (hab : a ≤ b) (hb : b ≤ q) {x y : (Fin n₁ × Fin n₂) × ℝ}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : F b x = F b y) : F a x = F a y := by
  rw [H.hrec a (hab.trans hb) x hx y hy]
  intro v hv
  exact (H.hrec b hb x hx y hy).mp hxy v (hv.trans hab)

/-- The two arms of an event of `S` are close at every time near the event time. -/
lemma arms_close {x : (Fin n₁ × Fin n₂) × ℝ} (hx : x ∈ S) {a : ℝ} (ha : 0 ≤ a)
    (ha1 : a ≤ 1) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1)
    (hdist : |c - x.2| ≤ N ^ (-jetRadius J β a)) (κ κ' : Bool) {j : ℕ} (hj : j ≤ J) :
    |iteratedDeriv j (arm f₁ f₂ κ x) c - iteratedDeriv j (arm f₁ f₂ κ' x) c| ≤
      5 * N ^ ε * N ^ (-jetAccuracy (jetRadius J β) j a) := by
  obtain ⟨k₀, hk₀, hk₀J, hβk₀⟩ := H.exists_zero
  have hS := H.hS x hx
  have ht : x.2 ∈ Icc (0 : ℝ) 1 := H.time_mem hx
  have hgap : ∀ j : ℕ, 1 ≤ j → j ≤ J →
      |iteratedDeriv j (f₁ x.1.1) x.2 - iteratedDeriv j (f₂ x.1.2) x.2| ≤ N ^ (-β j + ε) :=
    fun j h1 h2 => (hS.2.2 j h1 h2).1
  have key := arm_gap_at_level H.hJ hk₀ hk₀J hβk₀ H.hN (H.hf₁ x.1.1) (H.hf₂ x.1.2)
    (H.hB₁ x.1.1 (J + 1) le_rfl) (H.hB₂ x.1.2 (J + 1) le_rfl) ht hc hS.2.1 hgap ha ha1
    hdist hj
  have hpos : 0 ≤ 5 * N ^ ε * N ^ (-jetAccuracy (jetRadius J β) j a) := by
    have := H.Npow_pos ε; have := H.Npow_pos (-jetAccuracy (jetRadius J β) j a); positivity
  cases κ <;> cases κ'
  · simpa using hpos
  · simpa using key
  · simpa [abs_sub_comm] using key
  · simpa using hpos

/-- The two arms of an event of `S` are close at its dyadic center of any level `v ≤ q`. -/
lemma arms_close_center {x : (Fin n₁ × Fin n₂) × ℝ} (hx : x ∈ S) {v : ℕ} (hv : v ≤ q)
    (κ κ' : Bool) {j : ℕ} (hj : j ≤ J) :
    |iteratedDeriv j (arm f₁ f₂ κ x) (dcenter h v x.2) -
        iteratedDeriv j (arm f₁ f₂ κ' x) (dcenter h v x.2)| ≤
      5 * N ^ ε * N ^ (-jetAccuracy (jetRadius J β) j ((v : ℝ) / (q : ℝ))) := by
  refine H.arms_close hx (H.level_nonneg v) (H.level_le_one hv)
    (dcenter_mem_Icc h v (H.hS x hx).1) ?_ κ κ' hj
  refine (abs_dcenter_sub_le h v x.2).trans ?_
  have := H.inv_pow_le hv
  have h0 : (0 : ℝ) ≤ ((2 : ℝ) ^ h v)⁻¹ := by positivity
  linarith

end Det

end Submission.Obl.k4_matching_switching_target_certificate
