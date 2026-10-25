-- Adapted from this LOT tree, o080/x0272 commit 4d767e4, Submission/Obl/k4_matching_geometric_path_cover/PathNeighbors.lean.
import Submission.Obl.k4_matching_switching_target_certificate.Path
import Submission.Obl.k4_matching_switching_target_certificate.CoarseJetNeighbors
import Submission.Obl.k4_matching_switching_target_certificate.DetControls

noncomputable section

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set
open Submission.Obl.k4_matching_homogeneous_records (offsetCutoff dyadicCenter)

/-- The whole-history bin radius for paths of at most `m+1` traversals. -/
def neighborRadius (J m : ℕ) (N ε : ℝ) : ℕ := 2 * (m + 1) * offsetCutoff J N ε

/-- One common neighbor set for all alternating paths from an exact start. -/
def neighborEvents {n₁ n₂ : ℕ} (J k m q : ℕ) (β : ℕ → ℝ) (N ε : ℝ)
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (h : ℕ → ℕ)
    (S : Set ((Fin n₁ × Fin n₂) × ℝ)) (a : (Fin n₁ × Fin n₂) × ℝ) :
    Set ((Fin n₁ × Fin n₂) × ℝ) :=
  coarseNeighborBox f₁ f₂ h (coarseJetScale J β N q) k J S a (neighborRadius J m N ε)

namespace Det

variable {n₁ n₂ J : ℕ} {β : ℕ → ℝ} {γ : ℝ} {q k m z : ℕ} {N ε : ℝ}
  {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ} {h : ℕ → ℕ}
  {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}

variable (H : Det J β γ q k m z N ε f₁ f₂ h F S)
include H

lemma coarse_record_eq_iff {x y : (Fin n₁ × Fin n₂) × ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    F k x = F k y ↔ coarseTimeProfile h k x = coarseTimeProfile h k y ∧
      coarseBinProfile f₁ f₂ h (coarseJetScale J β N q) k J x =
        coarseBinProfile f₁ f₂ h (coarseJetScale J β N q) k J y := by
  exact (H.hrec k H.k_le_q x hx y hy).trans
    (coarse_profiles_eq_iff f₁ f₂ h (coarseJetScale J β N q) k J x y).symm

lemma coarse_cross_gap {e : (Fin n₁ × Fin n₂) × ℝ} (he : e ∈ S) :
    ∀ i, |coarseBinProfile f₁ f₂ h (coarseJetScale J β N q) k J e 0 i -
      coarseBinProfile f₁ f₂ h (coarseJetScale J β N q) k J e 1 i| ≤
        (offsetCutoff J N ε : ℤ) := by
  obtain ⟨k₀, hk₀, hk₀J, hβk₀⟩ := H.exists_zero
  exact event_coarse_bin_gap H.hJ H.hq H.k_le_q hk₀ hk₀J hβk₀ H.hN f₁ f₂
    H.hf₁ H.hf₂ (fun i t ht => H.hB₁ i (J + 1) le_rfl t ht)
    (fun i t ht => H.hB₂ i (J + 1) le_rfl t ht) h
    (fun v hv => (H.hdepth v (hv.trans H.k_le_q)).1) e (H.hS e he).1
    (H.hS e he).2.1 (fun j hj hjJ => ((H.hS e he).2.2 j hj hjJ).1)

lemma path_traverse_profile {E W : ℕ → (Fin n₁ × Fin n₂) × ℝ} {κ : ℕ → Bool}
    (hP : IsPath F S f₁ f₂ h k (6 * (J + 1)) m E W κ) {p : ℕ} (hp : p ≤ m) :
    coarseTimeProfile h k (W p) = coarseTimeProfile h k (E (p + 1)) ∧
      ∃ a, coarseBinProfile f₁ f₂ h (coarseJetScale J β N q) k J (W p) a =
        coarseBinProfile f₁ f₂ h (coarseJetScale J β N q) k J (E (p + 1)) a := by
  have hfloor : ∀ v : ℕ, v ≤ k →
      Int.floor ((W p).2 * (2 : ℝ) ^ h v) =
        Int.floor ((E (p + 1)).2 * (2 : ℝ) ^ h v) :=
    fun v hv => H.floor_eq_of_le hv H.k_le_q (hP.ival p hp)
  have hc : ∀ v : ℕ, v ≤ k →
      dyadicCenter (h v) (W p).2 = dyadicCenter (h v) (E (p + 1)).2 := by
    intro v hv
    exact dcenter_congr (hfloor v hv)
  refine ⟨funext (fun v => hfloor v (Nat.le_of_lt_succ v.isLt)), ?_⟩
  have ha := hP.arm_eq p hp
  cases heq : κ p
  · refine ⟨0, ?_⟩
    simp only [heq, arm_false] at ha
    funext vj
    simp only [coarseBinProfile, ite_true]
    rw [hc vj.1 (Nat.le_of_lt_succ vj.1.isLt), ha]
  · refine ⟨1, ?_⟩
    simp only [heq, arm_true] at ha
    funext vj
    simp only [coarseBinProfile, show (1 : Fin 2) ≠ 0 by decide, ite_false]
    rw [hc vj.1 (Nat.le_of_lt_succ vj.1.isLt), ha]

/-- All histories along the path stay in one integer box around the start. -/
lemma path_neighbor_events {E W : ℕ → (Fin n₁ × Fin n₂) × ℝ} {κ : ℕ → Bool}
    (hP : IsPath F S f₁ f₂ h k (6 * (J + 1)) m E W κ) :
    (∀ p, p ≤ m + 1 → E p ∈ neighborEvents J k m q β N ε f₁ f₂ h S (E 0)) ∧
    (∀ p, p ≤ m → W p ∈ neighborEvents J k m q β N ε f₁ f₂ h S (E 0)) := by
  let b := coarseBinProfile f₁ f₂ h (coarseJetScale J β N q) k J
  let G := offsetCutoff J N ε
  have hrefresh : ∀ p, p ≤ m →
      coarseTimeProfile h k (W p) = coarseTimeProfile h k (E p) ∧ b (W p) = b (E p) := by
    intro p hp
    apply (H.coarse_record_eq_iff (hP.memW p hp) (hP.memE p (by omega))).mp
    exact H.rec_mono (Nat.le_add_right k _) H.kC_le_q
      (hP.memW p hp) (hP.memE p (by omega)) (hP.fine p hp)
  have hE : ∀ p, p ≤ m + 1 → coarseTimeProfile h k (E p) = coarseTimeProfile h k (E 0) ∧
      ∀ a i, |b (E p) a i - b (E 0) a i| ≤ ((2 * p * G : ℕ) : ℤ) := by
    intro p
    induction p with
    | zero => intro _; simp
    | succ p ih =>
      intro hp
      obtain ⟨ht, hb⟩ := ih (by omega)
      obtain ⟨htW, hbW⟩ := hrefresh p (by omega)
      obtain ⟨htT, hfixed⟩ := H.path_traverse_profile hP (p := p) (by omega)
      refine ⟨htT.symm.trans (htW.trans ht), ?_⟩
      intro a i
      have hs := two_color_bin_step (b (W p)) (b (E (p + 1))) G
        (H.coarse_cross_gap (hP.memW p (by omega)))
        (H.coarse_cross_gap (hP.memE (p + 1) hp)) hfixed a i
      rw [hbW] at hs
      calc |b (E (p + 1)) a i - b (E 0) a i|
          ≤ |b (E (p + 1)) a i - b (E p) a i| + |b (E p) a i - b (E 0) a i| :=
            abs_sub_le _ _ _
        _ ≤ 2 * (G : ℤ) + ((2 * p * G : ℕ) : ℤ) := add_le_add hs (hb a i)
        _ = ((2 * (p + 1) * G : ℕ) : ℤ) := by push_cast; ring
  have hcut : ∀ p, p ≤ m + 1 → ((2 * p * G : ℕ) : ℤ) ≤ (neighborRadius J m N ε : ℤ) := by
    intro p hp
    exact_mod_cast Nat.mul_le_mul_right G (Nat.mul_le_mul_left 2 hp)
  refine ⟨?_, ?_⟩
  · intro p hp
    exact ⟨hP.memE p hp, (hE p hp).1,
      fun a i => ((hE p hp).2 a i).trans (hcut p hp)⟩
  · intro p hp
    obtain ⟨htW, hbW⟩ := hrefresh p hp
    refine ⟨hP.memW p hp, htW.trans (hE p (by omega)).1, ?_⟩
    intro a i
    change |b (W p) a i - b (E 0) a i| ≤ _
    rw [hbW]
    exact ((hE p (by omega)).2 a i).trans (hcut p (by omega))

lemma neighbor_record_count (a : (Fin n₁ × Fin n₂) × ℝ) :
    (F k '' neighborEvents J k m q β N ε f₁ f₂ h S a).Finite ∧
      (F k '' neighborEvents J k m q β N ε f₁ f₂ h S a).ncard ≤
        (2 * neighborRadius J m N ε + 1) ^ (2 * (k + 1) * (J + 1)) := by
  apply coarse_neighbor_record_count
  intro x hx y hy ht hb
  exact (H.coarse_record_eq_iff hx hy).mpr ⟨ht, hb⟩

/-- The finite common collection of coarse labels associated with a start. -/
def neighborRecords (a : (Fin n₁ × Fin n₂) × ℝ) : Finset ℕ :=
  (H.neighbor_record_count a).1.toFinset

lemma mem_neighborRecords_iff (a : (Fin n₁ × Fin n₂) × ℝ) (b : ℕ) :
    b ∈ H.neighborRecords a ↔ b ∈ F k '' neighborEvents J k m q β N ε f₁ f₂ h S a :=
  Set.Finite.mem_toFinset _

lemma card_neighborRecords (a : (Fin n₁ × Fin n₂) × ℝ) :
    (H.neighborRecords a).card ≤
      (2 * neighborRadius J m N ε + 1) ^ (2 * (k + 1) * (J + 1)) := by
  change (H.neighbor_record_count a).1.toFinset.card ≤ _
  rw [← Set.ncard_eq_toFinset_card _ (H.neighbor_record_count a).1]
  exact (H.neighbor_record_count a).2

/-- A neighbor set is saturated under equality of the coarse record. -/
lemma mem_neighborEvents_of_record {a e : (Fin n₁ × Fin n₂) × ℝ} (he : e ∈ S)
    (hA : F k e ∈ H.neighborRecords a) :
    e ∈ neighborEvents J k m q β N ε f₁ f₂ h S a := by
  obtain ⟨y, hy, heq⟩ := (H.mem_neighborRecords_iff a (F k e)).mp hA
  obtain ⟨ht, hb⟩ := (H.coarse_record_eq_iff he hy.1).mp heq.symm
  exact ⟨he, ht.trans hy.2.1, fun c i => by rw [hb]; exact hy.2.2 c i⟩

lemma neighbor_floor {a e : (Fin n₁ × Fin n₂) × ℝ}
    (he : e ∈ neighborEvents J k m q β N ε f₁ f₂ h S a) :
    Int.floor (e.2 * (2 : ℝ) ^ h k) = Int.floor (a.2 * (2 : ℝ) ^ h k) :=
  congrFun he.2.1 ⟨k, Nat.lt_succ_self k⟩

/-- Every arm with one of the selected coarse labels has a uniformly bounded
jet in the common Taylor frame at the start's coarse center. -/
lemma neighbor_frame {a e : (Fin n₁ × Fin n₂) × ℝ} (ha : a ∈ S)
    (he : e ∈ neighborEvents J k m q β N ε f₁ f₂ h S a) (κ : Bool)
    {j : ℕ} (hj : j ≤ J) :
    |iteratedDeriv j (arm f₁ f₂ κ e) (dcenter h k a.2) -
        iteratedDeriv j (f₁ a.1.1) (dcenter h k a.2)| ≤
      ((neighborRadius J m N ε : ℝ) + 1 + 5 * N ^ ε) *
        N ^ (-jetAccuracy (jetRadius J β) j ((k : ℝ) / (q : ℝ))) := by
  have hc : dyadicCenter (h k) e.2 = dcenter h k a.2 :=
    dcenter_congr (H.neighbor_floor he)
  have hbin : |(Int.floor (N ^ jetAccuracy (jetRadius J β) j ((k : ℝ) / (q : ℝ)) *
        iteratedDeriv j (arm f₁ f₂ κ e) (dcenter h k a.2)) : ℝ) -
      (Int.floor (N ^ jetAccuracy (jetRadius J β) j ((k : ℝ) / (q : ℝ)) *
        iteratedDeriv j (arm f₁ f₂ κ a) (dcenter h k a.2)) : ℝ)| ≤
        (neighborRadius J m N ε : ℝ) := by
    have hb := he.2.2 (if κ then 1 else 0)
      ((⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)), (⟨j, by omega⟩ : Fin (J + 1)))
    cases κ <;> simp only [coarseBinProfile, coarseJetScale, Bool.false_eq_true,
      Bool.true_eq_false, ite_true, ite_false, show (1 : Fin 2) ≠ 0 by decide,
      Fin.isValue, hc, arm_false, arm_true] at hb ⊢ <;> exact_mod_cast hb
  have hnear := real_gap_of_floor_gap (H.Npow_pos _) hbin
  have hnear' : |iteratedDeriv j (arm f₁ f₂ κ e) (dcenter h k a.2) -
      iteratedDeriv j (arm f₁ f₂ κ a) (dcenter h k a.2)| ≤
      ((neighborRadius J m N ε : ℝ) + 1) *
        N ^ (-jetAccuracy (jetRadius J β) j ((k : ℝ) / (q : ℝ))) := by
    simpa only [Real.rpow_neg H.N_pos.le, div_eq_mul_inv] using hnear
  have hcross := H.arms_close_center ha H.k_le_q κ false hj
  simp only [arm_false] at hcross
  calc _ ≤ |iteratedDeriv j (arm f₁ f₂ κ e) (dcenter h k a.2) -
          iteratedDeriv j (arm f₁ f₂ κ a) (dcenter h k a.2)| +
        |iteratedDeriv j (arm f₁ f₂ κ a) (dcenter h k a.2) -
          iteratedDeriv j (f₁ a.1.1) (dcenter h k a.2)| := abs_sub_le _ _ _
    _ ≤ ((neighborRadius J m N ε : ℝ) + 1) *
        N ^ (-jetAccuracy (jetRadius J β) j ((k : ℝ) / (q : ℝ))) +
        5 * N ^ ε * N ^ (-jetAccuracy (jetRadius J β) j ((k : ℝ) / (q : ℝ))) :=
      add_le_add hnear' hcross
    _ = _ := by ring

lemma path_neighbor_records {E W : ℕ → (Fin n₁ × Fin n₂) × ℝ} {κ : ℕ → Bool}
    (hP : IsPath F S f₁ f₂ h k (6 * (J + 1)) m E W κ) :
    (∀ p, p ≤ m + 1 → F k (E p) ∈ H.neighborRecords (E 0)) ∧
    (∀ p, p ≤ m → F k (W p) ∈ H.neighborRecords (E 0)) := by
  obtain ⟨hE, hW⟩ := H.path_neighbor_events hP
  constructor
  · intro p hp
    exact (H.mem_neighborRecords_iff _ _).mpr ⟨E p, hE p hp, rfl⟩
  · intro p hp
    exact (H.mem_neighborRecords_iff _ _).mpr ⟨W p, hW p hp, rfl⟩

end Det

end Submission.Obl.k4_matching_switching_target_certificate
