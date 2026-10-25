-- Adapted from this LOT tree, o080/x0272 commit 4d767e4, Submission/Obl/k4_matching_geometric_path_cover/Certificate.lean.
import Submission.Obl.k4_matching_switching_target_certificate.ControlsOnNeighbors
import Submission.Obl.k4_matching_switching_target_certificate.Numerics

noncomputable section

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set MeasureTheory

/-- The final geometric certificate, using the named normalizations. -/
def GeometricCovers {n₁ n₂ : ℕ} (J q k m z : ℕ) (β u : ℕ → ℝ) (N η : ℝ)
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (h : ℕ → ℕ)
    (F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ) (S : Set ((Fin n₁ × Fin n₂) × ℝ)) : Prop :=
  ∃ K δ : ℝ, 2 ≤ K ∧ K ≤ N ^ η ∧ 0 < δ ∧
    ∀ a ∈ S, ∃ (A : Finset ℕ) (C : ℕ → (ℤ × ℤ) → Bool → ℝ)
      (T : Set (ℝ × (Fin m → ℝ))),
      |ntime h k a a.2| ≤ 1 ∧ (A.card : ℝ) ≤ K ∧
      (∀ e ∈ S, F k e ∈ A → ∀ c : Bool,
        |C (F k e) (referencePalette m z q β N h f₁ f₂ e) c| ≤ K) ∧
      (∀ e ∈ S, F k e ∈ A →
        2 / K ≤ |C (F k e) (referencePalette m z q β N h f₁ f₂ e) true -
          C (F k e) (referencePalette m z q β N h f₁ f₂ e) false|) ∧
      MeasurableSet T ∧
      volume T ≤ ENNReal.ofReal (K * N ^ (u (k + 1) - u k -
        (1 / (m : ℝ) + ((m : ℝ) + 1) / 2) / (q : ℝ))) ∧
      ∀ (E W : ℕ → ((Fin n₁ × Fin n₂) × ℝ)) (c : ℕ → Bool),
        E 0 = a → (∀ p : ℕ, p ≤ m + 1 → E p ∈ S) →
        (∀ p : ℕ, p ≤ m → W p ∈ S ∧
          F (k + 6 * (J + 1)) (W p) = F (k + 6 * (J + 1)) (E p) ∧
          (if c p then (W p).1.1 = (E (p + 1)).1.1 else (W p).1.2 = (E (p + 1)).1.2) ∧
          Int.floor ((W p).2 * (2 : ℝ) ^ h k) = Int.floor ((E (p + 1)).2 * (2 : ℝ) ^ h k)) →
        (∀ p : ℕ, p ≤ m + 1 → F k (E p) ∈ A) ∧
        (∀ p : ℕ, p ≤ m → F k (W p) ∈ A) ∧
        ∀ x : ℝ × (Fin m → ℝ), |x.1 - ntime h k a (E (m + 1)).2| ≤ δ →
          (∀ p : Fin m, |x.2 p - ntime h k a (E ((p : ℕ) + 1)).2| ≤ δ) →
          endpointMap m
            (fun p : Fin (m + 1) => C (F k (W p)) (referencePalette m z q β N h f₁ f₂ (W p)) (c p))
            (ntime h k a a.2) x ∈ T

/-- The frozen shared-index path convention is the opposite of `arm`'s Bool convention. -/
lemma isPath_of_shared_indices {n₁ n₂ J k m : ℕ}
    {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (h : ℕ → ℕ)
    {E W : ℕ → (Fin n₁ × Fin n₂) × ℝ} {c : ℕ → Bool}
    (hE : ∀ p : ℕ, p ≤ m + 1 → E p ∈ S)
    (hW : ∀ p : ℕ, p ≤ m → W p ∈ S ∧
      F (k + 6 * (J + 1)) (W p) = F (k + 6 * (J + 1)) (E p) ∧
      (if c p then (W p).1.1 = (E (p + 1)).1.1 else (W p).1.2 = (E (p + 1)).1.2) ∧
      Int.floor ((W p).2 * (2 : ℝ) ^ h k) = Int.floor ((E (p + 1)).2 * (2 : ℝ) ^ h k)) :
    IsPath F S f₁ f₂ h k (6 * (J + 1)) m E W (fun p => !(c p)) := by
  refine ⟨hE, fun p hp => (hW p hp).1, fun p hp => (hW p hp).2.1, ?_,
    fun p hp => (hW p hp).2.2.2⟩
  intro p hp
  have hi := (hW p hp).2.2.1
  cases hc : c p <;> simp only [hc, Bool.false_eq_true, ite_false, ite_true] at hi
  · simp only [hc, Bool.not_false, arm_true]
    rw [hi]
  · simp only [hc, Bool.not_true, arm_false]
    rw [hi]

namespace Det

variable {n₁ n₂ J : ℕ} {β : ℕ → ℝ} {γ : ℝ} {q k m z : ℕ} {N ε : ℝ}
  {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ} {h : ℕ → ℕ}
  {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}

/-- The target layer still needed after the controls and path localization.
The positive radius is common to all starts. -/
def TargetCovers (H : Det J β γ q k m z N ε f₁ f₂ h F S) (u : ℕ → ℝ) (C δ : ℝ) : Prop :=
  ∀ a ∈ S, ∃ T : Set (ℝ × (Fin m → ℝ)), MeasurableSet T ∧
    volume T ≤ ENNReal.ofReal
      (C * (H.neighborRecords a).card * N ^ (((m : ℝ) + 2) * ε) *
        N ^ (u (k + 1) - u k - (1 / (m : ℝ) + ((m : ℝ) + 1) / 2) / (q : ℝ))) ∧
    ∀ (E W : ℕ → ((Fin n₁ × Fin n₂) × ℝ)) (κ : ℕ → Bool), E 0 = a →
      IsPath F S f₁ f₂ h k (6 * (J + 1)) m E W κ →
      ∀ x : ℝ × (Fin m → ℝ), |x.1 - ntime h k a (E (m + 1)).2| ≤ δ →
        (∀ p : Fin m, |x.2 p - ntime h k a (E ((p : ℕ) + 1)).2| ≤ δ) →
        endpointMap m
          (fun p : Fin (m + 1) => codedControl J m k z q β N (dcenter h k a.2) (cref f₁ h k a m)
            h F S f₁ f₂ (F k (W p)) (referencePalette m z q β N h f₁ f₂ (W p)) (!(κ p)))
          (ntime h k a a.2) x ∈ T

variable (H : Det J β γ q k m z N ε f₁ f₂ h F S)
include H

lemma covers_of_targets (u : ℕ → ℝ) {C δ η : ℝ} (hC : 0 ≤ C)
    (hεq : ε ≤ 1 / (q : ℝ)) (hroot : 32 ≤ N ^ (1 / (q : ℝ)))
    (hscale : coverScale J k m C N ε ≤ N ^ η) (hδ : 0 < δ)
    (htargets : H.TargetCovers u C δ) :
    GeometricCovers J q k m z β u N η f₁ f₂ h F S := by
  let K := coverScale J k m C N ε
  have hK2 : 2 ≤ K := coverScale_ge_two J k m hC H.hN H.hε.le
  have hK0 : 0 < K := by linarith
  refine ⟨K, δ, hK2, hscale, hδ, ?_⟩
  intro a ha
  obtain ⟨T, hTm, hvol, hends⟩ := htargets a ha
  let Coded := codedControl J m k z q β N (dcenter h k a.2) (cref f₁ h k a m) h F S f₁ f₂
  have hcard : ((H.neighborRecords a).card : ℝ) ≤
      (((2 * neighborRadius J m N ε + 1 : ℕ) ^ coarseLossDegree J k : ℕ) : ℝ) := by
    exact_mod_cast H.card_neighborRecords a
  refine ⟨H.neighborRecords a, Coded, T,
    (abs_ntime_le (a := a) (e := a) rfl).trans (by norm_num),
    hcard.trans (record_count_le_coverScale J k m hC H.hN H.hε.le), ?_, ?_, hTm, ?_, ?_⟩
  · intro e he hA c
    exact (H.neighbor_controls_bound hεq hroot ha he hA c).trans
      (controls_le_coverScale J k m hC H.hN H.hε.le)
  · intro e he hA
    exact H.neighbor_controls_separated hεq hroot hK0
      (four_rpow_le_coverScale J k m hC H.hN H.hε.le) ha he hA
  · exact hvol.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (target_loss_le_coverScale J k m hC H.hN H.hε.le hcard)
        (H.Npow_pos _).le))
  · intro E W c hE0 hE hW
    have hP := isPath_of_shared_indices f₁ f₂ h hE hW
    obtain ⟨hEA, hWA⟩ := H.path_neighbor_records hP
    rw [hE0] at hEA hWA
    refine ⟨hEA, hWA, ?_⟩
    intro x hx hx'
    simpa only [Bool.not_not] using hends E W (fun p => !(c p)) hE0 hP x hx hx'

end Det

end Submission.Obl.k4_matching_switching_target_certificate
