import Submission.Obl.k4_matching_abstract_switching_mixture.Instance
import Submission.Obl.k4_matching_abstract_switching_mixture.Certificate

namespace Submission.Obl.k4_matching_abstract_switching_mixture

open MeasureTheory
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

/-- The cover hypothesis at one original event, before passing to representatives. -/
structure EventCover {n₁ n₂ : ℕ} (D : Data n₁ n₂) (m : ℕ) (K δ V : ℝ)
    (a : Ev n₁ n₂) where
  A : Finset ℕ
  C : ℕ → (ℤ × ℤ) → Bool → ℝ
  T : Set (ℝ × (Fin m → ℝ))
  start_bound : |Data.sigma D.H a a| ≤ 1
  card_bound : (A.card : ℝ) ≤ K
  control_bound : ∀ e ∈ D.S, D.F₀ e ∈ A → ∀ c, |C (D.F₀ e) (D.Z e) c| ≤ K
  control_gap : ∀ e ∈ D.S, D.F₀ e ∈ A →
    2 / K ≤ |C (D.F₀ e) (D.Z e) true - C (D.F₀ e) (D.Z e) false|
  measurable : MeasurableSet T
  volume_bound : volume T ≤ ENNReal.ofReal (K * V)
  paths : ∀ (E W : ℕ → Ev n₁ n₂) (c : ℕ → Bool), E 0 = a →
    (∀ p, p ≤ m + 1 → E p ∈ D.S) →
    (∀ p, p ≤ m → W p ∈ D.S ∧ D.F₁ (W p) = D.F₁ (E p) ∧
      (if c p then (W p).1.1 = (E (p + 1)).1.1 else (W p).1.2 = (E (p + 1)).1.2) ∧
      Int.floor ((W p).2 * (2 : ℝ) ^ D.H) = Int.floor ((E (p + 1)).2 * (2 : ℝ) ^ D.H)) →
    (∀ p, p ≤ m + 1 → D.F₀ (E p) ∈ A) ∧
    (∀ p, p ≤ m → D.F₀ (W p) ∈ A) ∧
    ∀ x : ℝ × (Fin m → ℝ), |x.1 - Data.sigma D.H a (E (m + 1))| ≤ δ →
      (∀ p : Fin m, |x.2 p - Data.sigma D.H a (E ((p : ℕ) + 1))| ≤ δ) →
      endpoint (fun p : Fin (m + 1) => C (D.F₀ (W p)) (D.Z (W p)) (c p))
        (Data.sigma D.H a a) x ∈ T

/-- Representatives transfer an original cover to a finite switching model. -/
noncomputable def EventCover.lift {n₁ n₂ : ℕ} {D : Data n₁ n₂}
    {Ω Ar Iv Tc : Type*} [Fintype Ω] [DecidableEq Ar] [DecidableEq Iv]
    [Fintype Tc] [DecidableEq Tc]
    {m : ℕ} {K δ V : ℝ} (r : Ω → Ev n₁ n₂) (hr : ∀ e, r e ∈ D.S)
    (X : SwitchData Ω ℕ ℕ Ar Iv (ℤ × ℤ) Tc)
    (hcoarse : ∀ e, X.coarse e = D.F₀ (r e))
    (hlegal : ∀ e er c e', legalStep X e (er, c, e') →
      D.F₁ (r er) = D.F₁ (r e) ∧
      (if c then (r er).1.1 = (r e').1.1 else (r er).1.2 = (r e').1.2) ∧
      Int.floor ((r er).2 * (2 : ℝ) ^ D.H) = Int.floor ((r e').2 * (2 : ℝ) ^ D.H))
    (a : Ω) (C : EventCover D m K δ V (r a))
    (hctrl : ∀ e c, X.ctrl e c = C.C (D.F₀ (r e)) (D.Z (r e)) c) :
    PathCover X (fun e => Data.sigma D.H (r a) (r e)) m K δ V a where
  A := C.A
  T := C.T
  start_bound := C.start_bound
  card_bound := C.card_bound
  control_bound := by
    intro e he c
    rw [hctrl]
    apply C.control_bound _ (hr e)
    rwa [← hcoarse]
  control_gap := by
    intro e he
    rw [hctrl, hctrl]
    apply C.control_gap _ (hr e)
    rwa [← hcoarse]
  measurable := C.measurable
  volume_bound := C.volume_bound
  paths := by
    intro E W c hE hpath
    obtain ⟨hEA, hWA, hx⟩ := C.paths (fun p => r (E p)) (fun p => r (W p)) c
      (congrArg r hE) (fun p _ => hr (E p))
      (fun p hp => ⟨hr (W p), hlegal _ _ _ _ (hpath p hp)⟩)
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      rw [hcoarse]
      exact hEA p hp
    · intro p hp
      rw [hcoarse]
      exact hWA p hp
    · intro x hfinal hinternal
      simpa only [hctrl] using hx x hfinal hinternal

end Submission.Obl.k4_matching_abstract_switching_mixture
