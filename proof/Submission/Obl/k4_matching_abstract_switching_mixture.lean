import Mathlib
import ChallengeDeps
import Submission.Obl.k4_matching_abstract_switching_mixture.Wrapper
import Submission.Obl.k4_matching_abstract_switching_mixture.Assembly
set_option linter.unusedVariables false

/-!
# `Submission.k4_matching_abstract_switching_mixture`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_matching_abstract_switching_mixture`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_matching_abstract_switching_mixture/`
belong to this obligation.
-/

open Submission.Obl.k4_matching_abstract_switching_mixture
open MeasureTheory

theorem Submission.k4_matching_abstract_switching_mixture : ∀ m : ℕ, 1 ≤ m → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ → ∃ η : ℝ, 0 < η ∧ ∃ R : ℝ, 2 ≤ R ∧ ∀ N : ℝ, R ≤ N → ∀ B K δ V : ℝ, 1 ≤ B → B ≤ N ^ η → 2 ≤ K → K ≤ N ^ η → 0 < δ → 0 ≤ V → ∀ n₁ n₂ : ℕ, ∀ (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ)) (H : ℕ) (F₀ F₁ : ((Fin n₁ × Fin n₂) × ℝ) → ℕ) (Z : ((Fin n₁ × Fin n₂) × ℝ) → ℤ × ℤ) (S : Set ((Fin n₁ × Fin n₂) × ℝ)), (∀ i : Fin n₁, 0 ≤ π₁ i) → (∀ i : Fin n₂, 0 ≤ π₂ i) → (∑ i : Fin n₁, π₁ i) = 1 → (∑ i : Fin n₂, π₂ i) = 1 → MeasureTheory.IsProbabilityMeasure μ → (∀ (i : Fin n₁) (E : Set ℝ), MeasurableSet E → μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (B * π₁ i) * MeasureTheory.volume E) → (∀ (i : Fin n₂) (E : Set ℝ), MeasurableSet E → μ {p | p.1.2 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (B * π₂ i) * MeasureTheory.volume E) → MeasurableSet S → μ Sᶜ = 0 → (∀ e ∈ S, e.2 ∈ Set.Ico (0 : ℝ) 1) → (∀ x ∈ S, ∀ y ∈ S, F₁ x = F₁ y → F₀ x = F₀ y) → (∀ x ∈ S, ∀ y ∈ S, F₀ x = F₀ y → Int.floor (x.2 * (2 : ℝ) ^ H) = Int.floor (y.2 * (2 : ℝ) ^ H)) → (∃ H' : ℕ, H ≤ H' ∧ ∀ x ∈ S, ∀ y ∈ S, x.1 = y.1 → Int.floor (x.2 * (2 : ℝ) ^ H') = Int.floor (y.2 * (2 : ℝ) ^ H') → F₀ x = F₀ y ∧ F₁ x = F₁ y ∧ Z x = Z y) → ((fun P : (((Fin n₁ × Fin n₂) × ℝ) → ℕ) → ((Fin n₁ × Fin n₂) × ℝ) → ℝ => μ {x | x ∈ S ∧ N ^ θ * P F₀ x < P F₁ x} ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ (m + 10))) (fun (F : ((Fin n₁ × Fin n₂) × ℝ) → ℕ) (x : ((Fin n₁ × Fin n₂) × ℝ)) => (μ {y | y ∈ S ∧ F y = F x ∧ Z y = Z x}).toReal / (μ {y | y ∈ S ∧ F y = F x}).toReal)) → (fun σ : ((Fin n₁ × Fin n₂) × ℝ) → ((Fin n₁ × Fin n₂) × ℝ) → ℝ => (fun Φ : (Fin (m + 1) → ℝ) → ℝ → (ℝ × (Fin m → ℝ)) → (ℝ × (Fin m → ℝ)) => (∀ a ∈ S, ∃ (A : Finset ℕ) (C : ℕ → (ℤ × ℤ) → Bool → ℝ) (T : Set (ℝ × (Fin m → ℝ))), |σ a a| ≤ 1 ∧ (A.card : ℝ) ≤ K ∧ (∀ e ∈ S, F₀ e ∈ A → ∀ c : Bool, |C (F₀ e) (Z e) c| ≤ K) ∧ (∀ e ∈ S, F₀ e ∈ A → 2 / K ≤ |C (F₀ e) (Z e) true - C (F₀ e) (Z e) false|) ∧ MeasurableSet T ∧ MeasureTheory.volume T ≤ ENNReal.ofReal (K * V) ∧ ∀ (E W : ℕ → ((Fin n₁ × Fin n₂) × ℝ)) (c : ℕ → Bool), E 0 = a → (∀ p : ℕ, p ≤ m + 1 → E p ∈ S) → (∀ p : ℕ, p ≤ m → W p ∈ S ∧ F₁ (W p) = F₁ (E p) ∧ (if c p then (W p).1.1 = (E (p + 1)).1.1 else (W p).1.2 = (E (p + 1)).1.2) ∧ Int.floor ((W p).2 * (2 : ℝ) ^ H) = Int.floor ((E (p + 1)).2 * (2 : ℝ) ^ H)) → (∀ p : ℕ, p ≤ m + 1 → F₀ (E p) ∈ A) ∧ (∀ p : ℕ, p ≤ m → F₀ (W p) ∈ A) ∧ ∀ x : ℝ × (Fin m → ℝ), |x.1 - σ a (E (m + 1))| ≤ δ → (∀ p : Fin m, |x.2 p - σ a (E ((p : ℕ) + 1))| ≤ δ) → Φ (fun p : Fin (m + 1) => C (F₀ (W p)) (Z (W p)) (c p)) (σ a a) x ∈ T) → ∃ (L : ℝ) (n : ℕ) (w : Fin n → ℝ) (U : Fin n → Fin (m + 1) → ℝ) (s₀ : ℝ) (T : Set (ℝ × (Fin m → ℝ))), 2 ≤ L ∧ L ≤ N ^ κ ∧ (∀ i : Fin n, 0 ≤ w i) ∧ (∑ i : Fin n, w i) ≤ 1 ∧ (∀ (i : Fin n) (p : Fin (m + 1)), |U i p| ≤ L) ∧ |s₀| ≤ 1 ∧ (∀ (i : Fin n) (p : Fin m), L⁻¹ ≤ |U i p.succ - U i p.castSucc|) ∧ MeasurableSet T ∧ MeasureTheory.volume T ≤ ENNReal.ofReal (L * V) ∧ 1 / 4 ≤ L * N ^ (((m : ℝ) + 1) * θ) * (∑ i : Fin n, w i * (MeasureTheory.volume {x : ℝ × (Fin m → ℝ) | |x.1| ≤ 1 ∧ (∀ p : Fin m, |x.2 p| ≤ 1) ∧ (∀ p r : Fin m, p ≠ r → L⁻¹ ≤ |x.2 p - x.2 r|) ∧ Φ (U i) s₀ x ∈ T}).toReal)) ((fun (U : Fin (m + 1) → ℝ) (s₀ : ℝ) (x : ℝ × (Fin m → ℝ)) => (x.1, fun j : Fin m => (U 0 * (x.1 - s₀) ^ ((j : ℕ) + 1) + ∑ p : Fin m, (U p.succ - U p.castSucc) * (x.1 - x.2 p) ^ ((j : ℕ) + 1)) / (((j : ℕ) + 1).factorial : ℝ))))) ((fun (a e : ((Fin n₁ × Fin n₂) × ℝ)) => (e.2 - (((Int.floor (a.2 * (2 : ℝ) ^ H) : ℝ) + 1 / 2) / (2 : ℝ) ^ H)) * (2 : ℝ) ^ H)) := by
  classical
  intro m hm κ hκ θ hθ
  obtain ⟨η, hη, R, hR, hscale⟩ := sizeBound_subpower m κ hκ
  refine ⟨η, hη, R, hR, ?_⟩
  intro N hN B K δ V hB hBN hK hKN hδ hV n₁ n₂ π₁ π₂ μ H F₀ F₁ Z S
    hπ₁ hπ₂ hs₁ hs₂ hμ hm₁ hm₂ hSm hSc hSt hF₁₀ hF₀H hmesh hbad hcover
  obtain ⟨H', hHH', hconst⟩ := hmesh
  let D : Data n₁ n₂ := {
    π₁ := π₁, π₂ := π₂, μ := μ, H := H, F₀ := F₀, F₁ := F₁, Z := Z, S := S,
    B := B, H' := H', hB := by linarith,
    hπ₁ := hπ₁, hπ₂ := hπ₂, hs₁ := hs₁, hs₂ := hs₂, hμ := hμ,
    hm₁ := hm₁, hm₂ := hm₂, hSm := hSm, hSc := hSc, hSt := hSt,
    hF₁₀ := hF₁₀, hF₀H := hF₀H, hHH' := hHH', hconst := hconst }
  have hN0 : 0 < N := by linarith
  have hbadD : D.μ {x | x ∈ D.S ∧ N ^ θ * D.post D.F₀ x < D.post D.F₁ x} ≤
      ENNReal.ofReal (smallError m) := hbad
  have hcoverD : ∀ a ∈ D.S, Nonempty (EventCover D m K δ V a) := by
    intro a ha
    obtain ⟨A, C, T, hstart, hcard, hctrl, hgap, hTm, hTv, hpaths⟩ := hcover a ha
    exact ⟨{
      A := A, C := C, T := T, start_bound := hstart, card_bound := hcard,
      control_bound := hctrl, control_gap := hgap, measurable := hTm,
      volume_bound := hTv, paths := hpaths }⟩
  obtain ⟨U, s₀, T, hU, hs₀, hgap, hTm, hTv, hlarge⟩ :=
    D.exists_endpoint m hN0 hB hK hδ hbadD hcoverD
  obtain ⟨hL2, hKL, -, -⟩ := sizeBound_bounds m hB hK
  have hL0 : 0 < sizeBound m B K := by linarith
  have hK0 : 0 < K := by linarith
  refine ⟨sizeBound m B K, 1, (fun _ => 1), (fun _ => U), s₀, T,
    hL2, hscale N B K hN hB hBN hK hKN, (fun _ => zero_le_one), ?_,
    (fun _ p => (hU p).trans hKL), hs₀, ?_, hTm, ?_, ?_⟩
  · simp
  · intro _ p
    exact (inv_anti₀ hK0 hKL).trans (hgap p)
  · exact hTv.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hKL hV))
  · have hfinal := upgrade_pullback_bound hN0 hB hK U s₀ T hlarge
    simpa [pullback, timeDomain, endpoint, and_assoc] using hfinal
