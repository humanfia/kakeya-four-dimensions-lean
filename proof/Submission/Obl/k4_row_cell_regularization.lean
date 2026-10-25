import Mathlib
import ChallengeDeps
import Submission.Obl.k4_row_cell_regularization.Regularize
set_option linter.unusedVariables false

open MeasureTheory Set Submission.Obl.k4_row_cell_regularization

/-!
# `Submission.k4_row_cell_regularization`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_row_cell_regularization`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_row_cell_regularization/`
belong to this obligation.
-/

theorem Submission.k4_row_cell_regularization : ∀ S a ε : ℝ, 0 < S → 0 < a → 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α) (μ : MeasureTheory.Measure (α × ℝ)) (b v H : α → ℝ) (T : α × ℝ → Fin 2 → ℝ) (π : MeasureTheory.Measure ℝ) (E : ℝ) (F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)), (fun h : ℝ => (fun z : α × ℝ → Fin 2 → ℝ => (fun q : α × ℝ → Fin 2 → ℤ => (Measurable b) → (Measurable v) → (Measurable H) → (Measurable T) → (MeasureTheory.IsProbabilityMeasure ν) → (MeasureTheory.IsProbabilityMeasure π) → (h ≤ E) → (E ≤ 1) → (∀ l, |b l| + |v l| ≤ N ^ η) → (μ ≤ ENNReal.ofReal (N ^ η) • (ν.prod MeasureTheory.volume)) → (μ (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0) → (ENNReal.ofReal (N ^ (-η)) ≤ μ Set.univ) → (∀ x r : ℝ, h ≤ r → r ≤ 1 → π (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal (N ^ η * r ^ S)) → (∀ (q₀ : Fin 2 → ℤ) (j : ℤ), μ {p | q p = q₀ ∧ ⌊v p.1 / h⌋ = j} ≤ ENNReal.ofReal (N ^ η * h ^ 2) * π (Set.Ico ((j : ℝ) * h) (((j : ℝ) + 1) * h))) → (∀ q₀, ((F q₀).card : ℝ) ≤ N ^ η) → (∀ᵐ p ∂μ, (∀ j, |T p j| ≤ N ^ η) ∧ (fun j => ⌊T p j / E⌋) ∈ F (q p) ∧ |T p 0 + v p.1 * T p 1 - H p.1| ≤ N ^ η * E) → ∃ (K R : ℝ) (P : Finset (Fin 4 → ℤ)) (D : Finset ℤ) (u : ℤ → ℝ) (c : (Fin 4 → ℤ) → ℤ → ℝ) (C : (Fin 4 → ℤ) → Set (α × ℝ)), (1 ≤ K) ∧ (2 ≤ R) ∧ (K ≤ R) ∧ (R ≤ N ^ ε) ∧ (μ ≤ ENNReal.ofReal K • (ν.prod MeasureTheory.volume)) ∧ (∀ (p : Fin 4 → ℤ) (d : ℤ), 0 ≤ c p d) ∧ ((P.card : ℝ) ≤ K / h ^ 2) ∧ (∀ p ∈ P, ∀ d ∈ D, c p d ≤ K * h ^ 2 / (D.card : ℝ)) ∧ (1 / K ≤ ∑ p ∈ P, ∑ d ∈ D, c p d) ∧ (∀ d ∈ D, |u d| ≤ K) ∧ (∀ p ∈ P, ∀ j : Fin 4, |h * (p j : ℝ)| ≤ K) ∧ (∀ q : ℤ × ℤ, ((P.filter (fun p => (p 0, p 1) = q)).card : ℝ) ≤ K) ∧ (∀ d ∈ D, (((P.filter (fun p => 0 < c p d)).image (fun p : Fin 4 → ℤ => (⌊(p 1 : ℝ) - u d * (p 0 : ℝ)⌋, ⌊(p 2 : ℝ) + u d * (p 3 : ℝ)⌋))).card : ℝ) ≤ K / h) ∧ (∀ x r : ℝ, h ≤ r → r ≤ 1 → ((D.filter (fun d => u d ∈ Set.Icc x (x + r))).card : ℝ) ≤ K * r ^ (S / 4) * (D.card : ℝ)) ∧ (∀ d₀ ∈ D, ((D.filter (fun d => |u d - u d₀| < 1 / R)).card : ℝ) ≤ (D.card : ℝ) / (16 * K ^ 3)) ∧ (∀ p : Fin 4 → ℤ, MeasurableSet (C p)) ∧ (Pairwise (fun p q : Fin 4 → ℤ => Disjoint (C p) (C q))) ∧ (∀ p ∈ P, ENNReal.ofReal (∑ d ∈ D, c p d) ≤ μ (C p)) ∧ (∀ p ∈ P, ∀ x ∈ C p, |z x 0| ≤ 1 ∧ |z x 1| ≤ K ∧ ∀ j : Fin 2, |T x j| ≤ K) ∧ (∀ p ∈ P, ∀ x ∈ C p, ∀ j : Fin 2, |z x j - h * ((![p 0, p 1] : Fin 2 → ℤ) j : ℝ)| ≤ h) ∧ (∀ p ∈ P, ∀ x ∈ C p, ∀ j : Fin 2, |(h / E) * T x j - h * ((![p 2, p 3] : Fin 2 → ℤ) j : ℝ)| ≤ h)) (fun p j => ⌊z p j / h⌋)) (fun p => ![p.2, b p.1 + p.2 * v p.1])) (N ^ (-a)) := by
  intro S a ε hS ha hε
  obtain ⟨N₀, hN₀, hbudget⟩ := budget S a ε hS ha hε
  refine ⟨eta S a ε, eta_pos hS ha hε, N₀, hN₀, ?_⟩
  intro N hN α inst ν μ b v H T π E F
  dsimp only
  intro hb hv hH hT hν hπ hhE hE1 htraj hdom hsupport hmass hcap hjoint hF hrow
  let h := N ^ (-a)
  let L := N ^ eta S a ε
  let J := levels S a ε
  let K := lossK J L
  let R := N ^ rho a ε
  obtain ⟨hL128, hhpos, hh1, hR2, hKR, hReps, hRh, hlow, hsep⟩ := hbudget N hN
  have hNpos : 0 < N := by linarith
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hmass' : ENNReal.ofReal (1 / L) ≤ μ univ := by
    simpa only [L, Real.rpow_neg hNpos.le, one_div] using hmass
  let hyp : IncHyp ν μ b v H T π E F h L S := {
    meas_b := hb
    meas_v := hv
    meas_H := hH
    meas_T := hT
    prob_ν := hν
    prob_π := hπ
    h_pos := hhpos
    h_lt_one := hh1
    one_le_L := hL1
    h_le_E := hhE
    E_le_one := hE1
    traj_bound := htraj
    domination := hdom
    time_support := hsupport
    mass_lower := hmass'
    palette_cap := hcap
    joint_cap := hjoint
    bins_card := hF
    row := hrow }
  obtain ⟨P, D, u, c, C, hfields⟩ := hyp.regularize J R (levels_pos S a ε)
    hL128 hS hR2 hRh hlow hsep
  exact ⟨K, R, P, D, u, c, C, one_le_lossK (levels_pos S a ε) hL1,
    hR2, hKR, hReps, hfields⟩
