-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_concentrated_family_improvement.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_concentrated_family_improvement

abbrev Space := LeanEval.Analysis.WangZahlKakeya.Space

abbrev B : Set LeanEval.Analysis.WangZahlKakeya.Space :=
  Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1

abbrev μ : MeasureTheory.Measure LeanEval.Analysis.WangZahlKakeya.Space :=
  MeasureTheory.volume

abbrev o : ℝ → ENNReal :=
  ENNReal.ofReal

abbrev T : ℝ → LeanEval.Analysis.WangZahlKakeya.Space → LeanEval.Analysis.WangZahlKakeya.Space → Set LeanEval.Analysis.WangZahlKakeya.Space :=
  fun δ x v => Metric.thickening δ (segment ℝ x (x + v))

abbrev H : ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) → Prop → Prop :=
  fun η δ n x v Y P => 0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, T δ (x i) (v i) ⊆ B) → (∀ i j, i ≠ j → μ (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1/2 : ENNReal) * μ (T δ (x i) (v i))) → (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ T δ (x i) (v i)) → o (δ ^ η * n * δ ^ 2) ≤ Finset.sum Finset.univ (fun i => μ (Y i)) → P

abbrev J : (ℝ → ℝ → ℝ → ℝ → Prop) → Prop :=
  fun P => ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1/100 → P ε a η δ

abbrev K : ℝ → ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → Prop → Prop :=
  fun δ m l n x v P => (∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → o ((Set.ncard {i | T δ (x i) (v i) ⊆ W} : ℝ) * δ ^ 2) ≤ o m * μ W) → (∀ (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖ = 1 → 0 < r → o (Set.ncard {i | T δ (x i) (v i) ⊆ (B ∩ {p | |inner ℝ u p - t| ≤ r})} : ℝ) ≤ o (l * n) * μ (B ∩ {p | |inner ℝ u p - t| ≤ r})) → P

abbrev Q : ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → Prop :=
  fun η δ m l f => ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), H η δ n x v Y (K δ m l n x v (o (f n) ≤ μ (⋃ i, Y i)))

abbrev D : ℝ → ℝ → Prop :=
  fun s w => J (fun ε a η δ => Q η δ (δ ^ (-η)) (δ ^ (-η)) (fun N => a * δ ^ (w + ε) * (N * δ ^ 2) * (N * δ) ^ (-s)))

abbrev E : ℝ → ℝ → Prop :=
  fun s w => J (fun ε a η δ => ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → Q η δ m l (fun N => a * δ ^ (w + ε) * m⁻¹ * (N * δ ^ 2) * (m ^ (-(3/2 : ℝ)) * l * (N * δ)) ^ (-s)))

abbrev N : ℝ → ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → Prop :=
  fun θ ζ δ n x v => ∀ (k : ℕ) (g : Fin k → Fin n), Function.Injective g → δ ^ θ * n ≤ k → ¬ ∀ U : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ U → o (Set.ncard {i | T δ (x (g i)) (v (g i)) ⊆ U} : ℝ) ≤ o (δ ^ (-ζ) * k) * μ U

abbrev F : ℝ → ℝ → ℝ → ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → Prop :=
  fun ν δ a b m n x v => ∃ (k : ℕ) (g : Fin k → Fin n), Function.Injective g ∧ 0 < k ∧ δ ^ ν * n ≤ k ∧ ∃ c : ℝ, 1 ≤ c ∧ c ≤ m ∧ (∀ U : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ U → o ((Set.ncard {i | T δ (x (g i)) (v (g i)) ⊆ U} : ℝ) * δ ^ 2) ≤ o c * μ U) ∧ ∃ (q : ℕ), 0 < q ∧ ∃ W : Fin q → Set LeanEval.Analysis.WangZahlKakeya.Space, (∀ j, ∃ e : AffineIsometryEquiv ℝ LeanEval.Analysis.WangZahlKakeya.Space LeanEval.Analysis.WangZahlKakeya.Space, W j = e '' {p : LeanEval.Analysis.WangZahlKakeya.Space | |p 0| ≤ a ∧ |p 1| ≤ b ∧ |p 2| ≤ 2}) ∧ (∀ i, ∃ j, T δ (x (g i)) (v (g i)) ⊆ W j) ∧ (∀ i, (Set.ncard {j | T δ (x (g i)) (v (g i)) ⊆ W j} : ℝ) ≤ δ ^ (-ν)) ∧ (∀ j j', (Set.ncard {i | T δ (x (g i)) (v (g i)) ⊆ W j} : ℝ) ≤ δ ^ (-ν) * (Set.ncard {i | T δ (x (g i)) (v (g i)) ⊆ W j'} : ℝ)) ∧ (∀ j, δ ^ ν * c * a * b ≤ (Set.ncard {i | T δ (x (g i)) (v (g i)) ⊆ W j} : ℝ) * δ ^ 2) ∧ (∀ U : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ U → o ((Set.ncard {j | W j ⊆ U} : ℝ) * a * b) ≤ o (δ ^ (-ν)) * μ U) ∧ (∀ j, ∀ U : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ U → o ((Set.ncard {i | T δ (x (g i)) (v (g i)) ⊆ W j ∧ T δ (x (g i)) (v (g i)) ⊆ U} : ℝ) * a * b) ≤ o (δ ^ (-ν) * (Set.ncard {i | T δ (x (g i)) (v (g i)) ⊆ W j} : ℝ)) * μ U)

abbrev R : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℕ → ENNReal :=
  fun σ w ε A δ m n => o (A * δ ^ (w + ε) * m⁻¹ * (n * δ ^ 2) * (m ^ (-(3/2 : ℝ)) * (n * δ)) ^ (-σ))

end WangZahlLot.Obl.wz_concentrated_family_improvement
