-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.Repair.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_tube_packing_bound
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.Reduction

/-!
# A repaired interface for o038 (checked glue)

o038 as frozen cannot be proved from `D`, `E` and o037 alone: staggered line-sticky families
satisfy all its hypotheses (no exact-`S` subfamily), and only Theorem 6.2 (premise `A`, o015's
statement) bounds their union. This file states a repaired set of children and proves, in Lean,
that they give o038:

* `StatementA` -- o015's frozen statement verbatim (premise `A`; to be reused, not re-proved);
* `TrichotomyDerived` -- Prop. 6.3 for a Frostman family, with NO non-sticky hypothesis: for
  every count loss `κ` there is a Frostman threshold `ζ` such that a DERIVED family
  (`⋃ Z ⊆ ⋃ Y`, `k ≥ δ^κ n`, admissible, individually dense with exponent `θ + η` for every
  `θ`) has frozen `S`, `SB` (as in o071) or `SC'` (`SC` of o072 plus prism Katz–Tao). Its
  proof is expected to move tubes to canonical chord positions (left/right ends) first
  (`Canonical.lean`), which makes line-sticky families axially aligned so that frozen `S` can
  hold;
* `SeparatedGain` -- o071 `wz_separated_scales_gain` (accepted) verbatim;
* `FlatGainKT` -- o072 with the prism Katz–Tao clause in `(C)`; x0264's
  `flat_prism_frostman_gain_of_prismKT` (o072, branch x0264, FlatKT.lean) proves it from `E`.

`o038_of_repair : StatementA → TrichotomyDerived → SeparatedGain → FlatGainKT → O038`.
In the sticky branch `A` at `ε_A = ω'/2` and the packing bound o037 beat the target, as in
case 1 of o017's glue; the branches (B), (C) are as in x0106's `Assembly.lean`, except that the
count loss `δ^(κσ/2)`, `κ = min(α_B, α_C)/σ`, is paid by half of the gain:
`α = min(α_B, α_C, ω')/2`.
-/

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy

/-- o015's frozen statement (premise `A`, Wang–Zahl Theorem 6.2). -/
def StatementA : Prop := ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), 0 < n → (∀ i : Fin n, ‖v i‖ = 1) → (∀ i : Fin n, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ i j : Fin n, i ≠ j → MeasureTheory.volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)) ∩ Metric.thickening δ (segment ℝ (x j) (x j + v j))) ≤ (1 / 2 : ENNReal) * MeasureTheory.volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)))) → (∀ i : Fin n, MeasurableSet (Y i)) → (∀ i : Fin n, Y i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i))) → ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i : Fin n => MeasureTheory.volume (Y i)) → (∀ ρ₀ : ℝ, δ ≤ ρ₀ → ρ₀ ≤ 1 → ∃ ρ : ℝ, ρ₀ ≤ ρ ∧ ρ ≤ 1 ∧ ρ ≤ (δ ^ (-η)) * ρ₀ ∧ ∃ k : ℕ, 0 < k ∧ ∃ (z w : Fin k → LeanEval.Analysis.WangZahlKakeya.Space), (∀ j : Fin k, ‖w j‖ = 1) ∧ (∀ j j' : Fin k, j ≠ j' → MeasureTheory.volume (Metric.thickening ρ (segment ℝ (z j) (z j + w j)) ∩ Metric.thickening ρ (segment ℝ (z j') (z j' + w j'))) ≤ (1 / 2 : ENNReal) * MeasureTheory.volume (Metric.thickening ρ (segment ℝ (z j) (z j + w j)))) ∧ (∀ i : Fin n, ∃! j : Fin k, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.thickening ρ (segment ℝ (z j) (z j + w j))) ∧ (∀ j : Fin k, ∃ i : Fin n, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.thickening ρ (segment ℝ (z j) (z j + w j))) ∧ (∀ j j' : Fin k, (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.thickening ρ (segment ℝ (z j) (z j + w j))} : ℕ) : ℝ)) ≤ (δ ^ (-η)) * (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.thickening ρ (segment ℝ (z j') (z j' + w j'))} : ℕ) : ℝ))) ∧ (∀ j : Fin k, ∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal ((((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.thickening ρ (segment ℝ (z j) (z j + w j)) ∧ Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W} : ℕ) : ℝ)) * ρ ^ 2) ≤ ENNReal.ofReal ((δ ^ (-η)) * (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.thickening ρ (segment ℝ (z j) (z j + w j))} : ℕ) : ℝ))) * MeasureTheory.volume W)) → ENNReal.ofReal (a * δ ^ ε) ≤ MeasureTheory.volume (⋃ i : Fin n, Y i)

/-- The repaired trichotomy: a derived family with frozen `S`, `SB` or `SC'`
(3723 characters, within the 4000-character limit for child statements). -/
def TrichotomyDerived : Prop := (fun (μ:MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))=>(fun (o:ℝ→ENNReal)=>(fun (T:ℝ→EuclideanSpace ℝ (Fin 3)→EuclideanSpace ℝ (Fin 3)→Set (EuclideanSpace ℝ (Fin 3)))=>(fun (G:ℝ→ℝ→(n:ℕ)→(Fin n→EuclideanSpace ℝ (Fin 3))→(Fin n→EuclideanSpace ℝ (Fin 3))→(Fin n→Set (EuclideanSpace ℝ (Fin 3)))→Prop)=>(fun (S:ℝ→ℝ→(k:ℕ)→(Fin k→Set (EuclideanSpace ℝ (Fin 3)))→Prop)=>(fun (SB:ℝ→ℝ→ℝ→(k:ℕ)→(Fin k→Set (EuclideanSpace ℝ (Fin 3)))→Prop)=>(fun (SC:ℝ→ℝ→ℝ→(k:ℕ)→(Fin k→Set (EuclideanSpace ℝ (Fin 3)))→Prop)=>∀ ξ:ℝ,0<ξ→∃ ζ₁:ℝ,0<ζ₁∧∀ ζ₂ ζ₃:ℝ,0<ζ₃→ζ₃≤ζ₂→ζ₂≤ζ₁→∀ κ:ℝ,0<κ→∃ ζ:ℝ,0<ζ∧∀ θ:ℝ,0<θ→∃ δ₀:ℝ,0<δ₀∧∀ δ:ℝ,0<δ→δ≤δ₀→∀ η:ℝ,0<η→∀ (n:ℕ) (x v:Fin n→EuclideanSpace ℝ (Fin 3)) (Y:Fin n→Set (EuclideanSpace ℝ (Fin 3))),G δ η n x v Y→(∀ W:Set (EuclideanSpace ℝ (Fin 3)),Convex ℝ W→ o (Set.ncard {i | T δ (x i) (v i)⊆W})≤o (δ^(-ζ)*n)*μ W)→∃ (k:ℕ) (y u:Fin k→EuclideanSpace ℝ (Fin 3)) (Z:Fin k→Set (EuclideanSpace ℝ (Fin 3))),G δ (θ+η) k y u Z∧δ^κ*n≤k∧(⋃ j,Z j)⊆(⋃ i,Y i)∧(S ξ δ k (fun j=>T δ (y j) (u j))∨SB ζ₁ ζ₂ δ k (fun j=>T δ (y j) (u j))∨SC ζ₂ ζ₃ δ k (fun j=>T δ (y j) (u j)))) (fun ζ₂ ζ₃ δ k A=>∃ a b:ℝ,δ≤a∧a≤δ^(ζ₂/200)*b∧b≤1∧∃ (p:ℕ) (c e₁ e₂ e₃:Fin p→EuclideanSpace ℝ (Fin 3)),(∀ j,Orthonormal ℝ ![e₁ j,e₂ j,e₃ j])∧(fun (P:Fin p→Set (EuclideanSpace ℝ (Fin 3)))=>(∀ i,∃ j,A i⊆P j)∧(∀ j j',(Set.ncard {i | A i⊆P j}:ℝ)≤δ^(-ζ₃)*Set.ncard {i | A i⊆P j'})∧(∀ U:Set (EuclideanSpace ℝ (Fin 3)),Convex ℝ U→ o (Set.ncard {j | P j⊆U})≤o (δ^(-ζ₃)*p)*μ U)∧(∀ j (U:Set (EuclideanSpace ℝ (Fin 3))),Convex ℝ U→ o (Set.ncard {i | A i⊆P j∧A i⊆U})*μ (P j)≤o (δ^(-ζ₃)*Set.ncard {i | A i⊆P j})*μ U)∧(∀ j (U:Set (EuclideanSpace ℝ (Fin 3))),Convex ℝ U→ o (Set.ncard {j' | P j'⊆Metric.thickening b (P j)∧P j'⊆U})*μ (P j)≤o (δ^(-ζ₃))*μ U)∧(∀ U:Set (EuclideanSpace ℝ (Fin 3)),Convex ℝ U→ o (Set.ncard {j | P j⊆U}*(a*b))≤o (δ^(-ζ₃))*μ U)) (fun j=>{y | |inner ℝ (e₁ j) (y-c j)|≤a∧|inner ℝ (e₂ j) (y-c j)|≤b∧|inner ℝ (e₃ j) (y-c j)|≤1}))) (fun ζ₁ ζ₂ δ k A=>∃ τ ρ:ℝ,δ≤τ∧τ<ρ∧ρ≤1∧τ≤δ^ζ₁*ρ∧∃ (p:ℕ) (y u:Fin p→EuclideanSpace ℝ (Fin 3)) (q:ℕ) (z w:Fin q→EuclideanSpace ℝ (Fin 3)),(∀ j,‖u j‖=1)∧(∀ l,‖w l‖=1)∧(fun (P:Fin p→Set (EuclideanSpace ℝ (Fin 3))) (R:Fin q→Set (EuclideanSpace ℝ (Fin 3)))=>(∀ j j',j≠j'→μ (P j∩P j')≤1/2*μ (P j))∧(∀ l l',l≠l'→μ (R l∩R l')≤1/2*μ (R l))∧(∀ i,∃! j,A i⊆P j)∧(∀ j,∃ i,A i⊆P j)∧(∀ j,∃! l,P j⊆R l)∧(∀ l,∃ j,P j⊆R l)∧(∀ j j',(Set.ncard {i | A i⊆P j}:ℝ)≤δ^(-ζ₂)*Set.ncard {i | A i⊆P j'})∧(∀ l l',(Set.ncard {j | P j⊆R l}:ℝ)≤δ^(-ζ₂)*Set.ncard {j | P j⊆R l'})∧(∀ j (W:Set (EuclideanSpace ℝ (Fin 3))),Convex ℝ W→ o (Set.ncard {i | A i⊆P j∧A i⊆W}*τ^2)≤o (δ^(-ζ₂)*Set.ncard {i | A i⊆P j})*μ W)∧(∀ l (W:Set (EuclideanSpace ℝ (Fin 3))),Convex ℝ W→ o (Set.ncard {j | P j⊆R l∧P j⊆W}*τ^2)≤o (δ^(-ζ₂))*μ W)∧(∀ l,δ^ζ₂*(ρ/τ)^2≤Set.ncard {j | P j⊆R l})∧(∀ W:Set (EuclideanSpace ℝ (Fin 3)),Convex ℝ W→ o (Set.ncard {l | R l⊆W})≤o (δ^(-ζ₂)*q)*μ W)) (fun j=>T τ (y j) (u j)) (fun l=>T ρ (z l) (w l)))) (fun ξ δ k A=>∀ ρ₀:ℝ,δ≤ρ₀→ρ₀≤1→∃ ρ:ℝ,ρ₀≤ρ∧ρ≤1∧ρ≤δ^(-ξ)*ρ₀∧∃ q:ℕ,0<q∧∃ z w:Fin q→EuclideanSpace ℝ (Fin 3),(∀ j,‖w j‖=1)∧(fun (R:Fin q→Set (EuclideanSpace ℝ (Fin 3)))=>(∀ j j',j≠j'→μ (R j∩R j')≤1/2*μ (R j))∧(∀ i,∃! j,A i⊆R j)∧(∀ j,∃ i,A i⊆R j)∧(∀ j j',(Set.ncard {i | A i⊆R j}:ℝ)≤δ^(-ξ)*Set.ncard {i | A i⊆R j'})∧(∀ j (W:Set (EuclideanSpace ℝ (Fin 3))),Convex ℝ W→ o (Set.ncard {i | A i⊆R j∧A i⊆W}*ρ^2)≤o (δ^(-ξ)*Set.ncard {i | A i⊆R j})*μ W)) (fun j=>T ρ (z j) (w j)))) (fun (δ η:ℝ) (n:ℕ) (x v:Fin n→EuclideanSpace ℝ (Fin 3)) (Y:Fin n→Set (EuclideanSpace ℝ (Fin 3)))=>0<n∧(∀ i,‖v i‖=1)∧(∀ i,T δ (x i) (v i)⊆Metric.ball 0 1)∧(∀ i j,i≠j→μ (T δ (x i) (v i)∩T δ (x j) (v j))≤1/2*μ (T δ (x i) (v i)))∧(∀ i,MeasurableSet (Y i))∧(∀ i,Y i⊆T δ (x i) (v i))∧(∀ i,o (δ^η*δ^2)≤μ (Y i)))) (fun δ x v=>Metric.thickening δ (segment ℝ x (x+v)))) ENNReal.ofReal) MeasureTheory.volume

/-- o071's statement (accepted; `WangZahlLot.wz_separated_scales_gain`), as a hypothesis here so
that this file does not depend on lib's build. -/
def SeparatedGain : Prop := ∀ σ ω ω' : ℝ, (fun (B : Set (EuclideanSpace ℝ (Fin 3))) => (fun (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) => (fun (o : ℝ → ENNReal) => (fun (T : ℝ → (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))) => (fun (H : ℝ → ℝ → (n : ℕ) → (Fin n → (EuclideanSpace ℝ (Fin 3))) → (Fin n → (EuclideanSpace ℝ (Fin 3))) → (Fin n → Set (EuclideanSpace ℝ (Fin 3))) → Prop → Prop) => (fun (J : (ℝ → ℝ → ℝ → ℝ → Prop) → Prop) => (fun (K : ℝ → ℝ → ℝ → (n : ℕ) → (Fin n → (EuclideanSpace ℝ (Fin 3))) → (Fin n → (EuclideanSpace ℝ (Fin 3))) → Prop → Prop) => (fun (Q : ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → Prop) => (fun (d : ℝ → ℝ → Prop) => (fun (e : ℝ → ℝ → Prop) => (fun (SB : ℝ → ℝ → ℝ → (k : ℕ) → (Fin k → Set (EuclideanSpace ℝ (Fin 3))) → Prop) => 0 < σ → σ ≤ 1/2 → 0 < ω → ω < ω' → d σ ω → e σ ω' → ∀ ζ₁ : ℝ, 0 < ζ₁ → ∃ α : ℝ, 0 < α ∧ ∃ ζ₀ : ℝ, 0 < ζ₀ ∧ ∀ ζ₂ : ℝ, 0 < ζ₂ → ζ₂ ≤ ζ₀ → ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ (n : ℕ) (x v : Fin n → (EuclideanSpace ℝ (Fin 3))) (Y : Fin n → Set (EuclideanSpace ℝ (Fin 3))), H η δ n x v Y ((∀ i, o (δ ^ η * δ ^ 2) ≤ μ (Y i)) → SB ζ₁ ζ₂ δ n (fun i => T δ (x i) (v i)) → o (a * δ ^ (ω' - α + ε) * (n * δ ^ 4) ^ (σ / 2)) ≤ μ (⋃ i, Y i))) (fun ζ₁ ζ₂ δ k A => ∃ τ ρ : ℝ, δ ≤ τ ∧ τ < ρ ∧ ρ ≤ 1 ∧ τ ≤ δ ^ ζ₁ * ρ ∧ ∃ (p : ℕ) (y u : Fin p → (EuclideanSpace ℝ (Fin 3))) (q : ℕ) (z w : Fin q → (EuclideanSpace ℝ (Fin 3))), (∀ j, ‖u j‖ = 1) ∧ (∀ l, ‖w l‖ = 1) ∧ (fun (P : Fin p → Set (EuclideanSpace ℝ (Fin 3))) (R : Fin q → Set (EuclideanSpace ℝ (Fin 3))) => (∀ j j', j ≠ j' → μ (P j ∩ P j') ≤ 1/2 * μ (P j)) ∧ (∀ l l', l ≠ l' → μ (R l ∩ R l') ≤ 1/2 * μ (R l)) ∧ (∀ i, ∃! j, A i ⊆ P j) ∧ (∀ j, ∃ i, A i ⊆ P j) ∧ (∀ j, ∃! l, P j ⊆ R l) ∧ (∀ l, ∃ j, P j ⊆ R l) ∧ (∀ j j', (Set.ncard {i | A i ⊆ P j} : ℝ) ≤ δ ^ (-ζ₂) * Set.ncard {i | A i ⊆ P j'}) ∧ (∀ l l', (Set.ncard {j | P j ⊆ R l} : ℝ) ≤ δ ^ (-ζ₂) * Set.ncard {j | P j ⊆ R l'}) ∧ (∀ j (W : Set (EuclideanSpace ℝ (Fin 3))), Convex ℝ W → o (Set.ncard {i | A i ⊆ P j ∧ A i ⊆ W} * τ ^ 2) ≤ o (δ ^ (-ζ₂) * Set.ncard {i | A i ⊆ P j}) * μ W) ∧ (∀ l (W : Set (EuclideanSpace ℝ (Fin 3))), Convex ℝ W → o (Set.ncard {j | P j ⊆ R l ∧ P j ⊆ W} * τ ^ 2) ≤ o (δ ^ (-ζ₂)) * μ W) ∧ (∀ l, δ ^ ζ₂ * (ρ / τ) ^ 2 ≤ Set.ncard {j | P j ⊆ R l}) ∧ (∀ W : Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ W → o (Set.ncard {l | R l ⊆ W}) ≤ o (δ ^ (-ζ₂) * q) * μ W)) (fun j => T τ (y j) (u j)) (fun l => T ρ (z l) (w l)))) (fun s w => J (fun ε a η δ => ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → Q η δ m l (fun N => a * δ ^ (w + ε) * m⁻¹ * (N * δ ^ 2) * (m ^ (-(3/2 : ℝ)) * l * (N * δ)) ^ (-s))))) (fun s w => J (fun ε a η δ => Q η δ (δ ^ (-η)) (δ ^ (-η)) (fun N => a * δ ^ (w + ε) * (N * δ ^ 2) * (N * δ) ^ (-s))))) (fun η δ m l f => ∀ (n : ℕ) (x v : Fin n → (EuclideanSpace ℝ (Fin 3))) (Y : Fin n → Set (EuclideanSpace ℝ (Fin 3))), H η δ n x v Y (K δ m l n x v (o (f n) ≤ μ (⋃ i, Y i))))) (fun δ m l n x v P => (∀ W : Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ W → o ((Set.ncard {i | T δ (x i) (v i) ⊆ W} : ℝ) * δ ^ 2) ≤ o m * μ W) → (∀ (u : (EuclideanSpace ℝ (Fin 3))) (t r : ℝ), ‖u‖ = 1 → 0 < r → o (Set.ncard {i | T δ (x i) (v i) ⊆ (B ∩ {p | |inner ℝ u p - t| ≤ r})} : ℝ) ≤ o (l * n) * μ (B ∩ {p | |inner ℝ u p - t| ≤ r})) → P)) (fun P => ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1/100 → P ε a η δ)) (fun η δ n x v Y P => 0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, T δ (x i) (v i) ⊆ B) → (∀ i j, i ≠ j → μ (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1/2 : ENNReal) * μ (T δ (x i) (v i))) → (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ T δ (x i) (v i)) → o (δ ^ η * n * δ ^ 2) ≤ ∑ i, μ (Y i) → P)) (fun δ x v => Metric.thickening δ (segment ℝ x (x + v)))) ENNReal.ofReal) MeasureTheory.volume) (Metric.ball 0 1)

/-- o072 with the prism Katz–Tao clause (x0264's `flat_prism_frostman_gain_of_prismKT`). -/
def FlatGainKT : Prop := ∀ σ ω' : ℝ, (fun (B : Set (EuclideanSpace ℝ (Fin 3))) => (fun (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) => (fun (o : ℝ → ENNReal) => (fun (T : ℝ → (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))) => (fun (H : ℝ → ℝ → (n : ℕ) → (Fin n → (EuclideanSpace ℝ (Fin 3))) → (Fin n → (EuclideanSpace ℝ (Fin 3))) → (Fin n → Set (EuclideanSpace ℝ (Fin 3))) → Prop → Prop) => (fun (J : (ℝ → ℝ → ℝ → ℝ → Prop) → Prop) => (fun (K : ℝ → ℝ → ℝ → (n : ℕ) → (Fin n → (EuclideanSpace ℝ (Fin 3))) → (Fin n → (EuclideanSpace ℝ (Fin 3))) → Prop → Prop) => (fun (Q : ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → Prop) => (fun (e : ℝ → ℝ → Prop) => (fun (SC : ℝ → ℝ → ℝ → (k : ℕ) → (Fin k → Set (EuclideanSpace ℝ (Fin 3))) → Prop) => 0 < σ → σ ≤ 1/2 → 0 < ω' → e σ ω' → ∀ ζ₂ : ℝ, 0 < ζ₂ → ∃ α : ℝ, 0 < α ∧ ∃ ζ₀ : ℝ, 0 < ζ₀ ∧ ∀ ζ₃ : ℝ, 0 < ζ₃ → ζ₃ ≤ ζ₀ → ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ (n : ℕ) (x v : Fin n → (EuclideanSpace ℝ (Fin 3))) (Y : Fin n → Set (EuclideanSpace ℝ (Fin 3))), H η δ n x v Y ((∀ i, o (δ ^ η * δ ^ 2) ≤ μ (Y i)) → SC ζ₂ ζ₃ δ n (fun i => T δ (x i) (v i)) → o (a * δ ^ (ω' - α + ε) * (n * δ ^ 4) ^ (σ / 2)) ≤ μ (⋃ i, Y i))) (fun ζ₂ ζ₃ δ k A => ∃ a b : ℝ, δ ≤ a ∧ a ≤ δ ^ (ζ₂ / 200) * b ∧ b ≤ 1 ∧ ∃ (p : ℕ) (c e₁ e₂ e₃ : Fin p → (EuclideanSpace ℝ (Fin 3))), (∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j]) ∧ (fun (P : Fin p → Set (EuclideanSpace ℝ (Fin 3))) => (∀ i, ∃ j, A i ⊆ P j) ∧ (∀ j j', (Set.ncard {i | A i ⊆ P j} : ℝ) ≤ δ ^ (-ζ₃) * Set.ncard {i | A i ⊆ P j'}) ∧ (∀ U : Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ U → o (Set.ncard {j | P j ⊆ U}) ≤ o (δ ^ (-ζ₃) * p) * μ U) ∧ (∀ j (U : Set (EuclideanSpace ℝ (Fin 3))), Convex ℝ U → o (Set.ncard {i | A i ⊆ P j ∧ A i ⊆ U}) * μ (P j) ≤ o (δ ^ (-ζ₃) * Set.ncard {i | A i ⊆ P j}) * μ U) ∧ (∀ j (U : Set (EuclideanSpace ℝ (Fin 3))), Convex ℝ U → o (Set.ncard {j' | P j' ⊆ Metric.thickening b (P j) ∧ P j' ⊆ U}) * μ (P j) ≤ o (δ ^ (-ζ₃)) * μ U) ∧ (∀ U : Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ U → o (Set.ncard {j | P j ⊆ U} * (a * b)) ≤ o (δ ^ (-ζ₃)) * μ U)) (fun j => {y | |inner ℝ (e₁ j) (y - c j)| ≤ a ∧ |inner ℝ (e₂ j) (y - c j)| ≤ b ∧ |inner ℝ (e₃ j) (y - c j)| ≤ 1}))) (fun s w => J (fun ε a η δ => ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → Q η δ m l (fun N => a * δ ^ (w + ε) * m⁻¹ * (N * δ ^ 2) * (m ^ (-(3/2 : ℝ)) * l * (N * δ)) ^ (-s))))) (fun η δ m l f => ∀ (n : ℕ) (x v : Fin n → (EuclideanSpace ℝ (Fin 3))) (Y : Fin n → Set (EuclideanSpace ℝ (Fin 3))), H η δ n x v Y (K δ m l n x v (o (f n) ≤ μ (⋃ i, Y i))))) (fun δ m l n x v P => (∀ W : Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ W → o ((Set.ncard {i | T δ (x i) (v i) ⊆ W} : ℝ) * δ ^ 2) ≤ o m * μ W) → (∀ (u : (EuclideanSpace ℝ (Fin 3))) (t r : ℝ), ‖u‖ = 1 → 0 < r → o (Set.ncard {i | T δ (x i) (v i) ⊆ (B ∩ {p | |inner ℝ u p - t| ≤ r})} : ℝ) ≤ o (l * n) * μ (B ∩ {p | |inner ℝ u p - t| ≤ r})) → P)) (fun P => ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1/100 → P ε a η δ)) (fun η δ n x v Y P => 0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, T δ (x i) (v i) ⊆ B) → (∀ i j, i ≠ j → μ (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1/2 : ENNReal) * μ (T δ (x i) (v i))) → (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ T δ (x i) (v i)) → o (δ ^ η * n * δ ^ 2) ≤ ∑ i, μ (Y i) → P)) (fun δ x v => Metric.thickening δ (segment ℝ x (x + v)))) ENNReal.ofReal) MeasureTheory.volume) (Metric.ball 0 1)


/-! ### Real-number comparisons (x0106's `Assembly.lean`, branch x0106) -/

/-- `x^s ≤ max 1 x` for `x ≥ 0` and `0 ≤ s ≤ 1`. -/
lemma rpow_le_max_one' (x s : ℝ) (hx : 0 ≤ x) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    x ^ s ≤ max 1 x := by
  rcases le_total x 1 with h | h
  · exact le_trans (Real.rpow_le_one hx h hs0) (le_max_left _ _)
  · calc x ^ s ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hs1
      _ = x := Real.rpow_one x
      _ ≤ max 1 x := le_max_right _ _

/-- The compact range: the target is at most `δ₀^(η+2) ≤ δ^η δ²`. -/
lemma target_compact' (σ w ε η a δ δ₀ C N : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1/2)
    (hw : 0 ≤ w + ε) (hη : 0 < η) (ha0 : 0 ≤ a) (ha : a ≤ δ₀ ^ (η + 2) / max 1 C)
    (hδ₀ : 0 < δ₀) (hδ : δ₀ < δ) (hδ1 : δ ≤ 1) (hN : 0 ≤ N) (hNC : N * δ ^ 4 ≤ C) :
    a * δ ^ (w + ε) * (N * δ ^ 4) ^ (σ / 2) ≤ δ ^ η * δ ^ 2 := by
  have hδ0 : 0 < δ := lt_trans hδ₀ hδ
  have hM : 0 < max 1 C := lt_of_lt_of_le one_pos (le_max_left _ _)
  have e1 : δ ^ (w + ε) ≤ 1 := Real.rpow_le_one hδ0.le hδ1 hw
  have e2 : (N * δ ^ 4) ^ (σ / 2) ≤ max 1 C :=
    le_trans (rpow_le_max_one' _ _ (by positivity) (by positivity) (by linarith))
      (max_le_max (le_refl 1) hNC)
  have e3 : δ₀ ^ (η + 2) ≤ δ ^ (η + 2) :=
    Real.rpow_le_rpow hδ₀.le hδ.le (by linarith)
  have e4 : δ ^ (η + 2) = δ ^ η * δ ^ 2 := by
    rw [Real.rpow_add hδ0, Real.rpow_two]
  calc a * δ ^ (w + ε) * (N * δ ^ 4) ^ (σ / 2) ≤ a * 1 * max 1 C := by
        gcongr
    _ = a * max 1 C := by ring
    _ ≤ δ₀ ^ (η + 2) / max 1 C * max 1 C := by gcongr
    _ = δ₀ ^ (η + 2) := by field_simp
    _ ≤ δ ^ η * δ ^ 2 := by rw [← e4]; exact e3

/-- The comparison of targets after passing to a family of at least `δ^κ N` tubes, when the
exponents leave room for the loss `δ^(κσ/2)`. -/
lemma target_refine_gen (σ w α αX ε κ a aX δ N K : ℝ) (hσ0 : 0 < σ)
    (hexp : w - αX + ε / 2 + κ * (σ / 2) ≤ w - α + ε) (ha0 : 0 ≤ a) (ha : a ≤ aX)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hN : 0 ≤ N) (hNK : δ ^ κ * N ≤ K) :
    a * δ ^ (w - α + ε) * (N * δ ^ 4) ^ (σ / 2)
      ≤ aX * δ ^ (w - αX + ε / 2) * (K * δ ^ 4) ^ (σ / 2) := by
  have hσ2 : 0 ≤ σ / 2 := by positivity
  have hK : (δ ^ κ * N) * δ ^ 4 ≤ K * δ ^ 4 := by gcongr
  have h1 : (δ ^ κ * N * δ ^ 4) ^ (σ / 2) ≤ (K * δ ^ 4) ^ (σ / 2) :=
    Real.rpow_le_rpow (by positivity) hK hσ2
  have h2 : (δ ^ κ * N * δ ^ 4) ^ (σ / 2)
      = δ ^ (κ * (σ / 2)) * (N * δ ^ 4) ^ (σ / 2) := by
    rw [mul_assoc, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hδ0.le]
  have h3 : δ ^ (w - α + ε) ≤ δ ^ (w - αX + ε / 2) * δ ^ (κ * (σ / 2)) := by
    rw [← Real.rpow_add hδ0]
    exact Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hexp
  have haX : 0 ≤ aX := le_trans ha0 ha
  have hX : 0 ≤ (N * δ ^ 4) ^ (σ / 2) := by positivity
  have hd1 : 0 ≤ δ ^ (w - αX + ε / 2) := by positivity
  calc a * δ ^ (w - α + ε) * (N * δ ^ 4) ^ (σ / 2)
      ≤ aX * (δ ^ (w - αX + ε / 2) * δ ^ (κ * (σ / 2))) * (N * δ ^ 4) ^ (σ / 2) := by
        apply mul_le_mul_of_nonneg_right _ hX
        exact mul_le_mul ha h3 (by positivity) haX
    _ = aX * δ ^ (w - αX + ε / 2) * (δ ^ (κ * (σ / 2)) * (N * δ ^ 4) ^ (σ / 2)) := by ring
    _ ≤ aX * δ ^ (w - αX + ε / 2) * (K * δ ^ 4) ^ (σ / 2) := by
        rw [← h2]
        exact mul_le_mul_of_nonneg_left h1 (mul_nonneg haX hd1)

/-- The sticky branch: the target is at most `a_A δ^(ω'/2)` once `a ≤ a_A / max 1 C`. -/
lemma target_sticky (σ w α ε a aA δ C N : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1/2)
    (hαw : α ≤ w / 2) (hε : 0 < ε) (ha0 : 0 ≤ a) (ha : a ≤ aA / max 1 C) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) (hN : 0 ≤ N) (hNC : N * δ ^ 4 ≤ C) :
    a * δ ^ (w - α + ε) * (N * δ ^ 4) ^ (σ / 2) ≤ aA * δ ^ (w / 2) := by
  have hM : 0 < max 1 C := lt_of_lt_of_le one_pos (le_max_left _ _)
  have e1 : δ ^ (w - α + ε) ≤ δ ^ (w / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
  have e2 : (N * δ ^ 4) ^ (σ / 2) ≤ max 1 C :=
    le_trans (rpow_le_max_one' _ _ (by positivity) (by positivity) (by linarith))
      (max_le_max (le_refl 1) hNC)
  have hd : 0 ≤ δ ^ (w / 2) := by positivity
  have hq : 0 ≤ aA / max 1 C := le_trans ha0 ha
  calc a * δ ^ (w - α + ε) * (N * δ ^ 4) ^ (σ / 2)
      ≤ (aA / max 1 C) * δ ^ (w / 2) * max 1 C :=
        mul_le_mul (mul_le_mul ha e1 (by positivity) hq) e2 (by positivity) (mul_nonneg hq hd)
    _ = aA * δ ^ (w / 2) := by field_simp

/-! ### The glue -/

theorem core_of_repair (hA : StatementA) (hT : TrichotomyDerived) (hB0 : SeparatedGain)
    (hC : FlatGainKT) : Core := by
  intro σ ω ω'
  have hB := hB0 σ ω ω'
  have hC' := hC σ ω'
  obtain ⟨Cp, hCp, hpack⟩ := WangZahlLot.wz_tube_packing_bound
  unfold StatementA at hA
  unfold TrichotomyDerived at hT
  beta_reduce at hT hB hC' ⊢
  intro hσ0 hσ1 hω0 hωω' hd he ξ hξ
  have hω'0 : 0 < ω' := lt_trans hω0 hωω'
  -- premise `A` at `ε_A = ω'/2`; its `η` is the stickiness error fed to the trichotomy
  obtain ⟨aA, haA, ηA, hηA, hAδ⟩ := hA (ω' / 2) (by positivity)
  obtain ⟨ζ₁, hζ₁, hT1⟩ := hT ηA hηA
  obtain ⟨αB, hαB, ζB, hζB, hB1⟩ := hB hσ0 hσ1 hω0 hωω' hd he ζ₁ hζ₁
  have hζ₂ : 0 < min ζB ζ₁ := lt_min hζB hζ₁
  obtain ⟨αC, hαC, ζC, hζC, hC1⟩ := hC' hσ0 hσ1 hω'0 he (min ζB ζ₁) hζ₂
  have hζ₃ : 0 < min ζC (min ζB ζ₁) := lt_min hζC hζ₂
  -- the loss `δ^κ` of the trichotomy is paid by half of the gain
  set κ : ℝ := min αB αC / σ with hκdef
  have hκ : 0 < κ := by rw [hκdef]; exact div_pos (lt_min hαB hαC) hσ0
  have hκσ : κ * (σ / 2) = min αB αC / 2 := by rw [hκdef]; field_simp
  obtain ⟨ζ, hζ, hT2⟩ := hT1 (min ζB ζ₁) (min ζC (min ζB ζ₁)) hζ₃ (min_le_right _ _)
    (min_le_right _ _) κ hκ
  set α : ℝ := min (min αB αC) ω' / 2 with hαdef
  have hα : 0 < α := by rw [hαdef]; exact half_pos (lt_min (lt_min hαB hαC) hω'0)
  have hαB2 : α ≤ αB / 2 := by
    rw [hαdef]; have := min_le_left (min αB αC) ω'; have := min_le_left αB αC; linarith
  have hαC2 : α ≤ αC / 2 := by
    rw [hαdef]; have := min_le_left (min αB αC) ω'; have := min_le_right αB αC; linarith
  have hαω : α ≤ ω' / 2 := by
    rw [hαdef]; have := min_le_right (min αB αC) ω'; linarith
  have hκB : κ * (σ / 2) ≤ αB / 2 := by rw [hκσ]; have := min_le_left αB αC; linarith
  have hκC : κ * (σ / 2) ≤ αC / 2 := by rw [hκσ]; have := min_le_right αB αC; linarith
  refine ⟨α, hα, ζ, hζ, ?_⟩
  intro ε hε
  obtain ⟨aB, haB, ηB, hηB, δB, hδB, hB2⟩ := hB1 (min ζB ζ₁) hζ₂ (min_le_left _ _) (ε / 2)
    (by positivity)
  obtain ⟨aC, haC, ηC, hηC, δC, hδC, hC2⟩ := hC1 (min ζC (min ζB ζ₁)) hζ₃ (min_le_left _ _)
    (ε / 2) (by positivity)
  -- the density exponent `θ` of the family (and the density loss of the trichotomy)
  set θ : ℝ := min (min ηA ηB) (min ηC ε) / 2 with hθdef
  have hθ : 0 < θ := by
    have : 0 < min (min ηA ηB) (min ηC ε) := lt_min (lt_min hηA hηB) (lt_min hηC hε)
    rw [hθdef]; positivity
  have hθA : θ + θ ≤ ηA := by
    have := min_le_left (min ηA ηB) (min ηC ε)
    have := min_le_left ηA ηB
    rw [hθdef]; linarith
  have hθB : θ + θ ≤ ηB := by
    have := min_le_left (min ηA ηB) (min ηC ε)
    have := min_le_right ηA ηB
    rw [hθdef]; linarith
  have hθC : θ + θ ≤ ηC := by
    have := min_le_right (min ηA ηB) (min ηC ε)
    have := min_le_left ηC ε
    rw [hθdef]; linarith
  obtain ⟨δT, hδT, hT3⟩ := hT2 θ hθ
  set δ₀ : ℝ := min (min δB δC) (min δT (1 / 100)) with hδ₀def
  have hδ₀ : 0 < δ₀ := lt_min (lt_min hδB hδC) (lt_min hδT (by norm_num))
  have hM : 0 < max 1 Cp := lt_of_lt_of_le one_pos (le_max_left _ _)
  set a : ℝ := min (min aB aC) (min (aA / max 1 Cp) (δ₀ ^ (θ + 2) / max 1 Cp)) with hadef
  have ha : 0 < a := lt_min (lt_min haB haC) (lt_min (by positivity) (by positivity))
  refine ⟨a, ha, θ, hθ, ?_⟩
  intro δ hδ0 hδ1 n x v Y hn hv hTB hov hYm hYT hsum hind hfrost hnost
  have hδ1' : δ ≤ 1 := by linarith
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hNC : (n : ℝ) * δ ^ 4 ≤ Cp := hpack δ hδ0 hδ1 n x v hv hTB hov
  by_cases hsmall : δ ≤ δ₀
  · have hδT' : δ ≤ δT := le_trans hsmall (le_trans (min_le_right _ _) (min_le_left _ _))
    obtain ⟨k, y, u, Z, ⟨hk, hu, hTB', hov', hZm, hZT, hZind⟩, hkn, hZY, hcase⟩ :=
      hT3 δ hδ0 hδT' θ hθ n x v Y ⟨hn, hv, hTB, hov, hYm, hYT, hind⟩ hfrost
    have hunion : MeasureTheory.volume (⋃ j, Z j) ≤ MeasureTheory.volume (⋃ i, Y i) :=
      MeasureTheory.measure_mono hZY
    -- individual and average density of the derived family with a larger exponent
    have hindZ : ∀ η' : ℝ, θ + θ ≤ η' → ∀ j, ENNReal.ofReal (δ ^ η' * δ ^ 2)
        ≤ MeasureTheory.volume (Z j) := fun η' hη' j =>
      le_trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1' hη') (by positivity))) (hZind j)
    have hsumZ : ∀ η' : ℝ, θ + θ ≤ η' → ENNReal.ofReal (δ ^ η' * (k : ℝ) * δ ^ 2)
        ≤ ∑ j, MeasureTheory.volume (Z j) := fun η' hη' => by
      calc ENNReal.ofReal (δ ^ η' * (k : ℝ) * δ ^ 2)
          = ∑ _j : Fin k, ENNReal.ofReal (δ ^ η' * δ ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
            congr 1; ring
        _ ≤ ∑ j, MeasureTheory.volume (Z j) :=
            Finset.sum_le_sum fun j _ => hindZ η' hη' j
    have hcmp : ∀ αX aX : ℝ, α ≤ αX / 2 → κ * (σ / 2) ≤ αX / 2 → a ≤ aX →
        a * δ ^ (ω' - α + ε) * ((n : ℝ) * δ ^ 4) ^ (σ / 2)
          ≤ aX * δ ^ (ω' - αX + ε / 2) * ((k : ℝ) * δ ^ 4) ^ (σ / 2) :=
      fun αX aX hαX hκX haX => target_refine_gen σ ω' α αX ε κ a aX δ n k hσ0
        (by linarith) ha.le haX hδ0 hδ1' hnR hkn
    rcases hcase with hS | hSB | hSC
    · -- the sticky branch: premise `A` on the derived family
      have hvol := hAδ δ hδ0 hδ1 k y u Z hk hu hTB' hov' hZm hZT (hsumZ ηA hθA) hS
      refine le_trans ?_ (le_trans hvol hunion)
      apply ENNReal.ofReal_le_ofReal
      exact target_sticky σ ω' α ε a aA δ Cp n hσ0 hσ1 hαω hε ha.le
        (le_trans (min_le_right _ _) (min_le_left _ _)) hδ0 hδ1' hnR hNC
    · have hδB' : δ ≤ δB :=
        le_trans hsmall (le_trans (min_le_left _ _) (min_le_left _ _))
      have hvol := hB2 δ hδ0 hδB' k y u Z hk hu hTB' hov' hZm hZT (hsumZ ηB hθB)
        (hindZ ηB hθB) hSB
      refine le_trans ?_ (le_trans hvol hunion)
      exact ENNReal.ofReal_le_ofReal (hcmp αB aB hαB2 hκB
        (le_trans (min_le_left _ _) (min_le_left _ _)))
    · have hδC' : δ ≤ δC :=
        le_trans hsmall (le_trans (min_le_left _ _) (min_le_right _ _))
      have hvol := hC2 δ hδ0 hδC' k y u Z hk hu hTB' hov' hZm hZT (hsumZ ηC hθC)
        (hindZ ηC hθC) hSC
      refine le_trans ?_ (le_trans hvol hunion)
      exact ENNReal.ofReal_le_ofReal (hcmp αC aC hαC2 hκC
        (le_trans (min_le_left _ _) (min_le_right _ _)))
  · -- the compact range `δ₀ < δ ≤ 1/100`
    replace hsmall : δ₀ < δ := lt_of_not_ge hsmall
    have hw : 0 ≤ ω' - α + ε := by linarith
    have hbound := target_compact' σ (ω' - α) ε θ a δ δ₀ Cp n hσ0
      hσ1 hw hθ ha.le (le_trans (min_le_right _ _) (min_le_right _ _)) hδ₀ hsmall hδ1' hnR
      hNC
    have hY0 : ENNReal.ofReal (δ ^ θ * δ ^ 2) ≤ MeasureTheory.volume (⋃ i, Y i) :=
      le_trans (hind ⟨0, hn⟩)
        (MeasureTheory.measure_mono (Set.subset_iUnion Y ⟨0, hn⟩))
    refine le_trans ?_ hY0
    apply ENNReal.ofReal_le_ofReal
    simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using hbound

/-- o038 from the repaired children: premise `A` (o015, reused), the derived-family trichotomy,
o071 (accepted) and the flat gain with prism Katz–Tao. -/
theorem o038_of_repair (hA : StatementA) (hT : TrichotomyDerived) (hB : SeparatedGain)
    (hC : FlatGainKT) : O038 :=
  o038_of_core (core_of_repair hA hT hB hC)

/-! ### Variant: frozen `SC` and frozen o072

If frozen o072 (`wz_flat_prism_frostman_gain`) is proved, the trichotomy need not produce prism
Katz–Tao: `TrichotomyDerivedSC` is `TrichotomyDerived` with o072's frozen `SC`, and
`o038_of_repairSC` uses o072 itself. -/

/-- `TrichotomyDerived` with frozen `SC` (no prism Katz–Tao clause). -/
def TrichotomyDerivedSC : Prop := (fun (μ:MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))=>(fun (o:ℝ→ENNReal)=>(fun (T:ℝ→EuclideanSpace ℝ (Fin 3)→EuclideanSpace ℝ (Fin 3)→Set (EuclideanSpace ℝ (Fin 3)))=>(fun (G:ℝ→ℝ→(n:ℕ)→(Fin n→EuclideanSpace ℝ (Fin 3))→(Fin n→EuclideanSpace ℝ (Fin 3))→(Fin n→Set (EuclideanSpace ℝ (Fin 3)))→Prop)=>(fun (S:ℝ→ℝ→(k:ℕ)→(Fin k→Set (EuclideanSpace ℝ (Fin 3)))→Prop)=>(fun (SB:ℝ→ℝ→ℝ→(k:ℕ)→(Fin k→Set (EuclideanSpace ℝ (Fin 3)))→Prop)=>(fun (SC:ℝ→ℝ→ℝ→(k:ℕ)→(Fin k→Set (EuclideanSpace ℝ (Fin 3)))→Prop)=>∀ ξ:ℝ,0<ξ→∃ ζ₁:ℝ,0<ζ₁∧∀ ζ₂ ζ₃:ℝ,0<ζ₃→ζ₃≤ζ₂→ζ₂≤ζ₁→∀ κ:ℝ,0<κ→∃ ζ:ℝ,0<ζ∧∀ θ:ℝ,0<θ→∃ δ₀:ℝ,0<δ₀∧∀ δ:ℝ,0<δ→δ≤δ₀→∀ η:ℝ,0<η→∀ (n:ℕ) (x v:Fin n→EuclideanSpace ℝ (Fin 3)) (Y:Fin n→Set (EuclideanSpace ℝ (Fin 3))),G δ η n x v Y→(∀ W:Set (EuclideanSpace ℝ (Fin 3)),Convex ℝ W→ o (Set.ncard {i | T δ (x i) (v i)⊆W})≤o (δ^(-ζ)*n)*μ W)→∃ (k:ℕ) (y u:Fin k→EuclideanSpace ℝ (Fin 3)) (Z:Fin k→Set (EuclideanSpace ℝ (Fin 3))),G δ (θ+η) k y u Z∧δ^κ*n≤k∧(⋃ j,Z j)⊆(⋃ i,Y i)∧(S ξ δ k (fun j=>T δ (y j) (u j))∨SB ζ₁ ζ₂ δ k (fun j=>T δ (y j) (u j))∨SC ζ₂ ζ₃ δ k (fun j=>T δ (y j) (u j)))) (fun ζ₂ ζ₃ δ k A=>∃ a b:ℝ,δ≤a∧a≤δ^(ζ₂/200)*b∧b≤1∧∃ (p:ℕ) (c e₁ e₂ e₃:Fin p→EuclideanSpace ℝ (Fin 3)),(∀ j,Orthonormal ℝ ![e₁ j,e₂ j,e₃ j])∧(fun (P:Fin p→Set (EuclideanSpace ℝ (Fin 3)))=>(∀ i,∃ j,A i⊆P j)∧(∀ j j',(Set.ncard {i | A i⊆P j}:ℝ)≤δ^(-ζ₃)*Set.ncard {i | A i⊆P j'})∧(∀ U:Set (EuclideanSpace ℝ (Fin 3)),Convex ℝ U→ o (Set.ncard {j | P j⊆U})≤o (δ^(-ζ₃)*p)*μ U)∧(∀ j (U:Set (EuclideanSpace ℝ (Fin 3))),Convex ℝ U→ o (Set.ncard {i | A i⊆P j∧A i⊆U})*μ (P j)≤o (δ^(-ζ₃)*Set.ncard {i | A i⊆P j})*μ U)∧(∀ j (U:Set (EuclideanSpace ℝ (Fin 3))),Convex ℝ U→ o (Set.ncard {j' | P j'⊆Metric.thickening b (P j)∧P j'⊆U})*μ (P j)≤o (δ^(-ζ₃))*μ U)) (fun j=>{y | |inner ℝ (e₁ j) (y-c j)|≤a∧|inner ℝ (e₂ j) (y-c j)|≤b∧|inner ℝ (e₃ j) (y-c j)|≤1}))) (fun ζ₁ ζ₂ δ k A=>∃ τ ρ:ℝ,δ≤τ∧τ<ρ∧ρ≤1∧τ≤δ^ζ₁*ρ∧∃ (p:ℕ) (y u:Fin p→EuclideanSpace ℝ (Fin 3)) (q:ℕ) (z w:Fin q→EuclideanSpace ℝ (Fin 3)),(∀ j,‖u j‖=1)∧(∀ l,‖w l‖=1)∧(fun (P:Fin p→Set (EuclideanSpace ℝ (Fin 3))) (R:Fin q→Set (EuclideanSpace ℝ (Fin 3)))=>(∀ j j',j≠j'→μ (P j∩P j')≤1/2*μ (P j))∧(∀ l l',l≠l'→μ (R l∩R l')≤1/2*μ (R l))∧(∀ i,∃! j,A i⊆P j)∧(∀ j,∃ i,A i⊆P j)∧(∀ j,∃! l,P j⊆R l)∧(∀ l,∃ j,P j⊆R l)∧(∀ j j',(Set.ncard {i | A i⊆P j}:ℝ)≤δ^(-ζ₂)*Set.ncard {i | A i⊆P j'})∧(∀ l l',(Set.ncard {j | P j⊆R l}:ℝ)≤δ^(-ζ₂)*Set.ncard {j | P j⊆R l'})∧(∀ j (W:Set (EuclideanSpace ℝ (Fin 3))),Convex ℝ W→ o (Set.ncard {i | A i⊆P j∧A i⊆W}*τ^2)≤o (δ^(-ζ₂)*Set.ncard {i | A i⊆P j})*μ W)∧(∀ l (W:Set (EuclideanSpace ℝ (Fin 3))),Convex ℝ W→ o (Set.ncard {j | P j⊆R l∧P j⊆W}*τ^2)≤o (δ^(-ζ₂))*μ W)∧(∀ l,δ^ζ₂*(ρ/τ)^2≤Set.ncard {j | P j⊆R l})∧(∀ W:Set (EuclideanSpace ℝ (Fin 3)),Convex ℝ W→ o (Set.ncard {l | R l⊆W})≤o (δ^(-ζ₂)*q)*μ W)) (fun j=>T τ (y j) (u j)) (fun l=>T ρ (z l) (w l)))) (fun ξ δ k A=>∀ ρ₀:ℝ,δ≤ρ₀→ρ₀≤1→∃ ρ:ℝ,ρ₀≤ρ∧ρ≤1∧ρ≤δ^(-ξ)*ρ₀∧∃ q:ℕ,0<q∧∃ z w:Fin q→EuclideanSpace ℝ (Fin 3),(∀ j,‖w j‖=1)∧(fun (R:Fin q→Set (EuclideanSpace ℝ (Fin 3)))=>(∀ j j',j≠j'→μ (R j∩R j')≤1/2*μ (R j))∧(∀ i,∃! j,A i⊆R j)∧(∀ j,∃ i,A i⊆R j)∧(∀ j j',(Set.ncard {i | A i⊆R j}:ℝ)≤δ^(-ξ)*Set.ncard {i | A i⊆R j'})∧(∀ j (W:Set (EuclideanSpace ℝ (Fin 3))),Convex ℝ W→ o (Set.ncard {i | A i⊆R j∧A i⊆W}*ρ^2)≤o (δ^(-ξ)*Set.ncard {i | A i⊆R j})*μ W)) (fun j=>T ρ (z j) (w j)))) (fun (δ η:ℝ) (n:ℕ) (x v:Fin n→EuclideanSpace ℝ (Fin 3)) (Y:Fin n→Set (EuclideanSpace ℝ (Fin 3)))=>0<n∧(∀ i,‖v i‖=1)∧(∀ i,T δ (x i) (v i)⊆Metric.ball 0 1)∧(∀ i j,i≠j→μ (T δ (x i) (v i)∩T δ (x j) (v j))≤1/2*μ (T δ (x i) (v i)))∧(∀ i,MeasurableSet (Y i))∧(∀ i,Y i⊆T δ (x i) (v i))∧(∀ i,o (δ^η*δ^2)≤μ (Y i)))) (fun δ x v=>Metric.thickening δ (segment ℝ x (x+v)))) ENNReal.ofReal) MeasureTheory.volume

/-- o072's frozen statement. -/
def FlatGain : Prop := ∀ σ ω' : ℝ, (fun (B : Set (EuclideanSpace ℝ (Fin 3))) => (fun (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) => (fun (o : ℝ → ENNReal) => (fun (T : ℝ → (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))) => (fun (H : ℝ → ℝ → (n : ℕ) → (Fin n → (EuclideanSpace ℝ (Fin 3))) → (Fin n → (EuclideanSpace ℝ (Fin 3))) → (Fin n → Set (EuclideanSpace ℝ (Fin 3))) → Prop → Prop) => (fun (J : (ℝ → ℝ → ℝ → ℝ → Prop) → Prop) => (fun (K : ℝ → ℝ → ℝ → (n : ℕ) → (Fin n → (EuclideanSpace ℝ (Fin 3))) → (Fin n → (EuclideanSpace ℝ (Fin 3))) → Prop → Prop) => (fun (Q : ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → Prop) => (fun (e : ℝ → ℝ → Prop) => (fun (SC : ℝ → ℝ → ℝ → (k : ℕ) → (Fin k → Set (EuclideanSpace ℝ (Fin 3))) → Prop) => 0 < σ → σ ≤ 1/2 → 0 < ω' → e σ ω' → ∀ ζ₂ : ℝ, 0 < ζ₂ → ∃ α : ℝ, 0 < α ∧ ∃ ζ₀ : ℝ, 0 < ζ₀ ∧ ∀ ζ₃ : ℝ, 0 < ζ₃ → ζ₃ ≤ ζ₀ → ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ (n : ℕ) (x v : Fin n → (EuclideanSpace ℝ (Fin 3))) (Y : Fin n → Set (EuclideanSpace ℝ (Fin 3))), H η δ n x v Y ((∀ i, o (δ ^ η * δ ^ 2) ≤ μ (Y i)) → SC ζ₂ ζ₃ δ n (fun i => T δ (x i) (v i)) → o (a * δ ^ (ω' - α + ε) * (n * δ ^ 4) ^ (σ / 2)) ≤ μ (⋃ i, Y i))) (fun ζ₂ ζ₃ δ k A => ∃ a b : ℝ, δ ≤ a ∧ a ≤ δ ^ (ζ₂ / 200) * b ∧ b ≤ 1 ∧ ∃ (p : ℕ) (c e₁ e₂ e₃ : Fin p → (EuclideanSpace ℝ (Fin 3))), (∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j]) ∧ (fun (P : Fin p → Set (EuclideanSpace ℝ (Fin 3))) => (∀ i, ∃ j, A i ⊆ P j) ∧ (∀ j j', (Set.ncard {i | A i ⊆ P j} : ℝ) ≤ δ ^ (-ζ₃) * Set.ncard {i | A i ⊆ P j'}) ∧ (∀ U : Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ U → o (Set.ncard {j | P j ⊆ U}) ≤ o (δ ^ (-ζ₃) * p) * μ U) ∧ (∀ j (U : Set (EuclideanSpace ℝ (Fin 3))), Convex ℝ U → o (Set.ncard {i | A i ⊆ P j ∧ A i ⊆ U}) * μ (P j) ≤ o (δ ^ (-ζ₃) * Set.ncard {i | A i ⊆ P j}) * μ U) ∧ (∀ j (U : Set (EuclideanSpace ℝ (Fin 3))), Convex ℝ U → o (Set.ncard {j' | P j' ⊆ Metric.thickening b (P j) ∧ P j' ⊆ U}) * μ (P j) ≤ o (δ ^ (-ζ₃)) * μ U)) (fun j => {y | |inner ℝ (e₁ j) (y - c j)| ≤ a ∧ |inner ℝ (e₂ j) (y - c j)| ≤ b ∧ |inner ℝ (e₃ j) (y - c j)| ≤ 1}))) (fun s w => J (fun ε a η δ => ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → Q η δ m l (fun N => a * δ ^ (w + ε) * m⁻¹ * (N * δ ^ 2) * (m ^ (-(3/2 : ℝ)) * l * (N * δ)) ^ (-s))))) (fun η δ m l f => ∀ (n : ℕ) (x v : Fin n → (EuclideanSpace ℝ (Fin 3))) (Y : Fin n → Set (EuclideanSpace ℝ (Fin 3))), H η δ n x v Y (K δ m l n x v (o (f n) ≤ μ (⋃ i, Y i))))) (fun δ m l n x v P => (∀ W : Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ W → o ((Set.ncard {i | T δ (x i) (v i) ⊆ W} : ℝ) * δ ^ 2) ≤ o m * μ W) → (∀ (u : (EuclideanSpace ℝ (Fin 3))) (t r : ℝ), ‖u‖ = 1 → 0 < r → o (Set.ncard {i | T δ (x i) (v i) ⊆ (B ∩ {p | |inner ℝ u p - t| ≤ r})} : ℝ) ≤ o (l * n) * μ (B ∩ {p | |inner ℝ u p - t| ≤ r})) → P)) (fun P => ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1/100 → P ε a η δ)) (fun η δ n x v Y P => 0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, T δ (x i) (v i) ⊆ B) → (∀ i j, i ≠ j → μ (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1/2 : ENNReal) * μ (T δ (x i) (v i))) → (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ T δ (x i) (v i)) → o (δ ^ η * n * δ ^ 2) ≤ ∑ i, μ (Y i) → P)) (fun δ x v => Metric.thickening δ (segment ℝ x (x + v)))) ENNReal.ofReal) MeasureTheory.volume) (Metric.ball 0 1)

theorem core_of_repairSC (hA : StatementA) (hT : TrichotomyDerivedSC) (hB0 : SeparatedGain)
    (hC : FlatGain) : Core := by
  intro σ ω ω'
  have hB := hB0 σ ω ω'
  have hC' := hC σ ω'
  obtain ⟨Cp, hCp, hpack⟩ := WangZahlLot.wz_tube_packing_bound
  unfold StatementA at hA
  unfold TrichotomyDerivedSC at hT
  beta_reduce at hT hB hC' ⊢
  intro hσ0 hσ1 hω0 hωω' hd he ξ hξ
  have hω'0 : 0 < ω' := lt_trans hω0 hωω'
  -- premise `A` at `ε_A = ω'/2`; its `η` is the stickiness error fed to the trichotomy
  obtain ⟨aA, haA, ηA, hηA, hAδ⟩ := hA (ω' / 2) (by positivity)
  obtain ⟨ζ₁, hζ₁, hT1⟩ := hT ηA hηA
  obtain ⟨αB, hαB, ζB, hζB, hB1⟩ := hB hσ0 hσ1 hω0 hωω' hd he ζ₁ hζ₁
  have hζ₂ : 0 < min ζB ζ₁ := lt_min hζB hζ₁
  obtain ⟨αC, hαC, ζC, hζC, hC1⟩ := hC' hσ0 hσ1 hω'0 he (min ζB ζ₁) hζ₂
  have hζ₃ : 0 < min ζC (min ζB ζ₁) := lt_min hζC hζ₂
  -- the loss `δ^κ` of the trichotomy is paid by half of the gain
  set κ : ℝ := min αB αC / σ with hκdef
  have hκ : 0 < κ := by rw [hκdef]; exact div_pos (lt_min hαB hαC) hσ0
  have hκσ : κ * (σ / 2) = min αB αC / 2 := by rw [hκdef]; field_simp
  obtain ⟨ζ, hζ, hT2⟩ := hT1 (min ζB ζ₁) (min ζC (min ζB ζ₁)) hζ₃ (min_le_right _ _)
    (min_le_right _ _) κ hκ
  set α : ℝ := min (min αB αC) ω' / 2 with hαdef
  have hα : 0 < α := by rw [hαdef]; exact half_pos (lt_min (lt_min hαB hαC) hω'0)
  have hαB2 : α ≤ αB / 2 := by
    rw [hαdef]; have := min_le_left (min αB αC) ω'; have := min_le_left αB αC; linarith
  have hαC2 : α ≤ αC / 2 := by
    rw [hαdef]; have := min_le_left (min αB αC) ω'; have := min_le_right αB αC; linarith
  have hαω : α ≤ ω' / 2 := by
    rw [hαdef]; have := min_le_right (min αB αC) ω'; linarith
  have hκB : κ * (σ / 2) ≤ αB / 2 := by rw [hκσ]; have := min_le_left αB αC; linarith
  have hκC : κ * (σ / 2) ≤ αC / 2 := by rw [hκσ]; have := min_le_right αB αC; linarith
  refine ⟨α, hα, ζ, hζ, ?_⟩
  intro ε hε
  obtain ⟨aB, haB, ηB, hηB, δB, hδB, hB2⟩ := hB1 (min ζB ζ₁) hζ₂ (min_le_left _ _) (ε / 2)
    (by positivity)
  obtain ⟨aC, haC, ηC, hηC, δC, hδC, hC2⟩ := hC1 (min ζC (min ζB ζ₁)) hζ₃ (min_le_left _ _)
    (ε / 2) (by positivity)
  -- the density exponent `θ` of the family (and the density loss of the trichotomy)
  set θ : ℝ := min (min ηA ηB) (min ηC ε) / 2 with hθdef
  have hθ : 0 < θ := by
    have : 0 < min (min ηA ηB) (min ηC ε) := lt_min (lt_min hηA hηB) (lt_min hηC hε)
    rw [hθdef]; positivity
  have hθA : θ + θ ≤ ηA := by
    have := min_le_left (min ηA ηB) (min ηC ε)
    have := min_le_left ηA ηB
    rw [hθdef]; linarith
  have hθB : θ + θ ≤ ηB := by
    have := min_le_left (min ηA ηB) (min ηC ε)
    have := min_le_right ηA ηB
    rw [hθdef]; linarith
  have hθC : θ + θ ≤ ηC := by
    have := min_le_right (min ηA ηB) (min ηC ε)
    have := min_le_left ηC ε
    rw [hθdef]; linarith
  obtain ⟨δT, hδT, hT3⟩ := hT2 θ hθ
  set δ₀ : ℝ := min (min δB δC) (min δT (1 / 100)) with hδ₀def
  have hδ₀ : 0 < δ₀ := lt_min (lt_min hδB hδC) (lt_min hδT (by norm_num))
  have hM : 0 < max 1 Cp := lt_of_lt_of_le one_pos (le_max_left _ _)
  set a : ℝ := min (min aB aC) (min (aA / max 1 Cp) (δ₀ ^ (θ + 2) / max 1 Cp)) with hadef
  have ha : 0 < a := lt_min (lt_min haB haC) (lt_min (by positivity) (by positivity))
  refine ⟨a, ha, θ, hθ, ?_⟩
  intro δ hδ0 hδ1 n x v Y hn hv hTB hov hYm hYT hsum hind hfrost hnost
  have hδ1' : δ ≤ 1 := by linarith
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hNC : (n : ℝ) * δ ^ 4 ≤ Cp := hpack δ hδ0 hδ1 n x v hv hTB hov
  by_cases hsmall : δ ≤ δ₀
  · have hδT' : δ ≤ δT := le_trans hsmall (le_trans (min_le_right _ _) (min_le_left _ _))
    obtain ⟨k, y, u, Z, ⟨hk, hu, hTB', hov', hZm, hZT, hZind⟩, hkn, hZY, hcase⟩ :=
      hT3 δ hδ0 hδT' θ hθ n x v Y ⟨hn, hv, hTB, hov, hYm, hYT, hind⟩ hfrost
    have hunion : MeasureTheory.volume (⋃ j, Z j) ≤ MeasureTheory.volume (⋃ i, Y i) :=
      MeasureTheory.measure_mono hZY
    -- individual and average density of the derived family with a larger exponent
    have hindZ : ∀ η' : ℝ, θ + θ ≤ η' → ∀ j, ENNReal.ofReal (δ ^ η' * δ ^ 2)
        ≤ MeasureTheory.volume (Z j) := fun η' hη' j =>
      le_trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1' hη') (by positivity))) (hZind j)
    have hsumZ : ∀ η' : ℝ, θ + θ ≤ η' → ENNReal.ofReal (δ ^ η' * (k : ℝ) * δ ^ 2)
        ≤ ∑ j, MeasureTheory.volume (Z j) := fun η' hη' => by
      calc ENNReal.ofReal (δ ^ η' * (k : ℝ) * δ ^ 2)
          = ∑ _j : Fin k, ENNReal.ofReal (δ ^ η' * δ ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
            congr 1; ring
        _ ≤ ∑ j, MeasureTheory.volume (Z j) :=
            Finset.sum_le_sum fun j _ => hindZ η' hη' j
    have hcmp : ∀ αX aX : ℝ, α ≤ αX / 2 → κ * (σ / 2) ≤ αX / 2 → a ≤ aX →
        a * δ ^ (ω' - α + ε) * ((n : ℝ) * δ ^ 4) ^ (σ / 2)
          ≤ aX * δ ^ (ω' - αX + ε / 2) * ((k : ℝ) * δ ^ 4) ^ (σ / 2) :=
      fun αX aX hαX hκX haX => target_refine_gen σ ω' α αX ε κ a aX δ n k hσ0
        (by linarith) ha.le haX hδ0 hδ1' hnR hkn
    rcases hcase with hS | hSB | hSC
    · -- the sticky branch: premise `A` on the derived family
      have hvol := hAδ δ hδ0 hδ1 k y u Z hk hu hTB' hov' hZm hZT (hsumZ ηA hθA) hS
      refine le_trans ?_ (le_trans hvol hunion)
      apply ENNReal.ofReal_le_ofReal
      exact target_sticky σ ω' α ε a aA δ Cp n hσ0 hσ1 hαω hε ha.le
        (le_trans (min_le_right _ _) (min_le_left _ _)) hδ0 hδ1' hnR hNC
    · have hδB' : δ ≤ δB :=
        le_trans hsmall (le_trans (min_le_left _ _) (min_le_left _ _))
      have hvol := hB2 δ hδ0 hδB' k y u Z hk hu hTB' hov' hZm hZT (hsumZ ηB hθB)
        (hindZ ηB hθB) hSB
      refine le_trans ?_ (le_trans hvol hunion)
      exact ENNReal.ofReal_le_ofReal (hcmp αB aB hαB2 hκB
        (le_trans (min_le_left _ _) (min_le_left _ _)))
    · have hδC' : δ ≤ δC :=
        le_trans hsmall (le_trans (min_le_left _ _) (min_le_right _ _))
      have hvol := hC2 δ hδ0 hδC' k y u Z hk hu hTB' hov' hZm hZT (hsumZ ηC hθC)
        (hindZ ηC hθC) hSC
      refine le_trans ?_ (le_trans hvol hunion)
      exact ENNReal.ofReal_le_ofReal (hcmp αC aC hαC2 hκC
        (le_trans (min_le_left _ _) (min_le_right _ _)))
  · -- the compact range `δ₀ < δ ≤ 1/100`
    replace hsmall : δ₀ < δ := lt_of_not_ge hsmall
    have hw : 0 ≤ ω' - α + ε := by linarith
    have hbound := target_compact' σ (ω' - α) ε θ a δ δ₀ Cp n hσ0
      hσ1 hw hθ ha.le (le_trans (min_le_right _ _) (min_le_right _ _)) hδ₀ hsmall hδ1' hnR
      hNC
    have hY0 : ENNReal.ofReal (δ ^ θ * δ ^ 2) ≤ MeasureTheory.volume (⋃ i, Y i) :=
      le_trans (hind ⟨0, hn⟩)
        (MeasureTheory.measure_mono (Set.subset_iUnion Y ⟨0, hn⟩))
    refine le_trans ?_ hY0
    apply ENNReal.ofReal_le_ofReal
    simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using hbound

/-- o038 from the repaired children, with frozen `SC` and frozen o072. -/
theorem o038_of_repairSC (hA : StatementA) (hT : TrichotomyDerivedSC) (hB : SeparatedGain)
    (hC : FlatGain) : O038 :=
  o038_of_core (core_of_repairSC hA hT hB hC)

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy
