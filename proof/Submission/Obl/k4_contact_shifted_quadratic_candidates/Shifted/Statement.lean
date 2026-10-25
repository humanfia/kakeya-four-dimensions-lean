import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.Model
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.MeshCalibration

/-!
# The shifted-candidate statement in field-named form

`ShiftedCandidates cfg` is the conclusion of o260 for the data `cfg`:
original-label shifted quadratic candidates or velocity candidates below every
positive depth horizon `V ≤ U`. `ShiftedTransfer` is the whole obligation in the
field-named model of `Transfer.Model`; `raw_statement_of_shifted_transfer`
turns it into the frozen statement.
-/

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates

open MeasureTheory Set Filter MvPolynomial
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

noncomputable section

/-- The trajectory point with its hidden coordinate shifted by an affine
function of the base. -/
def shiftedPoint {α : Type} [MeasurableSpace α] (cfg : Data α) (k : ℕ)
    (L : Fin 4 → ℝ) (l : α) (t : ℝ) : Fin 4 → ℝ :=
  ![t, (cfg.x k l t) 1, (cfg.x k l t) 2,
    (cfg.x k l t) 3 - (L 0 + L 1 * t + L 2 * (cfg.x k l t) 1 + L 3 * (cfg.x k l t) 2)]

/-- The polynomial alternative of a shifted candidate at index `k`, label `i`
of depth `s`, improvement `v` and loss `ε`. -/
def ShiftedPoly {α : Type} [MeasurableSpace α] (cfg : Data α) (k : ℕ) (R ε s v : ℝ)
    (i : Fin (cfg.n k s)) : Prop :=
  ∃ (L : Fin 4 → ℝ) (G : MvPolynomial (Fin 4) ℝ), G.totalDegree ≤ 2 ∧
    (∀ e, |G.coeff e| ≤ cfg.N k ^ R) ∧
    ENNReal.ofReal (cfg.N k ^ (-cfg.d * v - ε) / (2 : ℝ) ^ cfg.T k s) * cfg.ν k (cfg.A k s i) ≤
      cfg.ρ k {p | p.1 ∈ cfg.B k s i ∧ p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i) ∧
        (∀ t ∈ Data.I (cfg.T k s) (cfg.j k s i),
          |(shiftedPoint cfg k L p.1 t) 3| ≤ 1 ∧
          |eval (shiftedPoint cfg k L p.1 t) G| ≤ cfg.N k ^ ε * cfg.N k ^ (-s - v) ∧
          |eval (shiftedPoint cfg k L p.1 t) (pderiv (3 : Fin 4) G)| ≤ cfg.N k ^ ε ∧
          |eval (shiftedPoint cfg k L p.1 t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) G))| ≤
            cfg.N k ^ ε / cfg.N k ^ (-s - v)) ∧
        cfg.N k ^ (-ε) ≤ |eval (shiftedPoint cfg k L p.1 p.2) (pderiv (3 : Fin 4) G)|}

/-- The velocity alternative, exactly as in the original candidate. -/
def ShiftedVelocity {α : Type} [MeasurableSpace α] (cfg : Data α) (k : ℕ) (R ε s v : ℝ)
    (i : Fin (cfg.n k s)) : Prop :=
  ∃ z : Fin 2 → ℝ, (∀ e, |z e| ≤ cfg.N k ^ R) ∧
    ENNReal.ofReal (cfg.N k ^ (-ε) / (2 : ℝ) ^ cfg.T k s) * cfg.ν k (cfg.A k s i) ≤
      cfg.ρ k {p | p.1 ∈ cfg.B k s i ∧ p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i) ∧
        |cfg.b k p.1 4 - z 0 - z 1 * cfg.b k p.1 3| ≤ cfg.N k ^ ε * cfg.N k ^ (-cfg.ℓ * s - v)}

/-- The conclusion of o260 for the data `cfg`. -/
def ShiftedCandidates {α : Type} [MeasurableSpace α] (cfg : Data α) : Prop :=
  ∀ V : ℝ, 0 < V → V ≤ cfg.U → ∃ R : ℝ, 1 < R ∧ ∀ ε : ℝ, 0 < ε →
    ∃ᶠ k in atTop, ∃ (s v : ℝ) (i : Fin (cfg.n k s)), R⁻¹ ≤ s ∧ s ≤ R ∧ R⁻¹ ≤ v ∧ v ≤ R ∧
      s + v ≤ V ∧ (ShiftedPoly cfg k R ε s v i ∨ ShiftedVelocity cfg k R ε s v i)

/-- The whole obligation in the field-named model. -/
def ShiftedTransfer : Prop :=
  MeshCalibration → HorizontalPrinciple → ∀ (α : Type) [MeasurableSpace α] (cfg : Data α),
    ContactProblem cfg → ShiftedCandidates cfg

/-- The field-named transfer has exactly the frozen raw statement. -/
theorem raw_statement_of_shifted_transfer (htransfer : ShiftedTransfer) : (∃ C:ℝ,1 ≤ C ∧ ∀ K β m E δ:ℝ,1 ≤ K → 0 < β → 0 < m → 0 ≤ E → 0 < δ → C * (1 + K) ^ C * (1 + β / m) ^ (6:ℕ) * δ ≤ (1:ℝ) / 2 → ∀ μ:MeasureTheory.Measure (Fin 3 → ℝ),MeasureTheory.IsFiniteMeasure μ → ENNReal.ofReal m ≤ μ Set.univ → (∀ q:Fin 3 → ℤ,μ {z | (fun i:Fin 3 => ⌊z i / δ⌋) = q} ≤ ENNReal.ofReal (β * δ ^ (3:ℕ))) → ∀ G:MvPolynomial (Fin 3) ℝ,G.totalDegree ≤ 2 → (∀ᵐ z ∂μ,(∀ i,|z i| ≤ K) ∧ |MvPolynomial.eval z G| ≤ E) → ∀ e,|G.coeff e| ≤ C * (1 + K) ^ C * (1 + β / m) ^ (6:ℕ) * E) → (((fun (horizontal:Bool) (regime:ℝ → Prop) => ∀ (N K:ℕ → ℝ),(∀ k,2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → ((∀ k,1 ≤ K k) ∧ ∀ ε:ℝ,0 < ε → ∀ᶠ k in Filter.atTop,K k ≤ N k ^ ε) → ∀ d κ ℓ S U e₀:ℝ,0 ≤ d → d < 1 → 0 < κ → κ ≤ 1 → 0 < ℓ → 0 < S → S ≤ 1 → 0 < U → 0 < e₀ → regime κ → (horizontal = true → ℓ = κ) → ∀ (α:Type) [MeasurableSpace α] (ν:ℕ → MeasureTheory.Measure α) (μ ρ:ℕ → MeasureTheory.Measure (α × ℝ)) (π:ℕ → MeasureTheory.Measure ℝ) (b:ℕ → α → Fin 6 → ℝ) (P:ℕ → MvPolynomial (Fin 4) ℝ) (T n:ℕ → ℝ → ℕ) (j:(k:ℕ) → (s:ℝ) → Fin (n k s) → Fin (2 ^ T k s)) (A B:(k:ℕ) → (s:ℝ) → Fin (n k s) → Set α) (c:(k:ℕ) → (s:ℝ) → Fin (n k s) → Fin 5 → ℝ) (F:(k:ℕ) → (s:ℝ) → Fin (n k s) → MvPolynomial (Fin 4) ℝ),(fun (x:ℕ → α → ℝ → Fin 4 → ℝ) (I:(T:ℕ) → Fin (2 ^ T) → Set ℝ) => (fun z:ℕ → ℝ → ℝ → (α × ℝ) → Fin 3 → ℤ => (fun fit:ℕ → ℝ → ℝ → MvPolynomial (Fin 4) ℝ → α → Set ℝ → Prop => (∀ k,Measurable (b k) ∧ MeasureTheory.IsProbabilityMeasure (ν k) ∧ MeasureTheory.IsProbabilityMeasure (π k) ∧ μ k ≤ ENNReal.ofReal (K k) • ((ν k).prod MeasureTheory.volume) ∧ ρ k ≤ μ k ∧ μ k (Set.univ ×ˢ Set.Icc (0:ℝ) 1)ᶜ = 0 ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ρ k Set.univ ∧ (P k).totalDegree ≤ 2 ∧ (∀ᵐ l ∂ν k,|b k l 0| + |b k l 1| + |b k l 3| + |b k l 4| ≤ K k) ∧ (∀ᵐ p ∂μ k,(∀ t ∈ Set.Icc (0:ℝ) 1,|MvPolynomial.eval (x k p.1 t) (P k)| ≤ K k ∧ |MvPolynomial.eval (x k p.1 t) (MvPolynomial.pderiv (3:Fin 4) (P k))| ≤ K k ∧ |MvPolynomial.eval (x k p.1 t) (MvPolynomial.pderiv (3:Fin 4) (MvPolynomial.pderiv (3:Fin 4) (P k)))| ≤ K k) ∧ (K k)⁻¹ ≤ |MvPolynomial.eval (x k p.1 p.2) (MvPolynomial.pderiv (3:Fin 4) (P k))|)) → (∀ R:ℝ,1 < R → ∀ᶠ k in Filter.atTop,∀ r s v:ℝ,R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R → (∀ a:ℤ,π k {w:ℝ | ⌊w / (N k ^ (-v))⌋ = a} ≤ ENNReal.ofReal (K k * N k ^ (-S * v))) ∧ (∀ h:Bool,∀ (q:Fin 3 → ℤ) (a:ℤ),μ k {p | z k (N k) r p = q ∧ ⌊(if h then MvPolynomial.eval (x k p.1 p.2) (P k) else (x k p.1 p.2) 3) / (N k ^ (-s))⌋ = a} ≤ ENNReal.ofReal (K k * N k ^ (-3 * r - d * s))) ∧ (∀ h:Bool,∀ (q:Fin 3 → ℤ) (a v₀:ℤ),μ k {p | z k (N k) r p = q ∧ ⌊(if h then MvPolynomial.eval (x k p.1 p.2) (P k) else (x k p.1 p.2) 3) / (N k ^ (-s))⌋ = a ∧ ⌊b k p.1 3 / (N k ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (K k * N k ^ (-3 * r - d * s)) * π k {w:ℝ | ⌊w / (N k ^ (-v))⌋ = v₀})) → (∀ R:ℝ,1 < R → ∀ᶠ k in Filter.atTop,∀ s:ℝ,R⁻¹ ≤ s → s ≤ U → (fun (q:ℝ) (a g:ℝ → ℝ) => N k ^ (κ * s) / K k ≤ (2:ℝ) ^ T k s ∧ (2:ℝ) ^ T k s ≤ K k * N k ^ (κ * s) ∧ (∀ i,MeasurableSet (A k s i) ∧ MeasurableSet (B k s i) ∧ B k s i ⊆ A k s i) ∧ (∀ i i',i ≠ i' → j k s i = j k s i' → Disjoint (A k s i) (A k s i')) ∧ (∀ i,ENNReal.ofReal (a s ^ d * q ^ 2 * g s / K k) ≤ ν k (A k s i) ∧ ν k (A k s i) ≤ ENNReal.ofReal (K k * a s ^ d * q ^ 2 * g s) ∧ ENNReal.ofReal (q / K k) * ν k (A k s i) ≤ μ k (B k s i ×ˢ I (T k s) (j k s i)) ∧ (∀ e,|c k s i e| ≤ K k) ∧ (F k s i).totalDegree ≤ 2 ∧ (∀ l ∈ A k s i,∀ t ∈ I (T k s) (j k s i),|(x k l t) 1 - c k s i 0 - t * c k s i 1| ≤ K k * q ∧ |(x k l t) 2 - c k s i 2 - t * c k s i 3 - c k s i 4 * (x k l t) 1| ≤ K k * q * g s ∧ |b k l 4 - c k s i 3 - c k s i 4 * b k l 3| ≤ K k * g s) ∧ (∀ l ∈ B k s i,fit k (K k) (a s) (F k s i) l (I (T k s) (j k s i))) ∧ (∀ᵐ p ∂μ k,p.1 ∈ B k s i → p.2 ∈ I (T k s) (j k s i) → (K k)⁻¹ ≤ |MvPolynomial.eval (x k p.1 p.2) (MvPolynomial.pderiv (3:Fin 4) (F k s i))|) ∧ (horizontal = true → P k = MvPolynomial.X (3:Fin 4) ∧ (∀ᵐ p ∂μ k,|b k p.1 4 + b k p.1 0| ≤ N k ^ (-e₀)) ∧ |c k s i 3 + c k s i 0 + ((j k s i:ℕ) + (1:ℝ) / 2) * q * c k s i 1| + |c k s i 4 - ((j k s i:ℕ) + (1:ℝ) / 2) * q| ≤ K k * q ∧ (∃ L:Fin 4 → ℝ,F k s i = MvPolynomial.X (3:Fin 4) - (MvPolynomial.C (L 0) + MvPolynomial.C (L 1) * MvPolynomial.X (0:Fin 4) + MvPolynomial.C (L 2) * MvPolynomial.X (1:Fin 4) + MvPolynomial.C (L 3) * MvPolynomial.X (2:Fin 4)) ∧ |L 3| ≤ K k * (1 + a s / q ^ 2) ∧ ∀ l ∈ B k s i,∀ t ∈ I (T k s) (j k s i),|L 1 - (x k l t) 1 * L 3| + |L 2 + t * L 3| ≤ K k * (1 + a s / q)))) ∧ (∀ᵐ p ∂μ k,∃ i,p.1 ∈ B k s i ∧ p.2 ∈ I (T k s) (j k s i)) ∧ (∀ (i:Fin (n k s)) (v:ℝ) (v₀:ℤ),R⁻¹ ≤ v → v ≤ R → μ k {p | p.1 ∈ B k s i ∧ p.2 ∈ I (T k s) (j k s i) ∧ ⌊b k p.1 3 / (N k ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (K k * q) * ν k (A k s i) * π k {w:ℝ | ⌊w / (N k ^ (-v))⌋ = v₀})) ((2:ℝ) ^ (-(T k s:ℤ))) (fun s => N k ^ (-s)) (fun s => N k ^ (-ℓ * s))) → (∀ R:ℝ,1 < R → ∀ᶠ k in Filter.atTop,∀ s t:ℝ,R⁻¹ ≤ s → s < t → t ≤ U → ∀ i:Fin (n k t),∃ h:Fin (n k s),A k t i ⊆ A k s h ∧ I (T k t) (j k t i) ⊆ I (T k s) (j k s h)) → ∃ R:ℝ,1 < R ∧ ∀ ε:ℝ,0 < ε → ∃ᶠ k in Filter.atTop,∃ (s v:ℝ) (i:Fin (n k s)),R⁻¹ ≤ s ∧ s ≤ R ∧ R⁻¹ ≤ v ∧ v ≤ R ∧ s + v ≤ U ∧ ((∃ Q:MvPolynomial (Fin 4) ℝ,Q.totalDegree ≤ 2 ∧ (∀ e,|Q.coeff e| ≤ N k ^ R * ((1 + ∑ e ∈ (F k s i).support,|(F k s i).coeff e|) + ∑ e ∈ (P k).support,|(P k).coeff e|) ^ R) ∧ ENNReal.ofReal (N k ^ (-d * v - ε) / (2:ℝ) ^ T k s) * ν k (A k s i) ≤ ρ k {p | p.1 ∈ B k s i ∧ p.2 ∈ I (T k s) (j k s i) ∧ fit k (N k ^ ε) (N k ^ (-s - v)) Q p.1 (I (T k s) (j k s i)) ∧ N k ^ (-ε) ≤ |MvPolynomial.eval (x k p.1 p.2) (MvPolynomial.pderiv (3:Fin 4) Q)|}) ∨ (∃ z:Fin 2 → ℝ,(∀ e,|z e| ≤ N k ^ R) ∧ ENNReal.ofReal (N k ^ (-ε) / (2:ℝ) ^ T k s) * ν k (A k s i) ≤ ρ k {p | p.1 ∈ B k s i ∧ p.2 ∈ I (T k s) (j k s i) ∧ |b k p.1 4 - z 0 - z 1 * b k p.1 3| ≤ N k ^ ε * N k ^ (-ℓ * s - v)}))) (fun k H a Q l I => ∀ t ∈ I,|MvPolynomial.eval (x k l t) Q| ≤ H * a ∧ |MvPolynomial.eval (x k l t) (MvPolynomial.pderiv (3:Fin 4) Q)| ≤ H ∧ |MvPolynomial.eval (x k l t) (MvPolynomial.pderiv (3:Fin 4) (MvPolynomial.pderiv (3:Fin 4) Q))| ≤ H / a)) (fun k Nk r p e => ⌊(![p.2,(x k p.1 p.2) 1,(x k p.1 p.2) 2]:Fin 3 → ℝ) e / (Nk ^ (-r))⌋)) (fun k l t => ![t,b k l 0 + t * b k l 3,b k l 1 + t * b k l 4,b k l 2 + t * b k l 5]) (fun T j => Set.Icc (((j:ℕ):ℝ) / (2:ℝ) ^ T) ((((j:ℕ):ℝ) + 1) / (2:ℝ) ^ T)))) true (fun _ => True)) → (((fun (horizontal:Bool) (regime:ℝ → Prop) => ∀ (N K:ℕ → ℝ),(∀ k,2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → ((∀ k,1 ≤ K k) ∧ ∀ ε:ℝ,0 < ε → ∀ᶠ k in Filter.atTop,K k ≤ N k ^ ε) → ∀ d κ ℓ S U e₀:ℝ,0 ≤ d → d < 1 → 0 < κ → κ ≤ 1 → 0 < ℓ → κ ≤ ℓ → 0 < S → S ≤ 1 → 0 < U → 0 < e₀ → regime κ → (horizontal = true → ℓ = κ) → ∀ (α:Type) [MeasurableSpace α] (ν:ℕ → MeasureTheory.Measure α) (μ ρ:ℕ → MeasureTheory.Measure (α × ℝ)) (π:ℕ → MeasureTheory.Measure ℝ) (b:ℕ → α → Fin 6 → ℝ) (P:ℕ → MvPolynomial (Fin 4) ℝ) (T n:ℕ → ℝ → ℕ) (j:(k:ℕ) → (s:ℝ) → Fin (n k s) → Fin (2 ^ T k s)) (A B:(k:ℕ) → (s:ℝ) → Fin (n k s) → Set α) (c:(k:ℕ) → (s:ℝ) → Fin (n k s) → Fin 5 → ℝ) (F:(k:ℕ) → (s:ℝ) → Fin (n k s) → MvPolynomial (Fin 4) ℝ),(∀ k,∀ᵐ p ∂μ k,|b k p.1 4 + b k p.1 0| ≤ N k ^ (-e₀)) → (fun (x:ℕ → α → ℝ → Fin 4 → ℝ) (I:(T:ℕ) → Fin (2 ^ T) → Set ℝ) => (fun z:ℕ → ℝ → ℝ → (α × ℝ) → Fin 3 → ℤ => (fun fit:ℕ → ℝ → ℝ → MvPolynomial (Fin 4) ℝ → α → Set ℝ → Prop => (∀ k,Measurable (b k) ∧ MeasureTheory.IsProbabilityMeasure (ν k) ∧ MeasureTheory.IsProbabilityMeasure (π k) ∧ μ k ≤ ENNReal.ofReal (K k) • ((ν k).prod MeasureTheory.volume) ∧ ρ k ≤ μ k ∧ μ k (Set.univ ×ˢ Set.Icc (0:ℝ) 1)ᶜ = 0 ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ρ k Set.univ ∧ (P k).totalDegree ≤ 2 ∧ (∀ᵐ l ∂ν k,|b k l 0| + |b k l 1| + |b k l 3| + |b k l 4| ≤ K k) ∧ (∀ᵐ p ∂μ k,(∀ t ∈ Set.Icc (0:ℝ) 1,|MvPolynomial.eval (x k p.1 t) (P k)| ≤ K k ∧ |MvPolynomial.eval (x k p.1 t) (MvPolynomial.pderiv (3:Fin 4) (P k))| ≤ K k ∧ |MvPolynomial.eval (x k p.1 t) (MvPolynomial.pderiv (3:Fin 4) (MvPolynomial.pderiv (3:Fin 4) (P k)))| ≤ K k) ∧ (K k)⁻¹ ≤ |MvPolynomial.eval (x k p.1 p.2) (MvPolynomial.pderiv (3:Fin 4) (P k))|)) → (∀ R:ℝ,1 < R → ∀ᶠ k in Filter.atTop,∀ r s v:ℝ,R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R → (∀ a:ℤ,π k {w:ℝ | ⌊w / (N k ^ (-v))⌋ = a} ≤ ENNReal.ofReal (K k * N k ^ (-S * v))) ∧ (∀ h:Bool,∀ (q:Fin 3 → ℤ) (a:ℤ),μ k {p | z k (N k) r p = q ∧ ⌊(if h then MvPolynomial.eval (x k p.1 p.2) (P k) else (x k p.1 p.2) 3) / (N k ^ (-s))⌋ = a} ≤ ENNReal.ofReal (K k * N k ^ (-3 * r - d * s))) ∧ (∀ h:Bool,∀ (q:Fin 3 → ℤ) (a v₀:ℤ),μ k {p | z k (N k) r p = q ∧ ⌊(if h then MvPolynomial.eval (x k p.1 p.2) (P k) else (x k p.1 p.2) 3) / (N k ^ (-s))⌋ = a ∧ ⌊b k p.1 3 / (N k ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (K k * N k ^ (-3 * r - d * s)) * π k {w:ℝ | ⌊w / (N k ^ (-v))⌋ = v₀})) → (∀ R:ℝ,1 < R → ∀ᶠ k in Filter.atTop,∀ s:ℝ,R⁻¹ ≤ s → s ≤ U → (fun (q:ℝ) (a g:ℝ → ℝ) => N k ^ (κ * s) / K k ≤ (2:ℝ) ^ T k s ∧ (2:ℝ) ^ T k s ≤ K k * N k ^ (κ * s) ∧ (∀ i,MeasurableSet (A k s i) ∧ MeasurableSet (B k s i) ∧ B k s i ⊆ A k s i) ∧ (∀ i i',i ≠ i' → j k s i = j k s i' → Disjoint (A k s i) (A k s i')) ∧ (∀ i,ENNReal.ofReal (a s ^ d * q ^ 2 * g s / K k) ≤ ν k (A k s i) ∧ ν k (A k s i) ≤ ENNReal.ofReal (K k * a s ^ d * q ^ 2 * g s) ∧ ENNReal.ofReal (q / K k) * ν k (A k s i) ≤ μ k (B k s i ×ˢ I (T k s) (j k s i)) ∧ (∀ e,|c k s i e| ≤ K k) ∧ (F k s i).totalDegree ≤ 2 ∧ (∀ l ∈ A k s i,∀ t ∈ I (T k s) (j k s i),|(x k l t) 1 - c k s i 0 - t * c k s i 1| ≤ K k * q ∧ |(x k l t) 2 - c k s i 2 - t * c k s i 3 - c k s i 4 * (x k l t) 1| ≤ K k * q * g s ∧ |b k l 4 - c k s i 3 - c k s i 4 * b k l 3| ≤ K k * g s) ∧ (∀ l ∈ B k s i,fit k (K k) (a s) (F k s i) l (I (T k s) (j k s i))) ∧ (∀ᵐ p ∂μ k,p.1 ∈ B k s i → p.2 ∈ I (T k s) (j k s i) → (K k)⁻¹ ≤ |MvPolynomial.eval (x k p.1 p.2) (MvPolynomial.pderiv (3:Fin 4) (F k s i))|) ∧ (horizontal = true → P k = MvPolynomial.X (3:Fin 4) ∧ (∀ᵐ p ∂μ k,|b k p.1 4 + b k p.1 0| ≤ N k ^ (-e₀)) ∧ |c k s i 3 + c k s i 0 + ((j k s i:ℕ) + (1:ℝ) / 2) * q * c k s i 1| + |c k s i 4 - ((j k s i:ℕ) + (1:ℝ) / 2) * q| ≤ K k * q ∧ (∃ L:Fin 4 → ℝ,F k s i = MvPolynomial.X (3:Fin 4) - (MvPolynomial.C (L 0) + MvPolynomial.C (L 1) * MvPolynomial.X (0:Fin 4) + MvPolynomial.C (L 2) * MvPolynomial.X (1:Fin 4) + MvPolynomial.C (L 3) * MvPolynomial.X (2:Fin 4)) ∧ |L 3| ≤ K k * (1 + a s / q ^ 2) ∧ ∀ l ∈ B k s i,∀ t ∈ I (T k s) (j k s i),|L 1 - (x k l t) 1 * L 3| + |L 2 + t * L 3| ≤ K k * (1 + a s / q)))) ∧ (∀ᵐ p ∂μ k,∃ i,p.1 ∈ B k s i ∧ p.2 ∈ I (T k s) (j k s i)) ∧ (∀ (i:Fin (n k s)) (v:ℝ) (v₀:ℤ),R⁻¹ ≤ v → v ≤ R → μ k {p | p.1 ∈ B k s i ∧ p.2 ∈ I (T k s) (j k s i) ∧ ⌊b k p.1 3 / (N k ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (K k * q) * ν k (A k s i) * π k {w:ℝ | ⌊w / (N k ^ (-v))⌋ = v₀})) ((2:ℝ) ^ (-(T k s:ℤ))) (fun s => N k ^ (-s)) (fun s => N k ^ (-ℓ * s))) → (∀ R:ℝ,1 < R → ∀ᶠ k in Filter.atTop,∀ s t:ℝ,R⁻¹ ≤ s → s < t → t ≤ U → ∀ i:Fin (n k t),∃ h:Fin (n k s),A k t i ⊆ A k s h ∧ I (T k t) (j k t i) ⊆ I (T k s) (j k s h)) → ℓ = κ → (∃ U₁:ℝ,0 < U₁ ∧ U₁ ≤ U ∧ ∀ (m:ℕ) (σ:Fin m → ℝ),(∀ h,0 < σ h ∧ σ h ≤ U₁) → ∃ H:ℕ → ℝ,(∀ k,1 ≤ H k) ∧ (∀ ε:ℝ,0 < ε → ∀ᶠ k in Filter.atTop,H k ≤ N k ^ ε) ∧ ∀ᶠ k in Filter.atTop,∃ (M:Fin m → ℕ) (L:(h:Fin m) → Fin (n k (σ h)) → Fin (M h) → Fin 4 → ℝ),(∀ h,(M h:ℝ) ≤ H k) ∧ ENNReal.ofReal ((K k)⁻¹ / 2) ≤ ρ k {p | ∀ h,∃ (i:Fin (n k (σ h))) (u:Fin (M h)),p.1 ∈ B k (σ h) i ∧ p.2 ∈ I (T k (σ h)) (j k (σ h) i) ∧ ∀ t ∈ I (T k (σ h)) (j k (σ h) i),|(x k p.1 t) 3 - (L h i u 0 + L h i u 1 * t + L h i u 2 * (x k p.1 t) 1 + L h i u 3 * (x k p.1 t) 2)| ≤ H k * N k ^ (-σ h)}) → ((fun y:ℕ → (Fin 4 → ℝ) → α → ℝ → Fin 4 → ℝ => ∀ V:ℝ,0 < V → V ≤ U → ∃ R:ℝ,1 < R ∧ ∀ ε:ℝ,0 < ε → ∃ᶠ k in Filter.atTop,∃ (s v:ℝ) (i:Fin (n k s)),R⁻¹ ≤ s ∧ s ≤ R ∧ R⁻¹ ≤ v ∧ v ≤ R ∧ s + v ≤ V ∧ ((∃ (L:Fin 4 → ℝ) (G:MvPolynomial (Fin 4) ℝ),G.totalDegree ≤ 2 ∧ (∀ e,|G.coeff e| ≤ N k ^ R) ∧ ENNReal.ofReal (N k ^ (-d * v - ε) / (2:ℝ) ^ T k s) * ν k (A k s i) ≤ ρ k {p | p.1 ∈ B k s i ∧ p.2 ∈ I (T k s) (j k s i) ∧ (∀ t ∈ I (T k s) (j k s i),|(y k L p.1 t) 3| ≤ 1 ∧ |MvPolynomial.eval (y k L p.1 t) G| ≤ N k ^ ε * N k ^ (-s - v) ∧ |MvPolynomial.eval (y k L p.1 t) (MvPolynomial.pderiv (3:Fin 4) G)| ≤ N k ^ ε ∧ |MvPolynomial.eval (y k L p.1 t) (MvPolynomial.pderiv (3:Fin 4) (MvPolynomial.pderiv (3:Fin 4) G))| ≤ N k ^ ε / N k ^ (-s - v)) ∧ N k ^ (-ε) ≤ |MvPolynomial.eval (y k L p.1 p.2) (MvPolynomial.pderiv (3:Fin 4) G)|}) ∨ (∃ z:Fin 2 → ℝ,(∀ e,|z e| ≤ N k ^ R) ∧ ENNReal.ofReal (N k ^ (-ε) / (2:ℝ) ^ T k s) * ν k (A k s i) ≤ ρ k {p | p.1 ∈ B k s i ∧ p.2 ∈ I (T k s) (j k s i) ∧ |b k p.1 4 - z 0 - z 1 * b k p.1 3| ≤ N k ^ ε * N k ^ (-ℓ * s - v)}))) (fun k L l t => ![t,(x k l t) 1,(x k l t) 2,(x k l t) 3 - (L 0 + L 1 * t + L 2 * (x k l t) 1 + L 3 * (x k l t) 2)]))) (fun k H a Q l I => ∀ t ∈ I,|MvPolynomial.eval (x k l t) Q| ≤ H * a ∧ |MvPolynomial.eval (x k l t) (MvPolynomial.pderiv (3:Fin 4) Q)| ≤ H ∧ |MvPolynomial.eval (x k l t) (MvPolynomial.pderiv (3:Fin 4) (MvPolynomial.pderiv (3:Fin 4) Q))| ≤ H / a)) (fun k Nk r p e => ⌊(![p.2,(x k p.1 p.2) 1,(x k p.1 p.2) 2]:Fin 3 → ℝ) e / (Nk ^ (-r))⌋)) (fun k l t => ![t,b k l 0 + t * b k l 3,b k l 1 + t * b k l 4,b k l 2 + t * b k l 5]) (fun T j => Set.Icc (((j:ℕ):ℝ) / (2:ℝ) ^ T) ((((j:ℕ):ℝ) + 1) / (2:ℝ) ^ T)))) false (fun _ => True))
  := by
  intro hmesh hHraw
  have hH : HorizontalPrinciple := by
    intro α _ cfg hp heq hbasic hcaps hatlas hnested
    exact hHraw cfg.N cfg.K hp.scale hp.scale_limit hp.subpower
      cfg.d cfg.κ cfg.ℓ cfg.S cfg.U cfg.e₀ hp.dimension_nonneg hp.dimension_lt_one
      hp.rate_pos hp.rate_le_one hp.transverse_pos hp.palette_pos hp.palette_le_one
      hp.depth_pos hp.defect_pos trivial (fun _ => heq) α
      cfg.ν cfg.μ cfg.ρ cfg.π cfg.b cfg.P cfg.T cfg.n cfg.j cfg.A cfg.B cfg.c cfg.F
      hbasic hcaps hatlas hnested
  intro N K hN hNt hK d κ ℓ S U e₀ hd₀ hd₁ hκ₀ hκ₁ hℓ hκℓ hS₀ hS₁ hU he₀
    hreg hhor α _ ν μ ρ π b P T n j A B c F hcontact h1 h2 h3 h4 heq hpal
  let cfg : Data α :=
    { N := N, K := K, d := d, κ := κ, ℓ := ℓ, S := S, U := U, e₀ := e₀,
      ν := ν, μ := μ, ρ := ρ, π := π, b := b, P := P, T := T, n := n,
      j := j, A := A, B := B, c := c, F := F }
  have hp : Parameters cfg :=
    ⟨hN, hNt, hK, hd₀, hd₁, hκ₀, hκ₁, hℓ, hS₀, hS₁, hU, he₀⟩
  exact htransfer hmesh hH α cfg ⟨hp, h1, h2, h3, h4, hcontact, heq, hpal⟩

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates
