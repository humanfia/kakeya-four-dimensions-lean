import Submission.Obl.k4_scalar_candidate_original_return.Return
import Submission.Obl.k4_scalar_candidate_original_return.Fits

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 4096

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Filter
open scoped Topology

/-- The unchanged tangent laws and a finite menu of original layers. -/
structure TangentData where
  N : ℕ → ℝ
  K : ℕ → ℝ
  H : ℕ → ℝ
  d : ℝ
  κ : ℝ
  S : ℝ
  W : ℕ → ℕ
  weight : (k : ℕ) → Fin (W k) → ℝ
  prior : (k : ℕ) → Fin (W k) → Measure Line
  rho : (k : ℕ) → Fin (W k) → Measure Inc
  palette : (k : ℕ) → Fin (W k) → Measure ℝ
  count : ℕ → ℕ
  node : (k : ℕ) → ℝ → Fin (count k)
  layer : (k : ℕ) → Fin (count k) → Layer (W k)
  terminalStep : ℕ → ℝ

namespace TangentData

noncomputable def Valid (a : TangentData) : Prop :=
  TangentInput a.N a.K a.d a.κ a.S a.W a.weight a.prior a.rho a.palette
    (fun k s => Layer.T (a.layer k (a.node k s)))
    (fun k s => Layer.n (a.layer k (a.node k s)))
    (fun k s => Layer.world (a.layer k (a.node k s)))
    (fun k s => Layer.time (a.layer k (a.node k s)))
    (fun k s => Layer.prior (a.layer k (a.node k s)))
    (fun k s => Layer.u (a.layer k (a.node k s)))
    (fun k s => Layer.v (a.layer k (a.node k s)))
    (fun k s => Layer.poly (a.layer k (a.node k s))) ∧
  (∀ k, 2 ≤ a.H k ∧ (a.count k : ℝ) ≤ a.H k ∧
    ENNReal.ofReal ((a.H k)⁻¹) ≤
      ∑ g, ENNReal.ofReal (a.weight k g) * a.rho k g Set.univ) ∧
  (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, a.H k ≤ a.N k ^ ε)

noncomputable def observation (a : TangentData) (k : ℕ) (z : Inc) : Base × ℤ :=
  (![z.2, y z.1 z.2], ⌊x z.1 z.2 / a.terminalStep k⌋)

/-- Normalize a candidate minus the old graph on the full moving block rectangle. -/
noncomputable def normalizedResidual (a : TangentData) (k : ℕ) (q : Layer (a.W k))
    (s : ℝ) (i : Fin (Layer.n q)) (P : Poly) : Poly :=
  let Δ : ℝ := ((2 : ℝ) ^ Layer.T q)⁻¹
  let τ : Poly := MvPolynomial.C (((Layer.time q i : ℕ) : ℝ) * Δ) +
    MvPolynomial.C Δ * MvPolynomial.X 0
  let η : Poly := MvPolynomial.C (Layer.u q i) + MvPolynomial.C (Layer.v q i) * τ +
    MvPolynomial.C (a.K k * Δ) * MvPolynomial.X 1
  MvPolynomial.C (a.N k ^ s) * MvPolynomial.bind₁ ![τ, η] (P - Layer.poly q i)

/-- A priority assignment uses only original whole-block geometric tests. -/
noncomputable def assignment {w : ℕ} (q : Layer w) (s e : ℝ)
    (m : Fin (Layer.n q) → ℕ)
    (P : (i : Fin (Layer.n q)) → Fin (m i) → Poly)
    (i : Fin (Layer.n q)) (j : Fin (m i)) : Set Line :=
  Layer.prior q i ∩
    {l | l ∈ Fit (P i j)
        (((Layer.time q i : ℕ) : ℝ) / (2 : ℝ) ^ Layer.T q)
        ((((Layer.time q i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ Layer.T q) e ∧
      ∀ j' : Fin (m i), j' < j → l ∉ Fit (P i j')
        (((Layer.time q i : ℕ) : ℝ) / (2 : ℝ) ^ Layer.T q)
        ((((Layer.time q i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ Layer.T q) e}

/-- A finite greedy family, including the original-prior eligibility floors. -/
noncomputable def CoverAt (a : TangentData) (R center c σ C : ℝ) (k : ℕ) : Prop :=
  ∃ s : ℝ, R⁻¹ ≤ s ∧ s ≤ R ∧
  |s - center| ≤ σ / 4 ∧ |s - center| ≤ center / 2 ∧
  ∃ (m : Fin (Layer.n (a.layer k (a.node k s))) → ℕ)
    (P : (i : Fin (Layer.n (a.layer k (a.node k s)))) → Fin (m i) → Poly),
  let q := a.layer k (a.node k s)
  let e := a.N k ^ (σ - center - c)
  let A := assignment q s e m P
  (∀ i, (m i : ℝ) ≤ a.N k ^ (a.d * c + 2 * σ)) ∧
  (∀ i j, (P i j).totalDegree ≤ 2 ∧ ∀ b, |(P i j).coeff b| ≤ a.N k ^ R) ∧
  (∀ i j,
    ENNReal.ofReal (a.N k ^ (-a.d * c - σ) / (2 : ℝ) ^ Layer.T q) *
      a.prior k (Layer.world q i) (Layer.prior q i) ≤
    a.rho k (Layer.world q i) (A i j ×ˢ I (Layer.T q) (Layer.time q i))) ∧
  ENNReal.ofReal ((C * a.H k ^ 2)⁻¹) ≤
    ∑ g, ENNReal.ofReal (a.weight k g) *
      a.rho k g {z | ∃ i j, Layer.world q i = g ∧
        z.1 ∈ A i j ∧ z.2 ∈ I (Layer.T q) (Layer.time q i)}

/-- The same centered family with a small normalized coefficient range. -/
noncomputable def NormalizedCoverAt (a : TangentData) (R center c σ C α : ℝ) (k : ℕ) : Prop :=
  ∃ s : ℝ, R⁻¹ ≤ s ∧ s ≤ R ∧
  |s - center| ≤ σ / 4 ∧ |s - center| ≤ center / 2 ∧
  ∃ (m : Fin (Layer.n (a.layer k (a.node k s))) → ℕ)
    (P : (i : Fin (Layer.n (a.layer k (a.node k s)))) → Fin (m i) → Poly),
  let q := a.layer k (a.node k s)
  let e := a.N k ^ (σ - center - c)
  let A := assignment q s e m P
  (∀ i, (m i : ℝ) ≤ a.N k ^ (a.d * c + 2 * σ)) ∧
  (∀ i j, (P i j).totalDegree ≤ 2 ∧ ∀ b, |(P i j).coeff b| ≤ a.N k ^ R) ∧
  (∀ i j,
    ENNReal.ofReal (a.N k ^ (-a.d * c - σ) / (2 : ℝ) ^ Layer.T q) *
      a.prior k (Layer.world q i) (Layer.prior q i) ≤
    a.rho k (Layer.world q i) (A i j ×ˢ I (Layer.T q) (Layer.time q i))) ∧
  ENNReal.ofReal ((C * a.H k ^ 2)⁻¹) ≤
    ∑ g, ENNReal.ofReal (a.weight k g) *
      a.rho k g {z | ∃ i j, Layer.world q i = g ∧
        z.1 ∈ A i j ∧ z.2 ∈ I (Layer.T q) (Layer.time q i)} ∧
  (∀ i j b, |(normalizedResidual a k q s i (P i j)).coeff b| ≤ a.N k ^ (α * c))

/-- Only terminal information already known for the current incidence law. -/
noncomputable def TerminalKnown (a : TangentData) : Prop :=
  (∀ k, 0 < a.terminalStep k) ∧
  (∀ R : ℝ, 0 < R → ∀ᶠ k in atTop, a.terminalStep k ≤ a.N k ^ (-R)) ∧
  (∀ k ℓ g z, ((Layer.lists (a.layer k ℓ) g z).card : ℝ) ≤ a.H k) ∧
  (∀ k ℓ g i, MeasurableSet {z | i ∈ Layer.lists (a.layer k ℓ) g z}) ∧
  (∀ k ℓ g, ((fun q : Layer (a.W k) =>
    a.rho k g {z | ¬∃ i, Layer.world q i = g ∧
      z.1 ∈ Layer.prior q i ∧ z.2 ∈ I (Layer.T q) (Layer.time q i) ∧
      i ∈ Layer.lists q g (a.observation k z)} = 0) (a.layer k ℓ)))

/-- Merged geometric labels and an analytical terminal list. The merge table
and the earlier priority predicates specify the full original assignment. -/
noncomputable def ListedAt (a : TangentData) (R gain C : ℝ) (p : ℕ) (k : ℕ) : Prop :=
  ∃ s : ℝ, R⁻¹ ≤ s ∧ s ≤ R ∧
  ∃ (m : Fin (Layer.n (a.layer k (a.node k s))) → ℕ)
    (P : (i : Fin (Layer.n (a.layer k (a.node k s)))) → Fin (m i) → Poly)
    (e : ℝ) (n : ℕ)
    (parent : Fin n → Fin (Layer.n (a.layer k (a.node k s))))
    (bin : (i : Fin (Layer.n (a.layer k (a.node k s)))) → Fin (m i) → Fin n)
    (Q : Fin n → Poly)
    (lists : Fin (a.W k) → (Base × ℤ) → Finset (Fin n)),
  let q := a.layer k (a.node k s)
  let A := fun j => {l | ∃ i h, bin i h = j ∧ l ∈ assignment q s e m P i h}
  (∀ i, (m i : ℝ) ≤ a.N k ^ R) ∧
  (n : ℝ) ≤ (Layer.n q : ℝ) * a.N k ^ R ∧
  0 ≤ e ∧ e ≤ a.N k ^ R ∧
  (∀ i h, parent (bin i h) = i) ∧
  (∀ i h, (P i h).totalDegree ≤ 2 ∧ ∀ b, |(P i h).coeff b| ≤ a.N k ^ R) ∧
  (∀ j, (Q j).totalDegree ≤ 2 ∧ ∀ b, |(Q j).coeff b| ≤ a.N k ^ R) ∧
  (∀ j, ∀ l ∈ A j, ∀ t ∈ I (Layer.T q) (Layer.time q (parent j)),
    |x l t - MvPolynomial.eval ![t, y l t] (Q j)| ≤ a.N k ^ (-s - gain)) ∧
  (∀ g z, ((lists g z).card : ℝ) ≤ C * a.H k ^ p) ∧
  (∀ g j, MeasurableSet {z | j ∈ lists g z}) ∧
  ENNReal.ofReal ((C * a.H k ^ p)⁻¹) ≤
    ∑ g, ENNReal.ofReal (a.weight k g) * a.rho k g
      {z | ∃ j, Layer.world q (parent j) = g ∧ z.1 ∈ A j ∧
        z.2 ∈ I (Layer.T q) (Layer.time q (parent j)) ∧
        j ∈ lists g (a.observation k z)}

end TangentData

/-- The generic tangent fields associated to an original prepared witness. -/
noncomputable def PreparedData.tangentData (a : PreparedData) : TangentData where
  N := a.tangent
  K := a.rK
  H := a.H
  d := a.rd
  κ := a.κ
  S := a.rS
  W := fun k => W (a.p k) (a.sm k)
  weight := fun k => ω (a.p k) (a.sm k)
  prior := fun k => ν (a.p k) (a.sm k)
  rho := a.ρ
  palette := a.π
  count := a.ct
  node := a.nd
  layer := a.ls
  terminalStep := fun k => a.original k ^ (-L (a.p k))

/-- The original sample hypotheses needed for finite encoding. This predicate
contains neither the finite guard nor the scalar improvement assertion. -/
noncomputable def EncodingCore (a : PreparedData) : Prop :=
  (∀ k, Exact (a.p k)) ∧
  (∀ k, 0 < a.sc k ∧ a.sc k ≤ 1 ∧ 2 ≤ a.H k ∧ 1 ≤ a.rM k ∧
    M (a.p k) ≤ a.rM k ∧ D (a.p k) ≤ a.rM k ∧
    L (a.p k) ≤ (a.rM k : ℝ) ∧ K (a.p k) (a.sm k) ≤ a.H k) ∧
  Tendsto a.tangent atTop atTop ∧
  (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, a.rK k ≤ a.tangent k ^ ε) ∧
  (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, a.H k ≤ a.tangent k ^ ε) ∧
  0 < a.κ ∧
  (∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, a.sc k * R < L (a.p k)) ∧
  (∀ k g, a.ρ k g ≤ mu (a.p k) (a.sm k) g) ∧
  (∀ k ℓ, ((fun q : Layer (W (a.p k) (a.sm k)) =>
    ∃ r h : ℝ,
      ChartData (a.p k) (a.rM k) r (L (a.p k)) h
        (Real.log (a.H k) / Real.log (a.original k)) true (a.sm k)
        (Layer.T q) (Layer.n q) (Layer.world q) (Layer.time q)
        (Layer.prior q) (Layer.selected q) (Layer.u q) (Layer.v q)
        (Layer.width q) (Layer.poly q) (Layer.lists q)) (a.ls k ℓ))) ∧
  (∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ R →
    (2 : ℝ) ^ Layer.T (a.ls k (a.nd k s)) ≤ a.rK k * a.tangent k ^ (a.κ * s))

/-- Comparison, coefficient bins and aggregate lists for one positive centered
scenario. The relative tolerance is chosen before the proved globalization. -/
noncomputable def Comparison : Prop :=
  ∀ a : TangentData, a.Valid → a.TerminalKnown →
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
      ∀ (R center c C : ℝ), 1 < R → 0 < center →
        R⁻¹ ≤ c → c ≤ R → 1 ≤ C →
        (∃ᶠ k in atTop, a.CoverAt R center c (θ * c) C k) →
        ∃ (R gain C' : ℝ) (p : ℕ), 1 < R ∧ 0 < gain ∧ 1 ≤ C' ∧
          ∃ᶠ k in atTop, a.ListedAt R gain C' p k

/-- Full-prior visibility controls every normalized candidate coefficient. -/
noncomputable def Visibility : Prop :=
  ∀ a : TangentData, a.Valid → ∀ α : ℝ, 0 < α →
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ θ ≤ α ∧
      ∀ (R center c C : ℝ), 1 < R → 0 < center →
        R⁻¹ ≤ c → c ≤ R → 1 ≤ C →
        (∃ᶠ k in atTop, a.CoverAt R center c (θ * c) C k) →
        ∃ᶠ k in atTop, a.NormalizedCoverAt R center c (θ * c) C α k

/-- Small normalized coefficients give aggregate original-observation bin lists. -/
noncomputable def Binning : Prop :=
  ∀ a : TangentData, a.Valid → a.TerminalKnown →
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ α →
      ∀ (R center c C : ℝ), 1 < R → 0 < center →
        R⁻¹ ≤ c → c ≤ R → 1 ≤ C →
        (∃ᶠ k in atTop, a.NormalizedCoverAt R center c (θ * c) C α k) →
        ∃ (R gain C' : ℝ) (p : ℕ), 1 < R ∧ 0 < gain ∧ 1 ≤ C' ∧
          ∃ᶠ k in atTop, a.ListedAt R gain C' p k

/-- Geometric predicates and analytical terminal lists yield actual
original charts, with separate polynomial complexity and path-slack budgets. -/
noncomputable def Encoding : Prop :=
  ∀ a : PreparedData, EncodingCore a →
    ∀ (R gain C : ℝ) (p : ℕ), 1 < R → 0 < gain → 1 ≤ C →
      (∃ᶠ k in atTop, a.tangentData.ListedAt R gain C p k) →
      ∃ (R' δ C' : ℝ) (q p' : ℕ), 1 < R' ∧ 0 < δ ∧
        ∃ᶠ k in atTop, RecoveredAt a R' δ C' q p' k

end Submission.Obl.k4_scalar_candidate_original_return
