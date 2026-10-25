import Submission.Obl.k4_scalar_candidate_original_return.Defs

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Filter
open scoped Topology

noncomputable def baseBin (B r : ℝ) (p : Inc) (e : Fin 2) : ℤ :=
  ⌊(![p.2, y p.1 p.2] : Fin 2 → ℝ) e / B ^ (-r)⌋
noncomputable def hiddenBin (B s : ℝ) (p : Inc) : ℤ := ⌊x p.1 p.2 / B ^ (-s)⌋
noncomputable def velocityBin (B b v : ℝ) : ℤ := ⌊v / B ^ (-b)⌋

/-- The literal scalar tangent input, using unchanged priors and mixture weights. -/
noncomputable def TangentInput (rN rK : ℕ → ℝ) (rd κ rS : ℝ)
    (rW : ℕ → ℕ) (rω : (k : ℕ) → Fin (rW k) → ℝ)
    (rν : (k : ℕ) → Fin (rW k) → Measure Line)
    (ρ : (k : ℕ) → Fin (rW k) → Measure Inc)
    (π : (k : ℕ) → Fin (rW k) → Measure ℝ)
    (T n : ℕ → ℝ → ℕ)
    (γ : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (rW k))
    (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s))
    (A : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set Line)
    (u v : (k : ℕ) → (s : ℝ) → Fin (n k s) → ℝ)
    (F : (k : ℕ) → (s : ℝ) → Fin (n k s) → Poly) : Prop :=
  (∀ k, 2 ≤ rN k) ∧ Tendsto rN atTop atTop ∧
  ((∀ k, 1 ≤ rK k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, rK k ≤ rN k ^ ε) ∧
  0 ≤ rd ∧ rd < 1 ∧ 0 < κ ∧ κ ≤ 1 ∧ 0 < rS ∧
  (∀ k, (∀ rg, 0 ≤ rω k rg) ∧ (∑ rg, rω k rg) = 1 ∧
    (∀ rg, IsProbabilityMeasure (rν k rg) ∧ IsProbabilityMeasure (π k rg) ∧
      (∀ᵐ l ∂rν k rg, ∀ e, |l.2 e| ≤ rK k) ∧
      ρ k rg ≤ ENNReal.ofReal (rK k) • ((rν k rg).prod volume) ∧
      ρ k rg (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0) ∧
    ENNReal.ofReal ((rK k)⁻¹) ≤ ∑ rg, ENNReal.ofReal (rω k rg) * ρ k rg Set.univ) ∧
  (∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ (rg : Fin (rW k)) (r s b : ℝ),
    R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ b → b ≤ R →
    (∀ c : ℤ, π k rg {v | velocityBin (rN k) b v = c} ≤
      ENNReal.ofReal (rK k * rN k ^ (-rS * b))) ∧
    (∀ (q : Fin 2 → ℤ) (c : ℤ),
      ρ k rg {p | baseBin (rN k) r p = q ∧ hiddenBin (rN k) s p = c} ≤
      ENNReal.ofReal (rK k * rN k ^ (-2 * r - rd * s))) ∧
    (∀ (q : Fin 2 → ℤ) (c e : ℤ),
      ρ k rg {p | baseBin (rN k) r p = q ∧ hiddenBin (rN k) s p = c ∧
        velocityBin (rN k) b (p.1.2 1) = e} ≤
      ENNReal.ofReal (rK k * rN k ^ (-2 * r - rd * s)) *
        π k rg {v | velocityBin (rN k) b v = e})) ∧
  (∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ R →
    rN k ^ (κ * s) / rK k ≤ (2 : ℝ) ^ T k s ∧
    (2 : ℝ) ^ T k s ≤ rK k * rN k ^ (κ * s) ∧
    (∀ i, MeasurableSet (A k s i)) ∧
    (∀ i i', i ≠ i' → γ k s i = γ k s i' → j k s i = j k s i' →
      Disjoint (A k s i) (A k s i')) ∧
    (∀ i, ENNReal.ofReal (rN k ^ (-rd * s) / (rK k * (2 : ℝ) ^ T k s)) ≤
        rν k (γ k s i) (A k s i) ∧
      rν k (γ k s i) (A k s i) ≤
        ENNReal.ofReal (rK k * rN k ^ (-rd * s) / (2 : ℝ) ^ T k s) ∧
      ENNReal.ofReal ((rK k * (2 : ℝ) ^ T k s)⁻¹) * rν k (γ k s i) (A k s i) ≤
        ρ k (γ k s i) (A k s i ×ˢ I (T k s) (j k s i)) ∧
      |u k s i| + |v k s i| ≤ rK k ∧ (F k s i).totalDegree ≤ 2 ∧
      (∀ t ∈ I (T k s) (j k s i), ∀ w ∈ Set.Icc (-2 : ℝ) 2,
        |MvPolynomial.eval ![t, u k s i + t * v k s i + w / (2 : ℝ) ^ T k s]
          (F k s i)| ≤ rK k) ∧
      (∀ l ∈ A k s i, ∀ t ∈ I (T k s) (j k s i),
        |y l t - u k s i - t * v k s i| ≤ rK k / (2 : ℝ) ^ T k s ∧
        |x l t - MvPolynomial.eval ![t, y l t] (F k s i)| ≤ rK k * rN k ^ (-s))) ∧
    (∀ rg : Fin (rW k),
      ρ k rg {p | ∃ i, γ k s i = rg ∧ p.1 ∈ A k s i ∧
        p.2 ∈ I (T k s) (j k s i)}ᶜ = 0))

/-- The shared prepared package in the frozen statement. -/
noncomputable def Prepared : Prop :=
  ∃ (p : ℕ → Code) (sm : ℕ → ℕ) (sc H bf rK : ℕ → ℝ) (rM ct : ℕ → ℕ)
    (nd : (k : ℕ) → ℝ → Fin (ct k))
    (dp tm : (k : ℕ) → Fin (ct k) → ℝ)
    (ls : (k : ℕ) → Fin (ct k) → Layer (W (p k) (sm k)))
    (ρ : (k : ℕ) → Fin (W (p k) (sm k)) → Measure Inc)
    (π : (k : ℕ) → Fin (W (p k) (sm k)) → Measure ℝ) (rd κ rS : ℝ),
  let N₀ := fun k => N (p k) (sm k)
  let rN := fun k => N₀ k ^ sc k
  let ac := fun k => (H k * Real.log (N₀ k)) ^ (k + 1)
  let loss := fun k => Real.log (ac k) / Real.log (N₀ k)
  let guard := fun k => 2 ^ ((rM k + k + 1) ^ 2)
  (∀ k, Exact (p k)) ∧
  (∀ k, 0 < sc k ∧ sc k ≤ 1 ∧ 2 ≤ H k ∧ 0 < bf k ∧ 1 ≤ rM k ∧
    M (p k) ≤ rM k ∧ D (p k) ≤ rM k ∧ L (p k) ≤ (rM k : ℝ) ∧
    K (p k) (sm k) ≤ H k ∧ (ct k : ℝ) ≤ H k ∧ H k ≤ N₀ k ^ (rM k : ℝ)) ∧
  Tendsto sc atTop (𝓝 0) ∧ Tendsto bf atTop (𝓝 0) ∧
  (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ac k ≤ rN k ^ ε) ∧
  (∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, sc k * R < L (p k)) ∧
  (∀ k g, ρ k g ≤ mu (p k) (sm k) g) ∧
  (∀ k, ENNReal.ofReal ((H k)⁻¹) ≤
    ∑ g, ENNReal.ofReal (ω (p k) (sm k) g) * ρ k g Set.univ) ∧
  (∀ k ℓ, let a := ls k ℓ
    0 ≤ dp k ℓ ∧ sc k * dp k ℓ < L (p k) ∧
    ChartData (p k) (rM k) (sc k * dp k ℓ) (L (p k)) (sc k * tm k ℓ)
      (Real.log (H k) / Real.log (N₀ k)) true (sm k)
      a.T a.n a.world a.time a.prior a.selected a.u a.v a.width a.poly a.lists ∧
    (∀ i, (H k * (2 : ℝ) ^ a.T)⁻¹ ≤ a.width i) ∧
    (∀ g, ρ k g {z | ∃ i, a.world i = g ∧ z ∈ a.selected i}ᶜ = 0)) ∧
  TangentInput rN rK rd κ rS (fun k => W (p k) (sm k))
    (fun k => ω (p k) (sm k)) (fun k => ν (p k) (sm k)) ρ π
    (fun k s => (ls k (nd k s)).T) (fun k s => (ls k (nd k s)).n)
    (fun k s => (ls k (nd k s)).world) (fun k s => (ls k (nd k s)).time)
    (fun k s => (ls k (nd k s)).prior) (fun k s => (ls k (nd k s)).u)
    (fun k s => (ls k (nd k s)).v) (fun k s => (ls k (nd k s)).poly) ∧
  (∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ r h : ℝ,
    R⁻¹ ≤ r → r ≤ R → h ≤ κ * r - bf k →
    ¬Chart (p k) (guard k) (sc k * r) (L (p k)) (sc k * h) (loss k) false (sm k))

/-- Chosen original samples and layers, before asserting their preparation properties. -/
structure PreparedData where
  p : ℕ → Code
  sm : ℕ → ℕ
  sc : ℕ → ℝ
  H : ℕ → ℝ
  bf : ℕ → ℝ
  rK : ℕ → ℝ
  rM : ℕ → ℕ
  ct : ℕ → ℕ
  nd : (k : ℕ) → ℝ → Fin (ct k)
  dp : (k : ℕ) → Fin (ct k) → ℝ
  tm : (k : ℕ) → Fin (ct k) → ℝ
  ls : (k : ℕ) → Fin (ct k) → Layer (W (p k) (sm k))
  ρ : (k : ℕ) → Fin (W (p k) (sm k)) → Measure Inc
  π : (k : ℕ) → Fin (W (p k) (sm k)) → Measure ℝ
  rd : ℝ
  κ : ℝ
  rS : ℝ

namespace PreparedData

noncomputable def original (a : PreparedData) (k : ℕ) : ℝ := N (a.p k) (a.sm k)
noncomputable def tangent (a : PreparedData) (k : ℕ) : ℝ := a.original k ^ a.sc k
noncomputable def allowance (a : PreparedData) (k : ℕ) : ℝ :=
  (a.H k * Real.log (a.original k)) ^ (k + 1)
noncomputable def loss (a : PreparedData) (k : ℕ) : ℝ :=
  Real.log (a.allowance k) / Real.log (a.original k)
def guard (a : PreparedData) (k : ℕ) : ℕ := 2 ^ ((a.rM k + k + 1) ^ 2)

noncomputable def Valid (a : PreparedData) : Prop :=
  let p := a.p
  let sm := a.sm
  let sc := a.sc
  let H := a.H
  let bf := a.bf
  let rK := a.rK
  let rM := a.rM
  let ct := a.ct
  let nd := a.nd
  let dp := a.dp
  let tm := a.tm
  let ls := a.ls
  let ρ := a.ρ
  let π := a.π
  let rd := a.rd
  let κ := a.κ
  let rS := a.rS
  let N₀ := fun k => N (p k) (sm k)
  let rN := fun k => N₀ k ^ sc k
  let ac := fun k => (H k * Real.log (N₀ k)) ^ (k + 1)
  let loss := fun k => Real.log (ac k) / Real.log (N₀ k)
  let guard := fun k => 2 ^ ((rM k + k + 1) ^ 2)
  (∀ k, Exact (p k)) ∧
  (∀ k, 0 < sc k ∧ sc k ≤ 1 ∧ 2 ≤ H k ∧ 0 < bf k ∧ 1 ≤ rM k ∧
    M (p k) ≤ rM k ∧ D (p k) ≤ rM k ∧ L (p k) ≤ (rM k : ℝ) ∧
    K (p k) (sm k) ≤ H k ∧ (ct k : ℝ) ≤ H k ∧ H k ≤ N₀ k ^ (rM k : ℝ)) ∧
  Tendsto sc atTop (𝓝 0) ∧ Tendsto bf atTop (𝓝 0) ∧
  (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ac k ≤ rN k ^ ε) ∧
  (∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, sc k * R < L (p k)) ∧
  (∀ k g, ρ k g ≤ mu (p k) (sm k) g) ∧
  (∀ k, ENNReal.ofReal ((H k)⁻¹) ≤
    ∑ g, ENNReal.ofReal (ω (p k) (sm k) g) * ρ k g Set.univ) ∧
  (∀ k ℓ, let a := ls k ℓ
    0 ≤ dp k ℓ ∧ sc k * dp k ℓ < L (p k) ∧
    ChartData (p k) (rM k) (sc k * dp k ℓ) (L (p k)) (sc k * tm k ℓ)
      (Real.log (H k) / Real.log (N₀ k)) true (sm k)
      a.T a.n a.world a.time a.prior a.selected a.u a.v a.width a.poly a.lists ∧
    (∀ i, (H k * (2 : ℝ) ^ a.T)⁻¹ ≤ a.width i) ∧
    (∀ g, ρ k g {z | ∃ i, a.world i = g ∧ z ∈ a.selected i}ᶜ = 0)) ∧
  TangentInput rN rK rd κ rS (fun k => W (p k) (sm k))
    (fun k => ω (p k) (sm k)) (fun k => ν (p k) (sm k)) ρ π
    (fun k s => (ls k (nd k s)).T) (fun k s => (ls k (nd k s)).n)
    (fun k s => (ls k (nd k s)).world) (fun k s => (ls k (nd k s)).time)
    (fun k s => (ls k (nd k s)).prior) (fun k s => (ls k (nd k s)).u)
    (fun k s => (ls k (nd k s)).v) (fun k s => (ls k (nd k s)).poly) ∧
  (∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ r h : ℝ,
    R⁻¹ ≤ r → r ≤ R → h ≤ κ * r - bf k →
    ¬Chart (p k) (guard k) (sc k * r) (L (p k)) (sc k * h) (loss k) false (sm k))


end PreparedData

lemma prepared_iff_exists_data : Prepared ↔ ∃ a : PreparedData, a.Valid := by
  constructor
  · rintro ⟨p, sm, sc, H, bf, rK, rM, ct, nd, dp, tm, ls, ρ, π, rd, κ, rS, h⟩
    exact ⟨⟨p, sm, sc, H, bf, rK, rM, ct, nd, dp, tm, ls, ρ, π, rd, κ, rS⟩, h⟩
  · rintro ⟨a, h⟩
    exact ⟨a.p, a.sm, a.sc, a.H, a.bf, a.rK, a.rM, a.ct, a.nd, a.dp, a.tm,
      a.ls, a.ρ, a.π, a.rd, a.κ, a.rS, h⟩

end Submission.Obl.k4_scalar_candidate_original_return
