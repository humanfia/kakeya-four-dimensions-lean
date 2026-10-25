-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_terminal_grains_restoration.Defs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
/-!
# Named versions of the frozen abbreviations of o149

Each definition below copies the body of the corresponding binder of the frozen statement of
`WangZahlLot.wz_terminal_grains_restoration` (with `V = Space`, `μ = volume`,
`ι = fun p i => p i`, `M = MeasurableSet`), so that the frozen statement is definitionally the
statement of `main` in `Main.lean`.
-/

namespace WangZahlLot.Obl.wz_terminal_grains_restoration

open MeasureTheory
open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-- The frozen coordinate map `ι`. -/
def ιc : Space → Fin 3 → ℝ := fun p i => p i

/-- The frozen tube `T`. -/
def Tb (d : ℝ) (p u : Space) : Set Space := Metric.thickening d (segment ℝ p (p + u))

/-- The frozen slab `Q`. -/
def Qs (u : Space) (t r : ℝ) : Set Space := {p : Space | |inner ℝ u p - t| ≤ r}

/-- The frozen count `q`. -/
def qc (n : ℕ) (s : Set (Fin n)) : ℝ := (s.ncard : ℝ)

/-- The frozen half-overlap condition `X`. -/
def Xp (d : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ i j, i ≠ j → volume (Tb d (x i) (v i) ∩ Tb d (x j) (v j)) ≤ 1/2 * volume (Tb d (x i) (v i))

/-- The frozen Katz--Tao condition `K`. -/
def Kp (d m : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ W, Convex ℝ W → ENNReal.ofReal (qc n {i | Tb d (x i) (v i) ⊆ W} * d^2) ≤
    ENNReal.ofReal m * volume W

/-- The frozen Frostman condition `F`. -/
def Fp (d l : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ (u : Space) (t r : ℝ), ‖u‖ = 1 → 0 < r →
    ENNReal.ofReal (qc n {i | Tb d (x i) (v i) ⊆ Metric.ball (0:Space) 1 ∩ Qs u t r}) ≤
      ENNReal.ofReal (l * n) * volume (Metric.ball (0:Space) 1 ∩ Qs u t r)

/-- The frozen admissibility `A`. -/
def Ap (d η m l : ℝ) (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) : Prop :=
  0 < n ∧ (∀ i, ‖v i‖ = 1 ∧ Tb d (x i) (v i) ⊆ Metric.ball (0:Space) 1 ∧ MeasurableSet (Y i) ∧
    Y i ⊆ Tb d (x i) (v i)) ∧ Xp d n x v ∧ ENNReal.ofReal (d^η * n * d^2) ≤ ∑ i, volume (Y i) ∧
    Kp d m n x v ∧ Fp d l n x v

/-- The frozen box `P`. -/
def Pb (a b c : ℝ) (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) : Set Space :=
  {p : Space | |ιc (e (p - z)) 0| ≤ a/2 ∧ |ιc (e (p - z)) 1| ≤ b/2 ∧ |ιc (e (p - z)) 2| ≤ c/2}

/-- The frozen cover `C`. -/
def Cp (d h : ℝ) (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) (S : Finset (Fin n))
    (Z : Fin n → Set Space) (ρ : ℝ) (N : ℕ) (y w : Fin N → Space) (f : Fin n → Fin N)
    (b : Prop) : Prop :=
  (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i ∧ (i ∉ S → Z i = ∅)) ∧
  ENNReal.ofReal (d^h) * ∑ i, volume (Y i) ≤ ∑ i ∈ S, volume (Z i) ∧
  (∀ k, ‖w k‖ = 1) ∧
  (∀ i ∈ S, Tb d (x i) (v i) ⊆ Tb ρ (y (f i)) (w (f i))) ∧
  Fp ρ (d^(-h)) N y w ∧ b ∧
  (∀ k k', qc n {i | i ∈ S ∧ f i = k} ≤ d^(-h) * qc n {i | i ∈ S ∧ f i = k'}) ∧
  Xp ρ N y w ∧
  ∀ i ∈ S, qc N {k | Tb d (x i) (v i) ⊆ Tb ρ (y k) (w k)} ≤ d^(-h)

/-- The body of the frozen grain structure `H`, for given boxes `U`. -/
def HBody (d h : ℝ) (n : ℕ) (x v : Fin n → Space) (S : Finset (Fin n)) (Z : Fin n → Set Space)
    (ρ : ℝ) (N : ℕ) (y w : Fin N → Space) (f : Fin n → Fin N) (a c b g : ℝ) (L : ℕ)
    (z : Fin L → Space) (e : Fin L → Space ≃ₗᵢ[ℝ] Space) (H : Fin L → Set Space)
    (γ : Fin L → Fin N) (m : ℝ) (U : Fin L → Set Space) : Prop :=
  d ≤ a ∧ a ≤ ρ*c ∧ ρ*c ≤ c ∧ c ≤ 1 ∧
  (∀ j, MeasurableSet (H j) ∧ H j ⊆ U j ∧ U j ⊆ Tb ρ (y (γ j)) (w (γ j)) ∧
    ιc (e j (w (γ j))) 0^2 + ιc (e j (w (γ j))) 1^2 ≤ (10*ρ)^2) ∧
  (∀ j j', j ≠ j' → γ j = γ j' → Disjoint (H j) (H j')) ∧
  (∀ k, {p | ∃ j, γ j = k ∧ p ∈ H j} = {p | ∃ i ∈ S, f i = k ∧ p ∈ Z i}) ∧
  ENNReal.ofReal (d^h * L * a * (ρ*c) * c) ≤ ∑ j, volume (H j) ∧
  (∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ Z i) →
    qc n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} ∈ Set.Icc m (2*m)) ∧
  (∀ i ∈ S, ∀ j, f i = γ j → (Z i ∩ H j).Nonempty → Z i ∩ U j ⊆ H j ∧
    (∀ p ∈ Tb d (x i) (v i) ∩ frontier (U j), |ιc (e j (p - z j)) 2| = c/2) ∧
    ∀ t ∈ ({-c/2, c/2} : Set ℝ), ∃ p ∈ Tb d (x i) (v i) ∩ U j, ιc (e j (p - z j)) 2 = t) ∧
  b ≤ c ∧
  ∀ j W, Convex ℝ W →
    ENNReal.ofReal (qc L {j' | Pb (a/ρ) c c (z j') (e j') ⊆ Pb (2*a/ρ) (2*c) (2*c) (z j) (e j) ∧
      U j' ⊆ W} * (a*(ρ*c)*c)) ≤ ENNReal.ofReal g * volume W

/-- The frozen grain structure `H`. -/
def Hp (d h : ℝ) (n : ℕ) (x v : Fin n → Space) (S : Finset (Fin n)) (Z : Fin n → Set Space)
    (ρ : ℝ) (N : ℕ) (y w : Fin N → Space) (f : Fin n → Fin N) (a c b g : ℝ) : Prop :=
  ∃ (L : ℕ) (z : Fin L → Space) (e : Fin L → Space ≃ₗᵢ[ℝ] Space) (H : Fin L → Set Space)
    (γ : Fin L → Fin N) (m : ℝ),
    HBody d h n x v S Z ρ N y w f a c b g L z e H γ m (fun j => Pb a (ρ*c) c (z j) (e j))

/-- The frozen state `D`. -/
def Dp (ω ζ d h ρ c : ℝ) (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) (t : Bool) :
    Prop :=
  ∃ (S : Finset (Fin n)) (Z : Fin n → Set Space) (N : ℕ) (y w : Fin N → Space)
    (f : Fin n → Fin N) (a g : ℝ),
    Cp d h n x v Y S Z ρ N y w f True ∧ d^(1-ω/100) ≤ ρ ∧ 0 < g ∧
    (∀ (k : Fin N) (p u : Space) (r : ℝ), ‖u‖ = 1 → d ≤ r → r ≤ ρ →
      qc n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        d^(-h) * (r/ρ)^(ω*ζ/100) * qc n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i}) ∧
    Hp d h n x v S Z ρ N y w f a c 0 g ∧
    (t = true → ρ ≤ d^(ω/100) ∧ d^ζ * (ρ/d) * N/n ≤ c ∧ g ≤ d^(-ζ))

/-- The frozen below-slab condition `B`. -/
def Bp (d ρ l : ℝ) (n N : ℕ) (x v : Fin n → Space) (S : Finset (Fin n)) (y w : Fin N → Space)
    (f : Fin n → Fin N) : Prop :=
  ∀ k, ∀ (u : Space) (t r : ℝ), ‖u‖ = 1 → 0 < r →
    ENNReal.ofReal (qc n {i | i ∈ S ∧ f i = k ∧
        Tb d (x i) (v i) ⊆ Tb (2*ρ) (y k - (1/2:ℝ) • w k) (2 • w k) ∩ Qs u t r}) *
      volume (Tb (2*ρ) (y k - (1/2:ℝ) • w k) (2 • w k)) ≤
    ENNReal.ofReal (l * qc n {i | i ∈ S ∧ f i = k}) *
      volume (Tb (2*ρ) (y k - (1/2:ℝ) • w k) (2 • w k) ∩ Qs u t r)

/-- The frozen grain alternative `G`. -/
def Gp (ω d h : ℝ) (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) (S : Finset (Fin n))
    (Z : Fin n → Set Space) (ρ : ℝ) (N : ℕ) (y w : Fin N → Space) (f : Fin n → Fin N) : Prop :=
  Cp d h n x v Y S Z ρ N y w f (Bp d ρ (d^(-h)) n N x v S y w f) ∧ d^(1-ω/100) ≤ ρ ∧
    ρ ≤ d^(ω/100) ∧ ∃ a c, Hp d h n x v S Z ρ N y w f a c (d^h * (ρ/d) * N/n) (d^(-h))

/-- The frozen gain expression. -/
def Gain (σ ω α κ δ : ℝ) (n : ℕ) (Y : Fin n → Set Space) : Prop :=
  ENNReal.ofReal (κ * δ^(ω-α) * (n*δ^2) * (n*δ)^(-σ)) ≤ volume (⋃ i, Y i)

/-- The frozen broadness condition, with exponent `β` and loss `l`. -/
def Broad (δ ρ l β : ℝ) (n N : ℕ) (v : Fin n → Space) (S : Finset (Fin n))
    (Z : Fin n → Set Space) (f : Fin n → Fin N) : Prop :=
  ∀ (k : Fin N) (p u : Space) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
    qc n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
      l * (r/ρ)^β * qc n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i}

/-- The frozen analytic refinement principle `R`. -/
def Rp (σ ω β τ : ℝ) : Prop :=
  ∃ α κ η d₀ : ℝ, 0 < α ∧ 0 < κ ∧ 0 < η ∧ η ≤ τ ∧ 0 < d₀ ∧ d₀ ≤ 1/100 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Ap δ η (δ^(-η)) (δ^(-η)) n x v Y →
      ∀ (ρ : ℝ) (S : Finset (Fin n)) (Z : Fin n → Set Space) (N : ℕ) (y w : Fin N → Space)
        (f : Fin n → Fin N), Cp δ η n x v Y S Z ρ N y w f True → δ ≤ ρ → ρ ≤ 1 →
        Broad δ ρ (δ^(-η)) β n N v S Z f →
        Gain σ ω α κ δ n Y ∨
        ∃ (S' : Finset (Fin n)) (Z' : Fin n → Set Space), S' ⊆ S ∧
          (∀ i, MeasurableSet (Z' i) ∧ Z' i ⊆ Z i ∧ (i ∉ S' → Z' i = ∅)) ∧
          ENNReal.ofReal (δ^τ) * ∑ i, volume (Y i) ≤ ∑ i ∈ S', volume (Z' i) ∧
          Bp δ ρ (δ^(-τ)) n N x v S' y w f

end

end WangZahlLot.Obl.wz_terminal_grains_restoration
