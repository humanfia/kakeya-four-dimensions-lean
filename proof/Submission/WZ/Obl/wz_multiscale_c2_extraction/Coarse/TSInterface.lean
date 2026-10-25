-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse.TSInterface.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Coarse.Basic

/-!
# Interface of the frozen two-scale decomposition (sticky Prop. 3.2)

`TwoScaleAt σ ε δ ρc n x v Y` packages the conclusions of the two-scale
decomposition of a fine family `(n, x, v, Y)` at scale `δ`, with a coarse frozen
family at scale `ρc`:

* `Y'` refines the fine shadings and keeps `δ ^ ε`-density;
* `(k, z, w, Yt)` is a `Family ε ρc` and `Separated ε ρc` family with union volume
  at most `ρc ^ (σ - ε)`;
* `a` assigns fine tubes to coarse tubes; the fine shading contracted by
  `1 - 4 ρc` about the origin lies in the coarse shading, and the directions agree
  up to `ρc / 2` (so a fine plane map of precision `ρc / 2` transfers to a coarse
  plane map of precision `ρc`);
* coarse shadings are finite unions of half-open grid cubes of side `s`, so the
  coarse multiplicity is constant on each grid cube;
* multiplicity bounds: fine lower bound on the refined union, sticky (iv) for
  each fibre, sticky (iii) and a matching lower bound for the coarse family.

`TwoScaleTheorem σ` states that every sufficiently extremal fine family has
such a decomposition at every intermediate scale.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse

open Set Metric MeasureTheory
open scoped ENNReal Pointwise

/-- The half-open grid cube of side `s` with integer corner `m`. -/
def gridCube (s : ℝ) (m : Fin 3 → ℤ) : Set Space :=
  {p | ∀ c : Fin 3, s * (m c : ℝ) ≤ p c ∧ p c < s * ((m c : ℝ) + 1)}

/-- Number of fine shadings containing a point. -/
noncomputable def fineMult {n : ℕ} (Y : Fin n → Set Space) (p : Space) : ℕ :=
  {i | p ∈ Y i}.ncard

/-- The conclusions of the two-scale decomposition at coarse scale `ρc`. -/
def TwoScaleAt (σ ε δ ρc : ℝ) (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) :
    Prop :=
  ∃ (Y' : Fin n → Set Space) (k : ℕ) (z w : Fin k → Space) (Yt : Fin k → Set Space)
    (a : Fin n → Fin k) (s : ℝ) (M : Fin k → Finset (Fin 3 → ℤ)),
    -- refinement of the fine family
    (∀ i, Y' i ⊆ Y i) ∧ (∀ i, MeasurableSet (Y' i)) ∧
    ENNReal.ofReal (δ ^ ε * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y' i) ∧
    -- the coarse family is an extremal frozen family at scale `ρc`
    Family ε ρc k z w Yt ∧ Separated ε ρc k z w ∧
    volume (⋃ j, Yt j) ≤ ENNReal.ofReal (ρc ^ (σ - ε)) ∧
    -- cover relation
    (∀ i, (1 - 4 * ρc) • Y' i ⊆ Yt (a i)) ∧
    (∀ i, (Y' i).Nonempty → min ‖v i - w (a i)‖ ‖v i + w (a i)‖ ≤ ρc / 2) ∧
    -- grid structure of the coarse shadings
    0 < s ∧ (∀ j, Yt j = ⋃ m ∈ M j, gridCube s m) ∧
    -- multiplicities
    (∀ p, p ∈ (⋃ i, Y' i) → δ ^ (2 - σ + ε) * (n : ℝ) ≤ (fineMult Y' p : ℝ)) ∧
    (∀ j p, ({i | a i = j ∧ p ∈ Y' i}.ncard : ℝ) ≤
      (δ / ρc) ^ (2 - σ - ε) * ((n : ℝ) / (k : ℝ))) ∧
    (∀ q, (fineMult Yt q : ℝ) ≤ ρc ^ (2 - σ - ε) * (k : ℝ)) ∧
    (∀ q, q ∈ (⋃ j, Yt j) → ρc ^ (2 - σ + ε) * (k : ℝ) ≤ (fineMult Yt q : ℝ)) ∧
    -- (R1) every coarse cube is reached by a contracted fine point of its fibre
    (∀ j, ∀ m ∈ M j, ∃ i, a i = j ∧ ∃ p ∈ Y' i, (1 - 4 * ρc) • p ∈ gridCube s m) ∧
    -- (R2) the underlying separated level cover at `ρ0`, with error `ε`; the coarse tubes
    -- are among its tubes (through the injection `g`)
    (∃ (ρ0 : ℝ) (k0 : ℕ) (z0 w0 : Fin k0 → Space) (g : Fin k → Fin k0),
      δ ≤ ρ0 ∧ ρc / 16 ≤ ρ0 ∧ ρ0 ≤ ρc ∧ Function.Injective g ∧ 0 < k0 ∧
      (∀ j, ‖w0 j‖ = 1) ∧
      (∀ j j', j ≠ j' → volume (tube ρ0 (z0 j) (w0 j) ∩ tube ρ0 (z0 j') (w0 j')) ≤
        (1 / 2 : ℝ≥0∞) * volume (tube ρ0 (z0 j) (w0 j))) ∧
      (∀ i, ∃! j, tube δ (x i) (v i) ⊆ tube ρ0 (z0 j) (w0 j)) ∧
      (∀ j, ∃ i, tube δ (x i) (v i) ⊆ tube ρ0 (z0 j) (w0 j)) ∧
      (∀ j j', ({i | tube δ (x i) (v i) ⊆ tube ρ0 (z0 j) (w0 j)}.ncard : ℝ) ≤
        δ ^ (-ε) * ({i | tube δ (x i) (v i) ⊆ tube ρ0 (z0 j') (w0 j')}.ncard : ℝ)) ∧
      (∀ j, ∀ W : Set Space, Convex ℝ W →
        ENNReal.ofReal (({i | tube δ (x i) (v i) ⊆ tube ρ0 (z0 j) (w0 j) ∧
          tube δ (x i) (v i) ⊆ W}.ncard : ℝ) * ρ0 ^ 2) ≤
        ENNReal.ofReal (δ ^ (-ε) *
          ({i | tube δ (x i) (v i) ⊆ tube ρ0 (z0 j) (w0 j)}.ncard : ℝ)) * volume W) ∧
      (∀ i j j', tube δ (x i) (v i) ⊆ dilatedTube ρ0 (z0 j) (w0 j) →
        tube δ (x i) (v i) ⊆ dilatedTube ρ0 (z0 j') (w0 j') → j = j') ∧
      (∀ i, (Y' i).Nonempty → tube δ (x i) (v i) ⊆ tube ρ0 (z0 (g (a i))) (w0 (g (a i))))) ∧
    -- (P1) the grid side is comparable to the coarse scale
    ρc / 16 ≤ s ∧ s ≤ ρc ∧
    -- (P2) balanced fibres
    (∀ j, ({i | a i = j ∧ (Y' i).Nonempty}.ncard : ℝ) ≤ δ ^ (-ε) * ((n : ℝ) / (k : ℝ))) ∧
    -- (P3) balanced cover: comparable fine density in every coarse cube
    (∃ θ : ℝ, 0 < θ ∧ ∀ j, ∀ m ∈ M j,
      ENNReal.ofReal θ * volume (gridCube s m) ≤
        volume ((⋃ i, (1 - 4 * ρc) • Y' i) ∩ gridCube s m) ∧
      volume ((⋃ i, (1 - 4 * ρc) • Y' i) ∩ gridCube s m) ≤
        ENNReal.ofReal (δ ^ (-ε) * θ) * volume (gridCube s m))

/-- Frozen sticky Prop. 3.2: for every output error there is an input error and a
cutoff such that every input-extremal family decomposes at every intermediate
scale, with a coarse scale comparable to the requested one. -/
def TwoScaleTheorem (σ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η d0 : ℝ, 0 < η ∧ 0 < d0 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1 / 100 : ℝ) →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Family η δ n x v Y → Separated η δ n x v →
      volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - η)) →
      ∀ r : ℝ, δ ^ (1 - ε) ≤ r → r ≤ δ ^ ε →
        ∃ ρc : ℝ, r ≤ ρc ∧ ρc ≤ δ ^ (-ε) * r ∧ TwoScaleAt σ ε δ ρc n x v Y

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse
