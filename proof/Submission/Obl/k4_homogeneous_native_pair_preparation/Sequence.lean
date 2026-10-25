import Submission.Obl.k4_homogeneous_native_pair_preparation.Front
import Submission.Obl.k4_homogeneous_native_pair_preparation.GoodMasks
import Submission.Obl.k4_homogeneous_native_pair_preparation.DepthGrid
import Submission.Obl.k4_homogeneous_native_pair_preparation.Numerics

namespace Submission.Obl.k4_homogeneous_native_pair_preparation

open MeasureTheory Set Filter
open Submission.Obl.k4_native_grid_profile_extension.Profiles

/-- Pointwise native bounds and simultaneous density caps on a measurable mask. -/
def GoodAt (N K : ℝ) (W : ℕ)
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (P : Fin W → MvPolynomial (Fin 4) ℝ) (B : Fin W → ℝ) (f : ℝ → ℝ)
    (g : Fin W → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal)
    (G : Fin W → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal)
    (L S a u : ℝ) (depths : Finset ℝ)
    (Good : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) : Prop :=
  ∀ γ, MeasurableSet (Good γ) ∧ Good γ ⊆ E γ ∧ ∀ p ∈ Good γ,
    ‖y p.1 p.2‖ + ‖v p.1‖ ≤ K ∧
    |MvPolynomial.eval (x p.1 p.2) (P γ)| ≤ K ∧
    B γ / K ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (P γ))| ∧
    (∀ r ∈ depths, g γ r (obs (B γ) (δ N r) p) ≤ ENNReal.ofReal (N ^ (-f r + a))) ∧
    G γ u (obs (B γ) (δ N L) p, fun j : Fin 2 => ⌊v p.1 j / δ N u⌋) ≤
      ENNReal.ofReal (N ^ (-f L - S * u + a))

/-- The finite-index construction needed by the sequence proof. All numerical
losses and all analytic exceptions are explicit hypotheses. -/
def SamplePreparation : Prop :=
  ∀ M₀ D₀ : ℕ, ∃ M D : ℕ,
    ∀ (N K : ℝ) (W : ℕ) (ω : Fin W → ℝ)
      (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ)))
      (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
      (P : Fin W → MvPolynomial (Fin 4) ℝ) (B : Fin W → ℝ) (f : ℝ → ℝ)
      (g : Fin W → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal)
      (G : Fin W → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal)
      (L S h e u a c τ ε : ℝ) (depths : Finset ℝ)
      (Good : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
      (cs : ClassSample N W ω ν E B f L h M₀ D₀ τ e),
      2 ≤ N → 0 < e → τ ≤ ε →
      (∀ γ, 0 ≤ ω γ) → (∑ γ, ω γ) = 1 →
      (∀ γ, IsProbabilityMeasure (ν γ)) → (∀ γ, 0 < B γ) →
      (∀ γ, MeasurableSet (E γ)) → (∀ γ, E γ ⊆ univ ×ˢ Icc (0 : ℝ) 1) →
      1 ≤ K → K ≤ N ^ τ → (cs.ncls : ℝ) ≤ N ^ τ →
      64 * N ^ (5 * τ) ≤ N ^ ε → 192 * N ^ (τ + 2 * e) ≤ N ^ a →
      8 * N ^ (-c) ≤ N ^ (-4 * τ) →
      32 * N ^ (τ - a) ≤ N ^ (-4 * τ) → 2 * N ^ (τ - a) ≤ 1 →
      GoodAt N K W E P B f g G L S a u depths Good →
      (∑ γ, ENNReal.ofReal (ω γ) * ((ν γ).prod volume).restrict (E γ) (Good γ)ᶜ) ≤
        ENNReal.ofReal (N ^ (-c)) →
      NativeAt False 8 N W ω ν E P B f g G L S a e u (h - e) M D depths ε

/-- Frequent old systems meet every eventual numerical and typicality bound.
The finite depth grid and the format exponents are fixed before the final slack. -/
theorem native_preparation_of_samples (hstep : SamplePreparation) :
    NativePreparationStatement := by
  refine ⟨8, by norm_num, ?_⟩
  intro N K L d S η W ω ν E P B f g G hp h e u he heh hu huL hknown
  obtain ⟨M₀, D₀, hknown⟩ := hknown
  obtain ⟨M, D, hsample⟩ := hstep M₀ D₀
  have hL : 0 < L := hp.2.2.2.1
  obtain ⟨depths, hzero, hlast, hdepths, hcover⟩ := exists_depth_grid hL.le he
  obtain ⟨Good, hGood, c, hc, hbad⟩ := problem_good_masks N K L d S η W ω ν E P B f g G
    hp depths hdepths (by positivity : 0 < 8 * e) hu huL
  obtain ⟨hN2, hNt, ⟨hK1, hKsub⟩, _, _, _, _, _, ⟨Mp, Dp, hworld⟩, _⟩ := hp
  refine ⟨M, D, depths, hzero, hlast, hdepths, hcover, ?_⟩
  intro ε hε
  obtain ⟨τ, hτ, hτε, hτgap, hnum⟩ :=
    eventual_preparation_numerics N hNt M₀ hε he hc (sub_pos.mpr heh)
  have htail : ∀ᶠ k in atTop,
      K k ≤ N k ^ τ ∧
      (∑ γ, ENNReal.ofReal (ω k γ) * ((ν k γ).prod volume).restrict (E k γ) (Good k γ)ᶜ) ≤
        ENNReal.ofReal (N k ^ (-c)) ∧
      (2 * (3 * (M₀ : ℝ) + 1) * Real.logb 2 (N k) + 2) ^ 2 ≤ N k ^ τ ∧
      64 * N k ^ (5 * τ) ≤ N k ^ ε ∧
      192 * N k ^ (τ + 2 * e) ≤ N k ^ (8 * e) ∧
      8 * N k ^ (-c) ≤ N k ^ (-4 * τ) ∧
      32 * N k ^ (τ - 8 * e) ≤ N k ^ (-4 * τ) ∧
      2 * N k ^ (τ - 8 * e) ≤ 1 := by
    filter_upwards [hKsub τ hτ, hbad, hnum] with k hk hb hn
    exact ⟨hk, hb, hn⟩
  refine ((hknown τ hτ).and_eventually htail).mono ?_
  rintro k ⟨hk, hKpow, hbadk, hclasses, hslack, hgeom, hgood, hder, hfloor⟩
  obtain ⟨old⟩ := (knownAt_iff N W ω ν E B f L h M₀ D₀ τ k).mp hk
  obtain ⟨cs⟩ := exists_classSample old (hN2 k) he.le (by linarith only [hτgap])
  have hω : ∀ γ, 0 ≤ ω k γ := (hworld k).2.1
  have hωsum : (∑ γ, ω k γ) = 1 := (hworld k).2.2.1
  have hν : ∀ γ, IsProbabilityMeasure (ν k γ) := fun γ => ((hworld k).2.2.2.1 γ).1
  have hB : ∀ γ, 0 < B k γ := fun γ => ((hworld k).2.2.2.1 γ).2.1
  have hEm : ∀ γ, MeasurableSet (E k γ) :=
    fun γ => ((hworld k).2.2.2.1 γ).2.2.2.2.2.2.2.1
  have hEt : ∀ γ, E k γ ⊆ univ ×ˢ Icc (0 : ℝ) 1 :=
    fun γ => ((hworld k).2.2.2.1 γ).2.2.2.2.2.2.2.2.1
  exact hsample (N k) (K k) (W k) (ω k) (ν k) (E k) (P k) (B k) f (g k) (G k)
    L S h e u (8 * e) c τ ε depths (Good k) cs
    (hN2 k) he hτε hω hωsum hν hB hEm hEt (hK1 k) hKpow
    (cs.hncls.trans hclasses) hslack hgeom hgood hder hfloor (hGood k) hbadk

end Submission.Obl.k4_homogeneous_native_pair_preparation
