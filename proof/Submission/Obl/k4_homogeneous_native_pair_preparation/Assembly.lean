import Submission.Obl.k4_homogeneous_native_pair_preparation.ClassFacts
import Submission.Obl.k4_homogeneous_native_pair_preparation.SampleFacts
import Submission.Obl.k4_homogeneous_native_pair_preparation.NativeExtrapolation
import Submission.Obl.k4_homogeneous_native_pair_preparation.NativeSample
import Submission.Obl.k4_scalar_pair_atlas_assembly.Dyadic

namespace Submission.Obl.k4_homogeneous_native_pair_preparation

open MeasureTheory Set

namespace ClassSample

variable {N : ℝ} {W : ℕ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
  {B : Fin W → ℝ} {f : ℝ → ℝ} {L h : ℝ} {M D : ℕ} {τ e : ℝ}
  (cs : ClassSample N W ω ν E B f L h M D τ e)

def trimmedIncidences (b : Fin cs.C) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  cs.F b ∩ {p | p.2 < (((cs.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (cs.T + cs.s)}

theorem trimmed_measurable (b : Fin cs.C) : MeasurableSet (cs.trimmedIncidences b) :=
  (cs.hchart b).2.2.2.2.2.2.2.1.inter (measurableSet_lt measurable_snd measurable_const)

theorem trimmed_selection (b : Fin cs.C) {p : (ℕ × (Fin 6 → ℝ)) × ℝ}
    (hp : p ∈ cs.trimmedIncidences b) :
    p ∈ E (cs.γ b) ∧ p.1 ∈ cs.A b ∧
      p.2 ∈ Ico (((cs.j b : ℕ) : ℝ) / (2 : ℝ) ^ (cs.T + cs.s))
        ((((cs.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (cs.T + cs.s)) ∧
      B (cs.γ b) / cs.κ ≤
        |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (cs.R b))| := by
  have hs := (cs.hchart b).2.2.2.2.2.2.2.2.2.2.1 p hp.1
  exact ⟨hs.1, hs.2.1, ⟨hs.2.2.1.1, hp.2⟩, hs.2.2.2⟩

theorem trimmed_disjoint {b b' : Fin cs.C} (hne : b ≠ b') (hγ : cs.γ b = cs.γ b') :
    Disjoint (cs.trimmedIncidences b) (cs.trimmedIncidences b') := by
  apply disjoint_left.mpr
  intro p hp hp'
  have hs := cs.trimmed_selection b hp
  have hs' := cs.trimmed_selection b' hp'
  by_cases hj : cs.j b = cs.j b'
  · exact disjoint_left.mp (cs.hdisj b b' hne hγ hj) hs.2.1 hs'.2.1
  · exact disjoint_left.mp
      (Submission.Obl.k4_scalar_pair_atlas_assembly.halfI_disjoint (cs.T + cs.s) hj)
      hs.2.2.1 hs'.2.2.1

theorem retained_trimmed_mass_le : ENNReal.ofReal (retainedMass cs.κ cs.ncls) ≤
    ∑ b, ENNReal.ofReal (ω (cs.γ b)) * ((ν (cs.γ b)).prod volume) (cs.trimmedIncidences b) := by
  apply cs.retained_mass_le.trans
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro b _
  rw [trimmedIncidences, chart_halfOpen_mass (cs.hchart b)]

/-- All non-pair fields of the final native package, and their compatibility
with any pair masks that satisfy the original-law native pair conditions. -/
theorem native_of_pairs
    (P : Fin W → MvPolynomial (Fin 4) ℝ)
    (g : Fin W → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal)
    (G : Fin W → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal)
    (S a u K κ ε : ℝ) (depths : Finset ℝ)
    (Good : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (H : Fin cs.C → Fin cs.C → Set ((ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ)))
    (hN : 2 ≤ N) (hτε : τ ≤ ε) (hK : 0 < K)
    (hκ1 : 1 ≤ κ) (hκpow : κ ≤ N ^ ε) (hκold : cs.κ ≤ κ) (hKκ : K ≤ κ)
    (hB : ∀ γ, 0 < B γ) (hbudget : 48 * cs.κ * ((2 : ℝ) ^ cs.s) ^ 2 ≤ N ^ a)
    (hGood : GoodAt N K W E P B f g G L S a u depths Good)
    (hPairs : ∀ b b', MeasurableSet (H b b') ∧ ∀ p ∈ H b b',
      cs.γ b = cs.γ b' ∧ (cs.j b : ℕ) / 2 ^ cs.s = (cs.j b' : ℕ) / 2 ^ cs.s ∧
      (p.1, p.2.1) ∈ cs.trimmedIncidences b ∧ (p.1, p.2.2) ∈ cs.trimmedIncidences b' ∧
      (p.1, p.2.1) ∈ Good (cs.γ b) ∧ (p.1, p.2.2) ∈ Good (cs.γ b) ∧
      ∀ R' : MvPolynomial (Fin 4) ℝ, R' = cs.R b ∨ R' = cs.R b' →
        ∀ t : ℝ, t = p.2.1 ∨ t = p.2.2 →
          B (cs.γ b) * N ^ (-a) ≤
            |MvPolynomial.eval (x p.1 t) (MvPolynomial.pderiv (3 : Fin 4) R')|)
    (hcov : ENNReal.ofReal (8 * κ⁻¹) ≤
      ∑ b, ENNReal.ofReal (ω (cs.γ b) * (2 : ℝ) ^ cs.T) *
        ((ν (cs.γ b)).prod (volume.prod volume)) {p | ∃ b', p ∈ H b b'}) :
    NativeAt False 8 N W ω ν E P B f g G L S a e u (h - e)
      (3 * M + 4) (max D 1) depths ε := by
  have hN1 : 1 ≤ N := one_le_two.trans hN
  have hN0 : 0 < N := zero_lt_one.trans_le hN1
  have hκ₀ : 0 < cs.κ := zero_lt_one.trans_le cs.κ_one
  have hM : M ≤ 3 * M + 4 := by omega
  have hpow : N ^ M ≤ N ^ (3 * M + 4) := pow_le_pow_right₀ hN1 hM
  have hscales := cs.homogeneous_scale_bounds hN
  have hscalePow : N ^ (3 * M + 2) ≤ N ^ (3 * M + 4) :=
    pow_le_pow_right₀ hN1 (by omega)
  apply (nativeSample_nonempty_iff False 8 N W ω ν E P B f g G L S a e u (h - e)
    (3 * M + 4) (max D 1) depths ε).mp
  refine ⟨{
    κ := κ, κ_one := hκ1, κ_le := hκpow, T := cs.T, s := cs.s, C := cs.C,
    R₁ := cs.R₁, R₂ := cs.R₂, γ := cs.γ, j := cs.j, c := cs.c, v₀ := cs.u,
    Q := cs.Q, R := cs.R, A := cs.A, F := cs.trimmedIncidences, lst := cs.lst,
    H := H, Good := Good,
    hT := cs.hT.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hτε])),
    hC := cs.hC.trans hpow, scale_lo := cs.hs₁, scale_hi := cs.hs₂,
    R₂_pos := cs.R₂pos, R₂_le := cs.R21,
    R₁_le := hscales.1.trans hscalePow, R₂_inv := hscales.2.trans hscalePow,
    classes := fun b => ⟨cs.r₁lo b, cs.r₁hi b, cs.r₂lo b, cs.r₂hi b⟩,
    disj := cs.hdisj, charts := ?_, halfopen := fun b p hp => hp.2,
    whole := ?_, list_card := fun γ o => (cs.hlst γ o).trans hκold,
    list_format := ?_, good := GoodAt.mono_slack hGood hK hKκ (fun γ => (hB γ).le),
    pairs := ?_, coverage := hcov }⟩
  · intro b
    exact true_chart_halfOpen_mono (ν (cs.γ b))
      (fun p => b ∈ cs.lst (cs.γ b) (obs (B (cs.γ b)) (δ N L) p))
      hN hκ₀ hκold (hB _).le (by positivity) (by omega) le_rfl (cs.hchart b)
  · intro b l hl t ht
    have hw := chart_native_coarse_extension (cs.j b) hκ₀.le (hB _).le hbudget
      (cs.hchart b) l hl t ht
    refine ⟨hw.1.trans ?_, hw.2⟩
    gcongr
  · intro γ b
    refine ⟨(cs.hlstfmt γ b).1, fun i => ?_⟩
    exact Submission.Lib.K4ChartLifting.Fmt.mono ((cs.hlstfmt γ b).2 i) hpow (le_max_left _ _)
  · intro b b'
    refine ⟨(hPairs b b').1, ?_⟩
    intro p hp
    obtain ⟨hγ, hj, hF, hF', hG, hG', hd⟩ := (hPairs b b').2 p hp
    exact ⟨hγ, hj, hF, hF', hG, hG', hd, False.elim⟩

end ClassSample
end Submission.Obl.k4_homogeneous_native_pair_preparation
