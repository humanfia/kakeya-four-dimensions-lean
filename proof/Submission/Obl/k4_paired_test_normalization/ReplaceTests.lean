-- Adapted from this LOT tree, o156, session x0524, commit86ade225;
-- Submission/Obl/k4_terminal_local_sheet_pairing/ReplaceTests.lean. Existing attribution comments are retained below.

import Submission.Obl.k4_paired_test_normalization.TestedSample
import Submission.Lib.K4RepresentativeAssembly.FiniteFormat

namespace Submission.Obl.k4_paired_test_normalization.NormalizationStep

open Set MeasureTheory

namespace TestedSample

variable {cv : Prop} {lam Nk : ℝ} {Wk : ℕ}
  {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure Trajectory}
  {Ek : Fin Wk → Set Incidence} {Bk : Fin Wk → ℝ}
  {L dc a h : ℝ} {M D : ℕ} {ε : ℝ}

/-- Change only the tests and restrict the pair masks. All moving frames,
source events, lists and original laws retain their exact frozen interface. -/
theorem replace_tests (d : TestedSample cv lam Nk Wk ωk νk Ek Bk L dc a h M D ε)
    {M' : ℕ} {ε' a' lam' : ℝ} (hN : 1 ≤ Nk) (hM : M ≤ M') (hε : ε ≤ ε') (ha : a ≤ a')
    (R : Fin d.m → MvPolynomial (Fin 4) ℝ) (H' : Fin d.m → Fin d.m → Set PairPoint)
    (hR : ∀ s, (R s).totalDegree ≤ 2 ∧ (∀ e, |(R s).coeff e| ≤ Nk ^ M') ∧
      |MvPolynomial.eval (0 : Fin 4 → ℝ) (MvPolynomial.pderiv (3 : Fin 4)
        (MvPolynomial.pderiv (3 : Fin 4) (R s)))| ≤ (δ Nk L)⁻¹ ∧
      (disc (R s)).totalDegree ≤ 2 ∧ (∀ e, |(disc (R s)).coeff e| ≤ Nk ^ a'))
    (hsub : ∀ s s', H' s s' ⊆ d.H s s')
    (hH' : ∀ s s', MeasurableSet (H' s s') ∧ ∀ p ∈ H' s s',
      SplitStatements.tst Nk a' (δ Nk L) (R s) (R s')
        (base d.T ((d.j (d.frame s) : ℕ) : ℝ) d.κ (d.c (d.frame s))
          (d.u (d.frame s)) (d.Q (d.frame s)) p.1)
        (fun t => Bk (d.γ (d.frame s)) * (x p.1 t) 3) p.2.1
        (Icc (((d.j (d.frame s) : ℕ) : ℝ) / (2 : ℝ) ^ d.T)
          ((((d.j (d.frame s) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ d.T)) True)
    (hcoverage : ENNReal.ofReal (lam' * d.κ⁻¹) ≤
      ∑ s, ENNReal.ofReal (ωk (d.γ (d.frame s)) * (2 : ℝ) ^ d.T) *
        ((νk (d.γ (d.frame s))).prod (volume.prod volume)) {p | ∃ s', p ∈ H' s s'}) :
    Nonempty (TestedSample True lam' Nk Wk ωk νk Ek Bk L dc a' h M' D ε') := by
  have hpow : Nk ^ M ≤ Nk ^ M' := pow_le_pow_right₀ hN hM
  have haPow : Nk ^ a ≤ Nk ^ a' := Real.rpow_le_rpow_of_exponent_le hN ha
  have hfmt {n : ℕ} {A : Set (Fin n → ℝ)} (hf : fmt n (Nk ^ M) D A) :
      fmt n (Nk ^ M') D A :=
    Submission.Lib.K4RepresentativeAssembly.fmt_mono hf hpow le_rfl
  refine ⟨{
    κ := d.κ, κ_one := d.κ_one,
    κ_le := d.κ_le.trans (Real.rpow_le_rpow_of_exponent_le hN hε),
    σ := d.σ, σ_pos := d.σ_pos, T := d.T, m := d.m, J := d.J,
    γ := d.γ, j := d.j, c := d.c, u := d.u, Q := d.Q, frame := d.frame,
    P := R, S := d.S, H := H', β := d.β, lst := d.lst,
    hT := d.hT.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)),
    hm := d.hm.trans hpow, hJ := d.hJ.trans hpow,
    hframe := ?_, hP := ?_, hS := ?_, hdisj := d.hdisj, hlst := d.hlst,
    hlstfmt := ?_, hH := ?_, hβ := ?_, hcount := ?_, hband := ?_, hcoverage := hcoverage }⟩
  · intro b
    have hb := d.hframe b
    exact ⟨hb.1, hb.2.1.trans hpow, hb.2.2.1.trans hpow, hb.2.2.2⟩
  · intro s
    exact ⟨(hR s).1, (hR s).2.1, fun _ => (hR s).2.2⟩
  · intro s
    refine ⟨(d.hS s).1, fun i => hfmt ((d.hS s).2.1 i), ?_⟩
    intro p hp
    have hs := (d.hS s).2.2 p hp
    refine ⟨hs.1, hs.2.1.trans hpow, fun e => (hs.2.2.1 e).trans hpow, hs.2.2.2.1, ?_⟩
    intro t ht
    have ht' := hs.2.2.2.2 t ht
    exact ⟨ht'.1, ht'.2.1.trans hpow, ht'.2.2⟩
  · intro γ s
    exact ⟨(d.hlstfmt γ s).1, fun i => hfmt ((d.hlstfmt γ s).2 i)⟩
  · intro s s'
    refine ⟨(hH' s s').1, ?_⟩
    intro p hp
    have hh := (d.hH s s').2 p (hsub s s' hp)
    exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2.1, (hH' s s').2 p hp⟩
  · intro s
    refine ⟨(d.hβ s).1, (d.hβ s).2.1.trans
      (mul_le_mul_of_nonneg_left haPow d.σ_pos.le), ?_⟩
    intro U hU
    constructor
    · refine le_trans ?_ (((d.hβ s).2.2 U hU).1)
      have hs : {p : PairPoint | (∃ s', p ∈ H' s s') ∧
          base d.T ((d.j (d.frame s) : ℕ) : ℝ) d.κ (d.c (d.frame s))
            (d.u (d.frame s)) (d.Q (d.frame s)) p.1 p.2.1 ∈ U} ⊆
          {p : PairPoint | (∃ s', p ∈ d.H s s') ∧
          base d.T ((d.j (d.frame s) : ℕ) : ℝ) d.κ (d.c (d.frame s))
            (d.u (d.frame s)) (d.Q (d.frame s)) p.1 p.2.1 ∈ U} := by
        rintro p ⟨⟨s', hp⟩, hz⟩
        exact ⟨⟨s', hsub s s' hp⟩, hz⟩
      gcongr <;> assumption
    · refine le_trans ?_ (((d.hβ s).2.2 U hU).2)
      have hs : {p : PairPoint | (∃ s', p ∈ H' s' s) ∧
          base d.T ((d.j (d.frame s) : ℕ) : ℝ) d.κ (d.c (d.frame s))
            (d.u (d.frame s)) (d.Q (d.frame s)) p.1 p.2.1 ∈ U} ⊆
          {p : PairPoint | (∃ s', p ∈ d.H s' s) ∧
          base d.T ((d.j (d.frame s) : ℕ) : ℝ) d.κ (d.c (d.frame s))
            (d.u (d.frame s)) (d.Q (d.frame s)) p.1 p.2.1 ∈ U} := by
        rintro p ⟨⟨s', hp⟩, hz⟩
        exact ⟨⟨s', hsub s' s hp⟩, hz⟩
      gcongr <;> assumption
  · intro γ j
    exact (d.hcount γ j).trans (div_le_div_of_nonneg_right haPow d.σ_pos.le)
  · intro b ρ U g hρ hU hg
    have hσ : 0 ≤ d.σ := d.σ_pos.le
    have hδ : 0 < δ Nk L := by unfold δ; positivity
    have hratio : 0 ≤ (max ρ (δ Nk L) / δ Nk L) ^ dc :=
      Real.rpow_nonneg (by positivity) _
    have hs : {p : PairPoint | (∃ s s', d.frame s = b ∧ p ∈ H' s s') ∧
        base d.T ((d.j b : ℕ) : ℝ) d.κ (d.c b) (d.u b) (d.Q b) p.1 p.2.1 ∈ U ∧
        |Bk (d.γ b) * (x p.1 p.2.1) 3 -
          g (base d.T ((d.j b : ℕ) : ℝ) d.κ (d.c b) (d.u b) (d.Q b) p.1 p.2.1)| ≤ ρ} ⊆
      {p : PairPoint | (∃ s s', d.frame s = b ∧ p ∈ d.H s s') ∧
        base d.T ((d.j b : ℕ) : ℝ) d.κ (d.c b) (d.u b) (d.Q b) p.1 p.2.1 ∈ U ∧
        |Bk (d.γ b) * (x p.1 p.2.1) 3 -
          g (base d.T ((d.j b : ℕ) : ℝ) d.κ (d.c b) (d.u b) (d.Q b) p.1 p.2.1)| ≤ ρ} := by
      rintro p ⟨⟨s, s', hfr, hp⟩, hz, hw⟩
      exact ⟨⟨s, s', hfr, hsub s s' hp⟩, hz, hw⟩
    refine le_trans ?_ ((d.hband b ρ U g hρ hU hg).trans ?_)
    · gcongr <;> assumption
    · gcongr <;> assumption

end TestedSample

end Submission.Obl.k4_paired_test_normalization.NormalizationStep
