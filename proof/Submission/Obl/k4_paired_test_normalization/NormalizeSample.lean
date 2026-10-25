-- Adapted from this LOT tree, o156, session x0524, commit86ade225;
-- Submission/Obl/k4_terminal_local_sheet_pairing/NormalizeSample.lean. Existing attribution comments are retained below.

import Submission.Obl.k4_paired_test_normalization.FiniteNormalization
import Submission.Obl.k4_paired_test_normalization.SampleLaw
import Submission.Obl.k4_paired_test_normalization.ReplaceTests
import Submission.Obl.k4_paired_test_normalization.NormalizationBounds
import Submission.Obl.k4_paired_test_normalization.NormalizationMass

namespace Submission.Obl.k4_paired_test_normalization.NormalizationStep

open Set Metric MeasureTheory MvPolynomial

noncomputable def normalizationBaseVolume : ENNReal :=
  volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 8))

theorem normalizationBaseVolume_ne_top : normalizationBaseVolume ≠ ⊤ :=
  (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 8)).measure_ne_top

/-- Normalize the exact finite sample of the proposed child, with the original
world weights, moving frames and format witnesses retained. -/
theorem normalize_sample :
    ∃ C : ℝ, 0 < C ∧ ∀ (Nk : ℝ) (Wk : ℕ)
      (ωk : Fin Wk → ℝ) (νk : Fin Wk → Measure Trajectory)
      (Ek : Fin Wk → Set Incidence) (Bk : Fin Wk → ℝ)
      (L dc a h : ℝ) (M D M' : ℕ) (ε ε' : ℝ)
      (d : TestedSample False 4 Nk Wk ωk νk Ek Bk L dc a h M D ε),
      (∀ γ, 0 ≤ ωk γ) → (∑ γ, ωk γ = 1) →
      NormalizationBounds Nk L a C normalizationBaseVolume.toReal M M' →
      ε ≤ a → ε ≤ ε' →
      Nonempty (TestedSample True 2 Nk Wk ωk νk Ek Bk L dc (100 * a) h M' D ε') := by
  classical
  obtain ⟨C, hC, hnormalize⟩ := finite_test_normalization
  refine ⟨C, hC, ?_⟩
  intro Nk Wk ωk νk Ek Bk L dc a h M D M' ε ε' d hω hωsum hb hεa hε'
  have hN1 : 1 ≤ Nk := by linarith [hb.N_two]
  have hNp : 0 < Nk := by linarith
  have hδp := δ_pos Nk L
  let cutoff : ℝ := (δ Nk L)⁻¹ * Nk ^ (-(30 * a))
  let ρ : ℝ := δ Nk L * Nk ^ a
  let η : ℝ := Nk ^ (-(25 * a))
  let θ : ℝ := Nk ^ (-(10 * a))
  let b₀ : ℝ := Nk ^ (-(3 * a))
  let bt (s : Fin d.m) : ℝ := d.worldWeight (d.world s) * d.β s
  have hbt (s : Fin d.m) : 0 ≤ bt s :=
    mul_nonneg (d.worldWeight_nonneg hω _) (d.hβ s).1
  have hcrossEq : 2 * cutoff * ρ = 2 * Nk ^ (-(29 * a)) :=
    normalization_cross_eq hNp hδp.ne'
  have hmeas (i j : Fin d.m) : MeasurableSet (tagPair d.world d.H i j) :=
    measurableSet_tagPair d.world d.H (fun i j => (d.hH i j).1) i j
  have hdisj : ∀ j, Pairwise fun i k =>
      Disjoint (tagPair d.world d.H i j) (tagPair d.world d.H k j) :=
    tagPair_disjoint_columns d.world d.H (fun j i k hik _ => d.disjoint_columns j hik)
  have hpoint (s : Fin d.m) (p : Fin Wk × PairPoint)
      (hp : p ∈ (⋃ j, tagPair d.world d.H s j) ∪ (⋃ j, tagPair d.world d.H j s)) :
      ‖d.basePoint s p.2‖ ≤ 1 / 8 ∧
      |eval (Fin.snoc (fun k => d.basePoint s p.2 k) (d.hiddenPoint s p.2)) (d.P s)| ≤ ρ ∧
      Nk ^ (-a) ≤ |eval (Fin.snoc (fun k => d.basePoint s p.2 k) (d.hiddenPoint s p.2))
        (pderiv (3 : Fin 4) (d.P s))| ∧
      |eval (Fin.snoc (fun k => d.basePoint s p.2 k) (d.hiddenPoint s p.2))
        (pderiv (3 : Fin 4) (d.P s))| ≤ Nk ^ a := by
    rw [tagPair_active d.world d.H d.common_world] at hp
    exact d.raw_point_tests s p.2 hp.2
  obtain ⟨R, K, hR, htests, hK, hgood, hloss⟩ := hnormalize d.law
    (tagPair d.world d.H) d.P (fun s p => d.basePoint s p.2)
    (fun s p => d.hiddenPoint s p.2) bt cutoff (Nk ^ M) ρ (Nk ^ a) (Nk ^ (-a)) b₀ η θ
    hmeas hdisj (fun s => (d.hP s).1) (fun s => (d.hP s).2.1)
    (fun s => (d.measurable_basePoint s).comp measurable_snd) hbt hpoint
    (d.tagged_density_source hω) (d.tagged_density_witness hω)
    (by dsimp [cutoff]; positivity) (by positivity) (by dsimp [ρ]; positivity)
    (by positivity) (by positivity) (by dsimp [b₀]; positivity)
    (le_min hb.anchor (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith [hb.a_pos])))
    (by dsimp [η]; positivity) (by dsimp [θ]; positivity)
    (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith [hb.a_pos]))
    (by simpa only [hcrossEq] using hb.raw_error)
    (by simpa only [hcrossEq] using hb.cross_error) hb.sublevel
  let H' (i j : Fin d.m) : Set PairPoint := (fun p => (d.world i, p)) ⁻¹' K i j
  have hH'm (i j : Fin d.m) : MeasurableSet (H' i j) :=
    (hK i j).1.preimage (measurable_const.prodMk measurable_id)
  have hsub (i j : Fin d.m) : H' i j ⊆ d.H i j := fun _ hp => ((hK i j).2 hp).2
  have hRglobal (s : Fin d.m) :
      (R s).totalDegree ≤ 2 ∧ (∀ e, |(R s).coeff e| ≤ Nk ^ M') ∧
      |eval (0 : Fin 4 → ℝ) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (R s)))| ≤ (δ Nk L)⁻¹ ∧
      (disc (R s)).totalDegree ≤ 2 ∧ (∀ e, |(disc (R s)).coeff e| ≤ Nk ^ (100 * a)) := by
    refine ⟨(hR s).1, fun e => ((hR s).2.2.1 e).trans hb.coeff, ?_,
      (hR s).2.2.2.1, fun e => ((hR s).2.2.2.2 e).trans ?_⟩
    · rw [Submission.Obl.k4_quadratic_atlas_normalization.second_pderiv_eq_curvature
        (R s) (hR s).1, eval_C]
      exact (hR s).2.1.trans hb.curvature
    · exact Real.one_le_rpow hN1 (by linarith [hb.a_pos])
  have htst (i j : Fin d.m) (p : PairPoint) (hp : p ∈ H' i j) :
      SplitStatements.tst Nk (100 * a) (δ Nk L) (R i) (R j)
        (base d.T ((d.j (d.frame i) : ℕ) : ℝ) d.κ (d.c (d.frame i))
          (d.u (d.frame i)) (d.Q (d.frame i)) p.1)
        (fun t => Bk (d.γ (d.frame i)) * (x p.1 t) 3) p.2.1
        (Icc (((d.j (d.frame i) : ℕ) : ℝ) / (2 : ℝ) ^ d.T)
          ((((d.j (d.frame i) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ d.T)) True := by
    have hold := (d.hH i j).2 p (hsub i j hp)
    have hfr := hold.2.2.2.2.1
    have hraw := hold.2.2.2.2.2
    obtain ⟨hDi, hDj, hqi, hqj⟩ := hgood i j (d.world i, p) hp
    have hDj' : η < eval (fun k => d.basePoint i p k) (disc (R j)) := by
      simpa only [TestedSample.basePoint, hfr] using hDj
    have hqj' : η / 2 ≤ (eval
        (Fin.snoc (fun k => d.basePoint i p k) (d.hiddenPoint i p))
        (pderiv (3 : Fin 4) (R j))) ^ 2 := by
      simpa only [TestedSample.basePoint, TestedSample.hiddenPoint, TestedSample.world, hfr] using hqj
    let y₀ : Fin 4 → ℝ := Fin.snoc (fun k => d.basePoint i p k) (d.hiddenPoint i p)
    have hpoint' (s : Fin d.m)
        (hv : |eval y₀ (d.P s)| ≤ ρ)
        (hd : |eval y₀ (pderiv (3 : Fin 4) (d.P s))| ≤ Nk ^ a)
        (hD : η < eval (fun k => d.basePoint i p k) (disc (R s)))
        (hq : η / 2 ≤ (eval y₀ (pderiv (3 : Fin 4) (R s))) ^ 2) :
        |eval y₀ (R s)| ≤ δ Nk L * Nk ^ (100 * a) ∧
        Nk ^ (-(100 * a)) ≤ |eval y₀ (pderiv (3 : Fin 4) (R s))| ∧
        |eval y₀ (pderiv (3 : Fin 4) (R s))| ≤ Nk ^ (100 * a) ∧
        (True → Nk ^ (-(100 * a)) ≤ eval (fun k => d.basePoint i p k) (disc (R s))) := by
      have hh := htests s y₀ hv hd
      have hsq := hb.deriv_floor_sq.trans (hb.derivative_square.trans hq)
      have hfloor : Nk ^ (-(100 * a)) ≤ |eval y₀ (pderiv (3 : Fin 4) (R s))| := by
        simpa only [abs_of_pos (Real.rpow_pos_of_pos hNp (-(100 * a)))] using (sq_le_sq.mp hsq)
      exact ⟨hh.1.trans hb.value, hfloor, hh.2.1.trans hb.deriv,
        fun _ => hb.disc_floor.trans hD.le⟩
    constructor
    · intro R₀ hR₀
      rcases hR₀ with rfl | rfl
      · have hr := hraw.1 (d.P i) (Or.inl rfl)
        exact hpoint' i hr.1 hr.2.2.1 hDi hqi
      · have hr := hraw.1 (d.P j) (Or.inr rfl)
        exact hpoint' j hr.1 hr.2.2.1 hDj' hqj'
    · intro t ht
      have hr := hraw.2 t ht
      have hn := htests i _ hr.1 hr.2
      exact ⟨hn.1.trans hb.value, hn.2.1.trans hb.deriv⟩
  have hbudget := d.weighted_beta_budget hN1 hω hωsum
  have hlossSmall :
      2 * (∑ s, ENNReal.ofReal (bt s) *
        (ENNReal.ofReal (128 * θ) * normalizationBaseVolume)) ≤
          ENNReal.ofReal (Nk ^ (-(6 * a))) := by
    exact (normalization_loss_budget bt hbt (sq_nonneg _) (by dsimp [θ]; positivity)
      hbudget normalizationBaseVolume normalizationBaseVolume_ne_top).trans
        (ENNReal.ofReal_le_ofReal hb.mass)
  have hκp : 0 < d.κ := by linarith [d.κ_one]
  have hκa : d.κ ≤ Nk ^ a := d.κ_le.trans (Real.rpow_le_rpow_of_exponent_le hN1 hεa)
  have hInv : (Nk ^ a)⁻¹ ≤ d.κ⁻¹ := by
    rw [← one_div, ← one_div]
    exact (div_le_div_iff₀ (Real.rpow_pos_of_pos hNp a) hκp).mpr (by simpa using hκa)
  have hlossκ : ENNReal.ofReal (Nk ^ (-(6 * a))) ≤ ENNReal.ofReal (2 * d.κ⁻¹) := by
    apply ENNReal.ofReal_le_ofReal
    calc
      Nk ^ (-(6 * a)) ≤ Nk ^ (-a) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [hb.a_pos])
      _ = (Nk ^ a)⁻¹ := Real.rpow_neg hNp.le a
      _ ≤ d.κ⁻¹ := hInv
      _ ≤ 2 * d.κ⁻¹ := by have hh := inv_nonneg.mpr hκp.le; linarith
  have hrow (H₀ : Fin d.m → Fin d.m → Set PairPoint) (s : Fin d.m) :
      (⋃ j, H₀ s j) = {p | ∃ j, p ∈ H₀ s j} := by ext p; simp
  have hstart : ENNReal.ofReal (4 * d.κ⁻¹) ≤
      ∑ s, d.law (⋃ j, tagPair d.world d.H s j) := by
    rw [d.weighted_rows_mass hω d.H (fun i j => (d.hH i j).1)]
    simpa only [hrow, TestedSample.world] using d.hcoverage
  have hcover := coverage_four_to_two hκp hstart hloss (hlossSmall.trans hlossκ)
  rw [d.weighted_pullback_mass hω K (fun i j => (hK i j).1) (fun i j => (hK i j).2)] at hcover
  have hcoverage : ENNReal.ofReal (2 * d.κ⁻¹) ≤
      ∑ s, ENNReal.ofReal (ωk (d.γ (d.frame s)) * (2 : ℝ) ^ d.T) *
        ((νk (d.γ (d.frame s))).prod (volume.prod volume)) {p | ∃ j, p ∈ H' s j} := by
    have heqRow (s : Fin d.m) :
        (⋃ j, (fun p => (d.world s, p)) ⁻¹' K s j) = {p | ∃ j, p ∈ H' s j} := by
      ext p
      simp [H']
    refine le_trans hcover (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro s _
    rw [heqRow s]
    rfl
  exact d.replace_tests hN1 hb.M_le hε' (by linarith [hb.a_pos]) R H' hRglobal hsub
    (fun i j => ⟨hH'm i j, htst i j⟩) hcoverage

end Submission.Obl.k4_paired_test_normalization.NormalizationStep
