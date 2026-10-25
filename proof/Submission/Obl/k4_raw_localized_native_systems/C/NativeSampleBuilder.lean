import Submission.Obl.k4_raw_localized_native_systems.C.CLaw
import Submission.Obl.k4_raw_localized_native_systems.C.LocalizationGeneric

/-
Adapted from this LOT tree, o178, session x0596, `NativeSampleBuilder.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# One localized native sample from a family of full-time charts

A family of full-time charts (frozen charts at depth zero and time exponent zero
with native test, unit-tangent strip frame of common width `g ≤ N^(-w)`, purely
normal centre and velocity, lists by the original observation at depth one,
disjoint assignments in each world), with measurable good sets `G c ⊆ F c` of
relative mass at least `N^(-χ)`, total good mass at least `N^(-loss)`, total
omission at most `N^(-a₀)`, and an earlier-witness certificate for the laws
`ν(A c)⁻¹ (ν ⊗ dt)|_{G c}`, is a `NativeSystemSample false` with `T = 0`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- The budgets of a family of full-time charts. -/
def cR {W C : ℕ} (ω : Fin W → ℝ) (ν : Fin W → Measure Traj) (γ : Fin C → Fin W)
    (A : Fin C → Set Traj) (a : Fin C) : ENNReal :=
  ENNReal.ofReal (ω (γ a)) * (ENNReal.ofReal (1 / (2 : ℝ) ^ 0) * ν (γ a) (A a))

/-- The native coefficients of a family of full-time charts. -/
def cCoeff {W C : ℕ} (P : Fin W → MvPolynomial (Fin 4) ℝ) (γ : Fin C → Fin W)
    (n : Fin C → Plane) (A : Fin C → Set Traj) (a : Fin C) : Traj → Fin 5 → ℝ :=
  nativeCoeff (P (γ a)) ((((0 : Fin (2 ^ 0)) : ℕ) : ℝ) / (2 : ℝ) ^ 0) (1 / (2 : ℝ) ^ 0) 0
    (stripTangent (n a)) (A a)

theorem cCoeff_eq {W C : ℕ} (P : Fin W → MvPolynomial (Fin 4) ℝ) (γ : Fin C → Fin W)
    (n : Fin C → Plane) (A : Fin C → Set Traj) (a : Fin C) :
    cCoeff P γ n A a = nativeCoeff (P (γ a)) 0 1 0 (stripTangent (n a)) (A a) := by
  simp [cCoeff]

/-- The laws of a family of full-time charts. -/
def cLaws {W C : ℕ} (ν : Fin W → Measure Traj) (γ : Fin C → Fin W) (A : Fin C → Set Traj)
    (G : Fin C → Set Inc) (a : Fin C) : Measure Inc :=
  cLaw (ν (γ a)) (A a) (G a)

/-- **One localized native sample**, for an arbitrary certificate. -/
theorem native_sample_cert_of_family (cert : CertPred) {p : Data} (hp : Valid p) {k M D : ℕ}
    {a₀ w loss χ d s m S U g : ℝ} {C : ℕ} (γC : Fin C → Fin (p.W k)) (n : Fin C → Plane)
    (int sp : Fin C → ℝ) (A : Fin C → Set Line) (F G : Fin C → Set Point)
    (lst : Fin (p.W k) → Observation → Finset (Fin C))
    (hK : p.K k ≤ p.N k ^ loss) (hloss : 0 ≤ loss) (hCM : (C : ℝ) ≤ p.N k ^ M)
    (hM : 1 ≤ p.N k ^ M)
    (hdisj : ∀ c c', c ≠ c' → γC c = γC c' → Disjoint (A c) (A c'))
    (hlst : ∀ γ o, ((lst γ o).card : ℝ) ≤ p.N k ^ loss)
    (hlstm : ∀ γ c, MeasurableSet {o | c ∈ lst γ o})
    (hchart : ∀ c, chart (p.N k) M D (p.N k ^ loss) 0 0 0 (p.B k (γC c)) (p.E k (γC c))
      (int c • n c) (sp c • n c) (stripFrame g (n c)) (p.P k (γC c)) (A c) (F c)
      (∀ z ∈ F c, c ∈ lst (γC c) (obs (p.B k (γC c)) (δ (p.N k) 1) z)))
    (hn : ∀ c, ‖n c‖ = 1) (hg : 0 < g) (hgw : g ≤ p.N k ^ (-w))
    (hGm : ∀ c, MeasurableSet (G c)) (hGF : ∀ c, G c ⊆ F c)
    (hpos : ∀ c, 0 < p.ν k (γC c) (A c))
    (hfl : ∀ c, ENNReal.ofReal (p.N k ^ (-χ)) ≤ cLaws (p.ν k) γC A G c Set.univ)
    (hχ : 8 * p.N k ^ loss ≤ p.N k ^ χ)
    (hsig : p.N k ^ loss * δ (p.N k) 1 ≤ p.N k ^ (-1 + χ))
    (hmass : ENNReal.ofReal (p.N k ^ (-loss)) ≤
      ∑ c, ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume) (G c))
    (homit : ∑ c, ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume) (F c) ≤
      ∑ c, ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume) (G c) +
        ENNReal.ofReal (p.N k ^ (-a₀)))
    (hcert : cert (p.N k) χ d s m C (cR (p.ω k) (p.ν k) γC A)
      (cLaws (p.ν k) γC A G) (cCoeff (p.P k) γC n A)) :
    NativeSampleCert cert (p.N k) (p.K k) (p.W k) (p.ω k) (p.ν k) (p.E k) (p.P k) (p.B k)
      M D a₀ w loss 1 χ d s m S U := by
  classical
  obtain ⟨M', D', hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  have hN : 0 < p.N k := hp.scale_pos k
  have hN1 : 1 ≤ p.N k := hp.scale_ge_one k
  have hprob : ∀ γ, IsProbabilityMeasure (p.ν k γ) := fun γ => ((hfmt k).2.2.2.1 γ).1
  have hAm : ∀ c, MeasurableSet (A c) := fun c => (hchart c).2.2.2.2.2.2.1
  have hFsub : ∀ c, ∀ z ∈ F c, z.1 ∈ A c ∧ z.2 ∈ Set.Icc (0 : ℝ) 1 := by
    intro c z hz
    obtain ⟨-, h2, h3, -⟩ := (hchart c).2.2.2.2.2.2.2.2.2.2.1 z hz
    refine ⟨h2, ?_⟩
    simpa using h3
  have hGA : ∀ c, G c ⊆ A c ×ˢ Set.Icc (0 : ℝ) 1 := fun c z hz =>
    let h := hFsub c z (hGF c hz)
    ⟨h.1, h.2⟩
  have hlines : ∀ c, ∀ l ∈ A c, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Matrix.toEuclideanLin (stripFrame g (n c))⁻¹ (y l t - int c • n c - t • (sp c • n c))‖ ≤
        p.N k ^ loss ∧
      |MvPolynomial.eval (x l t) (p.P k (γC c))| ≤ p.N k ^ loss * δ (p.N k) 0 ∧
      |MvPolynomial.eval (x l t) (MvPolynomial.pderiv 3 (p.P k (γC c)))| ≤
        p.N k ^ loss * p.B k (γC c) ∧
      |MvPolynomial.eval (x l t) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 (p.P k (γC c))))| ≤
        p.N k ^ loss * p.B k (γC c) ^ 2 / δ (p.N k) 0 := by
    intro c l hl t ht
    have := ((hchart c).2.2.2.2.2.2.2.2.2.1 l hl).2.2 t (by simpa using ht)
    exact this
  have hκ0 : 0 ≤ p.N k ^ loss := by positivity
  have hY : ∀ c, ∀ l ∈ A c, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |n c 1 * x l t 1 - n c 0 * x l t 2| ≤ p.N k ^ loss := by
    intro c l hl t ht
    have hfr := (hlines c l hl t ht).1
    rw [stripFrame_inv (hn c) hg.ne', stripFrameInv_apply] at hfr
    have h0 := (abs_coord_le_norm_fin2 _ 0).trans hfr
    have hz0 : (WithLp.toLp 2 ![n c 1 * (y l t - int c • n c - t • (sp c • n c)) 0 -
        n c 0 * (y l t - int c • n c - t • (sp c • n c)) 1,
        inner ℝ (n c) (y l t - int c • n c - t • (sp c • n c)) / g] : Plane) 0 =
        n c 1 * x l t 1 - n c 0 * x l t 2 := by
      show n c 1 * (y l t - int c • n c - t • (sp c • n c)) 0 -
        n c 0 * (y l t - int c • n c - t • (sp c • n c)) 1 = _
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      simp [y]
      ring
    rw [hz0] at h0
    exact h0
  have hX : ∀ c, ∀ l ∈ A c, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |MvPolynomial.eval (x l t) (p.P k (γC c))| ≤ p.N k ^ loss := by
    intro c l hl t ht
    have := (hlines c l hl t ht).2.1
    rwa [delta_zero, mul_one] at this
  have hcoeffm : ∀ c, Measurable (cCoeff (p.P k) γC n A c) := by
    intro c
    rw [cCoeff_eq, nativeCoeff_eq_clipped]
    exact clippedScalarCoeff_measurable _ _ _ _ _ (hAm c)
  have hcoeffb : ∀ c l i, |cCoeff (p.P k) γC n A c l i| ≤ p.N k ^ χ := by
    intro c l i
    rw [cCoeff_eq]
    exact (cCoeff_bound (p.P k (γC c)) (n c) hκ0 (hY c) (hX c) l i).trans hχ
  have hNχ : 1 ≤ p.N k ^ χ := by linarith [hκ0, Real.one_le_rpow hN1 hloss]
  have hRlaw : ∀ c, cR (p.ω k) (p.ν k) γC A c * cLaws (p.ν k) γC A G c Set.univ =
      ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume) (G c) := by
    intro c
    have := hprob (γC c)
    simp only [cR, cLaws, cLaw_univ, pow_zero, div_one, ENNReal.ofReal_one, one_mul]
    rw [mul_assoc, ← mul_assoc (p.ν k (γC c) (A c)),
      ENNReal.mul_inv_cancel (hpos c).ne' (measure_ne_top _ _), one_mul]
  have hδ1 : δ (p.N k) 1 ≤ 1 := by
    unfold δ
    have : (0 : ℝ) ≤ Real.log (p.N k) / Real.log 2 :=
      div_nonneg (Real.log_nonneg hN1) (Real.log_nonneg (by norm_num))
    have h0 : 0 ≤ (⌊1 * Real.log (p.N k) / Real.log 2⌋ : ℤ) := by
      apply Int.floor_nonneg.2; simpa using this
    calc (2 : ℝ) ^ (-(⌊1 * Real.log (p.N k) / Real.log 2⌋ : ℤ)) ≤ (2 : ℝ) ^ (0 : ℤ) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = 1 := by simp
  have hδpos : 0 < δ (p.N k) 1 := by unfold δ; positivity
  refine ⟨0, C, γC, fun _ => 0, fun c => int c • n c, fun c => sp c • n c,
    fun c => stripFrame g (n c), A, F, lst, fun _ => 0, fun c => stripTangent (n c),
    cLaws (p.ν k) γC A G, fun c => cBase (n c),
    fun c => cSignal (p.P k (γC c)) (p.B k (γC c)) (δ (p.N k) 1), ?_⟩
  intro q t₀ expand coeff budget R
  have hq : q = 1 := by simp [q]
  have hexp : ∀ c, expand c = id := by
    intro c
    funext z
    simp [expand, t₀, q]
  have hbud : ∀ c, budget c = p.ν k (γC c) (A c) := by
    intro c
    simp [budget, q]
  refine ⟨hK, ?_, hCM, ?_, hlst, hlstm, ?_, ?_, ?_, ?_, ?_, hcert, ?_⟩
  · rw [pow_zero]; exact Real.one_le_rpow hN1 (by linarith)
  · intro c c' hne hγ _
    exact hdisj c c' hne hγ
  · intro c
    have h0 : ((((fun _ : Fin C => (0 : Fin (2 ^ 0))) c : ℕ)) : ℝ) = 0 := by simp
    rw [h0]
    exact hchart c
  · intro c
    refine ⟨by simp; positivity, fun i => ?_, by rw [hq]; simpa using hM⟩
    have hn0 : |n c 0| ≤ 1 := (abs_coord_le_norm_fin2 _ 0).trans (hn c).le
    have hn1 : |n c 1| ≤ 1 := (abs_coord_le_norm_fin2 _ 1).trans (hn c).le
    fin_cases i
    · simp; positivity
    · exact hn1.trans hM
    · simp only [Fin.reduceFinMk, stripTangent_two, abs_neg]
      exact hn0.trans hM
  · -- weighted budgets
    calc ∑ c, R c = ∑ c, ENNReal.ofReal (p.ω k (γC c)) * p.ν k (γC c) (A c) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          show ENNReal.ofReal (p.ω k (γC c)) * budget c = _
          rw [hbud]
      _ ≤ 1 := weighted_prior_sum_le hp γC A hAm hdisj
  · intro c
    have := hprob (γC c)
    refine ⟨?_, hfl c, measurable_cBase _, measurable_cSignal _ _ _, ?_, ?_, ?_⟩
    · exact cLaw_regular (d := d) (s := s) (m := m) (S := S) (U := U) (hGm c) (hGA c) (hpos c)
        hNχ (hcoeffm c) (hcoeffb c)
    · show ∀ᵐ z ∂(cLaw (p.ν k (γC c)) (A c) (G c)), _
      refine Measure.ae_smul_measure ?_ _
      refine ae_restrict_of_forall_mem (hGm c) fun z hz => ?_
      obtain ⟨hzA, hzt⟩ := hGA c hz
      rw [hexp c]
      simp only [id]
      have hcz : coeff c = nativeCoeff (p.P k (γC c)) 0 1 0 (stripTangent (n c)) (A c) :=
        cCoeff_eq (p.P k) γC n A c
      rw [hcz]
      constructor
      · rw [cBase_obs, cCoeff_scalarY _ _ hzA]
      · rw [cCoeff_scalarX _ ((hfmt k).2.2.2.1 (γC c)).2.2.2.2.1 _ hzA]
        have hl := hlines c z.1 hzA z.2 hzt
        have h2 : |MvPolynomial.eval (x z.1 z.2) (MvPolynomial.pderiv 3
            (MvPolynomial.pderiv 3 (p.P k (γC c))))| ≤ p.N k ^ loss * p.B k (γC c) ^ 2 := by
          have := hl.2.2.2
          rwa [delta_zero, div_one] at this
        have := cSignal_close (p.P k (γC c)) ((hfmt k).2.2.2.1 (γC c)).2.2.2.2.1
          (hp.B_pos k (γC c)) hδpos hδ1 hκ0 z hl.2.2.1 h2
        exact this.trans hsig
    · show ∀ᵐ z ∂(cLaw (p.ν k (γC c)) (A c) (G c)), z.1 ∈ A c
      refine Measure.ae_smul_measure ?_ _
      exact ae_restrict_of_forall_mem (hGm c) fun z hz => (hGA c hz).1
    · rw [hexp c, Measure.map_id, hbud]
      show p.ν k (γC c) (A c) • cLaw (p.ν k (γC c)) (A c) (G c) ≤ _
      rw [budget_cLaw _ (hpos c)]
      exact Measure.restrict_mono (hGF c) le_rfl
  · calc ENNReal.ofReal (p.N k ^ (-loss)) ≤
          ∑ c, ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume) (G c) := hmass
      _ = ∑ c, R c * cLaws (p.ν k) γC A G c Set.univ := by
          refine Finset.sum_congr rfl fun c _ => ?_
          exact (hRlaw c).symm
  · refine ⟨rfl, fun c => ⟨rfl, stripTangent_unit (hn c)⟩,
      ⟨g, hg, hgw, fun c => stripFrame_eq_literal g (n c)⟩, ?_⟩
    calc ∑ c, ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume) (F c)
        ≤ ∑ c, ENNReal.ofReal (p.ω k (γC c)) * ((p.ν k (γC c)).prod volume) (G c) +
            ENNReal.ofReal (p.N k ^ (-a₀)) := homit
      _ = ∑ c, R c * cLaws (p.ν k) γC A G c Set.univ + ENNReal.ofReal (p.N k ^ (-a₀)) := by
          congr 1
          refine Finset.sum_congr rfl fun c _ => ?_
          exact (hRlaw c).symm

end

end Submission.Obl.k4_raw_localized_native_systems.C
