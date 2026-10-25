-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/GroupStep.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0581 (with x0598), commit 583cb89a,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/GroupStep.lean (namespace renamed).

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.GroupRecovery
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.RepresentativeBins
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.RepresentativeLists
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.GroupCoords
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.GroupGlue

/-!
# One group of entries

`group_step` runs one group of `n` heavy entries through the per-group kernels: the component laws
are `ω · (ν × vol)` restricted to the covered incidences of the entries, observed by the terminal
observation `obs B δ_L`, read in group coordinates `obase`, with hidden coordinate `B w`.
`GroupRecovery` gives merged-bin lists with loss `λ R^{-ε}` and representative sheet control,
`exists_bin_root_tests` one root test per bin, and `representativeLists` turns bin lists into lists of
actual representative indices. The output is exactly the per-group input of `coreOutput_of_groups`:
measurable lists, an idempotent representative map `rep` with bin data constant on bins, root tests
for every covered line and the success inequality.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MeasureTheory Set MvPolynomial Submission.Lib.K4XInterface Submission.Lib.K4QuadraticSheets
open Submission.Lib.K4OriginalLists

/-- One group: lists, representatives and root tests from the per-group kernels. -/
theorem group_step_of_ac {d₀ : ℝ} {params : GroupParameters}
    (hGR : GroupRecovery.{0, 0} 2 d₀ params)
    {R M ε : ℝ} (hR : params.radius ≤ R) (hM : 0 < M) (hε : 0 < ε) (hεp : ε ≤ params.epsilon)
    {n : ℕ} (hn : 0 < n)
    -- the world of the group
    (ν : Measure (ℕ × (Fin 6 → ℝ))) (ωw Bw δL : ℝ)
    (hBw : 0 < Bw) (hδL : 0 < δL)
    -- covered incidences of the entries
    (cov : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hcovm : ∀ a, MeasurableSet (cov a))
    (hfin : ∀ a, (ν.prod volume) (cov a) ≠ ⊤)
    (hACcov : ∀ a, ((ν.prod volume).restrict (cov a)).map (obs Bw δL) ≪
      (volume.prod Measure.count))
    -- group coordinates of observations and of lines
    (obase : EuclideanSpace ℝ (Fin 3) × ℤ → Real3) (hobase : Measurable obase)
    (lbase : (ℕ × (Fin 6 → ℝ)) → ℝ → Real3)
    (hbase : ∀ p : (ℕ × (Fin 6 → ℝ)) × ℝ, obase (obs Bw δL p) = lbase p.1 p.2)
    -- entry sheets, the true sheet, and the exact roots of the selected tests
    (F : Fin n → RealSheet 2) (F₀ : RealSheet 2)
    (Ptest : Fin n → MvPolynomial (Fin 4) ℝ) (s : Fin n → ℝ) (pos : Fin n → Bool)
    (hP : ∀ a, (Ptest a).totalDegree ≤ 2) (hs : ∀ a, 0 < s a)
    (hroots : ∀ a l t, ‖lbase l t‖ ≤ (1 : ℝ) / 2 →
      let w := ((F a).f (emb (lbase l t))).re / Bw
      eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (Ptest a) = 0 ∧
      if pos a then
        19 / 20 * s a ≤ eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (Ptest a)) ∧
        eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (Ptest a)) ≤ 21 / 20 * s a
      else
        19 / 20 * s a ≤ -eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (Ptest a)) ∧
        -eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (Ptest a)) ≤ 21 / 20 * s a)
    -- fits of the covered lines on the sub-block and at the incidences
    (ta tb ηfine ηold : ℝ) (hηfine : 0 < ηfine) (hηold : 0 < ηold)
    (hfitT : ∀ a, ∀ p ∈ cov a, ∀ t, t = ta ∨ t = (ta + tb) / 2 ∨ t = tb →
      ‖lbase p.1 t‖ ≤ (1 : ℝ) / 2 ∧ |Bw * gx p.1 t 3 - ((F a).f (emb (lbase p.1 t))).re| ≤ ηfine)
    (hfitP : ∀ a, ∀ p ∈ cov a, ‖lbase p.1 p.2‖ ≤ (1 : ℝ) / 2 ∧
      |Bw * gx p.1 p.2 3 - ((F a).f (emb (lbase p.1 p.2))).re| ≤ ηfine ∧
      |Bw * gx p.1 p.2 3 - (F₀.f (emb (lbase p.1 p.2))).re| ≤ ηold)
    -- caps, floors and the numerical conditions of the group recovery
    (θ H m lam : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hH : 0 < H) (hlam : 0 < lam)
    (hcount : (n : ℝ) ≤ R ^ (d₀ + ε))
    (htot : (∑ a, ENNReal.ofReal ωw * (ν.prod volume) (cov a)) ≤ ENNReal.ofReal lam)
    (hbudget : (n : ℝ) * H ≤ lam * R ^ ε)
    (hcap : ∀ a, (ENNReal.ofReal ωw • (ν.prod volume).restrict (cov a)).map
      (obase ∘ obs Bw δL) ≤ ENNReal.ofReal H • volume)
    (hfloor : ∀ a, ENNReal.ofReal m ≤ ENNReal.ofReal ωw * (ν.prod volume) (cov a))
    (hθmass : ENNReal.ofReal θ * volume (Metric.closedBall (0 : Real3) (1 / 2)) ≤
      ENNReal.ofReal (m / H))
    (hremez : params.remezScale *
      (params.remezExponent * θ ^ (-params.remezExponent) * (ηfine + ηold)) ≤ M * R ^ ε)
    (hwidth : 2 * ηfine + δL ≤ M * R ^ (-1 + ε)) :
    ∃ (Lg : (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin n)) (rep : Fin n → Fin n)
      (Qt : Fin n → MvPolynomial (Fin 4) ℝ) (sq m₀ : Fin n → ℝ),
      (∀ a, MeasurableSet {o | a ∈ Lg o}) ∧
      (∀ o, (Lg o).card ≤ 7 ^ Fintype.card (GroupJetIndex params)) ∧
      (∀ a, rep (rep a) = rep a) ∧
      (∀ a, Qt (rep a) = Qt a ∧ sq (rep a) = sq a ∧ m₀ (rep a) = m₀ a) ∧
      (∀ a, (Qt a = Ptest (rep a) ∨ Qt a = pderiv 3 (Ptest (rep a))) ∧
        (sq a = s (rep a) ∨ sq a = |qc (Ptest (rep a))|)) ∧
      (∀ a, (Qt a).totalDegree ≤ 2 ∧ 0 < sq a ∧ 0 ≤ m₀ a ∧
        m₀ a ≤ 85 * sq a * ((ηfine + (∑ i, groupJetWidth params R M ε i) / params.lower) / Bw) ∧
        |qc (Qt a)| * m₀ a ≤ sq a ^ 2 / 40 ∧
        s (rep a) / (1 + 80 * ((ηfine + (∑ i, groupJetWidth params R M ε i) / params.lower) / Bw)) ≤
          sq a) ∧
      (∀ a, ∀ p ∈ cov a, p.1 ∈ rootTestSet (Qt a) (sq a) (m₀ a) ta tb) ∧
      (∑ a, ENNReal.ofReal ωw * (ν.prod volume) (cov a)) ≤
        (∑ a, ENNReal.ofReal ωw * (ν.prod volume) (cov a ∩ {p | rep a ∈ Lg (obs Bw δL p)})) +
          ENNReal.ofReal (lam * R ^ (-ε)) := by
  classical
  -- the component laws
  let μ : Fin n → Measure ((ℕ × (Fin 6 → ℝ)) × ℝ) := fun a =>
    ENNReal.ofReal ωw • (ν.prod volume).restrict (cov a)
  have hμ (a : Fin n) (S : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) :
      μ a S = ENNReal.ofReal ωw * (ν.prod volume) (S ∩ cov a) := by
    simp only [μ, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply' (hcovm a)]
  haveI hfinμ : ∀ a, IsFiniteMeasure (μ a) := fun a => by
    constructor
    rw [hμ, Set.univ_inter]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr (hfin a))
  have hO : Measurable (obs Bw δL) := measurable_gobs' Bw δL
  have hAC : ∀ a, (μ a).map (obs Bw δL) ≪ (volume.prod Measure.count) := by
    intro a
    refine Measure.AbsolutelyContinuous.mk fun S hS hS0 => ?_
    have h1 := hACcov a hS0
    rw [Measure.map_apply hO hS, Measure.restrict_apply (hO hS)] at h1
    rw [Measure.map_apply hO hS, hμ, h1, mul_zero]
  have hfit : ∀ a, ∀ᵐ z ∂μ a,
      ‖obase (obs Bw δL z)‖ ≤ (1 : ℝ) / 2 ∧
      δL * ((obs Bw δL z).2 : ℝ) ≤ Bw * gx z.1 z.2 3 ∧
      Bw * gx z.1 z.2 3 ≤ δL * (((obs Bw δL z).2 : ℝ) + 1) ∧
      |Bw * gx z.1 z.2 3 - ((F a).f (emb (obase (obs Bw δL z)))).re| ≤ ηfine ∧
      |Bw * gx z.1 z.2 3 - (F₀.f (emb (obase (obs Bw δL z)))).re| ≤ ηold := by
    intro a
    refine Measure.ae_smul_measure ?_ _
    refine ae_restrict_of_forall_mem (hcovm a) fun z hz => ?_
    obtain ⟨hhalf, hfine, hold⟩ := hfitP a z hz
    have hbin := hidden_mem_bin (Bv := Bw) hδL z
    rw [hbase z]
    exact ⟨hhalf, hbin.1, hbin.2, hfine, hold⟩
  have htot' : (∑ a, μ a univ) ≤ ENNReal.ofReal lam := by
    simpa only [hμ, Set.univ_inter] using htot
  have hfloor' : ∀ a, ENNReal.ofReal m ≤ μ a univ := by
    intro a
    rw [hμ, Set.univ_inter]
    exact hfloor a
  -- the group recovery
  obtain ⟨L, hLm, hLc, hsucc, hrepr⟩ := hGR R M ε hR hM hε hεp n F F₀
    (volume.prod Measure.count) μ (obs Bw δL) hO hAC obase hobase (fun o => o.2) measurable_snd
    (fun z => Bw * gx z.1 z.2 3) δL ηfine ηold θ H m lam hn hηfine hηold hθ hθ1 hH hlam hcount
    htot' hbudget hcap hfloor' hθmass hremez hwidth hfit
  -- one root test per merged bin
  let jet : Fin n → GroupJetIndex params → ℝ :=
    fun a => directionalJets params.directions params.order (F a).f
  let width := groupJetWidth params R M ε
  have hwpos : ∀ i, 0 < width i := fun i =>
    mul_pos (params.upper_pos _) (mul_pos hM (Real.rpow_pos_of_pos (by linarith [params.radius_two]) _))
  have hηbin : 0 ≤ (∑ i, width i) / params.lower :=
    div_nonneg (Finset.sum_nonneg fun i _ => (hwpos i).le) params.lower_pos.le
  obtain ⟨Qb, sqb, m₀b, hQb, hsqb, hbnd, hmem⟩ := exists_bin_root_tests_bounded F jet width Ptest s pos
    hP hs (fun a => Prod.fst '' cov a) lbase Bw ηfine ((∑ i, width i) / params.lower) ta tb hBw
    hηfine hηbin (by
      rintro a l ⟨p, hp, rfl⟩ t ht
      exact hfitT a p hp t ht) hrepr hroots
  refine ⟨representativeLists width jet L, representativeOf width jet,
    fun a => Qb (mergedLabel width jet a), fun a => sqb (mergedLabel width jet a),
    fun a => m₀b (mergedLabel width jet a), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact measurable_representativeLists width jet L hLm
  · intro o
    rw [card_representativeLists]
    exact hLc o
  · exact representativeOf_idempotent width jet
  · intro a
    simp only [representativeOf, mergedLabel_binRepresentative]
    exact ⟨trivial, trivial, trivial⟩
  · intro a
    exact ⟨hQb _, hsqb _⟩
  · intro a
    exact hbnd _
  · intro a p hp
    exact hmem a p.1 ⟨p, hp, rfl⟩
  · have h1 : (∑ a, ENNReal.ofReal ωw * (ν.prod volume) (cov a)) = ∑ a, μ a univ := by
      simp only [hμ, Set.univ_inter]
    have h2 : (∑ a, μ a {z | mergedLabel width jet a ∈ L (obs Bw δL z)}) =
        ∑ a, ENNReal.ofReal ωw * (ν.prod volume)
          (cov a ∩ {p | representativeOf width jet a ∈
            representativeLists width jet L (obs Bw δL p)}) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← representativeLists_success_mass width jet L (μ a) (obs Bw δL) a, hμ, Set.inter_comm]
    rw [h1, ← h2]
    exact hsucc

/-- The full-world density-law version of `group_step_of_ac`. -/
theorem group_step {d₀ : ℝ} {params : GroupParameters}
    (hGR : GroupRecovery.{0, 0} 2 d₀ params)
    {R M ε : ℝ} (hR : params.radius ≤ R) (hM : 0 < M) (hε : 0 < ε) (hεp : ε ≤ params.epsilon)
    {n : ℕ} (hn : 0 < n)
    -- the world of the group
    (ν : Measure (ℕ × (Fin 6 → ℝ))) (Ew : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (ωw Bw δL : ℝ)
    (hBw : 0 < Bw) (hδL : 0 < δL) (g : (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal)
    (hlaw : ((ν.prod volume).restrict Ew).map (obs Bw δL) =
      (volume.prod Measure.count).withDensity g)
    -- covered incidences of the entries
    (cov : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hcovm : ∀ a, MeasurableSet (cov a))
    (hcovE : ∀ a, cov a ⊆ Ew) (hfin : ∀ a, (ν.prod volume) (cov a) ≠ ⊤)
    -- group coordinates of observations and of lines
    (obase : EuclideanSpace ℝ (Fin 3) × ℤ → Real3) (hobase : Measurable obase)
    (lbase : (ℕ × (Fin 6 → ℝ)) → ℝ → Real3)
    (hbase : ∀ p : (ℕ × (Fin 6 → ℝ)) × ℝ, obase (obs Bw δL p) = lbase p.1 p.2)
    -- entry sheets, the true sheet, and the exact roots of the selected tests
    (F : Fin n → RealSheet 2) (F₀ : RealSheet 2)
    (Ptest : Fin n → MvPolynomial (Fin 4) ℝ) (s : Fin n → ℝ) (pos : Fin n → Bool)
    (hP : ∀ a, (Ptest a).totalDegree ≤ 2) (hs : ∀ a, 0 < s a)
    (hroots : ∀ a l t, ‖lbase l t‖ ≤ (1 : ℝ) / 2 →
      let w := ((F a).f (emb (lbase l t))).re / Bw
      eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (Ptest a) = 0 ∧
      if pos a then
        19 / 20 * s a ≤ eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (Ptest a)) ∧
        eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (Ptest a)) ≤ 21 / 20 * s a
      else
        19 / 20 * s a ≤ -eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (Ptest a)) ∧
        -eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (Ptest a)) ≤ 21 / 20 * s a)
    -- fits of the covered lines on the sub-block and at the incidences
    (ta tb ηfine ηold : ℝ) (hηfine : 0 < ηfine) (hηold : 0 < ηold)
    (hfitT : ∀ a, ∀ p ∈ cov a, ∀ t, t = ta ∨ t = (ta + tb) / 2 ∨ t = tb →
      ‖lbase p.1 t‖ ≤ (1 : ℝ) / 2 ∧ |Bw * gx p.1 t 3 - ((F a).f (emb (lbase p.1 t))).re| ≤ ηfine)
    (hfitP : ∀ a, ∀ p ∈ cov a, ‖lbase p.1 p.2‖ ≤ (1 : ℝ) / 2 ∧
      |Bw * gx p.1 p.2 3 - ((F a).f (emb (lbase p.1 p.2))).re| ≤ ηfine ∧
      |Bw * gx p.1 p.2 3 - (F₀.f (emb (lbase p.1 p.2))).re| ≤ ηold)
    -- caps, floors and the numerical conditions of the group recovery
    (θ H m lam : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hH : 0 < H) (hlam : 0 < lam)
    (hcount : (n : ℝ) ≤ R ^ (d₀ + ε))
    (htot : (∑ a, ENNReal.ofReal ωw * (ν.prod volume) (cov a)) ≤ ENNReal.ofReal lam)
    (hbudget : (n : ℝ) * H ≤ lam * R ^ ε)
    (hcap : ∀ a, (ENNReal.ofReal ωw • (ν.prod volume).restrict (cov a)).map
      (obase ∘ obs Bw δL) ≤ ENNReal.ofReal H • volume)
    (hfloor : ∀ a, ENNReal.ofReal m ≤ ENNReal.ofReal ωw * (ν.prod volume) (cov a))
    (hθmass : ENNReal.ofReal θ * volume (Metric.closedBall (0 : Real3) (1 / 2)) ≤
      ENNReal.ofReal (m / H))
    (hremez : params.remezScale *
      (params.remezExponent * θ ^ (-params.remezExponent) * (ηfine + ηold)) ≤ M * R ^ ε)
    (hwidth : 2 * ηfine + δL ≤ M * R ^ (-1 + ε)) :
    ∃ (Lg : (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin n)) (rep : Fin n → Fin n)
      (Qt : Fin n → MvPolynomial (Fin 4) ℝ) (sq m₀ : Fin n → ℝ),
      (∀ a, MeasurableSet {o | a ∈ Lg o}) ∧
      (∀ o, (Lg o).card ≤ 7 ^ Fintype.card (GroupJetIndex params)) ∧
      (∀ a, rep (rep a) = rep a) ∧
      (∀ a, Qt (rep a) = Qt a ∧ sq (rep a) = sq a ∧ m₀ (rep a) = m₀ a) ∧
      (∀ a, (Qt a = Ptest (rep a) ∨ Qt a = pderiv 3 (Ptest (rep a))) ∧
        (sq a = s (rep a) ∨ sq a = |qc (Ptest (rep a))|)) ∧
      (∀ a, (Qt a).totalDegree ≤ 2 ∧ 0 < sq a ∧ 0 ≤ m₀ a ∧
        m₀ a ≤ 85 * sq a * ((ηfine + (∑ i, groupJetWidth params R M ε i) / params.lower) / Bw) ∧
        |qc (Qt a)| * m₀ a ≤ sq a ^ 2 / 40 ∧
        s (rep a) / (1 + 80 * ((ηfine + (∑ i, groupJetWidth params R M ε i) / params.lower) / Bw)) ≤
          sq a) ∧
      (∀ a, ∀ p ∈ cov a, p.1 ∈ rootTestSet (Qt a) (sq a) (m₀ a) ta tb) ∧
      (∑ a, ENNReal.ofReal ωw * (ν.prod volume) (cov a)) ≤
        (∑ a, ENNReal.ofReal ωw * (ν.prod volume) (cov a ∩ {p | rep a ∈ Lg (obs Bw δL p)})) +
          ENNReal.ofReal (lam * R ^ (-ε)) := by
  have hO : Measurable (obs Bw δL) := measurable_gobs' Bw δL
  have hACcov : ∀ a, ((ν.prod volume).restrict (cov a)).map (obs Bw δL) ≪
      (volume.prod Measure.count) := by
    intro a
    refine Measure.AbsolutelyContinuous.mk fun S hS hS0 => ?_
    have h1 : ((volume.prod Measure.count).withDensity g) S = 0 :=
      withDensity_absolutelyContinuous _ _ hS0
    rw [← hlaw, Measure.map_apply hO hS, Measure.restrict_apply (hO hS)] at h1
    rw [Measure.map_apply hO hS, Measure.restrict_apply (hO hS)]
    exact measure_mono_null (Set.inter_subset_inter_right _ (hcovE a)) h1
  exact group_step_of_ac hGR hR hM hε hεp hn ν ωw Bw δL hBw hδL cov hcovm hfin hACcov
    obase hobase lbase hbase F F₀ Ptest s pos hP hs hroots ta tb ηfine ηold hηfine hηold hfitT hfitP
    θ H m lam hθ hθ1 hH hlam hcount htot hbudget hcap hfloor hθmass hremez hwidth

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
