-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/FieldAssembly.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/-
x1037 (o287). The interpolated physical field with its witness frame
(paper tex-06, "Cartesian interpolation of the physical field"):

* `cartesian_field_of_witnesses`: x1035's `cartesian_whole_state_row` with the
  spanning frame, the qualified witnesses and the state family supplied by
  `cartesian_witness_frame` from per-state qualification, strip breadth and
  per-code palette domination; the density input from a base density relative to the
  whole law.
* `state_thinning`: deleting the states that lose more than half of their mass
  to a cut keeps each surviving state's whole fiber and half its mass.
* `long_line_cut`: incidences on lines whose time slice is shorter than `η h`
  carry mass at most `η h ν(univ)`.
-/
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.CartesianField
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.WitnessFrame

set_option autoImplicit false

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

open MeasureTheory Set MvPolynomial
open Submission.Lib.K4CommonLocalChoice (cell)
open scoped ENNReal RealInnerProductSpace

noncomputable section

/-- A qualified witness stays qualified under a larger coefficient bound and
a shorter required duration. -/
theorem QualWitness.mono {Λ σ : Type*} {Eref : Set (Λ × ℝ)} {st : Λ × ℝ → σ}
    {Gs : σ → Fin 3 → ℝ} {t0 h : ℝ} {M : ℕ} {K K' err dur dur' : ℝ} {w : Λ × ℝ}
    (hK : K ≤ K') (hdur : dur' ≤ dur) (hq : QualWitness Eref st Gs t0 h M K err dur w) :
    QualWitness Eref st Gs t0 h M K' err dur' w := by
  obtain ⟨P, hdeg, hcoeff, hpt, E, hE, hEsub, hvol, hfit⟩ := hq
  exact ⟨P, hdeg, fun j k => (hcoeff j k).trans hK, hpt, E, hE, hEsub,
    (ENNReal.ofReal_le_ofReal hdur).trans hvol, hfit⟩

/-- The masses of the fibers of finitely many states add up. -/
theorem sum_fiber_measure {Ω σ : Type*} [MeasurableSpace Ω] [MeasurableSpace σ]
    [MeasurableSingletonClass σ] (μ : Measure Ω) (st : Ω → σ) (hst : Measurable st)
    (F : Finset σ) : ∑ D ∈ F, μ (st ⁻¹' {D}) = μ (st ⁻¹' (F : Set σ)) := by
  rw [← measure_biUnion_finset]
  · congr 1
    ext x
    simp
  · intro a _ b _ hab
    exact Disjoint.preimage _ (disjoint_singleton.mpr hab)
  · intro D _
    exact hst (measurableSet_singleton D)

/-- **The interpolated field from qualified witnesses.** The witness frame
(`cartesian_witness_frame`: one common spanning triple of velocity bins
from per-state qualification, strip breadth and palette domination) feeds
`cartesian_whole_state_row`; the density input is derived from a base
density relative to the whole law, at the cost of the frame's mass loss. -/
theorem cartesian_field_of_witnesses (M : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ e : ℕ,
    ∀ {Λ σ : Type} [MeasurableSpace Λ] [MeasurableSpace σ] [Countable σ]
      [MeasurableSingletonClass σ]
      (μ : Measure (Λ × ℝ)) [IsFiniteMeasure μ]
      (E0 Eref : Set (Λ × ℝ)), MeasurableSet E0 → E0 ⊆ Eref → μ E0ᶜ = 0 →
      ∀ (st : Λ × ℝ → σ), Measurable st →
      ∀ (Gs cz : σ → Fin 3 → ℝ) (z : Λ × ℝ → Fin 3 → ℝ) (v : Λ → Fin 2 → ℝ), Measurable v →
      ∀ (t0 h : ℝ), 0 < h →
      (∀ l t, z (l, t) 0 = (t - t0) / h) →
      (∀ l t t', z (l, t') = z (l, t) + ((t' - t) / h) • lift (v l)) →
      ∀ (Fam : Finset σ), (∀ x ∈ E0, st x ∈ Fam) →
      ∀ (Q : Set (Λ × ℝ)), MeasurableSet Q →
      ∀ (πv : Measure (Fin 2 → ℤ)) [IsProbabilityMeasure πv],
      ∀ (K ξ ε p err ηq ps wv pv Vq Kr Kd : ℝ),
      1 ≤ K → 0 < ξ → C * K ^ e * ξ ≤ 1 → 0 ≤ ε → ε ≤ ξ → ξ ≤ p → p ≤ 1 →
      0 ≤ err → err ≤ p →
      (∀ w ∈ Q, w ∈ Eref ∧ t0 ≤ w.2 ∧ w.2 ≤ t0 + h ∧
        QualWitness Eref st Gs t0 h M K err (1 / K) w) →
      0 ≤ Vq → (∀ w ∈ Q, ∀ k, |v w.1 k| ≤ Vq) →
      0 ≤ ηq → 0 ≤ ps → 0 < (1 - ηq) ^ 3 - 2 * ps →
      (∀ D ∈ Fam, μ (st ⁻¹' {D} \ Q) ≤ ENNReal.ofReal ηq * μ (st ⁻¹' {D})) →
      0 < wv → 0 < pv → pv ≤ wv / 2 → pv / 2 ≤ ξ →
      max 1 (Vq + pv) ≤ K → 2 * (max 1 (Vq + pv)) ^ 2 / (wv / 2) ^ 2 ≤ K →
      (∀ D ∈ Fam, ∀ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 → ∀ s : ℝ,
        μ (st ⁻¹' {D} ∩
            {x | |⟪n, (WithLp.toLp 2 (v x.1) : EuclideanSpace ℝ (Fin 2))⟫ - s| ≤ wv}) ≤
          ENNReal.ofReal ps * μ (st ⁻¹' {D})) →
      0 ≤ Kr →
      (∀ D ∈ Fam, ∀ b : Fin 2 → ℤ,
        μ ({x | velBinOf pv (v x.1) = b} ∩ (st ⁻¹' {D} ∩ Q)) ≤
          ENNReal.ofReal Kr * μ (st ⁻¹' {D}) * πv {b}) →
      (∀ x ∈ Eref, ∀ i, |z x i - cz (st x) i| ≤ ε) →
      (∀ D ∈ Fam, ∀ i, |cz D i| ≤ K) → (∀ D ∈ Fam, ∀ j, |Gs D j| ≤ K) →
      (∀ c : Fin 3 → ℝ, ∃ F : Finset (Fin 3 → ℤ), (F.card : ℝ) ≤ K ∧
        ∀ x ∈ Eref, (∀ i, |z x i - c i| ≤ 30 * K ^ 2 * ξ) → cell p (Gs (st x)) ∈ F) →
      (∀ (c : Fin 3 → ℝ) (r : ℝ), 0 < r →
        μ.real {x | ∀ i, |z x i - c i| ≤ r} ≤ Kd * r ^ 3 * μ.real univ) →
      Kd * Kr ^ 3 / ((1 - ηq) ^ 3 - 2 * ps) ≤ K →
      0 < μ.real univ →
      ∃ (T : Fin 3 → MvPolynomial (Fin 3) ℝ) (S : Set (Λ × ℝ)),
        MeasurableSet S ∧ S ⊆ E0 ∧
        (∀ x ∈ E0, ∀ y ∈ S, st x = st y → x ∈ S) ∧
        (∀ j, (T j).totalDegree ≤ 3 * M) ∧ (∀ j d, |(T j).coeff d| ≤ C * K ^ e) ∧
        μ.real univ ≤ Kr ^ 3 / ((1 - ηq) ^ 3 - 2 * ps) * (C * K ^ e) * μ.real S ∧
        ∀ x ∈ S, ∀ j, |Gs (st x) j - eval (z x) (T j)| ≤ C * K ^ e * p := by
  obtain ⟨C, hC, e, hrow⟩ := cartesian_whole_state_row M
  refine ⟨C, hC, e, ?_⟩
  intro Λ σ _ _ _ _ μ _ E0 Eref hE0 hE0ref hconc st hst Gs cz z v hv t0 h hh hz0 hzline Fam hFam
    Q hQm πv _ K ξ ε p err ηq ps wv pv Vq Kr Kd hK hξ hCξ hε hεξ hξp hp1 herr herrp hQ hVq hvQ
    hηq hps hc₁ hqual hwv hpv hpvw hpvξ hJK hAK hstrip hKr hpal hcz hczK hGK hfield hdens hKd
    hmass0
  set c₁ := (1 - ηq) ^ 3 - 2 * ps with hc₁def
  obtain ⟨J, Ainv, Ωst, hΩsub, hframe, hwit, hframeMass⟩ := cartesian_witness_frame_bins μ st hst
    v hv Fam Q hQm Eref Gs t0 h M K err hQ hvQ hηq hps hqual hwv hpv hpvw hstrip πv hpal
  -- masses of state fibers
  have hFamAll : μ (st ⁻¹' (Fam : Set σ)) = μ univ := by
    apply le_antisymm (measure_mono (subset_univ _))
    calc μ univ = μ E0 := (measure_congr (ae_eq_univ.mpr hconc)).symm
      _ ≤ μ (st ⁻¹' (Fam : Set σ)) := measure_mono (fun x hx => hFam x hx)
  have hE0inter (X : Set (Λ × ℝ)) : μ (E0 ∩ X) = μ X := by
    rw [inter_comm]
    exact measure_inter_conull hconc
  have hframeReal : c₁ * μ.real univ ≤ Kr ^ 3 * μ.real (E0 ∩ st ⁻¹' (Ωst : Set σ)) := by
    rw [sum_fiber_measure μ st hst, sum_fiber_measure μ st hst, hFamAll,
      ← hE0inter (st ⁻¹' (Ωst : Set σ))] at hframeMass
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (measure_ne_top _ _)) hframeMass
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hc₁.le,
      ENNReal.toReal_ofReal hKr] at h
    exact h
  have hΩmass : 0 < μ.real (E0 ∩ st ⁻¹' (Ωst : Set σ)) := by
    have h1 : 0 < c₁ * μ.real univ := mul_pos hc₁ hmass0
    have h2 : 0 < Kr ^ 3 * μ.real (E0 ∩ st ⁻¹' (Ωst : Set σ)) := h1.trans_le hframeReal
    by_contra hn
    have hn := not_lt.mp hn
    have h3 : Kr ^ 3 * μ.real (E0 ∩ st ⁻¹' (Ωst : Set σ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hn
    linarith
  have hΩne : Ωst.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne] at hΩmass
    simp at hΩmass
  obtain ⟨hA, hJ, hAinv⟩ := hframe hΩne
  have hKr3 : 0 < Kr ^ 3 := by
    rcases hKr.lt_or_eq with h | h
    · positivity
    · exfalso
      rw [← h] at hframeReal
      have : 0 < c₁ * μ.real univ := mul_pos hc₁ hmass0
      simp at hframeReal
      linarith
  have hratio : μ.real univ ≤ Kr ^ 3 / c₁ * μ.real (E0 ∩ st ⁻¹' (Ωst : Set σ)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc₁]
    linarith
  have hdens' : ∀ (c : Fin 3 → ℝ) (r : ℝ), 0 < r →
      μ.real (E0 ∩ st ⁻¹' (Ωst : Set σ) ∩ {x | ∀ i, |z x i - c i| ≤ r}) ≤
        K * r ^ 3 * μ.real (E0 ∩ st ⁻¹' (Ωst : Set σ)) := by
    intro c r hr
    have hr3 : 0 ≤ r ^ 3 := by positivity
    have hKd0 : 0 ≤ Kd := by
      have h := hdens c r hr
      by_contra hneg
      have hneg := not_le.mp hneg
      have : Kd * r ^ 3 * μ.real univ < 0 :=
        mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg (by positivity)) hmass0
      linarith [measureReal_nonneg (μ := μ) (s := {x | ∀ i, |z x i - c i| ≤ r})]
    calc μ.real (E0 ∩ st ⁻¹' (Ωst : Set σ) ∩ {x | ∀ i, |z x i - c i| ≤ r})
        ≤ μ.real {x | ∀ i, |z x i - c i| ≤ r} := measureReal_mono inter_subset_right
      _ ≤ Kd * r ^ 3 * μ.real univ := hdens c r hr
      _ ≤ Kd * r ^ 3 * (Kr ^ 3 / c₁ * μ.real (E0 ∩ st ⁻¹' (Ωst : Set σ))) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (Kd * Kr ^ 3 / c₁) * r ^ 3 * μ.real (E0 ∩ st ⁻¹' (Ωst : Set σ)) := by ring
      _ ≤ K * r ^ 3 * μ.real (E0 ∩ st ⁻¹' (Ωst : Set σ)) := by gcongr
  have hwit' : ∀ D ∈ (Ωst : Set σ), ∀ axis : Fin 3, ∃ w ∈ Eref, st w = D ∧
      (∀ k, |v w.1 k - J axis k| ≤ pv / 2) ∧ t0 ≤ w.2 ∧ w.2 ≤ t0 + h ∧
      QualWitness Eref st Gs t0 h M K err (1 / K) w := hwit
  obtain ⟨T, S, hS, hSsub, hSsat, hTdeg, hTcoeff, hSmass, hfit⟩ :=
    hrow μ E0 Eref hE0 hE0ref st hst Gs cz z v t0 h hh hz0 hzline J Ainv hA K ξ ε (pv / 2) p
      err hK hξ hCξ hε hεξ (by positivity) hpvξ hξp hp1 herr herrp
      (fun i k => (hJ i k).trans hJK) (fun i k => (hAinv i k).trans hAK) hcz (Ωst : Set σ)
      (fun D hD i => hczK D (hΩsub hD) i) (fun D hD j => hGK D (hΩsub hD) j) hwit' hfield
      hdens' hΩmass
  refine ⟨T, S, hS, hSsub.trans inter_subset_left, hSsat, hTdeg, hTcoeff, ?_, hfit⟩
  calc μ.real univ ≤ Kr ^ 3 / c₁ * μ.real (E0 ∩ st ⁻¹' (Ωst : Set σ)) := hratio
    _ ≤ Kr ^ 3 / c₁ * (C * K ^ e * μ.real S) :=
        mul_le_mul_of_nonneg_left hSmass (by positivity)
    _ = Kr ^ 3 / c₁ * (C * K ^ e) * μ.real S := by ring


/-- **State thinning.** Removing the states that lose more than half of their
mass from `B` to `A` costs at most twice the loss; every surviving state keeps
its whole `A`-fiber and at least half of its `B`-mass. -/
theorem state_thinning {Ω σ : Type*} [MeasurableSpace Ω] [MeasurableSpace σ] [Countable σ]
    [MeasurableSingletonClass σ] (μ : Measure Ω) [IsFiniteMeasure μ] (st : Ω → σ)
    (hst : Measurable st) {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B) :
    ∃ A' : Set Ω, MeasurableSet A' ∧ A' ⊆ A ∧ μ (B \ A') ≤ 3 * μ (B \ A) ∧
      ∀ D : σ, A' ∩ st ⁻¹' {D} = ∅ ∨
        (A' ∩ st ⁻¹' {D} = A ∩ st ⁻¹' {D} ∧ μ (B ∩ st ⁻¹' {D}) ≤ 2 * μ (A' ∩ st ⁻¹' {D})) := by
  classical
  let good : Set σ := {D | μ (B ∩ st ⁻¹' {D}) ≤ 2 * μ (A ∩ st ⁻¹' {D})}
  let bad : Set σ := goodᶜ
  have hgoodm : MeasurableSet (st ⁻¹' good) := hst (Set.to_countable good).measurableSet
  refine ⟨A ∩ st ⁻¹' good, hA.inter hgoodm, inter_subset_left, ?_, ?_⟩
  · have hsplit : B \ (A ∩ st ⁻¹' good) ⊆ (B \ A) ∪ (B ∩ st ⁻¹' bad) := by
      intro x ⟨hxB, hxn⟩
      by_cases hxA : x ∈ A
      · right
        exact ⟨hxB, fun hg => hxn ⟨hxA, hg⟩⟩
      · left
        exact ⟨hxB, hxA⟩
    have hbad : μ (B ∩ st ⁻¹' bad) ≤ 2 * μ (B \ A) := by
      have hs : bad.Countable := Set.to_countable bad
      have hfib : ∀ D ∈ bad, MeasurableSet (st ⁻¹' {D}) :=
        fun D _ => hst (measurableSet_singleton D)
      have h1 : μ (B ∩ st ⁻¹' bad) = ∑' D : bad, (μ.restrict B) (st ⁻¹' {(D : σ)}) := by
        rw [tsum_measure_preimage_singleton hs hfib, Measure.restrict_apply (hst hs.measurableSet),
          inter_comm]
      have h2 : ∑' D : bad, (μ.restrict (B \ A)) (st ⁻¹' {(D : σ)}) ≤ μ (B \ A) := by
        rw [tsum_measure_preimage_singleton hs hfib]
        exact (measure_mono (subset_univ _)).trans (Measure.restrict_apply_univ _).le
      rw [h1]
      calc ∑' D : bad, (μ.restrict B) (st ⁻¹' {(D : σ)})
          ≤ ∑' D : bad, 2 * (μ.restrict (B \ A)) (st ⁻¹' {(D : σ)}) := by
            apply ENNReal.tsum_le_tsum
            rintro ⟨D, hD⟩
            have hDm := hst (measurableSet_singleton D)
            rw [Measure.restrict_apply hDm, Measure.restrict_apply hDm]
            have hD' : 2 * μ (A ∩ st ⁻¹' {D}) < μ (B ∩ st ⁻¹' {D}) := not_le.mp hD
            have hdec : μ (st ⁻¹' {D} ∩ B) =
                μ (A ∩ st ⁻¹' {D}) + μ (st ⁻¹' {D} ∩ (B \ A)) := by
              rw [← measure_union (by
                  rw [Set.disjoint_left]
                  rintro x ⟨hxA, -⟩ ⟨-, -, hxn⟩
                  exact hxn hxA) (hDm.inter (hB.diff hA))]
              congr 1
              ext x
              constructor
              · rintro ⟨hxD, hxB⟩
                by_cases hxA : x ∈ A
                · exact Or.inl ⟨hxA, hxD⟩
                · exact Or.inr ⟨hxD, hxB, hxA⟩
              · rintro (⟨hxA, hxD⟩ | ⟨hxD, hxB, -⟩)
                · exact ⟨hxD, hAB hxA⟩
                · exact ⟨hxD, hxB⟩
            rw [inter_comm B] at hD'
            rw [hdec] at hD' ⊢
            have hafin : μ (A ∩ st ⁻¹' {D}) ≠ ⊤ := measure_ne_top _ _
            have hlt : μ (A ∩ st ⁻¹' {D}) < μ (st ⁻¹' {D} ∩ (B \ A)) := by
              rw [two_mul] at hD'
              exact (ENNReal.add_lt_add_iff_left hafin).mp hD'
            rw [two_mul]
            exact add_le_add hlt.le le_rfl
        _ = 2 * ∑' D : bad, (μ.restrict (B \ A)) (st ⁻¹' {(D : σ)}) := ENNReal.tsum_mul_left
        _ ≤ 2 * μ (B \ A) := mul_le_mul' le_rfl h2
    calc μ (B \ (A ∩ st ⁻¹' good)) ≤ μ ((B \ A) ∪ (B ∩ st ⁻¹' bad)) := measure_mono hsplit
      _ ≤ μ (B \ A) + μ (B ∩ st ⁻¹' bad) := measure_union_le _ _
      _ ≤ μ (B \ A) + 2 * μ (B \ A) := add_le_add le_rfl hbad
      _ = 3 * μ (B \ A) := by ring
  · intro D
    by_cases hD : D ∈ good
    · right
      have heq : A ∩ st ⁻¹' good ∩ st ⁻¹' {D} = A ∩ st ⁻¹' {D} := by
        ext x
        simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
        constructor
        · rintro ⟨⟨hxA, -⟩, hx⟩
          exact ⟨hxA, hx⟩
        · rintro ⟨hxA, hx⟩
          exact ⟨⟨hxA, hx ▸ hD⟩, hx⟩
      refine ⟨heq, ?_⟩
      rw [heq]
      exact hD
    · left
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false,
        not_and]
      intro h1 hx
      exact hD (hx ▸ h1.2)

/-- **Long lines.** Incidences in a time window of length `h` lying on lines
whose slice is shorter than `η h` carry mass at most `η h ν(univ)`. -/
theorem long_line_cut {Λ : Type*} [MeasurableSpace Λ] (ν : Measure Λ) [IsFiniteMeasure ν]
    {S : Set (Λ × ℝ)} (hS : MeasurableSet S) {t0 h η : ℝ} (hh : 0 < h)
    (hwin : S ⊆ univ ×ˢ Icc t0 (t0 + h)) :
    let times : Λ → Set ℝ := fun l => (fun s => t0 + h * s) ⁻¹' (Prod.mk l ⁻¹' S)
    let long : Set Λ := {l | ENNReal.ofReal η ≤ volume (times l)}
    MeasurableSet long ∧ (∀ l, times l ⊆ Icc (0 : ℝ) 1) ∧
      (∀ l s, s ∈ times l → (l, t0 + h * s) ∈ S) ∧
      (ν.prod volume) (S \ (long ×ˢ univ)) ≤ ENNReal.ofReal (η * h) * ν univ := by
  intro times long
  have hvol (l : Λ) : volume (times l) = ENNReal.ofReal h⁻¹ * volume (Prod.mk l ⁻¹' S) := by
    have heq : times l = (fun s => h * s) ⁻¹' ((fun t => t0 + t) ⁻¹' (Prod.mk l ⁻¹' S)) := rfl
    rw [heq, Real.volume_preimage_mul_left hh.ne', MeasureTheory.measure_preimage_add,
      abs_of_pos (inv_pos.mpr hh)]
  have hslice : Measurable fun l => volume (Prod.mk l ⁻¹' S) := measurable_measure_prodMk_left hS
  have hlong : MeasurableSet long := by
    have : long = {l | ENNReal.ofReal η ≤ ENNReal.ofReal h⁻¹ * volume (Prod.mk l ⁻¹' S)} := by
      ext l
      simp only [long, mem_ofPred_eq, hvol]
    rw [this]
    exact measurableSet_le measurable_const (hslice.const_mul _)
  refine ⟨hlong, ?_, ?_, ?_⟩
  · intro l s hs
    have h1 := (hwin hs).2
    have h1' : t0 ≤ t0 + h * s ∧ t0 + h * s ≤ t0 + h := h1
    constructor
    · nlinarith [h1'.1]
    · nlinarith [h1'.2]
  · intro l s hs
    exact hs
  · rw [Measure.prod_apply (hS.diff (hlong.prod MeasurableSet.univ))]
    calc ∫⁻ l, volume (Prod.mk l ⁻¹' (S \ long ×ˢ univ)) ∂ν
        ≤ ∫⁻ _l, ENNReal.ofReal (η * h) ∂ν := by
          apply lintegral_mono
          intro l
          dsimp only
          by_cases hl : l ∈ long
          · have : Prod.mk l ⁻¹' (S \ long ×ˢ univ) = ∅ := by
              ext t
              simp [hl]
            rw [this, measure_empty]
            exact zero_le
          · have hl' : volume (times l) < ENNReal.ofReal η := not_le.mp hl
            rw [hvol] at hl'
            calc volume (Prod.mk l ⁻¹' (S \ long ×ˢ univ)) ≤ volume (Prod.mk l ⁻¹' S) :=
                  measure_mono (fun t ht => ht.1)
              _ = ENNReal.ofReal h * (ENNReal.ofReal h⁻¹ * volume (Prod.mk l ⁻¹' S)) := by
                  rw [← mul_assoc, ← ENNReal.ofReal_mul hh.le, mul_inv_cancel₀ hh.ne',
                    ENNReal.ofReal_one, one_mul]
              _ ≤ ENNReal.ofReal h * ENNReal.ofReal η := mul_le_mul' le_rfl hl'.le
              _ = ENNReal.ofReal (η * h) := by rw [← ENNReal.ofReal_mul hh.le, mul_comm]
      _ = ENNReal.ofReal (η * h) * ν univ := lintegral_const _

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
