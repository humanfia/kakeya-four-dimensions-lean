-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/FieldLongFits.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/-
x1037 (o287). The interpolated field in a frozen old packet with true long
fits: `cartesian_field_of_witnesses` in the old packet base `packetBase T j c u`
(lines move by `direction l / clock T`), the velocity graph
`|rate - Σ direction_i G_i| ≤ εg`, the long-line cut and state thinning give
exactly the field inputs of `Switch.frozen_packet_final` (`Tf`, `times`, `η`,
the fit error) on a set `S ⊆ E0`, each state of which keeps at least half of
its prepared mass. `field_density_of_ceiling` gives its base density input from
the frozen base ceiling and a mass floor; `state_center_of_base_code` its state
centers when states determine the base code.
-/
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.FieldAssembly
import Submission.Obl.k4_physical_row_packet_potential.PotentialFits

set_option autoImplicit false

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

open MeasureTheory Set MvPolynomial
open Submission.Lib.K4CommonLocalChoice (cell)
open Submission.Obl.k4_physical_row_packet_potential.PotentialFits
open scoped ENNReal RealInnerProductSpace

noncomputable section

/-- The planar velocity of an original line. -/
def lineVel (l : Ln) : Fin 2 → ℝ := ![l.2 3, l.2 4]

theorem lift_lineVel (l : Ln) : lift (lineVel l) = direction l := by
  funext i
  fin_cases i <;> rfl

theorem measurable_lineVel : Measurable lineVel := by
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i
  · exact (measurable_pi_apply 3).comp measurable_snd
  · exact (measurable_pi_apply 4).comp measurable_snd

theorem continuous_packetBase' (T j : ℕ) (c u : P2) : Continuous (packetBase T j c u) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i <;>
    simp only [xp, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    fun_prop

/-- The old packet base as a Cartesian base map. -/
def packetZ (T j : ℕ) (c u : P2) (x : Ev) : Fin 3 → ℝ := fun i => packetBase T j c u x i

theorem packetZ_time (T j : ℕ) (c u : P2) (l : Ln) (t : ℝ) :
    packetZ T j c u (l, t) 0 = (t - start T j) / clock T := rfl

theorem packetZ_line (T j : ℕ) (c u : P2) (l : Ln) (t t' : ℝ) :
    packetZ T j c u (l, t') = packetZ T j c u (l, t) + ((t' - t) / clock T) • lift (lineVel l) := by
  have hc := clock_pos T
  have key (τ : ℝ) : packetZ T j c u (l, τ) =
      packetZ T j c u (l, start T j) + ((τ - start T j) / clock T) • direction l := by
    have h := packetBase_normalized T j c u l ((τ - start T j) / clock T)
    have hτ : start T j + clock T * ((τ - start T j) / clock T) = τ := by
      field_simp
      ring
    rw [hτ] at h
    exact h
  rw [lift_lineVel, key t', key t, add_assoc, ← add_smul]
  congr 2
  field_simp
  ring

/-- **The interpolated field with long fits in a frozen old packet.** The
field `Tf` (degree `≤ 3M`, coefficients `≤ C K^e`) in the old packet base, its
long fit times and the fitted set `S` are exactly the field inputs of
`Switch.frozen_packet_final`: on every line of `S` the rate is fitted on a
set of normalized times of measure `≥ η`. Each state either leaves `S` or
keeps at least half of its prepared mass, so per-state ratios on `E0` pass
to `S` with a factor `2`. -/
theorem frozen_field_long_fits (M : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ e : ℕ,
    ∀ {σ : Type} [MeasurableSpace σ] [Countable σ] [MeasurableSingletonClass σ]
      (ν : Measure Ln) [IsFiniteMeasure ν] (T j : ℕ) (c u : P2) (P : Po)
      (E0 Eref : Set Ev), MeasurableSet E0 → E0 ⊆ Eref →
      E0 ⊆ univ ×ˢ Icc (start T j) (start T j + clock T) →
      ∀ (st : Ev → σ), Measurable st →
      ∀ (Gs cz : σ → Fin 3 → ℝ) (Fam : Finset σ), (∀ x ∈ E0, st x ∈ Fam) →
      ∀ (Q : Set Ev), MeasurableSet Q →
      ∀ (πv : Measure (Fin 2 → ℤ)) [IsProbabilityMeasure πv],
      ∀ (K ξ ε p err ηq ps wv pv Vq Kr Kd εg Vd η : ℝ),
      1 ≤ K → 0 < ξ → C * K ^ e * ξ ≤ 1 → 0 ≤ ε → ε ≤ ξ → ξ ≤ p → p ≤ 1 →
      0 ≤ err → err ≤ p →
      (∀ w ∈ Q, w ∈ Eref ∧ start T j ≤ w.2 ∧ w.2 ≤ start T j + clock T ∧
        QualWitness Eref st Gs (start T j) (clock T) M K err (1 / K) w) →
      0 ≤ Vq → (∀ w ∈ Q, ∀ k, |lineVel w.1 k| ≤ Vq) →
      0 ≤ ηq → 0 ≤ ps → 0 < (1 - ηq) ^ 3 - 2 * ps →
      (∀ D ∈ Fam, ((ν.prod volume).restrict E0) (st ⁻¹' {D} \ Q) ≤
        ENNReal.ofReal ηq * ((ν.prod volume).restrict E0) (st ⁻¹' {D})) →
      0 < wv → 0 < pv → pv ≤ wv / 2 → pv / 2 ≤ ξ →
      max 1 (Vq + pv) ≤ K → 2 * (max 1 (Vq + pv)) ^ 2 / (wv / 2) ^ 2 ≤ K →
      (∀ D ∈ Fam, ∀ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 → ∀ s : ℝ,
        ((ν.prod volume).restrict E0) (st ⁻¹' {D} ∩
            {x | |⟪n, (WithLp.toLp 2 (lineVel x.1) : EuclideanSpace ℝ (Fin 2))⟫ - s| ≤ wv}) ≤
          ENNReal.ofReal ps * ((ν.prod volume).restrict E0) (st ⁻¹' {D})) →
      0 ≤ Kr →
      (∀ D ∈ Fam, ∀ b : Fin 2 → ℤ,
        ((ν.prod volume).restrict E0) ({x | velBinOf pv (lineVel x.1) = b} ∩ (st ⁻¹' {D} ∩ Q)) ≤
          ENNReal.ofReal Kr * ((ν.prod volume).restrict E0) (st ⁻¹' {D}) * πv {b}) →
      (∀ x ∈ Eref, ∀ i, |packetZ T j c u x i - cz (st x) i| ≤ ε) →
      (∀ D ∈ Fam, ∀ i, |cz D i| ≤ K) → (∀ D ∈ Fam, ∀ i, |Gs D i| ≤ K) →
      (∀ c' : Fin 3 → ℝ, ∃ F : Finset (Fin 3 → ℤ), (F.card : ℝ) ≤ K ∧
        ∀ x ∈ Eref, (∀ i, |packetZ T j c u x i - c' i| ≤ 30 * K ^ 2 * ξ) →
          cell p (Gs (st x)) ∈ F) →
      (∀ (c' : Fin 3 → ℝ) (r : ℝ), 0 < r →
        (ν.prod volume).real (E0 ∩ {x | ∀ i, |packetZ T j c u x i - c' i| ≤ r}) ≤
          Kd * r ^ 3 * (ν.prod volume).real E0) →
      Kd * Kr ^ 3 / ((1 - ηq) ^ 3 - 2 * ps) ≤ K →
      0 < (ν.prod volume).real E0 →
      (∀ x ∈ E0, |ParentSignal.rate P x.1 x.2 -
        ∑ i : Fin 3, direction x.1 i * Gs (st x) i| ≤ εg) →
      (∀ x ∈ E0, ∀ i, |direction x.1 i| ≤ Vd) → 0 ≤ η →
      ∃ (Tf : Fin 3 → MvPolynomial (Fin 3) ℝ) (times : Ln → Set ℝ) (S : Set Ev),
        MeasurableSet S ∧ S ⊆ E0 ∧
        (∀ i, (Tf i).totalDegree ≤ 3 * M) ∧ (∀ i m, |(Tf i).coeff m| ≤ C * K ^ e) ∧
        (∀ z ∈ S, times z.1 ⊆ Icc (0 : ℝ) 1 ∧ ENNReal.ofReal η ≤ volume (times z.1)) ∧
        (∀ z ∈ S, ∀ s ∈ times z.1,
          |ParentSignal.rate P z.1 (start T j + clock T * s) - ∑ i : Fin 3,
            direction z.1 i * MvPolynomial.eval
              (fun i => packetBase T j c u (z.1, start T j + clock T * s) i) (Tf i)| ≤
            εg + 3 * Vd * (C * K ^ e * p)) ∧
        (∀ D : σ, S ∩ st ⁻¹' {D} = ∅ ∨
          (ν.prod volume) (E0 ∩ st ⁻¹' {D}) ≤ 2 * (ν.prod volume) (S ∩ st ⁻¹' {D})) ∧
        (ν.prod volume).real E0 ≤ Kr ^ 3 / ((1 - ηq) ^ 3 - 2 * ps) * (C * K ^ e) *
          ((ν.prod volume).real S + 3 * (η * clock T) * (ν univ).toReal) := by
  obtain ⟨C, hC, e, hfield⟩ := cartesian_field_of_witnesses M
  refine ⟨C, hC, e, ?_⟩
  intro σ _ _ _ ν _ T j c u P E0 Eref hE0 hE0ref hwin st hst Gs cz Fam hFam Q hQm πv _ K ξ ε p
    err ηq ps wv pv Vq Kr Kd εg Vd η hK hξ hCξ hε hεξ hξp hp1 herr herrp hQ hVq hvQ hηq hps hc₁
    hqual hwv hpv hpvw hpvξ hJK hAK hstrip hKr hpal hcz hczK hGK hfl hdens hKd hpos hgraph hVd hη
  set μ : Measure Ev := (ν.prod volume).restrict E0 with hμ
  have hfinE0 : (ν.prod volume) E0 ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (measure_mono hwin)
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (by simp [Real.volume_Icc])
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hfinE0
  have hconc : μ E0ᶜ = 0 := by
    rw [hμ, Measure.restrict_apply hE0.compl, compl_inter_self, measure_empty]
  have hsub (X : Set Ev) (hX : X ⊆ E0) : μ X = (ν.prod volume) X := by
    rw [hμ, Measure.restrict_apply' hE0, inter_eq_left.mpr hX]
  have hμuniv : μ.real univ = (ν.prod volume).real E0 := by
    rw [measureReal_def, measureReal_def, hμ, Measure.restrict_apply_univ]
  have hbox (c' : Fin 3 → ℝ) (r : ℝ) :
      MeasurableSet {x : Ev | ∀ i, |packetZ T j c u x i - c' i| ≤ r} := by
    have hz : Measurable (packetZ T j c u) := by
      apply measurable_pi_iff.mpr
      intro i
      unfold packetZ
      have hpb := (continuous_packetBase' T j c u).measurable
      exact ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).measurable).comp hpb
    have heq : {x : Ev | ∀ i, |packetZ T j c u x i - c' i| ≤ r} =
        ⋂ i, {x | |packetZ T j c u x i - c' i| ≤ r} := by
      ext x
      simp
    rw [heq]
    exact MeasurableSet.iInter fun i => measurableSet_le
      (((measurable_pi_apply i).comp hz).sub_const _).abs measurable_const
  have hdens' : ∀ (c' : Fin 3 → ℝ) (r : ℝ), 0 < r →
      μ.real {x | ∀ i, |packetZ T j c u x i - c' i| ≤ r} ≤ Kd * r ^ 3 * μ.real univ := by
    intro c' r hr
    rw [hμuniv, measureReal_def, hμ, Measure.restrict_apply (hbox c' r), inter_comm]
    exact hdens c' r hr
  obtain ⟨Tf, S0, hS0, hS0sub, hS0sat, hdeg, hcoeff, hmass, hfit⟩ :=
    hfield μ E0 Eref hE0 hE0ref hconc st hst Gs cz (packetZ T j c u) lineVel measurable_lineVel
      (start T j) (clock T) (clock_pos T) (packetZ_time T j c u) (packetZ_line T j c u) Fam hFam
      Q hQm πv K ξ ε p err ηq ps wv pv Vq Kr Kd hK hξ hCξ hε hεξ hξp hp1 herr herrp hQ hVq hvQ
      hηq hps hc₁ hqual hwv hpv hpvw hpvξ hJK hAK hstrip hKr hpal hcz hczK hGK hfl hdens' hKd
      (by rwa [hμuniv])
  have hwin0 : S0 ⊆ univ ×ˢ Icc (start T j) (start T j + clock T) := hS0sub.trans hwin
  obtain ⟨hlongm, htimesub, htimesmem, hshort⟩ :=
    long_line_cut ν hS0 (clock_pos T) (η := η) hwin0
  set times : Ln → Set ℝ :=
    fun l => (fun s => start T j + clock T * s) ⁻¹' (Prod.mk l ⁻¹' S0) with htimes
  set long : Set Ln := {l | ENNReal.ofReal η ≤ volume (times l)} with hlong
  set Slong : Set Ev := S0 ∩ long ×ˢ univ with hSlong
  have hSlongm : MeasurableSet Slong := hS0.inter (hlongm.prod MeasurableSet.univ)
  obtain ⟨A', hA'm, hA'sub, hA'loss, hA'states⟩ :=
    state_thinning μ st hst hSlongm hS0 inter_subset_left
  have hA'E0 : A' ⊆ E0 := hA'sub.trans (inter_subset_left.trans hS0sub)
  refine ⟨Tf, times, A', hA'm, hA'E0, hdeg, hcoeff, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact ⟨htimesub z.1, (hA'sub hz).2.1⟩
  · intro z hz s hs
    set x : Ev := (z.1, start T j + clock T * s) with hx
    have hxS : x ∈ S0 := htimesmem z.1 s hs
    have hxE0 : x ∈ E0 := hS0sub hxS
    have hg := hgraph x hxE0
    have hf := hfit x hxS
    have hsplit : ∑ i : Fin 3, direction z.1 i *
        MvPolynomial.eval (fun i => packetBase T j c u x i) (Tf i) =
        ∑ i : Fin 3, direction z.1 i * Gs (st x) i -
          ∑ i : Fin 3, direction z.1 i * (Gs (st x) i - MvPolynomial.eval (packetZ T j c u x) (Tf i)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      change _ = _ - direction z.1 i * (Gs (st x) i - MvPolynomial.eval (fun i => packetBase T j c u x i) (Tf i))
      ring
    have hsum : |∑ i : Fin 3, direction z.1 i *
        (Gs (st x) i - MvPolynomial.eval (packetZ T j c u x) (Tf i))| ≤ 3 * Vd * (C * K ^ e * p) := by
      calc |∑ i : Fin 3, direction z.1 i *
            (Gs (st x) i - MvPolynomial.eval (packetZ T j c u x) (Tf i))|
          ≤ ∑ i : Fin 3, |direction z.1 i *
            (Gs (st x) i - MvPolynomial.eval (packetZ T j c u x) (Tf i))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin 3, Vd * (C * K ^ e * p) := by
            apply Finset.sum_le_sum
            intro i _
            rw [abs_mul]
            exact mul_le_mul (hVd x hxE0 i) (hf i) (abs_nonneg _)
              ((abs_nonneg _).trans (hVd x hxE0 i))
        _ = 3 * Vd * (C * K ^ e * p) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            simp only [nsmul_eq_mul, Nat.cast_ofNat]
            ring
    change |ParentSignal.rate P x.1 x.2 - ∑ i : Fin 3, direction x.1 i *
        MvPolynomial.eval (fun i => packetBase T j c u x i) (Tf i)| ≤ _
    rw [hsplit]
    calc |ParentSignal.rate P x.1 x.2 - (∑ i : Fin 3, direction z.1 i * Gs (st x) i -
          ∑ i : Fin 3, direction z.1 i *
            (Gs (st x) i - MvPolynomial.eval (packetZ T j c u x) (Tf i)))|
        = |(ParentSignal.rate P x.1 x.2 - ∑ i : Fin 3, direction x.1 i * Gs (st x) i) +
            ∑ i : Fin 3, direction z.1 i *
              (Gs (st x) i - MvPolynomial.eval (packetZ T j c u x) (Tf i))| := by
          congr 1
          ring
      _ ≤ |ParentSignal.rate P x.1 x.2 - ∑ i : Fin 3, direction x.1 i * Gs (st x) i| +
            |∑ i : Fin 3, direction z.1 i *
              (Gs (st x) i - MvPolynomial.eval (packetZ T j c u x) (Tf i))| := abs_add_le _ _
      _ ≤ εg + 3 * Vd * (C * K ^ e * p) := add_le_add hg hsum
  · intro D
    rcases hA'states D with h0 | ⟨_, hhalf⟩
    · exact Or.inl h0
    · by_cases hne : (A' ∩ st ⁻¹' {D}).Nonempty
      · right
        obtain ⟨y, hyA, hyD⟩ := hne
        have hyS0 : y ∈ S0 := (hA'sub hyA).1
        have hE0D : E0 ∩ st ⁻¹' {D} ⊆ S0 ∩ st ⁻¹' {D} := by
          rintro x ⟨hxE0, hxD⟩
          refine ⟨hS0sat x hxE0 y hyS0 ?_, hxD⟩
          rw [show st x = D from hxD, show st y = D from hyD]
        calc (ν.prod volume) (E0 ∩ st ⁻¹' {D}) ≤ (ν.prod volume) (S0 ∩ st ⁻¹' {D}) :=
              measure_mono hE0D
          _ = μ (S0 ∩ st ⁻¹' {D}) := (hsub _ (inter_subset_left.trans hS0sub)).symm
          _ ≤ 2 * μ (A' ∩ st ⁻¹' {D}) := hhalf
          _ = 2 * (ν.prod volume) (A' ∩ st ⁻¹' {D}) := by
              rw [hsub _ (inter_subset_left.trans hA'E0)]
      · left
        exact not_nonempty_iff_eq_empty.mp hne
  · have hS0diff : μ (S0 \ Slong) ≤ ENNReal.ofReal (η * clock T) * ν univ := by
      rw [hsub _ (sdiff_subset.trans hS0sub)]
      have heq : S0 \ Slong = S0 \ (long ×ˢ univ) := by
        ext x
        simp only [hSlong, mem_sdiff, mem_inter_iff]
        tauto
      rw [heq]
      exact hshort
    have hloss : (ν.prod volume) (S0 \ A') ≤ 3 * (ENNReal.ofReal (η * clock T) * ν univ) := by
      rw [← hsub _ (sdiff_subset.trans hS0sub)]
      exact hA'loss.trans (mul_le_mul' le_rfl hS0diff)
    have hS0le : (ν.prod volume).real S0 ≤
        (ν.prod volume).real A' + 3 * (η * clock T) * (ν univ).toReal := by
      have hfinA' : (ν.prod volume) A' ≠ ⊤ :=
        ne_top_of_le_ne_top hfinE0 (measure_mono hA'E0)
      have h1 : (ν.prod volume) S0 ≤ (ν.prod volume) A' + (ν.prod volume) (S0 \ A') := by
        calc (ν.prod volume) S0 ≤ (ν.prod volume) (A' ∪ (S0 \ A')) := measure_mono (by
              intro x hx
              by_cases hxA : x ∈ A'
              · exact Or.inl hxA
              · exact Or.inr ⟨hx, hxA⟩)
          _ ≤ _ := measure_union_le _ _
      have h2 := h1.trans (add_le_add le_rfl hloss)
      have h3 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfinA', ENNReal.mul_ne_top
        ENNReal.ofNat_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))⟩) h2
      rw [ENNReal.toReal_add hfinA' (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))), ENNReal.toReal_mul,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hη (clock_pos T).le)] at h3
      rw [measureReal_def, measureReal_def]
      simpa [mul_assoc] using h3
    have hμS0 : μ.real S0 = (ν.prod volume).real S0 := by
      rw [measureReal_def, measureReal_def, hsub _ hS0sub]
    rw [← hμuniv]
    calc μ.real univ ≤ Kr ^ 3 / ((1 - ηq) ^ 3 - 2 * ps) * (C * K ^ e) * μ.real S0 := hmass
      _ ≤ Kr ^ 3 / ((1 - ηq) ^ 3 - 2 * ps) * (C * K ^ e) *
          ((ν.prod volume).real A' + 3 * (η * clock T) * (ν univ).toReal) := by
          rw [hμS0]
          apply mul_le_mul_of_nonneg_left hS0le
          have : 0 ≤ Kr ^ 3 := by positivity
          have : 0 ≤ C * K ^ e := by positivity
          positivity

/-- The volume of a closed cube of half-side `r` in `P3`. -/
theorem volume_cube_P3 (c : Fin 3 → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume {y : P3 | ∀ i, |y i - c i| ≤ r} = ENNReal.ofReal ((2 * r) ^ 3) := by
  have hpre : {y : P3 | ∀ i, |y i - c i| ≤ r} =
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm ⁻¹'
        Set.pi univ (fun i => Icc (c i - r) (c i + r)) := by
    ext y
    simp only [mem_ofPred_eq, mem_preimage, mem_pi, mem_univ, true_implies, mem_Icc]
    constructor
    · intro h i
      have := abs_le.mp (h i)
      exact ⟨by change c i - r ≤ y i; linarith, by change y i ≤ c i + r; linarith⟩
    · intro h i
      have h1 : c i - r ≤ y i := (h i).1
      have h2 : y i ≤ c i + r := (h i).2
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [hpre, (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).measure_preimage
    (MeasurableSet.univ_pi fun i => measurableSet_Icc).nullMeasurableSet, volume_pi_pi]
  simp only [Real.volume_Icc, add_sub_sub_cancel, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by linarith)]
  congr 1
  ring

/-- **Base density of a dense part of a frozen packet.** The frozen base
ceiling and a mass floor give the base density input of
`frozen_field_long_fits`, with `Kd = 8 K K₁`. -/
theorem field_density_of_ceiling (ν : Measure Ln) (T j : ℕ) (c u : P2) (A : Set Ln)
    {S E0 : Set Ev} (hE0S : E0 ⊆ S) {K K₁ : ℝ} (hK : 0 ≤ K) (hK₁ : 0 ≤ K₁)
    (hceil : ∀ U : Set P3, MeasurableSet U →
        ((ν.prod volume).restrict S) {p | packetBase T j c u p ∈ U} ≤
          ENNReal.ofReal K * (ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ * ν A) * volume U)
    (hfloor : ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ * ν A ≤ ENNReal.ofReal K₁ * (ν.prod volume) E0)
    (hfin : (ν.prod volume) E0 ≠ ⊤) :
    ∀ (c' : Fin 3 → ℝ) (r : ℝ), 0 < r →
      (ν.prod volume).real (E0 ∩ {x | ∀ i, |packetZ T j c u x i - c' i| ≤ r}) ≤
        (8 * K * K₁) * r ^ 3 * (ν.prod volume).real E0 := by
  intro c' r hr
  set U : Set P3 := {y : P3 | ∀ i, |y i - c' i| ≤ r} with hUdef
  have hU : MeasurableSet U := by
    have heq : U = ⋂ i, {y : P3 | |y i - c' i| ≤ r} := by
      ext y
      simp [hUdef]
    rw [heq]
    exact MeasurableSet.iInter fun i => measurableSet_le
      ((((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).measurable).sub_const _).abs)
      measurable_const
  have hbox : {x : Ev | ∀ i, |packetZ T j c u x i - c' i| ≤ r} = packetBase T j c u ⁻¹' U := rfl
  have hpre : MeasurableSet (packetBase T j c u ⁻¹' U) :=
    (continuous_packetBase' T j c u).measurable hU
  have hle : (ν.prod volume) (E0 ∩ {x | ∀ i, |packetZ T j c u x i - c' i| ≤ r}) ≤
      ENNReal.ofReal K * (ENNReal.ofReal K₁ * (ν.prod volume) E0) *
        ENNReal.ofReal ((2 * r) ^ 3) := by
    rw [hbox]
    calc (ν.prod volume) (E0 ∩ packetBase T j c u ⁻¹' U)
        ≤ ((ν.prod volume).restrict S) (packetBase T j c u ⁻¹' U) := by
          rw [Measure.restrict_apply hpre, inter_comm]
          exact measure_mono (inter_subset_inter_right _ hE0S)
      _ ≤ ENNReal.ofReal K * (ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ * ν A) * volume U := hceil U hU
      _ ≤ ENNReal.ofReal K * (ENNReal.ofReal K₁ * (ν.prod volume) E0) *
            ENNReal.ofReal ((2 * r) ^ 3) := by
          rw [hUdef, volume_cube_P3 c' hr.le]
          exact mul_le_mul' (mul_le_mul' le_rfl hfloor) le_rfl
  have hfin' : ENNReal.ofReal K * (ENNReal.ofReal K₁ * (ν.prod volume) E0) *
      ENNReal.ofReal ((2 * r) ^ 3) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)) ENNReal.ofReal_ne_top
  have h := ENNReal.toReal_mono hfin' hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK,
    ENNReal.toReal_ofReal hK₁, ENNReal.toReal_ofReal (by positivity)] at h
  rw [measureReal_def, measureReal_def]
  calc ((ν.prod volume) (E0 ∩ {x | ∀ i, |packetZ T j c u x i - c' i| ≤ r})).toReal
      ≤ K * (K₁ * ((ν.prod volume) E0).toReal) * (2 * r) ^ 3 := h
    _ = (8 * K * K₁) * r ^ 3 * ((ν.prod volume) E0).toReal := by ring

/-- **State centers from base codes.** If the state determines the base code
at mesh `ε`, the code centers are within `ε` of the base. -/
theorem state_center_of_base_code {σ : Type*} (T j : ℕ) (c u : P2) (st : Ev → σ)
    (code : σ → Fin 3 → ℤ) {ε : ℝ} (hε : 0 < ε)
    (hcode : ∀ x, code (st x) = fun i => ⌊packetZ T j c u x i / ε⌋) :
    ∀ x, ∀ i, |packetZ T j c u x i - (fun D i => ε * ((code D i : ℝ) + 1 / 2)) (st x) i| ≤ ε := by
  intro x i
  have hc := congrFun (hcode x) i
  dsimp only
  rw [hc]
  have h1 := Int.floor_le (packetZ T j c u x i / ε)
  have h2 := Int.lt_floor_add_one (packetZ T j c u x i / ε)
  have h1' : ε * (⌊packetZ T j c u x i / ε⌋ : ℝ) ≤ packetZ T j c u x i := by
    have := mul_le_mul_of_nonneg_left h1 hε.le
    rwa [mul_div_cancel₀ _ hε.ne'] at this
  have h2' : packetZ T j c u x i < ε * ((⌊packetZ T j c u x i / ε⌋ : ℝ) + 1) := by
    have := mul_lt_mul_of_pos_left h2 hε
    rwa [mul_div_cancel₀ _ hε.ne'] at this
  rw [abs_le]
  constructor <;> nlinarith

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
