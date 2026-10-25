import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.SourceNormalization
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.FrameFacts

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory MvPolynomial PhysicalPotentialData

noncomputable section

namespace SourceNormalization

/-- The discriminant coefficients of an actual source group have a bound
depending only on its degree, source constant and relative density. Large
coefficients of the original parent do not enter this estimate. -/
theorem source_discriminant_coeff_bound (q:ℕ) (hq:2≤q) :
    ∃ Cq:ℝ, 0<Cq ∧
    ∀ {T j:ℕ} {ν:Measure Ln} [IsFiniteMeasure ν] {B a ζ d:ℝ} {c u:P2} {P0:Po}
      {A:Set Ln} {F H:Set Ev} (source:PhysicalSource q ν B a ζ d T j c u P0 A F H),
    P0.totalDegree≤2 → 0<B → j<2^T →
    source.S ⊆ A ×ˢ Icc ((j:ℝ)*((2:ℝ)^T)⁻¹)
      ((j:ℝ)*((2:ℝ)^T)⁻¹+((2:ℝ)^T)⁻¹) →
    ∀ {w D:ℝ} (g:ℤ) (G:Set Ev), 0<w → ζ≤w → 1≤D →
      32*source.K^3*(a*w)≤1 → MeasurableSet G → G ⊆ source.S →
      (∀e∈G,e.1∈source.groupLines w g) → 0<(ν.prod volume) G →
      (∀U:Set P3,MeasurableSet U →
        ((ν.prod volume).restrict G) {e | packetBase T j c u e∈U} ≤
          ENNReal.ofReal D*((ν.prod volume).restrict G) univ*volume U) →
    let ci := inverseShift T j c u (8*source.K) (fun _ => 1/8)
    let Mi := inverseMatrix T (8*source.K)
    let Sx := Analytic.transportPolynomial ci Mi B⁻¹ (P0-C (physicalGroupCenter a w g))
    let Px := Analytic.basePullback ci Mi (Broad.parentPotentialPullback T j c u source.Pot)
    ∀m, |(Analytic.nativeBaseDiscriminant (Analytic.nativeA Sx) (Analytic.nativeB Sx)
      (Analytic.nativeC Sx Px)).coeff m| ≤
      Cq*(32*(((2*q:ℕ):ℝ)+1)*(D*(8*source.K)^3))^(3*(2*q))*((2*source.K)^2+1) := by
  obtain ⟨Cq,hCq,hdisc⟩ := Analytic.discriminant_coeff_bound_of_group q
  refine ⟨Cq,hCq,?_⟩
  intro T j ν _ B a ζ d c u P0 A F H source hP0 hB hj hSA w D g G hw hζw hD hsmall hG hGS
    hlines hGpos hdom ci Mi Sx Px
  have hK : 0<source.K := by linarith [source.K_two]
  have ha : 0<a := source.a_pos
  have hs : 0<8*source.K := by positivity
  have hDpos : 0<D := by linarith
  let cf := shift T j c u (8*source.K) (fun _ => 1/8)
  let Mf := matrix T (8*source.K)
  have hinv := inverse T j c u hs (fun _ => 1/8)
  have hBi : B⁻¹*B=1 := inv_mul_cancel₀ hB.ne'
  let X : Ev → P3 := fun e => (Analytic.pointOfCoordinates
    (Analytic.coordinateMap cf Mf B (Analytic.graphPoint e.1 e.2))).1
  have hXeq (e:Ev) : X e = baseMap (8*source.K) (fun _ => 1/8) (packetBase T j c u e) := by
    ext i
    simpa only [X,cf,Mf,baseMap,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,div_eq_inv_mul] using
      normalized_base_apply T j c u hs (fun _ => 1/8) B e i
  have hSdeg : Sx.totalDegree≤2 := (Analytic.totalDegree_transportPolynomial_le _ _ _ _).trans
    ((totalDegree_sub _ _).trans (max_le hP0 (by simp)))
  have hPdeg : Px.totalDegree≤q := (Analytic.totalDegree_basePullback _ _ _).trans
    ((Broad.totalDegree_parentPotentialPullback _ _ _ _ _).trans source.degree)
  have hBdeg : (Analytic.nativeB Sx).totalDegree≤q :=
    (Analytic.totalDegree_nativeB Sx hSdeg).trans (by omega)
  have hCdeg : (Analytic.nativeC Sx Px).totalDegree≤q :=
    Analytic.totalDegree_nativeC Sx Px hSdeg hq hPdeg
  have hrawbound := original_block_mass_le ν A ((j:ℝ)*((2:ℝ)^T)⁻¹) ((2:ℝ)^T)⁻¹ G
    (hGS.trans hSA)
  rw [Measure.restrict_apply_univ] at hrawbound
  have hGfin : (ν.prod volume) G≠⊤ := ne_top_of_le_ne_top (by finiteness) hrawbound
  let m : ℝ := (ν.prod volume).real G
  have hm : 0 < m := ENNReal.toReal_pos hGpos.ne' hGfin
  have hmass : ENNReal.ofReal m=(ν.prod volume) G := ENNReal.ofReal_toReal hGfin
  let β : ℝ := D*(8*source.K)^3*m
  have hβ : 0<β := by dsimp [β]; positivity
  have hmβ : m≤β := by
    have hmul : 1≤D*(8*source.K)^3 := by
      have hpow := one_le_pow₀ (by linarith [source.K_two] : 1≤8*source.K) (n:=3)
      nlinarith
    dsimp [β]
    nlinarith
  have hdomraw (U:Set P3) (hU:MeasurableSet U) :
      (ν.prod volume) (G ∩ packetBase T j c u ⁻¹' U) ≤
        ENNReal.ofReal D*(ν.prod volume) G*volume U := by
    simpa only [Measure.restrict_apply' hG,Measure.restrict_apply_univ,inter_comm,
      inter_univ,Set.preimage] using hdom U hU
  have hnormdom := density_after_normalization (ν.prod volume) G (packetBase T j c u)
    hDpos.le hs (fun _ => 1/8) hdomraw
  have hβeq : ENNReal.ofReal (D*(8*source.K)^3)*(ν.prod volume) G=ENNReal.ofReal β := by
    rw [←hmass,←ENNReal.ofReal_mul (by positivity : 0≤D*(8*source.K)^3)]
  have hPiDom (U:Set (Fin 3 → ℝ)) (hU:MeasurableSet U) :
      ((ν.prod volume).restrict G) ((fun e i => X e i) ⁻¹' U) ≤ ENNReal.ofReal β*volume U := by
    let Up : Set P3 := (WithLp.ofLp:P3 → Fin 3 → ℝ) ⁻¹' U
    have hUp : MeasurableSet Up := hU.preimage (measurable_pi_iff.mpr fun i =>
      (PiLp.continuous_apply 2 (fun _:Fin 3 => ℝ) i).measurable)
    have hvol : volume Up=(volume:Measure (Fin 3 → ℝ)) U := by
      rw [←(PiLp.volume_preserving_toLp (Fin 3)).measure_preimage hUp.nullMeasurableSet]
      rfl
    have hx := hnormdom Up hUp
    rw [hβeq,hvol] at hx
    have hset : (fun e => baseMap (8*source.K) (fun _ => 1/8) (packetBase T j c u e)) ⁻¹' Up =
        (fun e i => X e i) ⁻¹' U := by
      ext e
      change WithLp.ofLp (baseMap (8*source.K) (fun _ => 1/8) (packetBase T j c u e)) ∈ U ↔ _
      rw [←hXeq e]
      rfl
    rw [hset] at hx
    rw [Measure.restrict_apply' hG,inter_comm]
    exact hx
  obtain ⟨e0,he0⟩ := nonempty_of_measure_ne_zero (μ:=ν.prod volume) hGpos.ne'
  have hPsub : (P0-C (physicalGroupCenter a w g)).totalDegree≤2 :=
    (totalDegree_sub _ _).trans (max_le hP0 (by simp))
  have hAc : |Analytic.nativeA Sx| ≤ source.K/2 := by
    have hcurv : |eval (xp e0.1 0) (pderiv 3 (pderiv 3
        (P0-C (physicalGroupCenter a w g))))| ≤ source.K*B^2/1 := by
      simpa using ((source.point_bounds e0 (hGS he0)).2.2.1 0 (by norm_num)).2.2
    simpa only [mul_one] using Broad.abs_nativeA_transport_le hPsub ci Mi hB hBi
      (by norm_num : (0:ℝ)<1) (xp e0.1 0) hcurv
  have hsmall' : 4*|Analytic.nativeA Sx| * (2*a*w) ≤ (2*(2*source.K)^2)⁻¹ := by
    calc _ ≤ 4*(source.K/2)*(2*a*w) := by gcongr
      _ ≤ _ := by
        rw [←one_div,le_div_iff₀ (by positivity : 0<2*(2*source.K)^2)]
        convert hsmall using 1 <;> ring
  have htrace : ∀ᵐ e ∂(ν.prod volume).restrict G,
      (fun i => X e i) ∈ Icc (0:Fin 3 → ℝ) 1 ∧ ∃v:ℝ,
      |Analytic.nativeA Sx*v^2+eval (fun i => X e i) (Analytic.nativeB Sx)*v+
        eval (fun i => X e i) (Analytic.nativeC Sx Px)| ≤ 2*a*w ∧
      (2*source.K)⁻¹≤|2*Analytic.nativeA Sx*v+eval (fun i => X e i) (Analytic.nativeB Sx)| ∧
      |2*Analytic.nativeA Sx*v+eval (fun i => X e i) (Analytic.nativeB Sx)| ≤ 2*source.K := by
    filter_upwards [ae_restrict_mem hG] with e he
    have htime : e.2∈Icc ((j:ℝ)*((2:ℝ)^T)⁻¹) (((j:ℝ)+1)*((2:ℝ)^T)⁻¹) := by
      simpa only [add_mul,one_mul] using (hSA (hGS he)).2
    have hphys := source.physical_group_point_near hP0 hB hj hw hζw e (hGS he) (hlines e he)
      htime rfl htime (by simp; positivity)
    have hcube := source_cube source e (hGS he)
    have hball : X e ∈ Metric.ball (0:P3) 4 := by
      rw [Metric.mem_ball,dist_zero_right]
      exact lt_of_le_of_lt hcube.2 (by norm_num)
    obtain ⟨⟨_,hfit,_,hlo,hhi⟩,_⟩ :=
      Analytic.certifiedGroupPoint_of_physical hinv.1 hinv.2 hBi hphys hball
    change |eval ![X e 0,X e 1,X e 2,_] Sx-eval (fun i => X e i) Px| ≤ 2*a*w at hfit
    rw [Analytic.native_equation Sx hSdeg Px] at hfit
    rw [Analytic.native_derivative Sx hSdeg] at hlo hhi
    refine ⟨⟨fun i => (hcube.1 i).1,fun i => (hcube.1 i).2.trans (by norm_num)⟩,_,hfit,hlo,hhi⟩
  have hbound := hdisc Ev ((ν.prod volume).restrict G) (fun e i => X e i)
    (Analytic.nativeA Sx) (Analytic.nativeB Sx) (Analytic.nativeC Sx Px) hBdeg hCdeg
    m β (2*a*w) (2*source.K) hm hβ hmβ (by linarith [source.K_two]) hsmall'
    (by rw [Measure.restrict_apply_univ,hmass]) hPiDom htrace
  have hratio : m/β=(D*(8*source.K)^3)⁻¹ := by dsimp [β]; field_simp
  intro n
  simpa only [hratio,div_inv_eq_mul,mul_assoc] using hbound n

end SourceNormalization

end

end Submission.Obl.k4_physical_parent_potential_candidates
