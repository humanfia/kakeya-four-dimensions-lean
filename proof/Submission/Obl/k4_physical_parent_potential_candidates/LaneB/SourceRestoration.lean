import Submission.Obl.k4_physical_parent_potential_candidates.Restoration
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.SourceDiscriminant
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.SourcePhysicalWindow
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.SourceSevenInputs
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.ZoomBranch
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.NormalizedRestoration
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.PhysicalReturn
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.SourceAccuracy
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.SourceReturnPowers
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.SourcePowerSelection
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.SourceMeasure
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.SourceChartBounds
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.SourceBranchBounds

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory MvPolynomial Metric PhysicalPotentialData SourceNormalization

noncomputable section

/-- Restore a quadratic from the literal physical source, its original
fine-state breadth and its original group measure. -/
theorem source_restoration (hR : Analytic.DenseJet.SheetRemezAssertion) : RestorationAssertion := by
  intro Cden hCden q hq
  obtain ⟨Cd,hCd,hdisc⟩ := source_discriminant_coeff_bound q hq
  obtain ⟨Cx,hCx,hwindow⟩ := PhysicalSource.exists_extrapolated_group_window q
  obtain ⟨Cj,hCj,hcore⟩ := exists_seven_tube_core q hq
  obtain ⟨I,hI,hIbound⟩ := exists_initial_source_power q hCden hCd
  obtain ⟨Mexp,qz,hMexp,hqz,hzoom⟩ := Analytic.zoomed_branch_of_physical_group q hq
  obtain ⟨Ab,CW,hAb,hCW,hrestore⟩ := Analytic.normalized_restoration hR q
  obtain ⟨M,hM,hMbound⟩ := exists_final_source_power q I qz Mexp Ab Cx Cj Cden
  refine ⟨M*(2*CW+40),M*(7*CW+61),coefficientPower M CW,1,by norm_num,?_⟩
  intro Nk Mp Dp Mr κ T j rr B ζ d c u Qm Rb P0 Asrc F H ex ν _ source
    hNk hκ hκK hB hBN hBiN hTN hP0 hPcoeff hch hj hrr hd hd1 hSA
    w g beta G hw hw2 hcount hmargin hG hGsub hlines hbroad hbase hrel hGpos
  simp only [one_mul]
  let K := source.K
  let a := δ Nk rr
  let h := ((2:ℝ)^T)⁻¹
  let μ : Measure Ev := ν.prod volume
  let A0 := K^M
  let AR := K^I
  let lam := (AR^qz)^Mexp
  let D := Cden*K^209
  let Zloss := (AR^qz)^(3*(1+(Mexp+1))+14)
  let epsfit := Cx*(a*ζ)+a*w
  let epsc := Cj*(8*K)^3*a*ζ
  let Mz := (((((q+1)^3:ℕ):ℝ)^2)*K*(18*K)^q)*h
  let hdelt := lam*source.ε
  let b := errorPadding A0 CW a w
  let Eb := paddedError A0 CW a w epsc Mz hdelt
  have hK : 2 ≤ K := source.K_two
  have hK0 : 0 < K := by linarith only [hK]
  have hK1 : 1 ≤ K := by linarith only [hK]
  have ha : 0 < a := source.a_pos
  have hh : 0 < h := by dsimp only [h]; positivity
  have hζ : 0 < ζ := source.ε_pos.trans_le source.ε_le
  have hζ0 : 0 ≤ ζ := hζ.le
  have hD : 1 ≤ D := by
    exact one_le_mul_of_one_le_of_one_le hCden (one_le_pow₀ hK1)
  obtain ⟨hAR,hA1R,hdiscpower⟩ := hIbound K hK
  obtain ⟨hA0,hlarge,hAtv,hDet⟩ := power_frame_bounds hK hM
  obtain ⟨hAbA,hCxA,hCjA,hMzA0,hlamA,hZlossA,hDensityA⟩ := hMbound K hK
  have hA01 : 1 ≤ A0 := by exact le_trans (by norm_num) hA0
  have hA0pos : 0 < A0 := by exact lt_of_lt_of_le (by norm_num) hA0
  have hlam : 1 ≤ lam := by
    exact one_le_pow₀ (one_le_pow₀ (by linarith only [hAR] : 1 ≤ AR))
  have hLamPos : 0 < lam := by linarith only [hlam]
  have hZloss : 0 < Zloss := by dsimp only [Zloss]; positivity
  have hmarginA : A0^(2*CW+40)*ζ ≤ w := normalized_margin M CW hmargin
  have hsmall (n:ℕ) (hn:n ≤ 2*CW+40) : A0^n*ζ ≤ w :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA01 hn) hζ0).trans hmarginA
  have hζw : ζ ≤ w := by simpa using hsmall 0 (by omega)
  have haw : 0 < a*w := mul_pos ha hw
  have hfit : 0 < epsfit := by dsimp only [epsfit]; positivity
  have hfitA : epsfit ≤ A0*(a*w) := by
    calc
      _ ≤ Cx*(a*w)+a*w := by dsimp only [epsfit]; gcongr
      _ = (Cx+1)*(a*w) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCxA haw.le
  have hepsc0 : 0 ≤ epsc := by dsimp only [epsc]; positivity
  have hepscA : epsc ≤ A0*a*ζ := by
    calc
      _ = (512*Cj*K^3)*a*ζ := by dsimp only [epsc]; ring
      _ ≤ _ := by gcongr
  have hMz0 : 0 ≤ Mz := by dsimp only [Mz]; positivity
  have hMzA : Mz ≤ A0*h := mul_le_mul_of_nonneg_right hMzA0 hh.le
  have haKζ : a ≤ K*ζ := source.a_le.trans
    (mul_le_mul_of_nonneg_left source.clock_le hK0.le)
  have hεclock : h*source.ε ≤ a*ζ := by
    calc
      _ ≤ h*((a/h)*ζ) := mul_le_mul_of_nonneg_left source.ε_clock hh.le
      _ = _ := by field_simp
  have herrors := source_error_bounds CW hA0 hK
    (show 2*K ≤ A0 from (by linarith only [hAtv])) hh ha hζ0 source.ε_pos.le hw hw2
    hlam hlamA source.a_le source.clock_le source.ε_le hεclock hfitA hepsc0 hepscA hMz0 hMzA hmarginA
  have hEb : 0 < Eb := herrors.error_pos
  have hEbWidth : a*w ≤ Eb := herrors.width_le_error
  have hEbUpper : Eb ≤ A0^(CW+31)*(a*w) := herrors.error_upper
  have hEbSmall : Eb*A0^CW ≤ 1 := herrors.error_accuracy
  have hband0 : 0 ≤ epsfit*(2*K)^19 := by positivity
  have hbandEb : epsfit*(2*K)^19 ≤ Eb :=
    (le_mul_of_one_le_left hband0 (one_le_pow₀ hA01)).trans herrors.fit_in_tube
  have hEb1 : Eb ≤ 1 :=
    (le_mul_of_one_le_right hEb.le (one_le_pow₀ hA01)).trans hEbSmall
  have hband1 : epsfit*(2*K)^19 ≤ 1 := hbandEb.trans hEb1
  obtain ⟨hdiscrsmall,hcurvsmall⟩ := source_curvature_bounds hA0 hK hlarge ha hζ0 hw
    (by linarith only [hw2]) haKζ hfitA (hsmall 2 (by omega))
  have hGS : G ⊆ source.S := fun e he => source.positive_events_subset (hGsub he).1.1
  have hGpositive : G ⊆ source.positiveEvents := fun e he => (hGsub he).1.1
  obtain ⟨e0,he0⟩ := nonempty_of_measure_ne_zero (μ:=μ) hGpos.ne'
  have hR0 : (P0-C (physicalGroupCenter a w g)).totalDegree ≤ 2 :=
    (totalDegree_sub _ _).trans (max_le hP0 (by simp))
  have hNative (ci:Fin 3 → ℝ) (Mi:Matrix (Fin 3) (Fin 3) ℝ) :
      |Analytic.nativeA (Analytic.transportPolynomial ci Mi B⁻¹
        (P0-C (physicalGroupCenter a w g)))| ≤ K/2 := by
    have hp : |eval (xp e0.1 0) (pderiv 3 (pderiv 3
        (P0-C (physicalGroupCenter a w g))))| ≤ K*B^2/1 := by
      simpa using ((source.point_bounds e0 (hGS he0)).2.2.1 0 (by norm_num)).2.2
    simpa only [mul_one] using Broad.abs_nativeA_transport_le hR0 ci Mi hB
      (inv_mul_cancel₀ hB.ne') (by norm_num : (0:ℝ)<1) (xp e0.1 0) hp
  have hphys (e:Ev) (he:e∈G) (t:ℝ) (ht:|t-e.2| ≤ h/(4*K^2)) :
      Analytic.PhysicalGroupPoint B⁻¹ (P0-C (physicalGroupCenter a w g)) Rb
        (Broad.parentPotentialPullback T j c u source.Pot) epsfit (2*K) (branchSign beta)
        (Cx*(κ*δ Nk rr)) (Analytic.graphPoint e.1 t) :=
    hwindow source hP0 hB hj hκ hκK hch hw g beta e (hGS he) (hlines e he)
      (hGsub he).2 t ht
  obtain ⟨U,hU,hUG,hlaw,hseven⟩ := hcore source hP0 hB hSA G hG hGpositive hbroad
  have hmassU : μ U=μ G := by
    simpa only [Measure.restrict_apply_univ] using congrArg (fun m:Measure Ev => m univ) hlaw
  have hUpos : 0 < μ U := by rw [hmassU]; exact hGpos
  have hraw := original_block_mass_le ν Asrc ((j:ℝ)*h) h G (hGS.trans hSA)
  rw [Measure.restrict_apply_univ] at hraw
  have hGfin : μ G ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hraw
  have hUfin : μ U ≠ ⊤ := by rw [hmassU]; exact hGfin
  have hcapU (E:Set P3) (hE:MeasurableSet E) :
      μ (U ∩ packetBase T j c u ⁻¹' E) ≤ ENNReal.ofReal D*μ U*volume E := by
    have hx := hrel E hE
    rw [←hlaw,Measure.restrict_apply_univ,Measure.restrict_apply' hU] at hx
    simpa only [Set.preimage,inter_comm] using hx
  let cf := shift T j c u (8*K) (fun _ => 1/8)
  let ci := inverseShift T j c u (8*K) (fun _ => 1/8)
  let Mf := matrix T (8*K)
  let Mi := inverseMatrix T (8*K)
  let X0 : Ev → P3 := fun e => Analytic.normalizedBase cf Mf B (Analytic.graphPoint e.1 e.2)
  have hinv := inverse T j c u (by positivity : 0 < 8*K) (fun _ => 1/8)
  have hXeq (e:Ev) : X0 e=baseMap (8*K) (fun _ => 1/8) (packetBase T j c u e) := by
    ext i
    simpa only [X0,cf,Mf,Analytic.normalizedBase,baseMap,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,div_eq_inv_mul] using
      normalized_base_apply T j c u (by positivity : 0 < 8*K) (fun _ => 1/8) B e i
  have hdom0 (E:Set P3) (hE:MeasurableSet E) :
      μ (U ∩ X0 ⁻¹' E) ≤ ENNReal.ofReal (D*(8*K)^3)*μ U*volume E := by
    have hx := density_after_normalization μ U (packetBase T j c u) (by linarith only [hD])
      (by positivity : 0 < 8*K) (fun _ => 1/8) hcapU E hE
    simpa only [←hXeq] using hx
  have hdiscbound := hdisc source hP0 hB hj hSA g G hw hζw hD hdiscrsmall hG hGS hlines hGpos hrel
  let Sx := Analytic.transportPolynomial ci Mi B⁻¹ (P0-C (physicalGroupCenter a w g))
  let Px := Analytic.basePullback ci Mi (Broad.parentPotentialPullback T j c u source.Pot)
  have hdiscboundAR (m) :
      |(Analytic.nativeBaseDiscriminant (Analytic.nativeA Sx) (Analytic.nativeB Sx)
        (Analytic.nativeC Sx Px)).coeff m| ≤ AR := (hdiscbound m).trans hdiscpower
  obtain ⟨_,hcu,_,_,hRb,_,_,_,_,hlinech,_,_⟩ := hch
  have hPot : (Broad.parentPotentialPullback T j c u source.Pot).totalDegree ≤ q :=
    (Broad.totalDegree_parentPotentialPullback _ _ _ _ _).trans source.degree
  have hsign : branchSign beta ≠ 0 := by cases beta <;> norm_num [branchSign]
  have hA1 : 2 ≤ 2*K := by linarith only [hK]
  have hsmall0 : 4*|Analytic.nativeA Sx| *epsfit ≤ (2*(2*K)^2)⁻¹ := by
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hNative ci Mi) (by norm_num)) hfit.le).trans hcurvsmall
  let mU := μ.real U
  let density0 := D*(8*K)^3
  let beta0 := density0*mU
  have hmU : 0 < mU := ENNReal.toReal_pos hUpos.ne' hUfin
  have hmUeq : ENNReal.ofReal mU=μ U := by
    exact ENNReal.ofReal_toReal hUfin
  have hdomAbs (E:Set P3) (hE:MeasurableSet E) :
      μ (U ∩ X0 ⁻¹' E) ≤ ENNReal.ofReal beta0*volume E := by
    calc
      _ ≤ ENNReal.ofReal density0*μ U*volume E := hdom0 E hE
      _ = _ := by rw [←hmUeq,←ENNReal.ofReal_mul (by dsimp only [density0]; positivity)]
  obtain ⟨cz,Gz,Fc,f,Delta,Up,Vp,Wp,sq,hcz,hGz,hGzU,hGzmass,hGzcap,hGzhalf,
    hFc,hf6,hmatch,hroot,hWne,hDeltaNe,hsqDiff,hDeltaDeg,hUpDeg,hVpDeg,hWpDeg,
    hsq,hpres,hWpPoint,hfExt,hGzPhys⟩ :=
    hzoom AR hAR hB cf ci Mf Mi B⁻¹ hinv.1 hinv.2 (inv_mul_cancel₀ hB.ne')
      (P0-C (physicalGroupCenter a w g)) Rb (Broad.parentPotentialPullback T j c u source.Pot)
      hR0 hRb hPot (branchSign beta) epsfit (2*K) (Cx*(κ*δ Nk rr)) hsign hA1 hA1R hsmall0
      hdiscboundAR U beta0 mU (h/(4*K^2)) hU hmU (by positivity) hUfin
      (by
        intro e he
        refine ⟨?_,fun t ht => hphys e (hUG he) t ht⟩
        rw [mem_closedBall,dist_zero_right]
        exact (source_cube source e (hGS (hUG he))).2.trans (by norm_num))
      hdomAbs hmUeq.le
  let cfZ := Analytic.zoomForwardShift cf cz lam
  let ciZ := Analytic.zoomShift ci Mi cz
  let MfZ := lam • Mf
  let MiZ := Analytic.zoomMatrix Mi lam
  let X : Ev → P3 := fun e => Analytic.normalizedBase cfZ MfZ B (Analytic.graphPoint e.1 e.2)
  let S0 := Analytic.transportPolynomial ciZ MiZ B⁻¹ (P0-C (physicalGroupCenter a w g))
  let Pnorm := zoomPotential T j c u (8*K) (fun _ => 1/8) cz lam source.Pot
  let Sc := Analytic.transportPolynomial ciZ MiZ B⁻¹ Rb
  have hzinv := Analytic.zoomForward_inverse hinv.1 hinv.2 cz hLamPos.ne'
  have hS0 : S0.totalDegree ≤ 2 := (Analytic.totalDegree_transportPolynomial_le _ _ _ _).trans hR0
  have hPnorm : Pnorm.totalDegree ≤ q :=
    (Analytic.totalDegree_basePullback _ _ _).trans hPot
  have hsmallZ : 4*|Analytic.nativeA S0| *epsfit ≤ (2*(2*K)^2)⁻¹ := by
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hNative ciZ MiZ) (by norm_num)) hfit.le).trans hcurvsmall
  have hseq := Analytic.native_equation S0 hS0 Pnorm
  have hsder := Analytic.native_derivative S0 hS0
  have hX (e:Ev) (he:e∈Gz) : ‖X e‖ < 1/2 := hGzhalf e he
  have hbandreg (e:Ev) (he:e∈Gz) :
      |B*Analytic.graphPoint e.1 e.2 3-f (X e)| ≤ epsfit*(2*K)^19 ∧
      (2*(2*K))⁻¹ ≤ |2*Analytic.nativeA S0*f (X e)+
        eval (fun i => X e i) (Analytic.nativeB S0)| := by
    have hpoint := Analytic.certifiedGroupPoint_of_physical hzinv.1 hzinv.2
      (inv_mul_cancel₀ hB.ne')
      (hGzPhys e he e.2 (by simp; positivity))
      (by rw [mem_ball,dist_zero_right]; exact (hX e he).trans (by norm_num : (1:ℝ)/2 < 4))
    exact Analytic.band_and_regular_of_normalizedGroupPoint hA1 hfit hsmallZ hroot hseq hsder hpoint.1
  have hRelative := relative_density_of_zoom_floor μ U Gz X
    (by dsimp only [density0]; positivity : 0 ≤ density0) hlam hZloss hUfin hGzmass hGzcap
  have hretained : μ G ≤ ENNReal.ofReal Zloss*μ Gz := by
    rw [←hmassU]
    exact hRelative.1
  have hGzpos : μ Gz ≠ 0 := by
    intro hz
    have hh := hretained
    rw [hz,mul_zero] at hh
    exact hGpos.not_ge hh
  have hGzfin : μ Gz ≠ ⊤ := ne_top_of_le_ne_top hUfin (measure_mono hGzU)
  have hRelativeA (E:Set P3) (hE:MeasurableSet E) :
      μ (Gz ∩ X ⁻¹' E) ≤ ENNReal.ofReal A0*μ Gz*volume E := by
    exact (hRelative.2 E hE).trans (by gcongr)
  have hPnormCoeff (m) : |Pnorm.coeff m| ≤ Mz := by
    have hbframe (i:Fin 3) : |8*K| *(1+|(1:ℝ)/8|) ≤ 9*K := by
      rw [abs_of_pos (by positivity : 0 < 8*K)]
      norm_num
      linarith only []
    have hx := zoomed_potential_coefficient_bound (T := T) (j := j) source.degree c u hK0.le hh.le
      (by positivity : 0 < 8*K) (by linarith only [hK] : 1 ≤ 9*K) hlam
      (fun _ => 1/8) cz source.coeff hbframe hcz m
    simpa only [Pnorm,zoomPotential,Mz,show 2*(9*K)=18*K by ring] using hx
  have htimewindows := source_time_windows CW hK hlarge hlam hh
  have hTubeTime : scale T (8*K)/(8*A0*lam) ≤ h/(4*K^2) := htimewindows.1
  let Hpar := Nk^(Mp+Mr+1)
  let Vf := 4*Hpar
  have hHpar : 1 ≤ Hpar := one_le_pow₀ (by linarith only [hNk] : 1 ≤ Nk)
  have hVf : 0 ≤ Vf := by dsimp only [Vf]; positivity
  have hheight (e:Ev) (he:e∈Gz) : |f (X e)| ≤ Vf := by
    have hes := hGS (hUG (hGzU he))
    have htold : e.2∈Icc ((j:ℝ)*h) (((j:ℝ)+1)*h) := by
      simpa only [add_mul,one_mul] using (hSA hes).2
    have hunit := old_block_subset_unit T j hj htold
    exact branch_height_bound hNk Mp Mr (by simpa only [abs_of_pos hB] using hBN)
      e.1 (hlinech e.1 (hSA hes).1).2.1 e.2 hunit (X e) f (hbandreg e he).1 hband1
  have hevents (e:Ev) (he:e∈Gz) :
      X e∈ball (0:P3) (1/2) ∧ |f (X e)| ≤ Vf ∧
      (2*(2*K))⁻¹ ≤ |2*Analytic.nativeA S0*f (X e)+
        eval (fun i => X e i) (Analytic.nativeB S0)| ∧
      ∃ p y:Fin 7 → P3,
        (∀ i,p i 0=1 ∧ ‖p i‖ ≤ A0) ∧
        (∀ i j k:Fin 7,i≠j → i≠k → j≠k →
          A0⁻¹ ≤ |Matrix.det (Matrix.of fun r t:Fin 3 => (![p i,p j,p k] r) t)|) ∧
        (∀ i,Analytic.CertifiedTubeWitness S0 Pnorm Sc epsfit (2*K) (branchSign beta)
          (Cx*(κ*δ Nk rr)) A0 1 hdelt (X e) (p i)) ∧
        (∀ i,‖y i‖ ≤ 1 ∧ ‖X e-y i‖ ≤ hdelt ∧
          |iteratedFDeriv ℝ 3 (fun z:P3 => eval (fun j => z j) Pnorm) (y i) (fun _ => p i)| ≤ epsc) := by
    refine ⟨by simpa only [mem_ball,dist_zero_right] using hX e he,hheight e he,(hbandreg e he).2,?_⟩
    exact hseven (s := 8*K) (lam := lam) (At := A0) (τw := h/(4*K^2)) (hδ := hdelt)
      (εfit := epsfit) (A₁ := 2*K) (σ := branchSign beta) (Vc := Cx*(κ*δ Nk rr))
      (c0 := physicalGroupCenter a w g) (by positivity) hlam hAtv hDet
      herrors.mesh_nonneg herrors.mesh_covers_state herrors.mesh_half hTubeTime
      (fun _ => 1/8) cz Rb hphys e (hGzU he) (hX e he)
  have hb : 0 < b := by dsimp only [b,errorPadding]; positivity
  have hXmeas : Measurable X := Analytic.measurable_eventBase cfZ MfZ B
  obtain ⟨cq,r,Q,hcq,hrlo,hrhi,hQ,hQcoeff,hQmass,hQprop⟩ :=
    hrestore A0 hAbA Delta Up Vp Wp hDeltaDeg hUpDeg hVpDeg hWpDeg hDeltaNe hWne
      sq Fc f hsqDiff hsq hpres hWpPoint hFc hf6 hmatch hfExt hS0 hPnorm hA1
      (by linarith only [hAtv]) hfit hsmallZ hroot hseq hsder μ Gz X hGz hXmeas hGzpos hGzfin
      hRelativeA b hdelt epsc Mz Vf hb herrors.mesh_nonneg hepsc0 hMz0 hVf hPnormCoeff
      herrors.fit_input herrors.mesh_accuracy herrors.error_accuracy hevents
  have hNk1 : 1 ≤ Nk := by linarith only [hNk]
  have hMpPar : Nk^Mp ≤ Hpar := pow_le_pow_right₀ hNk1 (by omega)
  have hMrPar : Nk^Mr ≤ Hpar := pow_le_pow_right₀ hNk1 (by omega)
  have horiginPar (i:Fin 3) : |Broad.parentBaseOrigin T j c u i| ≤ Hpar :=
    (parent_origin_bound hNk Mp T j hj c u hcu i).trans hMpPar
  obtain ⟨hcfZ,hMfZ,hBframe⟩ := forward_frame_bounds T j c u (B := B) hK hA0 hHpar hLamPos.le
    hlamA (hTN.trans hMrPar) (by simpa only [abs_of_pos hB] using hBN.trans hMrPar) horiginPar cz hcz
  have hRcoeff (m) : |(Analytic.transportPolynomial cfZ MfZ B Q).coeff m| ≤
      (K*Hpar*(1+(a*w)⁻¹))^coefficientPower M CW :=
    restored_source_coefficients M CW hK (by omega) hHpar haw hEbWidth hVf le_rfl
      cfZ MfZ B Q hcfZ hMfZ hBframe hQ hQcoeff m
  let G0 := Gz ∩ X ⁻¹' ball cq r
  let theta := returnTime A0 CW
  let Cm := A0^(CW+1)
  let Cr := returnLoss A0 CW (CW+1)
  have hG0 : MeasurableSet G0 := hGz.inter (isOpen_ball.measurableSet.preimage hXmeas)
  have hG0G : G0 ⊆ G := fun e he => hUG (hGzU he.1)
  obtain ⟨hTheta,hThetaHalf,hStep,hCrMain,hCrQuad⟩ := source_return_powers CW (CW+1)
    hA0 hLamPos.le hlamA haw hEbWidth hEbUpper (show Cm ≤ A0^(CW+1) from le_rfl)
  have hStepR : lam*theta ≤ r := hStep.trans hrlo
  have hOrigMass : μ G ≤ ENNReal.ofReal Cm*μ G0 := by
    have hLoss : Zloss*A0^CW ≤ Cm := by
      calc
        _ ≤ A0*A0^CW := mul_le_mul_of_nonneg_right hZlossA (by positivity)
        _ = _ := by dsimp only [Cm]; rw [pow_succ']
    calc
      _ ≤ ENNReal.ofReal Zloss*μ Gz := hretained
      _ ≤ ENNReal.ofReal Zloss*(ENNReal.ofReal (A0^CW)*μ G0) := mul_le_mul_right hQmass _
      _ = ENNReal.ofReal (Zloss*A0^CW)*μ G0 := by rw [ENNReal.ofReal_mul hZloss.le]; ac_rfl
      _ ≤ _ := by gcongr
  have heventsOrig (e:Ev) (he:e∈G0) : e.1∈source.groupLines w g ∧
      e.2∈Icc ((j:ℝ)/(2:ℝ)^T) (((j:ℝ)+1)/(2:ℝ)^T) := by
    refine ⟨hlines e (hG0G he),?_⟩
    simpa only [div_eq_mul_inv,add_mul,one_mul] using (hSA (hGS (hG0G he))).2
  have hnearOrig (e:Ev) (he:e∈G0) (t:ℝ)
      (ht:t∈Icc ((j:ℝ)/(2:ℝ)^T) (((j:ℝ)+1)/(2:ℝ)^T))
      (hne:|t-e.2| ≤ theta*h) :
      Analytic.normalizedBase cfZ MfZ B (Analytic.graphPoint e.1 t)∈closedBall cq (2*r) ∧
      |B*Analytic.graphPoint e.1 t 3-
        f (Analytic.normalizedBase cfZ MfZ B (Analytic.graphPoint e.1 t))| ≤ epsfit*(2*K)^19 := by
    have hvel := (source.point_bounds e (hGS (hG0G he))).2.1
    have hball := eventBase_stays_double_ball T j c u hK hLamPos (fun _ => 1/8) cz e
      hvel cq he.2 hStepR t hne
    refine ⟨hball,?_⟩
    have hnorm : ‖X (e.1,t)‖ < 4 := by
      have hd := hball
      rw [mem_closedBall,dist_eq_norm] at hd
      change ‖X (e.1,t)-cq‖ ≤ 2*r at hd
      have htri : ‖X (e.1,t)‖ ≤ ‖X (e.1,t)-cq‖+‖cq‖ := by
        convert norm_add_le (X (e.1,t)-cq) cq using 1 <;> simp
      linarith only [htri,hd,hcq,hrhi]
    have hpoint := Analytic.certifiedGroupPoint_of_physical hzinv.1 hzinv.2
      (inv_mul_cancel₀ hB.ne') (hphys e (hG0G he) t (hne.trans htimewindows.2))
      (by rw [mem_ball,dist_zero_right]; exact hnorm)
    exact (Analytic.band_and_regular_of_normalizedGroupPoint hA1 hfit hsmallZ
      hroot hseq hsder hpoint.1).1
  have hout := physical_return ν cfZ MfZ T j (source.groupLines w g) G G0 Q cq f hQ hRcoeff
    hB ha hw hEb (one_le_pow₀ hA01) hband0 herrors.fit_in_tube hTheta hThetaHalf hQprop
    hG0 hG0G heventsOrig hnearOrig hOrigMass hCrMain hCrQuad
  simpa only [Cr,returnLoss,A0,←pow_mul,
    show 6*CW+(CW+1)+60=7*CW+61 by omega] using hout

end

end Submission.Obl.k4_physical_parent_potential_candidates
