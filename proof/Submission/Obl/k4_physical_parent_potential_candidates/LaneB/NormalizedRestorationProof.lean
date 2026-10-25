-- Lane B: the restoration in normalized coordinates, from the data at single events.
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.EventNumerator
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.AeTransfer
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.BranchRestoration
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.GraphExtensions
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.NormalizedErrorPowers
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.NormalizedAffine
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.NormalizedEventLaw

/-!
# Restoration in normalized coordinates (lane B, step 4)

The zoomed branch `f`, a law of retained events `μe` on `Core` with base points `X e` (relative
density at most `A`), and, at every retained event, seven tubes of group points of its fine state
with the potential's cubic tests at their anchors, give a quadratic `Q` in `(u, w)` on a ball
carrying a fixed power of the law (the quadratic is certified on the doubled ball): small on the tube of the graph `w = f u`, with a regular
signed hidden derivative and a curvature at most `A^C / Eb`, where `Eb = εc + b + Mz hδ` is the
total test precision (potential cubic tests, tube width, potential transfer).

The affine scale `s0` of `f` on the unit ball decides: if `s0 ≤ A^C Eb` the affine approximant is
the quadratic (curvature zero); otherwise the per-event tests (`event_cleared_bound`, through the
potential when `s0 ≥ Mz`, directly otherwise) hold almost everywhere (`AeTransfer`) and
`branch_restoration` applies.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open Metric Set MeasureTheory MvPolynomial FubiniHessian QuadraticTube
open scoped ENNReal

/-- **Normalized restoration.** -/
theorem normalized_restoration_verified (hR : DenseJet.SheetRemezAssertion) (d : ℕ) :
    ∃ (Ab : ℝ) (CW : ℕ), 2 ≤ Ab ∧ 1 ≤ CW ∧
    ∀ (A : ℝ), Ab ≤ A →
    ∀ (Δ U V W : MvPolynomial (Fin 3) ℂ), Δ.totalDegree ≤ 2 * (d + 1) →
      U.totalDegree ≤ 2 * (d + 1) → V.totalDegree ≤ 2 * (d + 1) →
      W.totalDegree ≤ 2 * (d + 1) → Δ ≠ 0 → W ≠ 0 →
      ∀ (sq F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ),
      DifferentiableOn ℂ sq (ball 0 4) →
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, (sq z) ^ 2 = eval (fun i => z i) Δ) →
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
        eval (fun i => z i) W * F z = eval (fun i => z i) U + eval (fun i => z i) V * sq z) →
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, eval (fun i => z i) W ≠ 0) →
      ContDiffOn ℂ ⊤ F (ball 0 4) → ContDiffOn ℝ 6 f (ball 0 3) →
      (∀ x ∈ ball (0 : Base) 4, F (DenseJet.realSlice x) = (f x : ℂ)) →
      HasRealExtension (864 * (2 * (d + 1)) + 2) f →
    ∀ {S0 : Poly} {P0 : MvPolynomial (Fin 3) ℝ} {Sc : Poly} {εfit A₁ σ Vc a : ℝ}
      {Bδ Cδ : MvPolynomial (Fin 3) ℝ},
      S0.totalDegree ≤ 2 → P0.totalDegree ≤ d →
      2 ≤ A₁ → A₁ ≤ A → 0 < εfit → 4 * |a| * εfit ≤ (2 * A₁ ^ 2)⁻¹ →
      (∀ z ∈ ball (0 : Base) 4, a * (f z) ^ 2 + eval (fun i => z i) Bδ * f z +
        eval (fun i => z i) Cδ = 0 ∧ 0 < (2 * a * f z + eval (fun i => z i) Bδ) * σ) →
      (∀ (z : Base) (w : ℝ), eval ![z 0, z 1, z 2, w] S0 - eval (fun i => z i) P0 =
        a * w ^ 2 + eval (fun i => z i) Bδ * w + eval (fun i => z i) Cδ) →
      (∀ (z : Base) (w : ℝ), eval ![z 0, z 1, z 2, w] (pderiv 3 S0) =
        2 * a * w + eval (fun i => z i) Bδ) →
    ∀ {Ω : Type*} [MeasurableSpace Ω] (μe : Measure Ω) (Core : Set Ω) (X : Ω → Base),
      MeasurableSet Core → Measurable X → μe Core ≠ 0 → μe Core ≠ ⊤ →
      (∀ E : Set Base, MeasurableSet E →
        μe (Core ∩ X ⁻¹' E) ≤ ENNReal.ofReal A * μe Core * volume E) →
    ∀ (b hδ εc Mz Vf : ℝ), 0 < b → 0 ≤ hδ → 0 ≤ εc → 0 ≤ Mz → 0 ≤ Vf →
      (∀ m, |P0.coeff m| ≤ Mz) →
      εfit * A₁ ^ 19 ≤ A * b →
      hδ * A ^ CW ≤ 1 → (εc + b + Mz * hδ) * A ^ CW ≤ 1 →
      (∀ e ∈ Core, X e ∈ ball (0 : Base) (1 / 2) ∧ |f (X e)| ≤ Vf ∧
        (2 * A₁)⁻¹ ≤ |2 * a * f (X e) + eval (fun i => X e i) Bδ| ∧
        ∃ p y : Fin 7 → Base, (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ A) ∧
          (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
            A⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)|) ∧
          (∀ i, CertifiedTubeWitness S0 P0 Sc εfit A₁ σ Vc A 1 hδ (X e) (p i)) ∧
          (∀ i, ‖y i‖ ≤ 1 ∧ ‖X e - y i‖ ≤ hδ ∧
            |iteratedFDeriv ℝ 3 (Pf P0) (y i) (fun _ => p i)| ≤ εc)) →
    ∃ (c : Base) (r : ℝ) (Q : Poly), ‖c‖ ≤ 1 / 2 ∧ (A ^ CW)⁻¹ ≤ r ∧ r ≤ 1 / 2 ∧
      Q.totalDegree ≤ 2 ∧
      (∀ e, |Q.coeff e| ≤ A ^ CW * (1 + Vf + (εc + b + Mz * hδ)⁻¹) ^ 5) ∧
      μe Core ≤ ENNReal.ofReal (A ^ CW) * μe (Core ∩ X ⁻¹' ball c r) ∧
      ∀ u ∈ closedBall c (2 * r), ∀ w : ℝ, A ^ CW * |w - f u| ≤ εc + b + Mz * hδ →
        |ev Q u w| ≤ A ^ CW * (εc + b + Mz * hδ + |w - f u|) ∧
        (A ^ CW)⁻¹ ≤ ev (pderiv (3 : Fin 4) Q) u w ∧ ev (pderiv (3 : Fin 4) Q) u w ≤ A ^ CW ∧
        |ev (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) Q)) u w| ≤ A ^ CW / (εc + b + Mz * hδ) := by
  classical
  obtain ⟨De,hentries⟩ := hasRealExtension_normalized_graph_entries (2*(d+1))
  let Dr := max De (max (864*(2*(d+1))+2) (8*(2*(d+1)+1)+2))
  obtain ⟨J,hJ,hjet⟩ := denseJetAssertion_of_sheetRemez hR Dr
  obtain ⟨M,C,hM,hMC,hbranch⟩ := branch_restoration hjet
  obtain ⟨Kt,Cq,N,hKt,hCq,hN,hevent⟩ := event_cleared_bound hR d
  let Ct := NormalizedErrors.cutPower J N (2*C+1)
  let CW := 100*(Ct+J+C+M+N+1)
  let Ab := max 2 (max Kt (max Cq (2*(2:ℝ)^J)))
  have hAb : 2 ≤ Ab := le_max_left _ _
  refine ⟨Ab,CW,hAb,by dsimp only [CW]; omega,?_⟩
  intro A hAbA Delta U V W hDelta hU hV hW hDne hWne sq F f
    hsqDiff hsq hpres hWp hF hf6 hmatch hfExt
    S0 P0 Sc epsfit A1 sigma Vc aa Bp Cp hS0 hP0 hA1 hA1A hepsfit hsmall hroot hseq hsder
    Ω instMeas μe Core X hCore hX hCore0 hCoreFin hdom
    b hdelta epsc Mz Vf hb hhd hepsc hMz hVf hPcoeff hband hmesh herror hevents
  have hA : 2 ≤ A := hAb.trans hAbA
  have hA0 : 0 < A := by linarith only [hA]
  have hA1' : 1 ≤ A := by linarith only [hA]
  have hKtA : Kt ≤ A :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hAbA)
  have hCqA : Cq ≤ A :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hAbA))
  have hJA : 2*(2:ℝ)^J ≤ A :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hAbA))
  let μ := (μe.restrict Core).map X
  obtain ⟨hmass,hμdom,hsupp,hballmass⟩ := event_base_law μe Core X hCore hX hdom
    (fun e he => ball_subset_closedBall (hevents e he).1)
  have hμ0 : μ univ ≠ 0 := by rw [hmass]; exact hCore0
  have hμfin : μ univ ≠ ⊤ := by rw [hmass]; exact hCoreFin
  have hfHalf : ContinuousOn f (closedBall (0:Base) (1/2)) :=
    hf6.continuousOn.mono (closedBall_subset_ball (by norm_num : (1:ℝ)/2 < 3))
  have hfUnit : ContinuousOn f (closedBall (0:Base) 1) :=
    hf6.continuousOn.mono (closedBall_subset_ball (by norm_num : (1:ℝ) < 3))
  have hfDr : HasRealExtension Dr f := hfExt.mono_degree (by dsimp only [Dr]; omega)
  have hfAE : ∀ᵐ x ∂μ, |f x| ≤ Vf := ae_base_function_bound μe Core X hX hfHalf
    (fun e he => ⟨ball_subset_closedBall (hevents e he).1,(hevents e he).2.1⟩)
  have hjets := MeasureNorming.dense_bound_of_ae hjet hfDr hfHalf hμ0 hμfin hA hVf hμdom hsupp hfAE
  let E := epsc+b+Mz*hdelta
  let cutoff := A^Ct*E
  let H0 := (2*A)^J*(1+Vf)
  let Z := 1+Vf+E⁻¹
  let Hbig := A^(2*J+4)*Z
  have hE : 0 < E := by dsimp only [E]; positivity
  have hZ : 1 ≤ Z := by dsimp only [Z]; linarith only [hVf,inv_nonneg.mpr hE.le]
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  have hH0 : 1 ≤ H0 := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (by linarith only [hA] : 1 ≤ 2*A)) (by linarith only [hVf])
  have hHbig : 1 ≤ Hbig := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hA1') hZ
  have hcut0 : 0 < cutoff := by dsimp only [cutoff]; positivity
  have hCtCW : Ct ≤ CW := by dsimp only [CW]; omega
  have hcut1 : cutoff ≤ 1 := by
    calc
      _ ≤ A^CW*E := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA1' hCtCW) hE.le
      _ ≤ _ := by simpa only [E,mul_comm] using herror
  have hfBound (x:Base) (hx:x∈closedBall (0:Base) 1) : |f x| ≤ H0 := by
    have hh := hjets 0 (by norm_num) x (closedBall_subset_closedBall (by norm_num : (1:ℝ) ≤ 2) hx)
    have h0 : ‖iteratedFDeriv ℝ 0 f x‖=|f x| := by simp
    rw [h0] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith only [hVf] : Vf ≤ 1+Vf) (by positivity))
  obtain ⟨s0,c,L,hs0,hsH,hlower,happrox,hc,hL,hcases⟩ :=
    AffineExit.controlled_scale hfUnit (zero_le_one.trans hH0) hcut0 hfBound
  have h2A : 2*A ≤ A^2 := by nlinarith only [hA]
  have hJpow : (2*A)^J ≤ A^(2*J) :=
    (pow_le_pow_left₀ (by positivity) h2A J).trans_eq (pow_mul A 2 J).symm
  have hCpow : (2*A)^C ≤ A^(2*C) :=
    (pow_le_pow_left₀ (by positivity) h2A C).trans_eq (pow_mul A 2 C).symm
  have hH0up : H0 ≤ A^(2*J)*(1+Vf) := mul_le_mul_of_nonneg_right hJpow (by positivity)
  have hZlo : 1+Vf ≤ Z := by dsimp only [Z]; exact le_add_of_nonneg_right (inv_nonneg.mpr hE.le)
  have h12 : (12:ℝ) ≤ A^4 :=
    (by norm_num : (12:ℝ) ≤ 2^4).trans (pow_le_pow_left₀ (by norm_num) hA 4)
  have hH0big : 12*H0 ≤ Hbig := by
    calc
      _ ≤ A^4*(A^(2*J)*(1+Vf)) := mul_le_mul h12 hH0up (by positivity) (by positivity)
      _ ≤ A^4*(A^(2*J)*Z) := by gcongr
      _ = _ := by dsimp only [Hbig]; rw [pow_add]; ring
  have hcBig : |c| ≤ Hbig := by linarith only [hc,hH0big,hcut1,hH0]
  have hLBig (i:Fin 3) : |L (EuclideanSpace.basisFun (Fin 3) ℝ i)| ≤ Hbig := by
    linarith only [hL i,hH0big,hcut1,hH0]
  have hsBig : s0 ≤ Hbig := by linarith only [hsH,hH0big,hH0]
  have hmono (n:ℕ) (hn:n ≤ CW) : A^n ≤ A^CW := pow_le_pow_right₀ hA1' hn
  have hAffCoeff : 5*Hbig ≤ A^CW*Z^5 := by
    have h5 : (5:ℝ) ≤ A^3 :=
      (by norm_num : (5:ℝ) ≤ 2^3).trans (pow_le_pow_left₀ (by norm_num) hA 3)
    have hZpow : Z ≤ Z^5 := by simpa using pow_le_pow_right₀ hZ (by decide : 1 ≤ 5)
    calc
      _ ≤ A^3*(A^(2*J+4)*Z) := mul_le_mul_of_nonneg_right h5 (by positivity)
      _ = A^(2*J+7)*Z := by simp only [pow_add]; ring
      _ ≤ _ := mul_le_mul (hmono _ (by dsimp only [CW]; omega)) hZpow hZ0 (by positivity)
  have hBranchCoeff : 2025*(2*A)^C*Hbig^5 ≤ A^CW*Z^5 := by
    have h2025 : (2025:ℝ) ≤ A^11 :=
      (by norm_num : (2025:ℝ) ≤ 2^11).trans (pow_le_pow_left₀ (by norm_num) hA 11)
    calc
      _ ≤ A^11*A^(2*C)*(A^(2*J+4)*Z)^5 := by gcongr
      _ = A^(2*C+10*J+31)*Z^5 := by simp only [pow_add,pow_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hmono _ (by dsimp only [CW]; omega)) (by positivity)
  rcases hcases with ⟨hsSmall,hFitSmall⟩ | ⟨hCutS,hFitBig⟩
  · obtain ⟨cq,Q,hcq,hQ,hQcoef,hQmass,hQprop⟩ := AffineExit.affine_ball_certificate μ
      hμ0 hμfin hsupp hA hHbig f c L hcBig hLBig hFitSmall
    have hrad : (A^2)⁻¹ ≤ 1/2 := by
      rw [one_div]
      exact inv_anti₀ (by norm_num) (hA.trans (by simpa using pow_le_pow_right₀ hA1' (by decide : 1 ≤ 2)))
    refine ⟨cq,(A^2)⁻¹,Q,hcq,inv_anti₀ (by positivity) (hmono 2 (by dsimp only [CW]; omega)),
      hrad,hQ,fun m => (hQcoef m).trans hAffCoeff,?_,?_⟩
    · have hm : μ univ ≤ ENNReal.ofReal (A^CW)*μ (ball cq (A^2)⁻¹) :=
        hQmass.trans (by gcongr; dsimp only [CW]; omega)
      simpa only [μ,hmass,hballmass] using hm
    · intro u hu w huw
      obtain ⟨hv,hd,hc⟩ := hQprop u hu w
      have hcutV : 2*cutoff ≤ A^CW*E := by
        calc
          _ ≤ A*(A^Ct*E) := mul_le_mul_of_nonneg_right hA (by positivity)
          _ = A^(Ct+1)*E := by rw [pow_succ']; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (hmono _ (by dsimp only [CW]; omega)) hE.le
      have hdist : |w-f u| ≤ A^CW*|w-f u| :=
        le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ hA1')
      refine ⟨by linarith only [hv,hcutV,hdist],?_,?_,?_⟩
      · rw [hd]
        exact inv_le_one_of_one_le₀ (one_le_pow₀ hA1')
      · rw [hd]
        exact one_le_pow₀ hA1'
      · rw [hc,abs_zero]
        positivity
  · obtain ⟨hsPos,hCutSmall,hEs,hEtaAcc,hEpsAcc⟩ := NormalizedErrors.accuracy_from_cutoff
      J N (2*C+1) CW hA hKt.le hKtA hb hhd hepsc hMz
      (show NormalizedErrors.cutPower J N (2*C+1) ≤ CW from hCtCW)
      (by dsimp only [CW,Ct,NormalizedErrors.cutPower,NormalizedErrors.errorPower]; omega)
      hmesh herror hCutS.le
    let g : Base → ℝ := fun x => (f x-c-L x)/s0
    let eta := NormalizedErrors.hessianError A Kt b hdelta s0 J
    let eps := A^NormalizedErrors.errorPower J N*E/s0
    let m := (2*A1)⁻¹
    have hm0 : 0 < m := by dsimp only [m]; positivity
    have hmLo : (A^2)⁻¹ ≤ m := inv_anti₀ (by linarith only [hA1] : 0 < 2*A1)
      ((mul_le_mul_of_nonneg_left hA1A (by norm_num : (0:ℝ) ≤ 2)).trans h2A)
    have heta : 0 < eta := by dsimp only [eta,NormalizedErrors.hessianError]; positivity
    have heps : 0 ≤ eps := by dsimp only [eps]; positivity
    have hFrep : SqrtRep (ball 0 4) sq (2*(d+1)) F := ⟨hF,U,V,W,hWne,hU,hV,hW,hpres⟩
    have hgExt : HasRealExtension Dr g :=
      (hasRealExtension_normalized_graph hDelta hsq hFrep hmatch c s0 L).mono_degree
        (by dsimp only [Dr]; omega)
    have hg6 : ContDiffOn ℝ 6 g (ball 0 4) := hgExt.contDiffOn.of_le (by simp)
    obtain ⟨hHentries,hNentries⟩ := hentries Delta U V W hDelta hU hV hW hDne hWne
      sq F hsqDiff hF hsq hpres f hmatch c s0 L
    have hHext (i j:Fin 3) : HasRealExtension Dr (fun x => hessian g x i j) :=
      (hHentries i j).mono_degree (by dsimp only [Dr]; omega)
    have hNext (i j k:Fin 3) : HasRealExtension Dr (fun x => clearedCubicError g x i j k) :=
      (hNentries i j k).mono_degree (by dsimp only [Dr]; omega)
    have hWreal (y:Base) (hy:y∈closedBall (0:Base) 1) :
        eval (fun i => DenseJet.realSlice y i) W ≠ 0 := by
      apply hWp
      rw [mem_ball,dist_zero_right,DenseJet.norm_realSlice_apply]
      have hy1 : ‖y‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hy
      linarith only [hy1]
    have htests (e:Ω) (he:e∈Core) :
        (∃ p:Fin 7 → Base,(∀ i,p i 0=1 ∧ ‖p i‖ ≤ A) ∧
          (∀ i j k:Fin 7,i≠j → i≠k → j≠k →
            A⁻¹ ≤ |Matrix.det (Matrix.of fun r t:Fin 3 => (![p i,p j,p k] r) t)|) ∧
          (∀ i,|iteratedFDeriv ℝ 2 g (X e) (fun _ => p i)| ≤ eta)) ∧
        (∀ i j k,|clearedCubicError g (X e) i j k| ≤ eps) := by
      obtain ⟨hXe,hfXe,hFw,p,y,hpn,hdet,htubes,hanchors⟩ := hevents e he
      have hXe1 : X e∈closedBall (0:Base) 1 :=
        closedBall_subset_closedBall (by norm_num : (1:ℝ)/2 ≤ 1) (ball_subset_closedBall hXe)
      have hh := hevent Delta U V W hDelta hU hV hW sq F f hsq hpres hF hmatch hWreal
        hjet hfDr A b hdelta s0 epsc Mz m hA hb.le hhd hsPos hepsc hMz hm0 happrox c L
        hS0 hP0 hPcoeff hA1 hepsfit hsmall hband hroot hseq hsder
        (X e) p y hXe1 hFw hpn hdet htubes hanchors
      refine ⟨⟨p,hpn,hdet,hh.1⟩,?_⟩
      intro i j k
      exact NormalizedErrors.two_route_error J N hA hKt.le hKtA hCq.le hCqA hb.le hhd
        hsPos hepsc hMz hmLo (hh.2.1 i j k) (hh.2.2 i j k)
    have hXfour (e:Ω) (he:e∈Core) : X e∈ball (0:Base) 4 :=
      ball_subset_ball (by norm_num : (1:ℝ)/2 ≤ 4) (hevents e he).1
    have hEtaAE := ae_directions_of_forall μe Core X hX hg6 hA heta
      (fun e he => ⟨hXfour e he,(htests e he).1⟩)
    have hErrAE := ae_cleared_of_forall μe Core X hX hg6
      (fun e he => ⟨hXfour e he,(htests e he).2⟩)
    have hEtaSmall : (2*eta)*(2*A)^C ≤ 1 := by
      calc
        _ ≤ (A*eta)*A^(2*C) := mul_le_mul
          (mul_le_mul_of_nonneg_right hA heta.le) hCpow (by positivity) (by positivity)
        _ = eta*A^(2*C+1) := by rw [pow_succ']; ring
        _ ≤ _ := hEtaAcc
    have hEpsSmall : eps*(2*A)^C ≤ 1 := by
      calc
        _ ≤ eps*A^(2*C) := mul_le_mul_of_nonneg_left hCpow heps
        _ ≤ eps*A^(2*C+1) := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA1' (by omega)) heps
        _ ≤ _ := hEpsAcc
    have hDoubleDom (S:Set Base) (hS:MeasurableSet S) :
        μ S ≤ ENNReal.ofReal (2*A)*μ univ*volume S :=
      (hμdom S hS).trans (by gcongr <;> linarith only [hA0])
    have hEIZ : E⁻¹ ≤ Z := by dsimp only [Z]; linarith only [hVf]
    have hsInvBig : s0⁻¹ ≤ Hbig :=
      (inv_anti₀ hE hEs).trans (hEIZ.trans
        (le_mul_of_one_le_left hZ0 (one_le_pow₀ hA1')))
    obtain ⟨cq,hcq,Q,hQ,hQcoef,hQmass,hQprop⟩ := hbranch (A := 2*A)
      (by linarith only [hA]) (hJA.trans (by linarith only [hA0])) hf6 c s0 L hsPos hgExt
      hFitBig hlower hHext hNext hμ0 hμfin hDoubleDom hsupp
      (by positivity : 0 ≤ 2*eta) heps hEtaSmall hEpsSmall hEtaAE hErrAE
      hHbig hcBig hLBig hsBig hsInvBig
    let r := ((2*A)^M)⁻¹
    have hCB : (2*A)^C ≤ A^CW := hCpow.trans (hmono _ (by dsimp only [CW]; omega))
    have hMPow : (2*A)^M ≤ A^(2*M) :=
      (pow_le_pow_left₀ (by positivity) h2A M).trans_eq (pow_mul A 2 M).symm
    have hMB : (2*A)^M ≤ A^CW := hMPow.trans (hmono _ (by dsimp only [CW]; omega))
    have htwo : 2 ≤ (2*A)^M := by
      exact (by linarith only [hA] : (2:ℝ) ≤ 2*A).trans
        (by simpa using pow_le_pow_right₀ (by linarith only [hA] : 1 ≤ 2*A) hM)
    have hrad : r ≤ 1/2 := by rw [one_div]; exact inv_anti₀ (by norm_num) htwo
    refine ⟨cq,r,Q,by simpa only [mem_closedBall,dist_zero_right] using hcq,
      inv_anti₀ (by positivity) hMB,hrad,hQ,fun k => (hQcoef k).trans hBranchCoeff,?_,?_⟩
    · have hm : μ univ ≤ ENNReal.ofReal (A^CW)*μ (ball cq r) :=
        hQmass.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hCB) le_rfl)
      simpa only [μ,hmass,hballmass] using hm
    · intro u hu w huw
      have huwE : A^CW*|w-f u| ≤ E := huw
      obtain ⟨hv,hlo,hhi,hcurv⟩ := hQprop u hu w
        ((mul_le_mul_of_nonneg_right hCB (abs_nonneg _)).trans (huwE.trans hEs))
      have hsEps : s0*eps=A^NormalizedErrors.errorPower J N*E := by
        dsimp only [eps]
        field_simp
      refine ⟨?_,(inv_anti₀ (by positivity) hCB).trans hlo,hhi.trans hCB,?_⟩
      · calc
          _ ≤ (2*A)^C*(s0*eps+|w-f u|) := hv
          _ = (2*A)^C*(A^NormalizedErrors.errorPower J N*E+|w-f u|) := by rw [hsEps]
          _ ≤ A^(2*C)*(A^NormalizedErrors.errorPower J N*E+|w-f u|) :=
            mul_le_mul_of_nonneg_right hCpow (by positivity)
          _ = A^(2*C+NormalizedErrors.errorPower J N)*E+A^(2*C)*|w-f u| := by rw [pow_add]; ring
          _ ≤ A^CW*E+A^CW*|w-f u| := add_le_add
            (mul_le_mul_of_nonneg_right (hmono _
              (by dsimp only [CW,Ct,NormalizedErrors.cutPower,NormalizedErrors.errorPower]; omega)) hE.le)
            (mul_le_mul_of_nonneg_right (hmono _ (by dsimp only [CW]; omega)) (abs_nonneg _))
          _ = _ := by dsimp only [E]; ring
      · exact hcurv.trans ((div_le_div_of_nonneg_left (by positivity) hE hEs).trans
          (div_le_div_of_nonneg_right hCB hE.le))

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
