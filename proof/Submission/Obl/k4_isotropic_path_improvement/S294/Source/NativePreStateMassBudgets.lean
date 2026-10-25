-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativePreStateMassBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestorPreStateSource
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.PostStateMassBudgets
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.OriginalPreStateScales

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Filter Parent.Qualification
open scoped ENNReal BigOperators

noncomputable section

/-- A negative power pays an original-reference inverse path mass,
uniformly in the subsequently supplied path coefficient. -/
theorem negative_power_le_inverse_mass
    {N κ target gap C : ℝ} (hN : 1 ≤ N) (hκ : 0 < κ) (hC : 0 < C)
    (hκN : κ ≤ N^gap) (hlarge : C ≤ N^(target-gap)) :
    ENNReal.ofReal (N^(-target)) ≤ ENNReal.ofReal (κ⁻¹/C) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hcost : N^(-target)*κ ≤ 1/C := by
    calc
      _ ≤ N^(-target)*N^gap := mul_le_mul_of_nonneg_left hκN (Real.rpow_nonneg hNp.le _)
      _ = N^(-(target-gap)) := by rw [←Real.rpow_add hNp]; congr 1; ring
      _ ≤ _ := by
        rw [Real.rpow_neg hNp.le]
        simpa only [one_div] using one_div_le_one_div_of_le hC hlarge
  apply ENNReal.ofReal_le_ofReal
  apply (mul_le_mul_iff_right₀ hκ).mp
  have heq : κ*(κ⁻¹/C)=1/C := by field_simp
  rw [heq]
  simpa only [mul_comm] using hcost

/-- The only fixed constants in the original native P1 loss. -/
def nativePreStateCostConstant (eta : ℝ) : ℝ :=
  max 4 (max Jets2.zoomBlockVisitConstant (36/(1-(2:ℝ)^(-eta))))

/-- The exact total original P1 loss is bounded from scalar powers.
It includes the census floor, coarse coefficient floor, geometric
parameter tail and every original derivative-table entry. -/
theorem native_prestate_mass_cost_le
    {I : Type*} [Fintype I] {N K Kc Kfloor width eta h low c t a d f b r target margin : ℝ}
    (steps L : ℕ) (cut : I → ℝ)
    (hN : 1 ≤ N) (hK : 1 ≤ K) (hKc : 0 ≤ Kc) (_hKfloor : 0 < Kfloor)
    (hwidth : 0 ≤ width) (heta : 0 < eta)
    (hKupper : K ≤ N^h) (hKlower : N^low ≤ K)
    (hKcN : Kc ≤ N^c) (hsteps : (2:ℝ)^steps ≤ N^t)
    (hL : (L:ℝ) ≤ N^a) (hcard : (Fintype.card I:ℝ) ≤ N^d)
    (hfloor : N^f ≤ Kfloor) (hwidthN : width ≤ N^(-b))
    (hcut : ∀ i, cut i ≤ N^(-r))
    (hconstant : nativePreStateCostConstant eta ≤ N^margin)
    (hfloorBudget : 2*c+3*t+a+target+margin ≤ f)
    (hlowBudget : target+margin ≤ low)
    (hwidthBudget : 2*h+target+2*margin ≤ b*eta)
    (hcutBudget : d+target+2*margin ≤ r) :
    ENNReal.ofReal ((Kc^2*((2:ℝ)^steps)^3)*(L:ℝ)/Kfloor)+ENNReal.ofReal K⁻¹+
      ENNReal.ofReal ((4*K+2)^2*width^eta/(1-(2:ℝ)^(-eta)))+
      (∑ i : I, ENNReal.ofReal (cut i*Jets2.zoomBlockVisitConstant)) ≤
        ENNReal.ofReal (N^(-target)) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hdenom : 0 < 1-(2:ℝ)^(-eta) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos heta))
  have hvisit0 : 0 ≤ Jets2.zoomBlockVisitConstant := by unfold Jets2.zoomBlockVisitConstant; positivity
  have hvisit : Jets2.zoomBlockVisitConstant ≤ N^margin :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hconstant)
  have htail : 36/(1-(2:ℝ)^(-eta)) ≤ N^margin :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hconstant)
  have hfour : (4:ℝ) ≤ N^margin := (le_max_left _ _).trans hconstant
  have hp2 : (N^c)^2=N^(2*c) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hNp.le]; congr 1; ring
  have hp3 : (N^t)^3=N^(3*t) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hNp.le]; congr 1; ring
  have hfirst : (Kc^2*((2:ℝ)^steps)^3)*(L:ℝ)/Kfloor ≤ N^(-(target+margin)) := by
    calc
      _ ≤ ((N^c)^2*(N^t)^3)*N^a/N^f := by gcongr
      _ = N^(2*c+3*t+a-f) := by
        rw [hp2,hp3,←Real.rpow_add hNp,←Real.rpow_add hNp,←Real.rpow_sub hNp]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hfloorBudget])
  have hsecond : K⁻¹ ≤ N^(-(target+margin)) := by
    calc
      _ ≤ (N^low)⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hNp _) hKlower
      _ = N^(-low) := (Real.rpow_neg hNp.le _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hlowBudget)
  have hthird : (4*K+2)^2*width^eta/(1-(2:ℝ)^(-eta)) ≤ N^(-(target+margin)) := by
    have hcoef : 4*K+2 ≤ 6*N^h := by linarith only [hK,hKupper]
    have hwidthEta : (N^(-b))^eta=N^(-b*eta) := (Real.rpow_mul hNp.le _ _).symm
    have hpH : (N^h)^2=N^(2*h) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hNp.le]; congr 1; ring
    calc
      _ ≤ (6*N^h)^2*(N^(-b))^eta/(1-(2:ℝ)^(-eta)) := by gcongr
      _ = (36/(1-(2:ℝ)^(-eta)))*N^(2*h)*N^(-b*eta) := by
        rw [hwidthEta,←hpH]
        ring
      _ ≤ N^margin*N^(2*h)*N^(-b*eta) := by gcongr
      _ = N^(margin+2*h-b*eta) := by
        rw [←Real.rpow_add hNp,←Real.rpow_add hNp]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hwidthBudget])
  have hfourth : (∑ i : I, ENNReal.ofReal (cut i*Jets2.zoomBlockVisitConstant)) ≤
      ENNReal.ofReal (N^(-(target+margin))) := by
    have hsingle (i : I) : cut i*Jets2.zoomBlockVisitConstant ≤ N^(margin-r) := by
      calc
        _ ≤ N^(-r)*Jets2.zoomBlockVisitConstant := mul_le_mul_of_nonneg_right (hcut i) hvisit0
        _ ≤ N^(-r)*N^margin := mul_le_mul_of_nonneg_left hvisit (Real.rpow_nonneg hNp.le _)
        _ = _ := by rw [←Real.rpow_add hNp]; congr 1; ring
    calc
      _ ≤ ∑ _i : I, ENNReal.ofReal (N^(margin-r)) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact ENNReal.ofReal_le_ofReal (hsingle i)
      _ = (Fintype.card I:ENNReal)*ENNReal.ofReal (N^(margin-r)) := by simp
      _ ≤ ENNReal.ofReal (N^d)*ENNReal.ofReal (N^(margin-r)) := mul_le_mul'
        (by simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hcard) le_rfl
      _ = ENNReal.ofReal (N^(d+margin-r)) := by
        rw [←ENNReal.ofReal_mul (Real.rpow_nonneg hNp.le _),←Real.rpow_add hNp]
        congr 2
        ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hcutBudget]))
  calc
    _ ≤ ENNReal.ofReal (N^(-(target+margin)))+ENNReal.ofReal (N^(-(target+margin)))+
        ENNReal.ofReal (N^(-(target+margin)))+ENNReal.ofReal (N^(-(target+margin))) :=
      add_le_add (add_le_add (add_le_add (ENNReal.ofReal_le_ofReal hfirst)
        (ENNReal.ofReal_le_ofReal hsecond)) (ENNReal.ofReal_le_ofReal hthird)) hfourth
    _ = ENNReal.ofReal (4*N^(-(target+margin))) := by
      repeat rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      calc
        _ ≤ N^margin*N^(-(target+margin)) :=
          mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg hNp.le _)
        _ = _ := by rw [←Real.rpow_add hNp]; congr 1; ring)

/-- The concrete original pre-state charge fits an inverse path mass.
Every tail and path tolerance is chosen before the actual scale
package, filtered derivative family and original root. -/
theorem eventually_original_prestate_charge_le
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop) (Lreg : ℕ)
    {h b eta : ℝ} (hh : 0 < h) (heta : 0 < eta) (hfloorRange : 100000*h ≤ b*eta) :
    ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ 1 ∧ ∀ᶠ k in atTop,
      ∀ (s : PhysicalModel.OriginalRootScales) (ps : PhysicalModel.OriginalPreStateScales s),
        s.H=N k^h →
        PhysicalModel.originalPreStateEta s.dimension s.floorExponent s.regLength=eta →
        s.regLength ≤ Lreg → N k^(100*h) ≤ ps.Kfloor →
        s.Kcensus ≤ N k^(h/1000) → (2:ℝ)^s.steps ≤ N k^(h/5) →
        (s.floorCount:ℝ) ≤ N k^h → Jets2.dyadicParameterWidth s.floorStart ≤ N k^(-b) →
        (∀ i, ps.cut i ≤ N k^(-h)) →
        ∀ κ : ℝ, 1 ≤ κ → κ ≤ N k^sigma → ps.charge ≤ ENNReal.ofReal (κ⁻¹/64) := by
  let sigma := min 1 (h/10)
  have hsigma : 0 < sigma := lt_min one_pos (by positivity)
  have hsigmaH : sigma ≤ h/10 := min_le_right _ _
  have hlarge := ((tendsto_rpow_atTop (by positivity : 0 < h/10)).comp hN).eventually
    (eventually_ge_atTop (max 64 (max (nativePreStateCostConstant eta) (Lreg:ℝ))))
  refine ⟨sigma,hsigma,min_le_left _ _,?_⟩
  filter_upwards [hN.eventually (eventually_ge_atTop 1),hlarge] with k hk hc
  change max 64 (max (nativePreStateCostConstant eta) (Lreg:ℝ)) ≤ N k^(h/10) at hc
  have hc64 : (64:ℝ) ≤ N k^(h/10) := (le_max_left _ _).trans hc
  have hcCost : nativePreStateCostConstant eta ≤ N k^(h/10) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hc)
  have hcLength : (Lreg:ℝ) ≤ N k^(h/10) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hc)
  intro s ps hH hEta hLength hKfloor hKc hSteps hCount hWidth hCut κ hκ hκN
  let I := {i : Fin s.regLength // s.floorStart ≤ s.regLevel i.val}
  have hcardNat : Fintype.card I ≤ s.regLength := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective (Subtype.val : I → Fin s.regLength) Subtype.val_injective
  have hcard : (Fintype.card I:ℝ) ≤ N k^(h/10) := by
    have hcardLength : (Fintype.card I:ℝ) ≤ (Lreg:ℝ) := by
      exact_mod_cast hcardNat.trans hLength
    exact hcardLength.trans hcLength
  have hsmall := native_prestate_mass_cost_le
    (N := N k) (K := s.H) (Kc := s.Kcensus) (Kfloor := ps.Kfloor)
    (width := Jets2.dyadicParameterWidth s.floorStart) (eta := eta)
    (h := h) (low := h) (c := h/1000) (t := h/5) (a := h) (d := h/10)
    (f := 100*h) (b := b) (r := h) (target := h/2) (margin := h/10)
    s.steps s.floorCount (fun i : I => ps.cut i.val)
    hk s.hH (zero_le_one.trans s.hKcensus) ps.hKfloor
    (Jets2.dyadicParameterWidth_pos _).le heta
    (by rw [hH]) (by rw [hH]) hKc hSteps hCount hcard hKfloor hWidth
    (fun i => hCut i.val) hcCost
    (by linarith only [hh]) (by linarith only [hh])
    (by linarith only [hh,hfloorRange]) (by linarith only [hh])
  have hcharge : ps.charge ≤ ENNReal.ofReal (N k^(-(h/2))) := by
    simpa only [PhysicalModel.OriginalPreStateScales.charge,hEta,I] using hsmall
  have hcMass : (64:ℝ) ≤ N k^(h/2-sigma) := hc64.trans
    (Real.rpow_le_rpow_of_exponent_le hk (by linarith only [hh,hsigmaH]))
  exact hcharge.trans (negative_power_le_inverse_mass hk (zero_lt_one.trans_le hκ)
    (by norm_num) hκN hcMass)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
