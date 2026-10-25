-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.NativeAncestorPreStateSource, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestorDerivativeSource
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalPreStateData

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestor

open Set MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent
open ParentSource ParentSource.Native
open Submission.Lib.K4ParentSignalPreparation.Census
open scoped ENNReal

noncomputable section

/-- Both actual native P1 preparations on one ORIGINAL source. All
full-prior coefficient floors and actual derivative tables are returned
before final states, with their total original-reference deletion. -/
theorem prepare_native_original_pre_state_data {I : Type*} [Fintype I] (dimension ε : ℝ)
    (hdim : 0≤dimension) (hdim1 : dimension<1) (hε : 0<ε) :
    ∃ η : ℝ, 0<η ∧ ∃ p₀ : ℝ, 0<p₀ ∧
    ∀ (d : ProblemData), d.Valid → ∀ (k m : ℕ) (p : PathData (d.W k))
      (κ₁ δ₀ σ : ℝ) (s : ℕ → ℝ) (Mp Dp : ℕ),
    ∀ hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ,
    ∀ (root : Fin p.C) (Vmax : ℝ) (hVmax : 0≤Vmax)
      (source : Set Ev) (hsource : MeasurableSet source) (hsourceF : source⊆p.F root),
    (p.R root).totalDegree≤2 → (∀ z∈source, ‖v z.1‖≤Vmax) →
    ∀ (S : Set Ev), MeasurableSet S → S⊆source →
    ∀ (n L : ℕ), 0<L → Jets2.dyadicParameterWidth n≤p₀ →
    ∀ (K C Kfloor Kcensus resolution : ℝ) (steps : ℕ),
    1≤K → coefficientBound (p:=p) Vmax≤K → 0≤C → 0<Kfloor →
    0<resolution → 1≤Kcensus → Kcensus^(100:ℕ)≤(2:ℝ)^steps →
    resolution*(2:ℝ)^steps≤Jets2.dyadicParameterWidth (n+L-1) →
    ∀ palette : Measure (Fin 2 → ℝ), IsProbabilityMeasure palette →
    2*K≤(Jets2.dyadicParameterWidth n)^(-η) →
    Jets2.originalParameterCapConstant K (4200*(12*K+3)*C) dimension≤
      (Jets2.dyadicParameterWidth n)^(-η) →
    4*(4*K+6)^3*(((12*K+2)*C)*Kfloor)≤(Jets2.dyadicParameterWidth n)^(-η) →
    (∀ a w : ℝ, resolution≤a → a≤1 → resolution≤w → w≤1 → Kcensus^(100:ℕ)*a≤w →
      (occupied S (fun z j => unshearedPacketBase p root z j)
        (physicalParentSignal (d.N k) p root (p.R root)) a w).Finite ∧
      ((occupied S (fun z j => unshearedPacketBase p root z j)
        (physicalParentSignal (d.N k) p root (p.R root)) a w).ncard:ℝ)≤Kcensus/(a^3*w^dimension)) →
    (∀ (i : Fin L) (w : ℝ), Jets2.dyadicParameterWidth (n+i.val)≤w → w≤1 →
      ∀ (b : Fin 3 → ℤ) (j : ℤ) (D : Set (Fin 2 → ℤ)), MeasurableSet D →
      (((d.ν k (p.γ root)).prod volume).restrict S) {z |
        (fun l => ⌊unshearedPacketBase p root z l/ Jets2.dyadicParameterWidth (n+i.val)⌋)=b ∧
        ⌊physicalParentSignal (d.N k) p root (p.R root) z/w⌋=j ∧
        Jets2.parameterCode (Jets2.dyadicParameterWidth (n+i.val)) (fun l => v z.1 l)∈D}≤
          (ENNReal.ofReal (C*(Jets2.dyadicParameterWidth (n+i.val))^3*w^dimension)*(palette.map (Jets2.parameterCode (Jets2.dyadicParameterWidth (n+i.val)))) D)*
            (ENNReal.ofReal ((hp.frozenPacket root).unitFrame.q)*d.ν k (p.γ root) (p.A root))) →

    ∀ (H : ℕ), K ≤ (H:ℝ) →
    ∀ (level : I → ℕ), (∀ i, level i < n+L) →
    ∀ (cut : I → ℝ), (∀ i, 0 < cut i) →
    ∀ (δ Cderiv KL : ℝ), 0 < δ → 0 ≤ Cderiv →
    (∀ i, δ ≤ Jets2.dyadicParameterWidth (level i)) →
    (∀ i, 3*((H:ℝ)+1)*δ ≤ Jets2.dyadicParameterWidth (level i)) →
    (∀ i, max (6*(H:ℝ)/Jets2.dyadicParameterWidth n+2)
      ((2*(H:ℝ)+3)^7*(6*(H:ℝ)+12)^4*
        ((151200*(12*(H:ℝ)+3)*Cderiv*(3:ℝ)^dimension)*
          (Jets2.dyadicParameterWidth (level i))^(-ε)/cut i)*
            (2*(⌈2*(H:ℝ)+5⌉:ℝ)+1)) ≤ KL) →
    (∀ (i : I) (w : ℝ), δ ≤ w → w ≤ 1 →
      ∀ (b : Fin 3 → ℤ) (j : ℤ) (D : Set (Fin 2 → ℤ)), MeasurableSet D →
      (((d.ν k (p.γ root)).prod volume).restrict S) {z |
        (fun l => ⌊unshearedPacketBase p root z l/δ⌋)=b ∧
        ⌊physicalParentSignal (d.N k) p root (p.R root) z/w⌋=j ∧
        Jets2.parameterCode (Jets2.dyadicParameterWidth (level i)) (fun l => v z.1 l)∈D} ≤
          (ENNReal.ofReal (Cderiv*δ^3*w^dimension)*
            (palette.map (Jets2.parameterCode (Jets2.dyadicParameterWidth (level i)))) D)*
              (ENNReal.ofReal ((hp.frozenPacket root).unitFrame.q)*d.ν k (p.γ root) (p.A root))) →
    let packet := hp.frozenPacket root
    let ν := d.ν k (p.γ root)
    ∃ R : Set Ev, MeasurableSet R ∧ R⊆S ∧
      (ν.prod volume) (S\R) ≤
        (ENNReal.ofReal ((Kcensus^2*((2:ℝ)^steps)^3)*(L:ℝ)/Kfloor)+
          ENNReal.ofReal K⁻¹+
          ENNReal.ofReal (((4*K+2)^2)*(Jets2.dyadicParameterWidth n)^η/(1-(2:ℝ)^(-η)))+
          ∑ i : {i : I // n ≤ level i}, ENNReal.ofReal (cut i.val*Jets2.zoomBlockVisitConstant))*
            (ENNReal.ofReal packet.unitFrame.q*ν (p.A root)) ∧
      Nonempty (Jets2.OriginalPreStateData (packet.prior ν) (coefficientTable (d.N k) p root Vmax)
        (packet.selectedEvent R) palette dimension ε n L level KL) := by
  obtain ⟨η,hη,p₀,hp₀,hprepare⟩ := prepare_native_original_dyadic_floor_data dimension ε hdim hdim1 hε
  refine ⟨η,hη,p₀,hp₀,?_⟩
  intro d hd k m p κ₁ δ₀ σ s Mp Dp hp root Vmax hVmax source hsource hsourceF hR hvelocity
    S hS hSsource n L hL hn K C Kfloor Kcensus resolution steps hK hcoeffK hC hKfloor
    hresolution hKcensus hsteps hresolved palette hpalette hCoeffBudget hCapBudget hSupportBudget hcensus hpure
    H hKH level hstop cut hcut δ Cderiv KL hδ hCderiv hδlevel hsmall hKL hpureDeriv
  let packet := hp.frozenPacket root
  let ν := d.ν k (p.γ root)
  let ref := ENNReal.ofReal packet.unitFrame.q*ν (p.A root)
  obtain ⟨Rfloor,hRfloor,hRfloorS,hFloorLoss,floors⟩ :=
    hprepare d hd k m p κ₁ δ₀ σ s Mp Dp hp root Vmax hVmax source hsource hsourceF hR hvelocity
      S hS hSsource n L hL hn K C Kfloor Kcensus resolution steps hK hcoeffK hC hKfloor
      hresolution hKcensus hsteps hresolved palette hpalette hCoeffBudget hCapBudget hSupportBudget hcensus hpure
  obtain ⟨R,hR,hRfloor',hDerivLoss,⟨tables⟩⟩ :=
    prepare_native_original_derivative_source hd hp root hVmax source hsource hsourceF hR hvelocity
      Rfloor hRfloor (hRfloorS.trans hSsource) H (hK.trans hKH) (hcoeffK.trans hKH) floors hdim
      level hstop cut hcut hδ hCderiv hδlevel hsmall (by
        intro i w hw hw1 b j D hD
        exact (Measure.restrict_mono hRfloorS le_rfl _).trans (hpureDeriv i w hw hw1 b j D hD))
  have hRS : R⊆S := hRfloor'.trans hRfloorS
  refine ⟨R,hR,hRS,?_,?_⟩
  · have hsub : S\R⊆(S\Rfloor)∪(Rfloor\R) := by
      intro z hz
      by_cases h : z∈Rfloor
      · exact Or.inr ⟨h,hz.2⟩
      · exact Or.inl ⟨hz.1,h⟩
    calc
      _ ≤ (ν.prod volume) (S\Rfloor)+(ν.prod volume) (Rfloor\R) :=
        (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ _ := add_le_add hFloorLoss hDerivLoss
      _ = _ := by ring
  · exact ⟨⟨floors.restrict (image_mono hRfloor'),
      ⟨tables.lists,fun i q v => (tables.card i q v).trans (hKL i),tables.known⟩⟩⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestor
