-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.NativeAncestorOriginalFloors, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestorCoefficientSource
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalDyadicFloorData
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ClockGoodSourceTransport

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestor

open Set MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent
open ParentSource ParentSource.Native
open Submission.Lib.K4ParentSignalPreparation.Census
open scoped ENNReal

noncomputable section

/-- The actual globally bounded ancestor coefficient table is fixed
before any current source. Only the model's event depends on that source. -/
def coefficientTable {W : ℕ} (N : ℝ) (p : PathData W) (root : Fin p.C) (Vmax : ℝ) : Ln → Fin 7 → ℝ :=
  Direct.boundedTable (ParentSignal.clockPacketCoefficients (SignalGraph.ancestorSignal N p root) p root)
    (p.κ+24*p.κ+p.κ^2+Vmax)

theorem measurable_coefficientTable {W : ℕ} (N : ℝ) (p : PathData W) (root : Fin p.C) (Vmax : ℝ) :
    Measurable (coefficientTable N p root Vmax) :=
  Direct.measurable_boundedTable _ (ParentSignal.measurable_clockPacketCoefficients _ _ _) _

section Path

variable {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (root : Fin p.C) {Vmax : ℝ} (hVmax : 0 ≤ Vmax)
    (source : Set Ev) (hsource : MeasurableSet source) (hsourceF : source⊆p.F root)

theorem model_coefficientTable :
    (model hp root Vmax hVmax source hsource hsourceF).scalarCoefficients=
      coefficientTable (d.N k) p root Vmax := rfl

end Path

/-- Prepare the original dyadic prior-floor metadata BEFORE final
child states. The returned original source can be arbitrarily cut;
its full original prior and ONE fixed velocity probability do not change. -/
theorem prepare_native_original_dyadic_floor_data (dimension ε : ℝ)
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

    let packet := hp.frozenPacket root
    let ν := d.ν k (p.γ root)
    ∃ R : Set Ev, MeasurableSet R ∧ R⊆S ∧
      (ν.prod volume) (S\R) ≤
        (ENNReal.ofReal ((Kcensus^2*((2:ℝ)^steps)^3)*(L:ℝ)/Kfloor)+
          ENNReal.ofReal K⁻¹+
          ENNReal.ofReal (((4*K+2)^2)*(Jets2.dyadicParameterWidth n)^η/(1-(2:ℝ)^(-η))))*
            (ENNReal.ofReal packet.unitFrame.q*ν (p.A root)) ∧
      Jets2.OriginalDyadicFloorData (packet.prior ν) (coefficientTable (d.N k) p root Vmax)
        (packet.selectedEvent R) palette dimension ε n L := by
  obtain ⟨η,hη,p₀,hp₀,hprepare⟩ := prepare_native_ancestor_coefficient_source dimension ε hdim hdim1 hε
  refine ⟨η,hη,p₀,hp₀,?_⟩
  intro d hd k m p κ₁ δ₀ σ s Mp Dp hp root Vmax hVmax source hsource hsourceF hR hvelocity
    S hS hSsource n L hL hn K C Kfloor Kcensus resolution steps hK hcoeffK hC hKfloor
    hresolution hKcensus hsteps hresolved palette hpalette hCoeffBudget hCapBudget hSupportBudget hcensus hpure
  let packet := hp.frozenPacket root
  let ν := d.ν k (p.γ root)
  let π : Fin L → Measure (Fin 2 → ℤ) := fun i =>
    palette.map (Jets2.parameterCode (Jets2.dyadicParameterWidth (n+i.val)))
  letI : IsProbabilityMeasure palette := hpalette
  letI : IsProbabilityMeasure ν := (hd.weights k).2.2 _
  have hπ (i : Fin L) : IsProbabilityMeasure (π i) :=
    (Measure.isProbabilityMeasure_map_iff (Jets2.measurable_parameterCode _).aemeasurable).mpr inferInstance
  obtain ⟨Ephys,Rclock,hEphys,hRclock,hRphys,hphysE,hloss,hphysical,hfloor⟩ :=
    hprepare d hd k m p κ₁ δ₀ σ s Mp Dp hp root Vmax hVmax source hsource hsourceF hR hvelocity
      S hS hSsource n L hL hn K C Kfloor Kcensus resolution steps hK hcoeffK hC hKfloor
      hresolution hKcensus hsteps hresolved π hπ hCoeffBudget hCapBudget hSupportBudget hcensus hpure
  let loss : ENNReal :=
    ENNReal.ofReal ((Kcensus^2*((2:ℝ)^steps)^3)*(L:ℝ)/Kfloor)+ENNReal.ofReal K⁻¹+
      ENNReal.ofReal (((4*K+2)^2)*(Jets2.dyadicParameterWidth n)^η/(1-(2:ℝ)^(-η)))
  have hA : ν (p.A root)≠0 := (hp.assignment_mass_pos (by linarith [hd.1 k]) root).ne'
  obtain ⟨R,hRmeas,hRS,hselected,hlossOriginal⟩ := original_good_source_of_clock packet ν hA
    S hS (hSsource.trans hsourceF) Rclock hRclock loss hloss
  have hselectedR : packet.selectedEvent R=Rclock :=
    hselected.trans (inter_eq_right.mpr (hRphys.trans hphysE))
  refine ⟨R,hRmeas,hRS,hlossOriginal,hpalette,?_⟩
  intro i z hz
  rw [hselectedR] at hz
  simpa only [model_coefficientTable] using hfloor i z hz

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestor
