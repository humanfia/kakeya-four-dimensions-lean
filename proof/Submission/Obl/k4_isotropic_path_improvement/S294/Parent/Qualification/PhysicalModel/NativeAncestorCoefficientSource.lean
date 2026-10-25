-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.NativeAncestorCoefficientSource, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestorPureCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalCoefficientSourceFromPureCells

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestor

open Set MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent
open ParentSource ParentSource.Native
open Submission.Lib.K4ParentSignalPreparation.Census
open scoped ENNReal

noncomputable section

/-- Construct the full ORIGINAL ancestor coefficient floors from its
actual joint census and CURRENT original-velocity pure-cell numerators.
Physical floors, line durations and all scalar cap conversions are
constructed internally on the unchanged full original assignment prior.
The cleanup constants precede every native path and incidence source. -/
theorem prepare_native_ancestor_coefficient_source (dimension ε : ℝ)
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
    ∀ π : Fin L → Measure (Fin 2 → ℤ), (∀ i, IsProbabilityMeasure (π i)) →
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
          (ENNReal.ofReal (C*(Jets2.dyadicParameterWidth (n+i.val))^3*w^dimension)*(π i) D)*
            (ENNReal.ofReal ((hp.frozenPacket root).unitFrame.q)*d.ν k (p.γ root) (p.A root))) →
    let c := (model hp root Vmax hVmax source hsource hsourceF).scalarCoefficients
    let νA := (hp.frozenPacket root).prior (d.ν k (p.γ root))
    let Eclock := (hp.frozenPacket root).selectedEvent S
      ∃ (Ephys R : Set Ev), MeasurableSet Ephys ∧ MeasurableSet R ∧ R⊆Ephys ∧ Ephys⊆Eclock ∧
        (νA.prod volume) (Eclock\R) ≤ ENNReal.ofReal ((Kcensus^2*((2:ℝ)^steps)^3)*(L:ℝ)/Kfloor)+
          ENNReal.ofReal K⁻¹+
          ENNReal.ofReal (((4*K+2)^2)*(Jets2.dyadicParameterWidth n)^η/(1-(2:ℝ)^(-η))) ∧
        (∀ i : Fin L, ∀ z∈Ephys,
          ENNReal.ofReal ((Jets2.dyadicParameterWidth (n+i.val))^((3:ℝ)+dimension)/Kfloor) ≤
            ((νA.prod volume).restrict Ephys)
              ((Jets2.originalFineState c (Jets2.dyadicParameterWidth (n+i.val))) ⁻¹'
                {Jets2.originalFineState c (Jets2.dyadicParameterWidth (n+i.val)) z})) ∧
        ∀ i : Fin L, ∀ z∈R,
          ENNReal.ofReal ((Jets2.dyadicParameterWidth (n+i.val))^(2+dimension)*
            (Jets2.dyadicParameterWidth (n+i.val))^ε)*(π i)
              {Jets2.vbin (Jets2.dyadicParameterWidth (n+i.val)) (c z.1)} ≤
            νA {l | Jets2.parameterCode (Jets2.dyadicParameterWidth (n+i.val)) (c l)=
              Jets2.parameterCode (Jets2.dyadicParameterWidth (n+i.val)) (c z.1)} := by
  obtain ⟨η,hη,p₀,hp₀,hcleanup⟩ := Jets2.prepare_original_coefficient_source_of_pure_cells
    dimension ε hdim hdim1 hε
  refine ⟨η,hη,p₀,hp₀,?_⟩
  intro d hd k m p κ₁ δ₀ σ s Mp Dp hp root Vmax hVmax source hsource hsourceF hR hvelocity
    S hS hSsource n L hL hn K C Kfloor Kcensus resolution steps hK hcoeffK hC hKfloor
    hresolution hKcensus hsteps hresolved π hπ hCoeffBudget hCapBudget hSupportBudget hcensus hpure
  let pm := model hp root Vmax hVmax source hsource hsourceF
  let νA := (hp.frozenPacket root).prior (d.ν k (p.γ root))
  let Eclock := (hp.frozenPacket root).selectedEvent S
  letI : IsProbabilityMeasure (d.ν k (p.γ root)) := (hd.weights k).2.2 _
  letI : IsProbabilityMeasure νA := hp.frozenPacket_prior_probability (by linarith [hd.1 k]) root
  letI : ∀ i, IsProbabilityMeasure (π i) := hπ
  have hEclock : MeasurableSet Eclock := (hp.frozenPacket root).measurable_selectedEvent hS
  have hunit : Eclock⊆univ×ˢ Icc (0:ℝ) 1 :=
    ((hp.frozenPacket root).selectedEvent_subset (hSsource.trans hsourceF)).trans
      (hp.frozenPacket root).event_unit_time
  have hcoeff : ∀ l∈(univ : Set Ln), ∀ j, |pm.scalarCoefficients l j|≤K :=
    fun l _ j => (model_global_coefficients hp root hVmax source hsource hsourceF l j).trans hcoeffK
  have hcensusClock (a w : ℝ) (ha : resolution≤a) (ha1 : a≤1) (hw : resolution≤w) (hw1 : w≤1)
      (hshape : Kcensus^(100:ℕ)*a≤w) :
      (occupied Eclock (fun z => ![z.2,Jets2.zy (pm.scalarCoefficients z.1) z.2 0,
        Jets2.zy (pm.scalarCoefficients z.1) z.2 1]) (fun z => Jets2.zx (pm.scalarCoefficients z.1) z.2) a w).Finite ∧
      ((occupied Eclock (fun z => ![z.2,Jets2.zy (pm.scalarCoefficients z.1) z.2 0,
        Jets2.zy (pm.scalarCoefficients z.1) z.2 1]) (fun z => Jets2.zx (pm.scalarCoefficients z.1) z.2) a w).ncard:ℝ)≤
          Kcensus/(a^3*w^dimension) := by
    have heq : occupied Eclock (Jets2.originalBaseCoordinates pm.scalarCoefficients)
        (fun z => Jets2.zx (pm.scalarCoefficients z.1) z.2) a w=
        occupied S (fun z j => unshearedPacketBase p root z j)
          (physicalParentSignal (d.N k) p root (p.R root)) a w := by
      have hb : Jets2.originalBaseCoordinates pm.scalarCoefficients=(fun z i => pm.originalBase z i) :=
        funext (scalar_originalBaseCoordinates pm)
      have hs : (fun z : Ev => Jets2.zx (pm.scalarCoefficients z.1) z.2)=(fun z => pm.originalPoint z 3) :=
        funext (scalar_originalSignal pm)
      rw [hb,hs]
      simpa only [div_one] using model_occupied hp root hVmax source hsource hsourceF hR hvelocity
        S hSsource a w 1
    change (occupied Eclock (Jets2.originalBaseCoordinates pm.scalarCoefficients)
      (fun z => Jets2.zx (pm.scalarCoefficients z.1) z.2) a w).Finite ∧
      ((occupied Eclock (Jets2.originalBaseCoordinates pm.scalarCoefficients)
        (fun z => Jets2.zx (pm.scalarCoefficients z.1) z.2) a w).ncard:ℝ)≤Kcensus/(a^3*w^dimension)
    rw [heq]
    exact hcensus a w ha ha1 hw hw1 hshape
  have hphysical := Jets2.original_dyadic_physical_census Eclock pm.scalarCoefficients
    hresolution hKcensus hdim hdim1.le hcensusClock steps n L hL hsteps hresolved
  have hpureClock (i : Fin L) (w : ℝ) (hw : Jets2.dyadicParameterWidth (n+i.val)≤w) (hw1 : w≤1)
      (b : Fin 3 → ℤ) (j : ℤ) (D : Set (Fin 2 → ℤ)) :
      ((νA.prod volume).restrict Eclock) {z |
        Jets2.originalBaseCode pm.scalarCoefficients (Jets2.dyadicParameterWidth (n+i.val)) z=b ∧
        ⌊Jets2.zx (pm.scalarCoefficients z.1) z.2/w⌋=j ∧
        Jets2.vbin (Jets2.dyadicParameterWidth (n+i.val)) (pm.scalarCoefficients z.1)∈D}≤
          ENNReal.ofReal (C*(Jets2.dyadicParameterWidth (n+i.val))^3*w^dimension)*(π i) D := by
    exact model_scalar_pure_cap hp root hVmax source hsource hsourceF hR hvelocity
      (d.ν k (p.γ root)) (hp.assignment_mass_pos (by linarith [hd.1 k]) root).ne'
      S hS hSsource (Jets2.dyadicParameterWidth (n+i.val)) w (Jets2.dyadicParameterWidth (n+i.val)) b j D
      (to_countable D).measurableSet _ (hpure i w hw hw1 b j D (to_countable D).measurableSet)
  exact hcleanup n L hL hn Ln νA pm.scalarCoefficients pm.measurable_scalarCoefficients Eclock hEclock
    univ MeasurableSet.univ hunit K C Kfloor (Kcensus^2*((2:ℝ)^steps)^3) hK hC hKfloor π
    hcoeff hCoeffBudget hCapBudget hSupportBudget hphysical hpureClock

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestor
