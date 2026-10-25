-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0812 f7bed5fb, x0891 a669339c, x0923 e8a77b3e, x0807 989bea46 (SourceParentPalette: x0812's version); namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.PathLikelihood
import Submission.Obl.k4_finite_affine_parent_sources.ParentChoice
import Submission.Obl.k4_finite_affine_parent_sources.OriginalPathProbability

/-!
# The information window and one parent of the fixed prepared law

For one fixed probability `μ₀` on the world-tagged incidences of the actual terminal path, the
likelihood window (`path_original_likelihood_window`) and the two-floor parent choice
(`exists_original_parent_reference_floors`) give one window `i`, one actual parent label `b₀`
at level `level i` and one measurable retained set `D` such that the retained incidences of the
parent have the joint numerator

  `μ₀ (D ∩ par ∩ {end = h, vbin = z}) ≤ C μ₀ (par ∩ {end = h}) μ₀ (par ∩ {vbin = z}) / μ₀ par`

for every end history `h` at level `level (i+1)` and every original planar velocity bin `z`,
together with a success floor of the parent and a floor against its full packet.

Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set
open Submission.Obl.k4_finite_forest_width_selection
open scoped Classical

noncomputable section

local instance optMeasSW (C : ℕ) : MeasurableSpace (Option (Fin C)) := ⊤
local instance optSingSW (C : ℕ) : MeasurableSingletonClass (Option (Fin C)) := ⟨fun _ => trivial⟩

/-- The original planar velocity of a world-tagged incidence. -/
def worldVel {W : ℕ} (y : Fin W × Incidence) : Fin 2 → ℝ := ![y.2.1.2 3, y.2.1.2 4]

theorem measurable_worldVel {W : ℕ} : Measurable (worldVel (W := W)) := by
  refine measurable_pi_iff.mpr fun e => ?_
  fin_cases e
  · exact ((measurable_pi_apply 3).comp (measurable_snd.comp (measurable_fst.comp measurable_snd)) :
      Measurable fun y : Fin W × Incidence => y.2.1.2 3)
  · exact ((measurable_pi_apply 4).comp (measurable_snd.comp (measurable_fst.comp measurable_snd)) :
      Measurable fun y : Fin W × Incidence => y.2.1.2 4)

/-- The original planar velocity bin of mesh `δv`. -/
def worldBin {W : ℕ} (δv : ℝ) (y : Fin W × Incidence) : Fin 2 → ℤ :=
  fun e => ⌊worldVel y e / δv⌋

theorem measurable_worldBin {W : ℕ} (δv : ℝ) : Measurable (worldBin (W := W) δv) := by
  refine measurable_pi_iff.mpr fun e => ?_
  exact Int.measurable_floor.comp (((measurable_pi_apply e).comp measurable_worldVel).div_const δv)

/-- Ancestors of ancestors are ancestors, for every label. -/
theorem forestAncestor_anc {C : ℕ} {lev : Fin C → ℕ} {par : Fin C → Fin C}
    (hpar : ∀ b, 0 < lev b → lev (par b) + 1 = lev b) (b : Fin C) {i j : ℕ} (hij : i ≤ j) :
    forestAncestor lev par (forestAncestor lev par b j) i = forestAncestor lev par b i := by
  by_cases hjb : j ≤ lev b
  · exact forestAncestor_comp lev par hpar b hij hjb
  · have h0 : lev b - j = 0 := by omega
    simp only [forestAncestor, h0, Function.iterate_zero, id_eq]

/-- Two maps that agree almost everywhere have the same level sets up to null sets. -/
theorem measureReal_eq_of_ae_eq {X Y : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → Y} (hfg : ∀ᵐ x ∂μ, f x = g x) (c : Y) :
    μ.real {x | f x = c} = μ.real {x | g x = c} := by
  rw [measureReal_def, measureReal_def]
  congr 1
  apply measure_congr
  filter_upwards [hfg] with x hx
  change (f x = c) = (g x = c)
  rw [hx]

section

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- Histories at any two levels refine, everywhere. -/
theorem history_refines' {i j : ℕ} (hij : i ≤ j) (y : Fin W × Incidence) :
    p.history m i y = p.ancestorCode i (p.history m j y) := by
  cases hcode : p.terminalCode m y with
  | none => simp [PathData.history, hcode, PathData.ancestorCode]
  | some b =>
    simp only [PathData.history, Function.comp_apply, hcode, PathData.ancestorCode,
      Option.map_some]
    congr 1
    exact (forestAncestor_anc (fun b hb => (hp.parent b hb).1) b hij).symm

/-- **The information window and one parent.** -/
theorem exists_window_parent
    (μ₀ : Measure (Fin W × Incidence)) [IsProbabilityMeasure μ₀]
    (level : ℕ → ℕ) (hlevel : Monotone level) (hle : ∀ i, level i ≤ m - 1)
    (δv Rv : ℝ) (hδv : 0 < δv) (hRv : 0 ≤ Rv)
    (hbound : ∀ᵐ y ∂μ₀, ∀ e, |worldVel y e| ≤ Rv)
    (J : ℕ) (hJ : 0 < J) (N : ℝ) (hN : 1 < N)
    (w : Option (Fin p.C) → ℝ) (hw : ∀ a, 0 ≤ w a) (Bw : ℝ) (hBw : 0 < Bw)
    (hwB : ∑ a, w a ≤ Bw)
    (hθ1 : Real.sqrt ((Real.log ((Finset.Icc ⌊-Rv / δv⌋ ⌊Rv / δv⌋).card ^ 2 + 1 : ℕ) /
      J + 1) / Real.log N) < 1) :
    ∃ i < J, ∃ (a : Option (Fin p.C)) (D : Set (Fin W × Incidence)), MeasurableSet D ∧
      μ₀ {y | p.history m (level i) y = a} ≠ 0 ∧
      (1 - Real.sqrt ((Real.log ((Finset.Icc ⌊-Rv / δv⌋ ⌊Rv / δv⌋).card ^ 2 + 1 : ℕ) /
        J + 1) / Real.log N)) / (4 * Bw) * w a ≤
        μ₀.real (D ∩ {y | p.history m (level i) y = a}) ∧
      (1 - Real.sqrt ((Real.log ((Finset.Icc ⌊-Rv / δv⌋ ⌊Rv / δv⌋).card ^ 2 + 1 : ℕ) /
        J + 1) / Real.log N)) / 4 * μ₀.real {y | p.history m (level i) y = a} ≤
        μ₀.real (D ∩ {y | p.history m (level i) y = a}) ∧
      ∀ (h : Option (Fin p.C)) (z : Fin 2 → ℤ),
        μ₀.real ({y | (p.history m (level (i + 1)) y, worldBin δv y) = (h, z)} ∩
            {y | p.history m (level i) y = a} ∩ D) ≤
          N ^ Real.sqrt ((Real.log ((Finset.Icc ⌊-Rv / δv⌋ ⌊Rv / δv⌋).card ^ 2 + 1 : ℕ) /
            J + 1) / Real.log N) *
            μ₀.real ({y | p.history m (level (i + 1)) y = h} ∩
              {y | p.history m (level i) y = a}) *
            μ₀.real ({y | worldBin δv y = z} ∩ {y | p.history m (level i) y = a}) /
            μ₀.real {y | p.history m (level i) y = a} := by
  set θ := Real.sqrt ((Real.log ((Finset.Icc ⌊-Rv / δv⌋ ⌊Rv / δv⌋).card ^ 2 + 1 : ℕ) /
    J + 1) / Real.log N) with hθ
  obtain ⟨n, hn, code, terminal, palette, hcode, hdecode, i, hi, D, hD, hmassD, hcapD⟩ :=
    path_original_likelihood_window hp μ₀ level hlevel hle worldVel measurable_worldVel
      δv Rv hδv hRv hbound J hJ N hN
  rw [← hθ] at hmassD hcapD
  -- the true maps
  let fine : Fin W × Incidence → Option (Fin p.C) := p.history m (level (i + 1))
  let coarse : Fin W × Incidence → Option (Fin p.C) := p.history m (level i)
  let pal : Fin W × Incidence → Fin 2 → ℤ := worldBin δv
  have hfine : Measurable fine := hp.measurable_history _
  have hcoarse : Measurable coarse := hp.measurable_history _
  have hpal : Measurable pal := measurable_worldBin δv
  have hrefine : ∀ y, coarse y = p.ancestorCode (level i) (fine y) :=
    fun y => history_refines' hp (hlevel (Nat.le_succ i)) y
  -- the code maps agree with the true maps almost everywhere
  have hfine_ae : ∀ᵐ y ∂μ₀, p.ancestorCode (level (i + 1)) (terminal (code y)) = fine y := by
    filter_upwards [hdecode] with y hy
    simp only [fine, PathData.history, Function.comp_apply, hy.1]
  have hcoarse_ae : ∀ᵐ y ∂μ₀, p.ancestorCode (level i) (terminal (code y)) = coarse y := by
    filter_upwards [hdecode] with y hy
    simp only [coarse, PathData.history, Function.comp_apply, hy.1]
  have hpal_ae : ∀ᵐ y ∂μ₀, (fun e => ((palette (code y) e : ℤ))) = pal y := by
    filter_upwards [hdecode] with y hy
    funext e
    exact hy.2 e
  have hpal_range : ∀ᵐ y ∂μ₀, ∀ e, pal y e ∈ Finset.Icc ⌊-Rv / δv⌋ ⌊Rv / δv⌋ := by
    filter_upwards [hbound] with y hy e
    have h1 := hy e
    rw [abs_le] at h1
    simp only [pal, worldBin, Finset.mem_Icc]
    constructor
    · exact Int.floor_mono (div_le_div_of_nonneg_right h1.1 hδv.le)
    · exact Int.floor_mono (div_le_div_of_nonneg_right h1.2 hδv.le)
  -- the window cap for the true maps
  have hcap : ∀ h z, (μ₀.restrict D).real {y | (fine y, pal y) = (h, z)} ≤
      N ^ θ * μ₀.real {y | fine y = h} *
        (μ₀.real {y | (coarse y, pal y) = (p.ancestorCode (level i) h, z)} /
          μ₀.real {y | coarse y = p.ancestorCode (level i) h}) := by
    intro h z
    by_cases hz : ∀ e, z e ∈ Finset.Icc ⌊-Rv / δv⌋ ⌊Rv / δv⌋
    · let z' : Fin 2 → {j : ℤ // j ∈ Finset.Icc ⌊-Rv / δv⌋ ⌊Rv / δv⌋} := fun e => ⟨z e, hz e⟩
      have hc := hcapD (μ₀.restrict D) le_rfl h z'
      have hzz : (fun e => ((z' e : ℤ))) = z := rfl
      have e1 : (μ₀.restrict D).real {y | (p.ancestorCode (level (i + 1)) (terminal (code y)),
          palette (code y)) = (h, z')} = (μ₀.restrict D).real {y | (fine y, pal y) = (h, z)} := by
        have hae : ∀ᵐ y ∂(μ₀.restrict D), (p.ancestorCode (level (i + 1)) (terminal (code y)),
            (fun e => ((palette (code y) e : ℤ)))) = (fine y, pal y) := by
          filter_upwards [ae_restrict_of_ae hfine_ae, ae_restrict_of_ae hpal_ae] with y h1 h2
          rw [h1, h2]
        rw [← measureReal_eq_of_ae_eq hae (h, z)]
        congr 1
        ext y
        simp only [mem_ofPred_eq, Prod.mk.injEq]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, by rw [h2]⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          funext e
          apply Subtype.ext
          exact congrFun h2 e
      have e2 : μ₀.real {y | p.ancestorCode (level (i + 1)) (terminal (code y)) = h} =
          μ₀.real {y | fine y = h} := measureReal_eq_of_ae_eq hfine_ae h
      have e3 : μ₀.real {y | (p.ancestorCode (level i) (terminal (code y)), palette (code y)) =
          (p.ancestorCode (level i) h, z')} =
          μ₀.real {y | (coarse y, pal y) = (p.ancestorCode (level i) h, z)} := by
        have hae : ∀ᵐ y ∂μ₀, (p.ancestorCode (level i) (terminal (code y)),
            (fun e => ((palette (code y) e : ℤ)))) = (coarse y, pal y) := by
          filter_upwards [hcoarse_ae, hpal_ae] with y h1 h2
          rw [h1, h2]
        rw [← measureReal_eq_of_ae_eq hae (p.ancestorCode (level i) h, z)]
        congr 1
        ext y
        simp only [mem_ofPred_eq, Prod.mk.injEq]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, by rw [h2]⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          funext e
          apply Subtype.ext
          exact congrFun h2 e
      have e4 : μ₀.real {y | p.ancestorCode (level i) (terminal (code y)) =
          p.ancestorCode (level i) h} = μ₀.real {y | coarse y = p.ancestorCode (level i) h} :=
        measureReal_eq_of_ae_eq hcoarse_ae _
      rw [e1, e2, e3, e4] at hc
      exact hc
    · push Not at hz
      obtain ⟨e, he⟩ := hz
      have hnull : (μ₀.restrict D) {y | (fine y, pal y) = (h, z)} = 0 := by
        apply measure_mono_null (t := {y | pal y e ∉ Finset.Icc ⌊-Rv / δv⌋ ⌊Rv / δv⌋})
        · intro y hy
          have := congrArg (fun q => q.2 e) hy
          simp only at this
          simp only [mem_ofPred_eq, this]
          exact he
        · rw [Measure.restrict_apply' hD]
          apply measure_mono_null inter_subset_left
          exact ae_iff.mp (hpal_range.mono fun y hy => hy e)
      rw [measureReal_def, hnull, ENNReal.toReal_zero]
      positivity
  -- the parent choice
  have hcur : μ₀.restrict D ≤ μ₀ := Measure.restrict_le_self
  have hδ : 0 < 1 - θ := by linarith
  have hmass : 1 - θ ≤ (μ₀.restrict D).real univ := by
    rw [measureReal_restrict_apply MeasurableSet.univ, univ_inter]
    exact hmassD
  have href : μ₀.real univ ≤ 1 := by
    rw [measureReal_def, measure_univ, ENNReal.toReal_one]
  obtain ⟨a, ha, hfloor1, -, hfloor2⟩ := exists_original_parent_reference_floors μ₀
    (μ₀.restrict D) hcur coarse hcoarse w hw Bw (1 - θ) hBw hδ href hwB hmass
  have hpar : MeasurableSet {y | coarse y = a} := hcoarse (measurableSet_singleton a)
  have hM : 0 < μ₀.real {y | coarse y = a} := ENNReal.toReal_pos ha (measure_ne_top _ _)
  obtain ⟨-, hpcap⟩ := likelihood_cap_in_original_parent μ₀ (μ₀.restrict D) fine coarse
    (p.ancestorCode (level i)) pal hfine hcoarse hpal hrefine (N ^ θ) hcap a ha
  refine ⟨i, hi, a, D, hD, ha, ?_, ?_, ?_⟩
  · rw [measureReal_restrict_apply hpar] at hfloor1
    rwa [inter_comm] at hfloor1
  · rw [fixedParentRestriction_real _ _ _ _ MeasurableSet.univ, univ_inter,
      measureReal_restrict_apply hpar, le_div_iff₀ hM] at hfloor2
    rw [inter_comm]
    exact hfloor2
  · intro h z
    have hc := hpcap h z
    have hX : MeasurableSet {y | (fine y, pal y) = (h, z)} :=
      (hfine.prodMk hpal) (measurableSet_singleton _)
    have hF : MeasurableSet {y | fine y = h} := hfine (measurableSet_singleton h)
    have hZ : MeasurableSet {y | pal y = z} := hpal (measurableSet_singleton z)
    rw [fixedParentRestriction_real _ _ _ _ hX, ← fixedParentRestriction_self, fixedParentRestriction_real _ _ _ _ hF,
      fixedParentRestriction_real _ _ _ _ hZ, measureReal_restrict_apply (hX.inter hpar)] at hc
    rw [div_le_iff₀ hM] at hc
    calc μ₀.real ({y | (p.history m (level (i + 1)) y, worldBin δv y) = (h, z)} ∩
            {y | p.history m (level i) y = a} ∩ D)
        ≤ N ^ θ * (μ₀.real ({y | fine y = h} ∩ {y | coarse y = a}) /
            μ₀.real {y | coarse y = a}) *
          (μ₀.real ({y | pal y = z} ∩ {y | coarse y = a}) / μ₀.real {y | coarse y = a}) *
          μ₀.real {y | coarse y = a} := hc
      _ = N ^ θ * μ₀.real ({y | fine y = h} ∩ {y | coarse y = a}) *
          μ₀.real ({y | pal y = z} ∩ {y | coarse y = a}) / μ₀.real {y | coarse y = a} := by
          field_simp

end

end

end Submission.Obl.k4_finite_affine_parent_sources
