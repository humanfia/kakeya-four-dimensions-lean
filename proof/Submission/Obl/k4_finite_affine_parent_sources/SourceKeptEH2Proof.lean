import Submission.Obl.k4_finite_affine_parent_sources.SourceKeptEH2

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! Assemble the pure and both joint bounds on one retained original law. -/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set MvPolynomial

noncomputable section

private lemma pure_cap_identity {Nk unit L d t r A B : ℝ} (hNk : 0 < Nk)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ENNReal.ofReal (A * Nk ^ (-(d * (unit * L * t)))) *
      (ENNReal.ofReal (((Nk ^ (unit * L)) ^ (-r)) ^ 3) * ENNReal.ofReal B) =
      ENNReal.ofReal (A * B * (Nk ^ (unit * L)) ^ (-3 * r - d * t)) := by
  have hn : 0 < Nk ^ (unit * L) := Real.rpow_pos_of_pos hNk _
  have ht : Nk ^ (-(d * (unit * L * t))) = (Nk ^ (unit * L)) ^ (-d * t) := by
    rw [← Real.rpow_mul hNk.le]
    congr 1
    ring
  have hr : ((Nk ^ (unit * L)) ^ (-r)) ^ 3 = (Nk ^ (unit * L)) ^ (-3 * r) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    congr 1
    ring
  rw [ht, hr, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [show -3 * r - d * t = -d * t + -3 * r by ring, Real.rpow_add hn]
  ring

private lemma source_base_mesh_eq (b : Trajectory → Fin 6 → ℝ) (N r : ℝ)
    (p : Incidence) :
    Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-r))
      (fun i : Fin 3 => exS b p.1 p.2 i.castSucc) = zS b N r p := by
  funext e
  fin_cases e <;> rfl

section Path

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- Collect the original density ceiling and the base-cell volume into a single power. -/
theorem source_cell_power_bound (D : SourceData p) (unit : ℝ)
    (hν : ∀ w, IsProbabilityMeasure (ν w)) (hNk : 1 < Nk) (hBw : 0 < B D.w₀)
    (hD₀ : D.D₀ = MajorFrame.frame (p.frame D.parent)) (hSm : MeasurableSet D.S)
    (hScount : D.S ⊆ p.counted D.parent)
    {G' : ℕ} (g : ℝ → Observation → ENNReal) (r : Fin G' → ℝ)
    (hg : ∀ j, Measurable (g (r j)))
    (hlaw : ∀ j, (((ν D.w₀).prod volume).restrict (E D.w₀)).map
      (obs (B D.w₀) (δ Nk (r j))) = (volume.prod Measure.count).withDensity (g (r j)))
    {τd hd d t : ℝ} (hmask : D.S ⊆ E D.w₀ ∩ densMask g (B D.w₀) Nk τd f r)
    (hd₀ : 0 ≤ d) (hhd : 0 ≤ hd) (ht : 0 ≤ t) (j : Fin G')
    (hj₁ : p.r D.i₀ + unit * L * t ≤ r j)
    (hj₂ : r j ≤ p.r D.i₀ + unit * L * t + hd)
    (hprof : f (p.r D.i₀) + d * (r j - p.r D.i₀) - 2 * (δ₀ * L) ≤ f (r j))
    {K : ℝ} (hK : pureConst p.κ Nk hd τd δ₀ L ≤ K)
    (rr : ℝ) (hb : Bool) (q : Fin 3 → ℤ) (a : ℤ) :
    (D.stage Nk L unit ν B).μ {z | zS (D.stage Nk L unit ν B).b
        (D.stage Nk L unit ν B).N rr z = q ∧
      ⌊(if hb then eval (exS (D.stage Nk L unit ν B).b z.1 z.2)
          (D.stage Nk L unit ν B).P else (exS (D.stage Nk L unit ν B).b z.1 z.2) 3) /
        ((D.stage Nk L unit ν B).N ^ (-t))⌋ = a} ≤
      ENNReal.ofReal (K * (Nk ^ (unit * L)) ^ (-3 * rr - d * t)) := by
  have hκ := hp.one_le_slack
  have hc := source_pure_cell hp D unit hν hNk hBw hD₀ hSm hScount hg hlaw hmask
    hd₀ hhd ht j hj₁ hj₂ hprof rr hb q a
  refine hc.trans ?_
  dsimp only [SourceData.stage]
  rw [pure_cap_identity (by linarith) (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hK (by positivity))

/-- The normalized counted measure is finite on every subset of a parent label. -/
theorem source_stage_isFinite (D : SourceData p) (unit : ℝ)
    (hν : ∀ w, IsProbabilityMeasure (ν w)) (hNk : 0 < Nk)
    (hcount : D.S ⊆ p.counted D.parent) :
    IsFiniteMeasure (D.stage Nk L unit ν B).μ := by
  letI : ∀ w, IsProbabilityMeasure (ν w) := hν
  have hκ := hp.one_le_slack
  have hdet : 0 < |(p.frame D.parent).det| := abs_pos.mpr (hp.chart D.parent).1
  have hA0 : 0 < ν D.w₀ (p.assigned D.parent) :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity))
      (label_prior_floor hp hNk D.parent)
  have hAt : ν D.w₀ (p.assigned D.parent) ≠ ⊤ := measure_ne_top _ _
  have hc0 : ENNReal.ofReal D.q₀ * ν D.w₀ (p.assigned D.parent) ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr D.q₀_pos).ne' hA0.ne'
  have hpkfin : ((ν D.w₀).prod volume) (p.packet D.parent) ≠ ⊤ := by
    rw [PathData.packet, Measure.prod_prod, Real.volume_Icc]
    exact ENNReal.mul_ne_top hAt ENNReal.ofReal_ne_top
  have hSfin : ((ν D.w₀).prod volume) D.S ≠ ⊤ :=
    ne_top_of_le_ne_top hpkfin (measure_mono fun z hz =>
      ⟨(hp.counted_support D.parent z (hcount hz)).2.1,
       (hp.counted_support D.parent z (hcount hz)).2.2.1⟩)
  constructor
  change muE (ν D.w₀) (p.assigned D.parent) D.t₀ D.q₀ D.S univ < ⊤
  rw [muE_apply _ _ _ _ _ MeasurableSet.univ, preimage_univ, univ_inter]
  exact lt_top_iff_ne_top.mpr
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hc0) hSfin)

end Path

/-- Both hidden and native joint caps from a common kept-state restriction. -/
theorem keptEH2 : KeptEH2 := by
  classical
  intro W m Mp Dp p ℓ Nk L κ₁ δ₀ σ d₁ S ω ν E B f sg hp hν hE hNk hL hd hd₁
    D n unit T N₀ hn hunit hnT hraw hBw hD₀ hSm hπ hpal S2 hS2m hS2count
    G' g r hg hlaw τd hdens hhdens hmask hgrid Hs _ _ _ endL hend w δs hδ0 hδt
    mesh hmesh hmeshT hkept Cn hnum K₀ hK₀ hκK hK₀N hN₀ hpureK hjointK hfinalK
  letI : ∀ w, IsProbabilityMeasure (ν w) := hν
  letI : IsProbabilityMeasure D.π := hπ
  have hNk0 : 0 < Nk := by linarith
  have hNt : 0 < Nk ^ (unit * L) := by positivity
  have hNt1 : 1 ≤ Nk ^ (unit * L) :=
    Real.one_le_rpow hNk.le (mul_pos hunit hL).le
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hT0 : 0 < T := lt_trans hn0 hnT
  have hcount : D.S ⊆ p.counted D.parent := fun z hz => hS2count (hkept hz).1
  have hDS2 : D.S ⊆ S2 := fun z hz => (hkept hz).1
  let D2 : SourceData p := { D with S := S2, c := fun _ _ _ => 0 }
  have hKpure0 : 0 ≤ pureConst p.κ Nk hdens τd δ₀ L := by
    have hκ := hp.one_le_slack
    unfold pureConst
    positivity
  have hpure : ∀ (D' : SourceData p), D'.parent = D.parent → D'.D₀ = D.D₀ →
      MeasurableSet D'.S → D'.S ⊆ S2 → ∀ rr t : ℝ, 0 ≤ t → t ≤ T →
      ∀ (hb : Bool) (q : Fin 3 → ℤ) (a : ℤ),
      (D'.stage Nk L unit ν B).μ {z | zS (D'.stage Nk L unit ν B).b
          (D'.stage Nk L unit ν B).N rr z = q ∧
        ⌊(if hb then eval (exS (D'.stage Nk L unit ν B).b z.1 z.2)
            (D'.stage Nk L unit ν B).P else (exS (D'.stage Nk L unit ν B).b z.1 z.2) 3) /
          ((D'.stage Nk L unit ν B).N ^ (-t))⌋ = a} ≤
        ENNReal.ofReal (pureConst p.κ Nk hdens τd δ₀ L *
          (Nk ^ (unit * L)) ^ (-3 * rr - d₁ * t)) := by
    intro D' hpar hframe hmeas hsub rr t ht htT hb q a
    obtain ⟨j, hj₁, hj₂, hprof⟩ := hgrid t ht htT
    have hw : D'.w₀ = D.w₀ := congrArg p.world hpar
    have hi : D'.i₀ = D.i₀ := congrArg p.lev hpar
    apply source_cell_power_bound hp D' unit hν hNk
      (by simpa only [hw] using hBw)
      (by rw [hframe, hpar]; exact hD₀) hmeas
      (by rw [hpar]; exact hsub.trans hS2count) g r
      (by simpa only [hw] using hg) (by simpa only [hw] using hlaw)
      (by simpa only [hw] using hsub.trans hmask) hd hhdens ht j
      (by simpa only [hi] using hj₁) (by simpa only [hi] using hj₂)
      (by simpa only [hi] using hprof) le_rfl rr hb q a
  have hA0 : ν D.w₀ (p.assigned D.parent) ≠ 0 := by
    have hκ := hp.one_le_slack
    have hdet := abs_pos.mpr (hp.chart D.parent).1
    exact (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity))
      (label_prior_floor hp hNk0 D.parent)).ne'
  have hAt : ν D.w₀ (p.assigned D.parent) ≠ ⊤ := measure_ne_top _ _
  let c : ENNReal := ENNReal.ofReal D.q₀ * ν D.w₀ (p.assigned D.parent)
  have hc0 : c ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.mpr D.q₀_pos).ne' hA0
  have hct : c ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAt
  have hsignal : ∀ rr t v : ℝ, rr ≤ T → 0 ≤ t → t ≤ T →
      (n : ℝ)⁻¹ ≤ v → v ≤ n → ∀ (q : Fin 3 → ℤ) (a v₀ : ℤ),
      (D.stage Nk L unit ν B).μ {z | zS (D.stage Nk L unit ν B).b
          (D.stage Nk L unit ν B).N rr z = q ∧
        ⌊eval (exS (D.stage Nk L unit ν B).b z.1 z.2) (D.stage Nk L unit ν B).P /
          ((D.stage Nk L unit ν B).N ^ (-t))⌋ = a ∧
        ⌊(D.stage Nk L unit ν B).b z.1 3 / ((D.stage Nk L unit ν B).N ^ (-v))⌋ = v₀} ≤
        ENNReal.ofReal (K₀ * (Nk ^ (unit * L)) ^ (-3 * rr - d₁ * t)) *
          D.π {w | ⌊w / ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀} := by
    intro rr t v hrr ht htT hv hvn q a v₀
    let Mmod := ENNReal.ofReal (pureConst p.κ Nk hdens τd δ₀ L *
      (Nk ^ (unit * L)) ^ (-3 * rr - d₁ * t))
    have hcell : ∀ q j, ((ν D.w₀).prod volume) (S2 ∩ bsCell (frameBase (D.frame Nk B))
        (frameSignal (D.frame Nk B) (D.stage Nk L unit ν B).P)
        ((Nk ^ (unit * L)) ^ (-rr)) ((Nk ^ (unit * L)) ^ (-t)) q j) ≤ c * Mmod := by
      intro q j
      exact cell_original_le hp D2 unit q j Mmod
        (hpure D2 rfl rfl hS2m Subset.rfl rr t ht htT true q j) hAt hA0
    have h := source_joint_cell hp D unit S2 hS2m endL hend w hδ0 hδt hmesh hkept
      (by positivity) (by positivity)
      (hmeshT.trans (Real.rpow_le_rpow_of_exponent_le hNt1 (by linarith)))
      (hmeshT.trans (Real.rpow_le_rpow_of_exponent_le hNt1 (by linarith))) v₀
      (hnum v hv hvn v₀) (c * Mmod) hcell q a
    refine h.trans ?_
    calc c⁻¹ * (Cn / δs * D.π {w | ⌊w / ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀} *
          (81 * (c * Mmod)))
        = (c⁻¹ * c) * ((81 * (Cn / δs) * ENNReal.ofReal (pureConst p.κ Nk hdens τd δ₀ L)) *
            ENNReal.ofReal ((Nk ^ (unit * L)) ^ (-3 * rr - d₁ * t)) *
            D.π {w | ⌊w / ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀}) := by
          dsimp [Mmod]
          rw [ENNReal.ofReal_mul hKpure0]
          ring
      _ ≤ ENNReal.ofReal K₀ * ENNReal.ofReal ((Nk ^ (unit * L)) ^ (-3 * rr - d₁ * t)) *
            D.π {w | ⌊w / ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀} := by
          rw [ENNReal.inv_mul_cancel hc0 hct, one_mul]
          gcongr
      _ = _ := by rw [ENNReal.ofReal_mul (by linarith : 0 ≤ K₀)]
  letI := source_stage_isFinite hp D unit hν hNk0 hcount
  have hb := SourceData.stage_b_measurable D unit (Nk := Nk) (L := L) (ν := ν) (B := B)
  have hgood := stage_good_bounds hp D unit hBw hD₀ hSm hcount
  have hgood' : ∀ᵐ z ∂(D.stage Nk L unit ν B).μ,
      (∀ i : Fin 3, |exS (D.stage Nk L unit ν B).b z.1 z.2 i.castSucc| ≤ K₀) ∧
      |eval (exS (D.stage Nk L unit ν B).b z.1 z.2) (D.stage Nk L unit ν B).P| ≤ K₀ ∧
      |eval (exS (D.stage Nk L unit ν B).b z.1 z.2)
        (pderiv (3 : Fin 4) (D.stage Nk L unit ν B).P)| ≤ K₀ ∧
      |eval (exS (D.stage Nk L unit ν B).b z.1 z.2)
        (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (D.stage Nk L unit ν B).P))| ≤ K₀ := by
    filter_upwards [hgood] with z hz
    exact ⟨fun i => (hz.1 i).trans hκK, hz.2.1.trans hκK,
      hz.2.2.1.trans hκK, hz.2.2.2.trans hκK⟩
  have hKle : K₀ ≤ D.K := by nlinarith [sq_nonneg (K₀ - 1)]
  intro rr t v hrr hrrn ht htn hv hvn
  refine ⟨hpal v hv hvn, ?_, ?_⟩
  · intro hh q a
    exact (hpure D rfl rfl hSm hDS2 rr t ht (htn.trans hnT.le) hh q a).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hpureK.trans hKle) (by positivity)))
  · intro hh q a v₀
    cases hh
    · have h := hraw (Nk ^ (unit * L)) K₀ d₁ hN₀ hK₀ hK₀N hd hd₁
        Incidence (D.stage Nk L unit ν B).μ
        (fun z => exS (D.stage Nk L unit ν B).b z.1 z.2) (measurable_exS hb)
        (D.stage Nk L unit ν B).P (SourceData.stage_P_degree hp D unit) hgood'
        (velBin (D.stage Nk L unit ν B).b ((Nk ^ (unit * L)) ^ (-v)) v₀)
        (D.π {w | ⌊w / ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀}) (measure_ne_top _ _) ?_
        rr t ((inv_pos.mpr hn0).le.trans hrr) hrrn ht htn q a
      · simp only [source_base_mesh_eq, velBin, mem_ofPred_eq] at h
        exact h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right hfinalK
            (show 0 ≤ (Nk ^ (unit * L)) ^ (-3 * rr - d₁ * t) from
              (Real.rpow_pos_of_pos hNt _).le))) le_rfl)
      · intro u s hu huT hs hsT q' a'
        simpa only [source_base_mesh_eq, velBin, mem_ofPred_eq, SourceData.stage] using
          hsignal u s v huT hs hsT hv hvn q' a' v₀
    · exact (hsignal rr t v (hrrn.trans hnT.le) ht (htn.trans hnT.le) hv hvn q a v₀).trans
        (mul_le_mul' (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right hKle
            (show 0 ≤ (Nk ^ (unit * L)) ^ (-3 * rr - d₁ * t) from
              (Real.rpow_pos_of_pos hNt _).le))) le_rfl)

end
end Submission.Obl.k4_finite_affine_parent_sources
