import Submission.Obl.k4_scalar_guarded_entropic_path.Reference.Exceptions
import Submission.Obl.k4_scalar_guarded_entropic_path.Info.WindowChoice
import Submission.Obl.k4_scalar_guarded_entropic_path.StageAssembly

/-!
# The reference fields of one stage

`withReference st Kb m α` keeps the geometric data of a stage `st` (problem, sample, scale,
reference laws, layers, ...) and fills in the reference fields: the canonical common finite
code of the box `canonM N Kb m` (`Info.Canonical`), the velocity palettes
`Info.velocityPalette σ_g`, and the exponent `α`.

`CandidateInput` lists the finite hypotheses on the stage under which these fields satisfy
the code, mesh pure ceiling and Frostman clauses of `RawStage.Good`:

* the reference laws lie under the incidence laws and charge none of the finitely many
  pure exceptions (at the mesh depths `scale · j / m`, `j ≤ m²`, and at the terminal depth
  `L`) nor the angular exceptions at a finite grid `us` of velocity resolutions covering
  `[scale / R, scale · R]` with gaps at most `ε` (`angularGrid`);
* every world is null or has mass at least `N₀^{-γ}`;
* the profile is at least `d r - ε` on `[0, scale · m]`, `S ≤ min(S_p, 1)`;
* `τ, γ ≤ ε`, `2 ≤ N₀^ε` and `N₀^{5ε} ≤ B`.

`good_withReference` assembles `RawStage.Good` from the geometric clauses, the reference
hypotheses, `k + 1 ≤ m`, the bounds on `α`, and the weighted information score of the
canonical code (the conclusion of `Info.exists_window_info_bins`, see `info_of_window`).
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Reference

open Submission.Obl.k4_scalar_linear_critical_extremizers
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-! ### Scaled resolutions -/

theorem rpow_rpow_neg {N₀ : ℝ} (hN₀ : 0 ≤ N₀) (a s : ℝ) :
    (N₀ ^ a) ^ (-s) = N₀ ^ (-(a * s)) := by
  rw [← Real.rpow_mul hN₀, mul_neg]

/-- Pure observations at resolution `N₀^a` and depth `s` are those at depth `a s` of `N₀`. -/
theorem pureObservation_rpow {N₀ : ℝ} (hN₀ : 0 ≤ N₀) (a s : ℝ) :
    pureObservation (N₀ ^ a) s = obsMap N₀ (a * s) := by
  funext z
  simp only [pureObservation, hiddenBin, obsMap, rpow_rpow_neg hN₀]

theorem velocityBin_rpow {N₀ : ℝ} (hN₀ : 0 ≤ N₀) (a b v : ℝ) :
    velocityBin (N₀ ^ a) b v = ⌊v / N₀ ^ (-(a * b))⌋ := by
  simp only [velocityBin, rpow_rpow_neg hN₀]

/-! ### Support of the reference laws -/

/-- A law under an incidence law of an exact problem lives on times in `[0, 1]` and
coefficients bounded by `K`. -/
theorem ae_bounded {p : Code} (hp : Split.Exact p) (k : ℕ) (g : Fin (p.1 k))
    {σ : Measure Incidence} (hσ : σ ≤ Split.mu p k g) :
    ∀ᵐ z ∂σ, z.2 ∈ Icc (0 : ℝ) 1 ∧ ∀ e, |z.1.2 e| ≤ p.K k := by
  obtain ⟨hprob, _, hK, hEm, hEsub, _⟩ := (hp.2.1 k).2.2.2.1 g
  have hprob' : IsProbabilityMeasure (p.prior k g) := hprob
  have hm : MeasurableSet {z : Incidence | ∀ e, |z.1.2 e| ≤ p.K k} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun e : Fin 5 =>
      measurableSet_le (show Measurable (fun z : Incidence => |z.1.2 e|) by fun_prop)
        measurable_const
  have hcoef : ∀ᵐ z ∂(p.prior k g).prod (volume : Measure ℝ), ∀ e, |z.1.2 e| ≤ p.K k := by
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    filter_upwards [hK] with l hl
    exact Filter.Eventually.of_forall fun _ => hl
  have hmu : ∀ᵐ z ∂(((p.prior k g).prod (volume : Measure ℝ)).restrict (p.support k g)),
      z.2 ∈ Icc (0 : ℝ) 1 ∧ ∀ e, |z.1.2 e| ≤ p.K k := by
    filter_upwards [ae_restrict_of_ae hcoef, ae_restrict_mem hEm] with z hz hE
    exact ⟨(hEsub hE).2, hz⟩
  exact ae_mono hσ hmu

/-! ### The reference fields -/

/-- The reference fields of a stage: the canonical common code of the box
`canonM N Kb m`, the velocity palettes of the reference laws, and the exponent `α`. -/
def withReference (st : RawStage) (Kb : ℝ) (m : ℕ) (α : ℝ) : RawStage :=
  { st with
    m := m
    n := fun _ => Info.canonN m (Info.canonM st.N Kb m)
    X := fun _ => Info.canonX st.N m (Info.canonM st.N Kb m)
    Y := fun _ => Info.canonY m (Info.canonM st.N Kb m)
    Z := fun _ => Info.canonZ m (Info.canonM st.N Kb m)
    q := fun _ => Info.canonQ m
    c := fun _ => Info.canonC m
    α := α
    π₀ := fun g => Info.velocityPalette (st.σ g) }

/-! ### Finite test grids -/

/-- The tangent mesh depths `scale · j / m`, `j ≤ m²`, of the pure ceilings. -/
def pureGrid (scale : ℝ) (m : ℕ) : Finset ℝ :=
  (Finset.range (m ^ 2 + 1)).image fun j : ℕ => scale * ((j : ℝ) / (m : ℝ))

theorem mem_pureGrid (scale : ℝ) (m : ℕ) (j : Fin (m ^ 2 + 1)) :
    scale * ((j : ℝ) / (m : ℝ)) ∈ pureGrid scale m :=
  Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr j.2, rfl⟩

theorem div_le_of_le_sq {m j : ℕ} (hm : 1 ≤ m) (hj : j ≤ m ^ 2) :
    (j : ℝ) / (m : ℝ) ≤ m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_le_iff₀ hm0]
  have : ((j : ℕ) : ℝ) ≤ (m : ℝ) ^ 2 := by exact_mod_cast hj
  nlinarith

theorem pureGrid_valid {scale : ℝ} {m : ℕ} (hscale : 0 ≤ scale) (hm : 1 ≤ m) :
    ∀ r ∈ pureGrid scale m, 0 ≤ r ∧ r ≤ scale * m := by
  intro r hr
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
  have hj' : j ≤ m ^ 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  exact ⟨mul_nonneg hscale (by positivity),
    mul_le_mul_of_nonneg_left (div_le_of_le_sq hm hj') hscale⟩

/-- A finite grid of velocity resolutions in `[scale / R, scale · R]` with gaps `ε`. -/
def angularGrid (scale R ε : ℝ) : Finset ℝ :=
  (Finset.range (⌊(scale * R - scale / R) / ε⌋₊ + 1)).image fun i : ℕ => scale / R + i * ε

theorem angularGrid_valid {scale R ε : ℝ} (hscale : 0 < scale) (hR : 1 ≤ R) (hε : 0 < ε) :
    ∀ u ∈ angularGrid scale R ε, 0 < u ∧ u ≤ scale * R := by
  intro u hu
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
  have hR0 : 0 < R := by linarith
  have hsR : scale / R ≤ scale * R := by
    rw [div_le_iff₀ hR0]
    have hRR : 1 ≤ R * R := by nlinarith
    calc scale = scale * 1 := (mul_one scale).symm
      _ ≤ scale * (R * R) := mul_le_mul_of_nonneg_left hRR hscale.le
      _ = scale * R * R := by ring
  have hx : 0 ≤ (scale * R - scale / R) / ε := div_nonneg (by linarith) hε.le
  have hi' : (i : ℝ) ≤ (scale * R - scale / R) / ε := by
    have h1 : i ≤ ⌊(scale * R - scale / R) / ε⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    exact (Nat.cast_le.mpr h1).trans (Nat.floor_le hx)
  have hiε : (i : ℝ) * ε ≤ scale * R - scale / R := by
    rwa [le_div_iff₀ hε] at hi'
  refine ⟨by positivity, by linarith⟩

theorem angularGrid_cover {scale R ε : ℝ} (hscale : 0 < scale) (hR : 0 < R) (hε : 0 < ε)
    {b : ℝ} (hb1 : R⁻¹ ≤ b) (hb2 : b ≤ R) :
    ∃ u ∈ angularGrid scale R ε, u ≤ scale * b ∧ scale * b - u ≤ ε := by
  have hsb : scale / R ≤ scale * b := by
    rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hb1 hscale.le
  have hbR : scale * b ≤ scale * R := mul_le_mul_of_nonneg_left hb2 hscale.le
  set y := (scale * b - scale / R) / ε with hy
  have hy0 : 0 ≤ y := div_nonneg (by linarith) hε.le
  refine ⟨scale / R + (⌊y⌋₊ : ℝ) * ε, Finset.mem_image.mpr ⟨⌊y⌋₊, ?_, rfl⟩, ?_, ?_⟩
  · apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.floor_le_floor
    exact div_le_div_of_nonneg_right (by linarith) hε.le
  · have h1 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
    have h2 : (⌊y⌋₊ : ℝ) * ε ≤ scale * b - scale / R := by
      rw [hy, le_div_iff₀ hε] at h1; exact h1
    linarith
  · have h1 : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
    have h2 : scale * b - scale / R < ((⌊y⌋₊ : ℝ) + 1) * ε := by
      rw [hy, div_lt_iff₀ hε] at h1; exact h1
    nlinarith

/-! ### The reference hypotheses of a candidate stage -/

/-- The finite reference hypotheses of one candidate stage (see the module docstring). -/
structure CandidateInput (st : RawStage) (d S R Kb : ℝ) (m : ℕ) (ε τ γ : ℝ)
    (us : Finset ℝ) : Prop where
  exact : Split.Exact st.p
  scale_pos : 0 < st.scale
  S_pos : 0 < S
  S_le_one : S ≤ 1
  S_le : S ≤ st.p.S
  R_pos : 0 < R
  m_pos : 1 ≤ m
  K_le : st.p.K st.sample ≤ Kb
  mesh_le : st.scale * m ≤ st.p.L
  tol_pos : 0 < τ
  tol_le : τ ≤ ε
  floor_le : γ ≤ ε
  two_le : 2 ≤ st.N₀ ^ ε
  B_ge : st.N₀ ^ (5 * ε) ≤ st.B
  profile : ∀ r, 0 ≤ r → r ≤ st.scale * m → d * r - ε ≤ st.p.profile r
  sigma_le : ∀ g, st.σ g ≤ Split.mu st.p st.sample g
  floor : ∀ g, st.σ g = 0 ∨ ENNReal.ofReal ((st.N₀ ^ γ)⁻¹) ≤ st.σ g Set.univ
  grid_valid : ∀ u ∈ us, 0 < u ∧ u ≤ st.p.U
  grid_cover : ∀ b, R⁻¹ ≤ b → b ≤ R → ∃ u ∈ us, u ≤ st.scale * b ∧ st.scale * b - u ≤ ε
  pure_null : ∀ g (j : Fin (m ^ 2 + 1)),
    st.σ g (pureExc st.p st.sample g (st.scale * ((j : ℝ) / (m : ℝ))) τ) = 0
  terminal_null : ∀ g, st.σ g (pureExc st.p st.sample g st.p.L τ) = 0
  angular_null : ∀ g, ∀ u ∈ us, st.σ g (angExc st.p st.sample g u τ) = 0

/-! ### Code and mesh pure ceilings -/

/-- **The code clause, unfolded.** For a law `σ ≤ μ_g` at resolution `N = N₀^scale`, the
canonical code of the box `canonM N Kb m` and the palette `velocityPalette σ` satisfy the
clauses of `RawStage.CodeGood`; stated unfolded, so that it closes `CodeGood` of any stage
whose reference fields are these (by definitional unfolding). -/
theorem codeGood_canonical {p : Code} (hp : Split.Exact p) {k : ℕ} {g : Fin (p.1 k)}
    {scale Kb B d ε τ : ℝ} {m : ℕ} (hscale : 0 < scale) (hm : 1 ≤ m) (hKb : p.K k ≤ Kb)
    (hmL : scale * m ≤ p.L) (hτ : τ ≤ ε)
    (hprof : ∀ r, 0 ≤ r → r ≤ scale * m → d * r - ε ≤ p.profile r)
    (hB : p.N k ^ (2 * ε) ≤ B) {σ : Measure Incidence} (hσ : σ ≤ Split.mu p k g)
    (hpure : ∀ j : Fin (m ^ 2 + 1), σ (pureExc p k g (scale * ((j : ℝ) / (m : ℝ))) τ) = 0) :
    Measurable (Info.canonX (p.N k ^ scale) m (Info.canonM (p.N k ^ scale) Kb m)) ∧
      IsProbabilityMeasure (Info.velocityPalette σ) ∧
      Measure.map (fun z : Incidence => z.1.2 1) σ = (σ Set.univ) • Info.velocityPalette σ ∧
      (∀ᵐ z ∂σ,
        Info.canonZ m (Info.canonM (p.N k ^ scale) Kb m)
            (Info.canonX (p.N k ^ scale) m (Info.canonM (p.N k ^ scale) Kb m) z) =
          velocityBin (p.N k ^ scale) (m : ℝ) (z.1.2 1) ∧
        ∀ j : Fin (m ^ 2 + 1),
          baseBin (p.N k ^ scale) ((j : ℝ) / (m : ℝ)) z =
            Info.canonQ m j (Info.canonY m (Info.canonM (p.N k ^ scale) Kb m)
              (Info.canonX (p.N k ^ scale) m (Info.canonM (p.N k ^ scale) Kb m) z)) ∧
          hiddenBin (p.N k ^ scale) ((j : ℝ) / (m : ℝ)) z =
            Info.canonC m j (Info.canonY m (Info.canonM (p.N k ^ scale) Kb m)
              (Info.canonX (p.N k ^ scale) m (Info.canonM (p.N k ^ scale) Kb m) z))) ∧
      ∀ j : Fin (m ^ 2 + 1),
        Measure.map (pureObservation (p.N k ^ scale) ((j : ℝ) / (m : ℝ))) σ ≤
          ENNReal.ofReal (B * (p.N k ^ scale) ^ (-d * ((j : ℝ) / (m : ℝ)))) •
            ((volume : Measure (Fin 2 → ℝ)).prod (Measure.count : Measure ℤ)) := by
  have hN₀1 : 1 ≤ p.N k := exact_N_ge_one hp k
  have hN₀0 : 0 < p.N k := by linarith
  have hN1 : 1 ≤ p.N k ^ scale := Real.one_le_rpow hN₀1 hscale.le
  have hK1 : 1 ≤ Kb := (hp.1.2.2.1.1 k).trans hKb
  have hfin : IsFiniteMeasure σ := isFiniteMeasure_of_le_mu hp hσ
  have hspec := Info.velocityPalette_spec σ
  refine ⟨Info.measurable_canonX _ _ _, hspec.1, hspec.2, ?_, ?_⟩
  · filter_upwards [ae_bounded hp k g hσ] with z hz
    exact Info.canon_decode hN1 hK1 hm hz.1 (fun e => (hz.2 e).trans hKb)
  · intro j
    have hj0 : (0 : ℝ) ≤ (j : ℝ) / (m : ℝ) := by positivity
    have hjm : (j : ℝ) / (m : ℝ) ≤ m := div_le_of_le_sq hm (Nat.lt_succ_iff.mp j.2)
    set s : ℝ := (j : ℝ) / (m : ℝ) with hs
    set r := scale * s with hr
    have hr0 : 0 ≤ r := mul_nonneg hscale.le hj0
    have hrm : r ≤ scale * m := mul_le_mul_of_nonneg_left hjm hscale.le
    have hceil := map_obsMap_le hp hr0 (hrm.trans hmL) hσ (hpure j)
    rw [pureObservation_rpow hN₀0.le scale s]
    refine hceil.trans (Measure.le_iff'.mpr fun A => ?_)
    simp only [Measure.smul_apply, smul_eq_mul]
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
    have hf := hprof r hr0 hrm
    have hexp : -p.profile r + τ ≤ 2 * ε + scale * (-d * s) := by
      have : scale * (-d * s) = -(d * r) := by rw [hr]; ring
      rw [this]; linarith
    calc p.N k ^ (-p.profile r + τ) ≤ p.N k ^ (2 * ε + scale * (-d * s)) :=
          Real.rpow_le_rpow_of_exponent_le hN₀1 hexp
      _ = p.N k ^ (2 * ε) * p.N k ^ (scale * (-d * s)) := Real.rpow_add hN₀0 _ _
      _ ≤ B * p.N k ^ (scale * (-d * s)) :=
          mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg hN₀0.le _)
      _ = B * (p.N k ^ scale) ^ (-d * s) := by rw [← Real.rpow_mul hN₀0.le]

/-- **The code clause** of the canonical reference fields in one world. -/
theorem withReference_codeGood (st : RawStage) {Kb α d ε τ : ℝ} {m : ℕ}
    (hp : Split.Exact st.p) (hscale : 0 < st.scale) (hm : 1 ≤ m)
    (hKb : st.p.K st.sample ≤ Kb) (hmL : st.scale * m ≤ st.p.L) (hτ : τ ≤ ε)
    (hprof : ∀ r, 0 ≤ r → r ≤ st.scale * m → d * r - ε ≤ st.p.profile r)
    (hB : st.N₀ ^ (2 * ε) ≤ st.B) (g : Fin st.W)
    (hσ : st.σ g ≤ Split.mu st.p st.sample g)
    (hpure : ∀ j : Fin (m ^ 2 + 1),
      st.σ g (pureExc st.p st.sample g (st.scale * ((j : ℝ) / (m : ℝ))) τ) = 0) :
    (withReference st Kb m α).CodeGood d g :=
  codeGood_canonical hp hscale hm hKb hmL hτ hprof hB hσ hpure

/-! ### Frostman bounds of the palettes -/

/-- **Frostman bound** of the palette of one world at one velocity resolution `b`, from a
tested angular resolution `u ∈ [scale · b - ε, scale · b]`. -/
theorem palette_frostman {p : Code} (hp : Split.Exact p) {k : ℕ} {g : Fin (p.1 k)}
    {scale S ε τ γ B b u : ℝ} (hscale : 0 < scale) (hS0 : 0 < S) (hS1 : S ≤ 1)
    (hSp : S ≤ p.S) (hτ0 : 0 < τ) (hτ : τ ≤ ε) (hγ : γ ≤ ε) (h2 : 2 ≤ p.N k ^ ε)
    (hB : p.N k ^ (5 * ε) ≤ B) (hb : 0 < b) {σ : Measure Incidence}
    (hσ : σ ≤ Split.mu p k g)
    (hfloor : σ = 0 ∨ ENNReal.ofReal ((p.N k ^ γ)⁻¹) ≤ σ Set.univ)
    (hL : σ (pureExc p k g p.L τ) = 0)
    (hu0 : 0 < u) (huU : u ≤ p.U) (hA : σ (angExc p k g u τ) = 0)
    (hub : u ≤ scale * b) (hgap : scale * b - u ≤ ε) (e : ℤ) :
    Info.velocityPalette σ {v | velocityBin (p.N k ^ scale) b v = e} ≤
      ENNReal.ofReal (B * (p.N k ^ scale) ^ (-S * b)) := by
  have hN1 : 1 ≤ p.N k := exact_N_ge_one hp k
  have hN0 : 0 < p.N k := by linarith
  have hε0 : 0 ≤ ε := hτ0.le.trans hτ
  have hsb : 0 < scale * b := mul_pos hscale hb
  set w := p.N k ^ (-(scale * b)) with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos hN0 _
  have hset : {v : ℝ | velocityBin (p.N k ^ scale) b v = e} = {v | (⌊v / w⌋ : ℤ) = e} := by
    ext v
    simp only [mem_ofPred_eq, velocityBin_rpow hN0.le]
    exact Iff.rfl
  have htarget : (p.N k ^ scale) ^ (-S * b) = p.N k ^ (scale * (-S * b)) := by
    rw [← Real.rpow_mul hN0.le]
  rw [hset, htarget]
  have hB1 : 1 ≤ B := le_trans (Real.one_le_rpow hN1 (by linarith)) hB
  have hpow0 : 0 ≤ p.N k ^ (scale * (-S * b)) := Real.rpow_nonneg hN0.le _
  rcases hfloor with h0 | hθ
  · -- a null world: the palette is uniform on `[0, 1)`
    have hpal : Info.velocityPalette σ = volume.restrict (Ico (0 : ℝ) 1) := by
      rw [Info.velocityPalette, if_pos (by rw [h0]; rfl)]
    rw [hpal]
    have hbin : {v : ℝ | (⌊v / w⌋ : ℤ) = e} ⊆ Icc ((e : ℝ) * w) ((e : ℝ) * w + w) := by
      intro v hv
      simp only [mem_ofPred_eq, Int.floor_eq_iff] at hv
      obtain ⟨h1, h2⟩ := hv
      rw [le_div_iff₀ hw0] at h1
      rw [div_lt_iff₀ hw0] at h2
      constructor <;> nlinarith
    have hwle : w ≤ p.N k ^ (scale * (-S * b)) := by
      apply Real.rpow_le_rpow_of_exponent_le hN1
      have : S * (scale * b) ≤ scale * b := mul_le_of_le_one_left hsb.le hS1
      nlinarith
    calc volume.restrict (Ico (0 : ℝ) 1) {v : ℝ | (⌊v / w⌋ : ℤ) = e}
        ≤ volume {v : ℝ | (⌊v / w⌋ : ℤ) = e} := Measure.restrict_le_self _
      _ ≤ volume (Icc ((e : ℝ) * w) ((e : ℝ) * w + w)) := measure_mono hbin
      _ = ENNReal.ofReal w := by rw [Real.volume_Icc]; congr 1; ring
      _ ≤ ENNReal.ofReal (B * p.N k ^ (scale * (-S * b))) := by
          apply ENNReal.ofReal_le_ofReal
          calc w ≤ p.N k ^ (scale * (-S * b)) := hwle
            _ = 1 * p.N k ^ (scale * (-S * b)) := (one_mul _).symm
            _ ≤ B * p.N k ^ (scale * (-S * b)) := mul_le_mul_of_nonneg_right hB1 hpow0
  · -- a world of mass at least `N^{-γ}`
    have hww' : w ≤ p.N k ^ (-u) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hθ' : ENNReal.ofReal (p.N k ^ (-γ)) ≤ σ Set.univ := by
      rw [Real.rpow_neg hN0.le]; exact hθ
    have hpb := palette_bin_le hp hu0 huU hσ hL hA (Real.rpow_pos_of_pos hN0 (-γ)) hθ' hw0
      hww' e
    refine hpb.trans (ENNReal.ofReal_le_ofReal ?_)
    have hSu : -p.S * u ≤ -(S * u) := by
      rw [neg_mul]; exact neg_le_neg (mul_le_mul_of_nonneg_right hSp hu0.le)
    have hgapS : S * (scale * b) - S * u ≤ ε := by
      have : S * (scale * b - u) ≤ S * ε := mul_le_mul_of_nonneg_left hgap hS0.le
      have : S * ε ≤ ε := mul_le_of_le_one_left hε0 hS1
      nlinarith
    have hneg : scale * (-S * b) = -(S * (scale * b)) := by ring
    have hexp : ε + (-p.S * u + 2 * τ - -γ) ≤ 5 * ε + scale * (-S * b) := by
      rw [hneg]; linarith
    calc 2 * p.N k ^ (-p.S * u + 2 * τ) / p.N k ^ (-γ)
        = 2 * p.N k ^ (-p.S * u + 2 * τ - -γ) := by
          rw [mul_div_assoc, Real.rpow_sub hN0]
      _ ≤ p.N k ^ ε * p.N k ^ (-p.S * u + 2 * τ - -γ) :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hN0.le _)
      _ = p.N k ^ (ε + (-p.S * u + 2 * τ - -γ)) := (Real.rpow_add hN0 _ _).symm
      _ ≤ p.N k ^ (5 * ε + scale * (-S * b)) := Real.rpow_le_rpow_of_exponent_le hN1 hexp
      _ = p.N k ^ (5 * ε) * p.N k ^ (scale * (-S * b)) := Real.rpow_add hN0 _ _
      _ ≤ B * p.N k ^ (scale * (-S * b)) := mul_le_mul_of_nonneg_right hB hpow0

/-- **The Frostman clause, unfolded**, for one world: all velocity resolutions
`b ∈ [R⁻¹, R]`, from a finite grid `us` of tested angular resolutions covering
`[scale / R, scale · R]` with gaps at most `ε`. -/
theorem frostman_canonical {p : Code} (hp : Split.Exact p) {k : ℕ} {g : Fin (p.1 k)}
    {scale S R ε τ γ B : ℝ} {us : Finset ℝ} (hscale : 0 < scale) (hS0 : 0 < S)
    (hS1 : S ≤ 1) (hSp : S ≤ p.S) (hτ0 : 0 < τ) (hτ : τ ≤ ε) (hγ : γ ≤ ε)
    (h2 : 2 ≤ p.N k ^ ε) (hB : p.N k ^ (5 * ε) ≤ B) (hR : 0 < R)
    {σ : Measure Incidence} (hσ : σ ≤ Split.mu p k g)
    (hfloor : σ = 0 ∨ ENNReal.ofReal ((p.N k ^ γ)⁻¹) ≤ σ Set.univ)
    (hL : σ (pureExc p k g p.L τ) = 0) (hus : ∀ u ∈ us, 0 < u ∧ u ≤ p.U)
    (hcover : ∀ b, R⁻¹ ≤ b → b ≤ R → ∃ u ∈ us, u ≤ scale * b ∧ scale * b - u ≤ ε)
    (hA : ∀ u ∈ us, σ (angExc p k g u τ) = 0) :
    ∀ b : ℝ, R⁻¹ ≤ b → b ≤ R → ∀ e : ℤ,
      Info.velocityPalette σ {v | velocityBin (p.N k ^ scale) b v = e} ≤
        ENNReal.ofReal (B * (p.N k ^ scale) ^ (-S * b)) := by
  intro b hb1 hb2 e
  have hb : 0 < b := lt_of_lt_of_le (inv_pos.mpr hR) hb1
  obtain ⟨u, hu, hub, hgap⟩ := hcover b hb1 hb2
  exact palette_frostman hp hscale hS0 hS1 hSp hτ0 hτ hγ h2 hB hb hσ hfloor hL
    (hus u hu).1 (hus u hu).2 (hA u hu) hub hgap e

/-- **The Frostman clause** of the canonical reference fields. -/
theorem withReference_frostman (st : RawStage) {Kb α S R ε τ γ : ℝ} {m : ℕ}
    {us : Finset ℝ} (hp : Split.Exact st.p) (hscale : 0 < st.scale) (hS0 : 0 < S)
    (hS1 : S ≤ 1) (hSp : S ≤ st.p.S) (hτ0 : 0 < τ) (hτ : τ ≤ ε) (hγ : γ ≤ ε)
    (h2 : 2 ≤ st.N₀ ^ ε) (hB : st.N₀ ^ (5 * ε) ≤ st.B) (hR : 0 < R)
    (hσ : ∀ g, st.σ g ≤ Split.mu st.p st.sample g)
    (hfloor : ∀ g, st.σ g = 0 ∨ ENNReal.ofReal ((st.N₀ ^ γ)⁻¹) ≤ st.σ g Set.univ)
    (hL : ∀ g, st.σ g (pureExc st.p st.sample g st.p.L τ) = 0)
    (hus : ∀ u ∈ us, 0 < u ∧ u ≤ st.p.U)
    (hcover : ∀ b, R⁻¹ ≤ b → b ≤ R → ∃ u ∈ us, u ≤ st.scale * b ∧ st.scale * b - u ≤ ε)
    (hA : ∀ g, ∀ u ∈ us, st.σ g (angExc st.p st.sample g u τ) = 0) :
    ∀ (g : Fin (withReference st Kb m α).W) (b : ℝ), R⁻¹ ≤ b → b ≤ R → ∀ e : ℤ,
      (withReference st Kb m α).π₀ g {v | velocityBin (withReference st Kb m α).N b v = e} ≤
        ENNReal.ofReal ((withReference st Kb m α).B *
          (withReference st Kb m α).N ^ (-S * b)) := fun g =>
  frostman_canonical hp hscale hS0 hS1 hSp hτ0 hτ hγ h2 hB hR (hσ g) (hfloor g) (hL g) hus
    hcover (hA g)

/-! ### The information budget -/

/-- The information budget of the canonical reference fields is the weighted score of the
canonical code. -/
theorem withReference_info (st : RawStage) {Kb α : ℝ} {m : ℕ}
    (h : (∑ g : Fin st.W, st.p.weight st.sample g *
        Info.rlScore (st.σ g) (Info.canonX st.N m (Info.canonM st.N Kb m))
          (Info.canonY m (Info.canonM st.N Kb m)) (Info.canonZ m (Info.canonM st.N Kb m))) ≤
      ((∑ g : Fin st.W, ENNReal.ofReal (st.p.weight st.sample g) * st.σ g Set.univ).toReal / 2) *
        Real.log (st.N ^ α)) :
    (withReference st Kb m α).InfoBudget := h

/-- The information budget from the conclusion of `Info.exists_window_info_bins` at the
selected window, whose weighted slices are the reference laws of the stage. -/
theorem info_of_window (st : RawStage) {Kb α : ℝ} {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (π : Ω → Fin st.W × Incidence) {c : ℝ} (hc : 0 ≤ c)
    (hw : ∀ g, 0 ≤ st.p.weight st.sample g) (hfin : ∀ g, IsFiniteMeasure (st.σ g))
    (hslice : ∀ g, ENNReal.ofReal (st.p.weight st.sample g) • st.σ g =
      ENNReal.ofReal c • Info.tagSlice P π g)
    (hwin : ∀ (wt : Fin st.W → ℝ), (∀ i, 0 ≤ wt i) → ∀ (c : ℝ), 0 ≤ c →
      ∀ (σ : Fin st.W → Measure Incidence), (∀ i, IsFiniteMeasure (σ i)) →
      (∀ i, ENNReal.ofReal (wt i) • σ i = ENNReal.ofReal c • Info.tagSlice P π i) →
      (∑ i, wt i * Info.rlScore (σ i) (Info.canonX st.N m (Info.canonM st.N Kb m))
          (Info.canonY m (Info.canonM st.N Kb m)) (Info.canonZ m (Info.canonM st.N Kb m))) ≤
        ((∑ i, ENNReal.ofReal (wt i) * σ i Set.univ).toReal / 2) * Real.log (st.N ^ α)) :
    (withReference st Kb m α).InfoBudget :=
  withReference_info st (hwin _ hw c hc _ hfin hslice)

/-! ### Assembly -/

/-- The reference fields do not change the geometric clauses. -/
theorem geometryGood_withReference (st : RawStage) {d κ R δ Kb α : ℝ} {k m : ℕ}
    (hgeo : st.GeometryGood d κ k R δ) : (withReference st Kb m α).GeometryGood d κ k R δ :=
  ⟨hgeo.exact, hgeo.budgets, hgeo.scale_le, hgeo.buffer_le, hgeo.actual_le, hgeo.length_gt,
    hgeo.resolution_ge, hgeo.B_ge_one, hgeo.B_le, hgeo.sigma_le, hgeo.sigma_mass,
    hgeo.layer_good, hgeo.node_round, hgeo.guard⟩

/-- **Stage assembly.** The geometric clauses of a stage (`RawStage.GeometryGood`), the
reference hypotheses of `CandidateInput`, `k + 1 ≤ m`, the bounds on `α` and the weighted
information score of the canonical code give a good stage with the canonical reference
fields. -/
theorem good_withReference (st : RawStage) {d κ S R δ Kb ε τ γ α : ℝ} {k m : ℕ}
    {us : Finset ℝ} (hgeo : st.GeometryGood d κ k R δ)
    (hin : CandidateInput st d S R Kb m ε τ γ us)
    (hm : (k : ℝ) + 1 ≤ m) (hα0 : 0 < α) (hα2 : 2 ≤ st.N ^ α) (hαδ : α ≤ δ)
    (hinfo : (∑ g : Fin st.W, st.p.weight st.sample g *
        Info.rlScore (st.σ g) (Info.canonX st.N m (Info.canonM st.N Kb m))
          (Info.canonY m (Info.canonM st.N Kb m)) (Info.canonZ m (Info.canonM st.N Kb m))) ≤
      ((∑ g : Fin st.W, ENNReal.ofReal (st.p.weight st.sample g) * st.σ g Set.univ).toReal / 2) *
        Real.log (st.N ^ α)) :
    (withReference st Kb m α).Good d κ S k R δ := by
  have hN₀1 : 1 ≤ st.N₀ := exact_N_ge_one hin.exact st.sample
  have hε0 : 0 ≤ ε := hin.tol_pos.le.trans hin.tol_le
  have hB2 : st.N₀ ^ (2 * ε) ≤ st.B :=
    (Real.rpow_le_rpow_of_exponent_le hN₀1 (by linarith)).trans hin.B_ge
  exact RawStage.Good.of_geometry (geometryGood_withReference st hgeo) hm hα0 hα2 hαδ
    (fun g => withReference_codeGood st hin.exact hin.scale_pos hin.m_pos hin.K_le
      hin.mesh_le hin.tol_le hin.profile hB2 g (hin.sigma_le g) (hin.pure_null g))
    (withReference_frostman st hin.exact hin.scale_pos hin.S_pos hin.S_le_one hin.S_le
      hin.tol_pos hin.tol_le hin.floor_le hin.two_le hin.B_ge hin.R_pos hin.sigma_le
      hin.floor hin.terminal_null hin.grid_valid hin.grid_cover hin.angular_null)
    (withReference_info st hinfo)

end

end Submission.Obl.k4_scalar_guarded_entropic_path.Reference
