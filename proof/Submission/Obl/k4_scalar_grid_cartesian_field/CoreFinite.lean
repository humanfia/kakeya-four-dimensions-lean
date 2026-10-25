-- From this LOT obligation o230, session x0803, commit fa89c812,
-- Submission/Obl/k4_scalar_grid_cartesian_field/CoreFinite.lean.
import Submission.Obl.k4_scalar_grid_cartesian_field.CorePalettes
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.TimedMeshCartesian
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.OriginalWholeBlockFields

/-!
# The packet-level Cartesian field with explicit parameters

Inputs as in `CartesianCoreStatement`, with the list budget `K`, the grid
density `η` and the anchor gap `gap` as explicit parameters. The proof chains
the witnesses (`CoreWitness`), the frame grid (`CoreFrame`, `CoreCells`), the
local palettes (`CorePalettes`), x0212's timed Cartesian mesh field
(`Cart.TimedMeshCartesian`), the frame polynomial and the whole-block rows
(`Cart.OriginalWholeBlockFields`).
-/

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open scoped Submission.Obl.k4_scalar_grid_cartesian_field

open MeasureTheory Set MvPolynomial
open scoped ENNReal

/-- The frame box size. -/
noncomputable def coreBf (Λ : ℝ) : ℝ := 2 * (Λ + 1) ^ 2 * Λ

/-- Velocity of a witness bin: bounded by the coefficient bound. -/
theorem bin_velocity_bound {δv Λ : ℝ} (hδv : 0 < δv) (hδv1 : δv ≤ 1) (p : Incidence)
    (hV : |p.1.2 1| ≤ Λ) : |(velBin δv p : ℝ) * δv| ≤ Λ + 1 := by
  have h1 : ((velBin δv p : ℤ) : ℝ) ≤ p.1.2 1 / δv := Int.floor_le _
  have h2 : p.1.2 1 / δv < (velBin δv p : ℝ) + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hδv] at h1
  rw [div_lt_iff₀ hδv] at h2
  have := abs_le.mp hV
  rw [abs_le]
  constructor <;> nlinarith

/-- Separated narrow bins give separated directions. -/
theorem bin_separation {δv δs Λ : ℝ} (hδv : 0 < δv) (hδs : 0 < δs) (hΛ : 0 < Λ)
    (hδsΛ : 1 ≤ Λ * δs) (b₀ b₁ : ℤ) (hb : ⌈δs / δv⌉ + 1 ≤ |b₀ - b₁|) :
    1 / Λ ≤ |(b₁ : ℝ) * δv - (b₀ : ℝ) * δv| := by
  have hc : δs / δv ≤ (⌈δs / δv⌉ : ℝ) := Int.le_ceil _
  have hb' : (⌈δs / δv⌉ : ℝ) + 1 ≤ |((b₀ - b₁ : ℤ) : ℝ)| := by exact_mod_cast hb
  rw [show (b₁ : ℝ) * δv - (b₀ : ℝ) * δv = -(((b₀ - b₁ : ℤ) : ℝ) * δv) by push_cast; ring,
    abs_neg, abs_mul, abs_of_pos hδv]
  have h1 : δs ≤ |((b₀ - b₁ : ℤ) : ℝ)| * δv := by
    have : δs / δv * δv ≤ (⌈δs / δv⌉ : ℝ) * δv := mul_le_mul_of_nonneg_right hc hδv.le
    rw [div_mul_cancel₀ _ hδv.ne'] at this
    nlinarith
  have h2 : 1 / Λ ≤ δs := by
    rw [div_le_iff₀ hΛ]; linarith
  linarith


set_option maxHeartbeats 8000000 in
/-- The packet-level Cartesian field with explicit list budget `K`, grid
density `η` and anchor gap `gap`. -/
theorem core_finite (M : ℕ) (hM : 1 ≤ M) :
    ∃ Cb Cm Cu Cc : ℝ, 0 < Cb ∧ 0 < Cm ∧ 0 < Cu ∧ 0 < Cc ∧
    ∀ (N Λ h a y₀ εT rT B L ξ δv δs : ℝ)
      (ρ : Measure Incidence) (θ ν : Measure Trajectory) (π : Measure ℝ)
      (E S₀ : Set Incidence) (A : Set Trajectory) (G : (Fin 3 → ℤ) → Fin 2 → ℝ)
      (K η gap : ℝ),
      2 ≤ N → 1 ≤ Λ → 0 < h → h ≤ 1 → 0 ≤ a → a + h ≤ 1 →
      εT = N ^ (-rT) → εT ≤ 1 → 0 < ξ → 0 < δv → 0 < δs →
      h ^ M ≤ εT → Λ * N ^ (-L) ≤ εT → Λ ^ 2 * N ^ (-(1 : ℝ)) ≤ εT → Λ ^ 4 * ξ ≤ εT →
      Λ ^ 2 * δv ≤ ξ → Λ ^ 4 * N ^ (-B) ≤ ξ * h → 1 ≤ Λ * δs → δs ≤ 1 →
      IsFiniteMeasure ρ → IsFiniteMeasure θ → SigmaFinite ν → IsProbabilityMeasure π →
      MeasurableSet E → MeasurableSet S₀ → MeasurableSet A →
      S₀ ⊆ E → S₀ ⊆ {p | p.1 ∈ A ∧ p.2 ∈ Icc a (a + h)} → 0 < ρ S₀ →
      ρ.restrict S₀ ≤ ENNReal.ofReal Λ • ν.prod volume →
      ENNReal.ofReal h * ν A ≤ ENNReal.ofReal Λ * ρ S₀ →
      (θ.prod volume).restrict E ≤ ENNReal.ofReal Λ • ρ.restrict E →
      ρ.restrict E ≤ ENNReal.ofReal Λ • (θ.prod volume).restrict E →
      (∀ l ∈ A, ∀ e, |l.2 e| ≤ Λ) →
      (∀ l ∈ A, ∀ t ∈ Icc a (a + h), |scalarY l t - y₀| ≤ Λ * h) →
      (∀ l ∈ A, ∀ l' ∈ A, ∀ t ∈ Icc a (a + h), ∀ t' ∈ Icc a (a + h),
        |scalarX l t - scalarX l' t'| ≤
          Λ * N ^ (-(1 : ℝ)) + Λ / h * (|t - t'| + |scalarY l t - scalarY l' t'|)) →
      (∀ p ∈ E, (∀ e, |G (physCube N B p) e| ≤ Λ) ∧
        |p.1.2 3 + 2 * p.2 * p.1.2 4 - G (physCube N B p) 0 -
          G (physCube N B p) 1 * p.1.2 1| ≤ Λ * N ^ (-L)) →
      (∀ q : Fin 3 → ℤ, ({w : Fin 2 → ℤ | ρ.restrict E
        {p | physCube N rT p = q ∧ rowBin N rT (G (physCube N B p)) = w} ≠ 0}.ncard : ℝ) ≤ Λ) →
      (∀ (q : Fin 3 → ℤ) (c : ℤ),
        16 * ρ.restrict S₀ {p | physCube N B p = q ∧ ⌊p.1.2 1 / δs⌋ = c} ≤
          ρ.restrict S₀ {p | physCube N B p = q}) →
      (∀ (q : Fin 3 → ℤ) (c : ℤ),
        ρ.restrict S₀ {p | physCube N B p = q ∧ ⌊p.1.2 1 / δv⌋ = c} ≤
          ENNReal.ofReal Λ * ρ.restrict S₀ {p | physCube N B p = q} *
            π {w | ⌊w / δv⌋ = c}) →
      (∀ p ∈ S₀, ∃ P : Fin 2 → Polynomial ℝ,
        (∀ e, (P e).natDegree ≤ M ∧ ∀ i, |(P e).coeff i| ≤ Λ) ∧
        (∀ e, |G (physCube N B p) e - (P e).eval p.2| ≤ h ^ M) ∧
        ENNReal.ofReal (h / Λ) ≤ volume {t | (p.1, t) ∈ E ∧ t ∈ Icc a (a + h) ∧
          ∀ e, |G (physCube N B (p.1, t)) e - (P e).eval t| ≤ h ^ M}) →
      (∀ c : Fin 2 → ℤ, ρ.restrict S₀
        {p | ∀ e, ⌊normalizedBase h ![a, y₀] p e / ξ⌋ = c e} ≤
          ENNReal.ofReal (Λ * ξ ^ 2) * ρ S₀) →
      1 ≤ K →
      (Cb * (max Λ ((4 * 141 + 11) ^ 3 * Λ + 2)) ^ (3 * (M + 1) + (M + 1) ^ 2 * M)) ^ 2 ≤ K →
      (4 * 141 + 11) ^ 3 * Λ ≤ K →
      0 < η → η ≤ 1 →
      η * (40 * (4 * Λ + 9) * Λ ^ 3 * K ^ 3 * (2 * coreBf Λ + 2) ^ 2) ≤ 1 →
      0 < gap → 14 * ((M : ℝ) + 2) ^ 2 * gap ≤ η ^ ((M + 2) ^ 2) / 2 → ξ ≤ gap →
      ∃ (𝒯 : Fin 2 → MvPolynomial (Fin 2) ℝ) (S₁ : Set Incidence),
        MeasurableSet S₁ ∧ S₁ ⊆ S₀ ∧
        (∀ e, (𝒯 e).totalDegree ≤ 2 * M) ∧
        (∀ e b, |(𝒯 e).coeff b| ≤
          Cc ^ 2 * ((εT + Λ) * (((M : ℝ) + 1) * (2 * (coreBf Λ + 2) / gap) ^ M) ^ 2)) ∧
        ENNReal.ofReal (η ^ ((M + 2) ^ 2) / (32 * Λ ^ 4 * K ^ 3)) * ρ S₀ ≤ ρ S₁ ∧
        ∀ p ∈ S₁, ∀ t ∈ Icc a (a + h),
          |coreResidual 𝒯 h ![a, y₀] p.1 t| ≤
            (8 * (((2 * M : ℕ) : ℝ) + 3) / (η ^ ((M + 2) ^ 2) / (32 * Λ ^ 4 * K ^ 3))) ^
              (2 * M + 2) *
            ((1 + (1 + Λ) * (1 + (2 + ((M : ℝ) + 1) * M * (Cu * (((M : ℝ) + 1) * Λ)) *
              (1 + 2 ^ (M + 1)) + 2 * ((M : ℝ) + 1) * 2 ^ M) *
              (1 + 2 * (((M : ℝ) + 1) * (2 * (coreBf Λ + 2) / gap) ^ M) +
                (((M : ℝ) + 1) * (2 * (coreBf Λ + 2) / gap) ^ M) ^ 2) +
              2 * Cm * (1 + Λ) * (((M : ℝ) + 1) * (2 * (coreBf Λ + 2) / gap) ^ M) ^ 2)) * εT) := by
  classical
  obtain ⟨Cb, hCb, hfiber⟩ := exists_fiber_lists M
  obtain ⟨Cm, hCm, hmesh⟩ := Cart.exists_timed_mesh_cartesian_field_constant M
  obtain ⟨Cu, hCu, hnorm⟩ := exists_normPoly_coeff_constant M
  obtain ⟨Cc, hCc, hcoef⟩ := Cart.Switching.exists_multivariate_coefficient_constant (2 * M)
  refine ⟨Cb, Cm, Cu, Cc, hCb, hCm, hCu, hCc, ?_⟩
  intro N Λ h a y₀ εT rT B L ξ δv δs ρ θ ν π E S₀ A G K η gap
    hN hΛ hh hh1 ha hah hεT hε1 hξ hδv hδs hfitp hgraphp hlayer hcellsmall hδvξ hfine hδs1 hδs2
    hρfin hθfin hνsf hπ hEm hS₀m hAm hS₀E hS₀A hρpos hdens hmassA hθρ hρθ hcoefA hconf hlip
    hgraph hlists hbreadth hpal hqual hbase hK1 hKrow hKcell hη hη1 hηdef hgap hloss hξgap
  -- basic facts
  have hN0 : 0 < N := by linarith
  have hεpos : 0 < εT := hεT ▸ Real.rpow_pos_of_pos hN0 _
  have hΛ0 : 0 < Λ := by linarith
  have hρS₀fin : ρ S₀ ≠ ⊤ := measure_ne_top ρ S₀
  set ρ₀ := (ρ S₀).toReal with hρ₀def
  have hρ₀ : 0 < ρ₀ := ENNReal.toReal_pos hρpos.ne' hρS₀fin
  have hρS₀eq : ρ S₀ = ENNReal.ofReal ρ₀ := (ENNReal.ofReal_toReal hρS₀fin).symm
  have hΛ14 : Λ ≤ Λ ^ 4 := by
    calc Λ = Λ ^ 1 := (pow_one Λ).symm
      _ ≤ Λ ^ 4 := pow_le_pow_right₀ hΛ (by norm_num)
  have hξε : ξ ≤ εT := by
    have : ξ ≤ Λ ^ 4 * ξ := le_mul_of_one_le_left hξ.le (one_le_pow₀ hΛ)
    linarith
  have hgap1 : gap ≤ 1 / 28 := by
    have hη2 : η ^ ((M + 2) ^ 2) ≤ 1 := pow_le_one₀ hη.le hη1
    have h0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have hM2 : (1 : ℝ) ≤ ((M : ℝ) + 2) ^ 2 := one_le_pow₀ (by linarith)
    have h3 : 14 * ((M : ℝ) + 2) ^ 2 * gap ≤ 1 / 2 := hloss.trans (by linarith)
    have h4 : 14 * 1 * gap ≤ 14 * ((M : ℝ) + 2) ^ 2 * gap := by
      apply mul_le_mul_of_nonneg_right _ hgap.le
      linarith
    linarith
  have hξ1 : ξ ≤ 1 / 28 := hξgap.trans hgap1
  have hδv1 : δv ≤ 1 := by
    have : δv ≤ Λ ^ 2 * δv := le_mul_of_one_le_left hδv.le (one_le_pow₀ hΛ)
    linarith
  have hvs : 2 * δv ≤ δs := by
    have h1 : 1 / Λ ≤ δs := by rw [div_le_iff₀ hΛ0]; linarith
    have h2 : Λ ^ 2 * δv ≤ 1 / 28 := hδvξ.trans hξ1
    have hΛΛ : Λ ≤ Λ ^ 2 := by
      calc Λ = Λ ^ 1 := (pow_one Λ).symm
        _ ≤ Λ ^ 2 := pow_le_pow_right₀ hΛ (by norm_num)
    have h3 : 2 * δv * Λ ≤ 1 := by
      have : δv * Λ ≤ δv * Λ ^ 2 := mul_le_mul_of_nonneg_left hΛΛ hδv.le
      have e : δv * Λ ^ 2 = Λ ^ 2 * δv := by ring
      linarith
    calc 2 * δv = 2 * δv * Λ / Λ := by field_simp
      _ ≤ 1 / Λ := by apply div_le_div_of_nonneg_right h3 hΛ0.le
      _ ≤ δs := h1
  -- Step 1: witnesses in two separated narrow velocity bins
  obtain ⟨b, A₁, wit, hbsep, hA₁m, hA₁S₀, hA₁mass, hA₁null, hwit⟩ :=
    exists_core_witnesses ρ θ π E S₀ hEm hS₀m hS₀E N B rT δv δs Λ hΛ hδv hδs hvs hθρ hρθ
      hbreadth hpal hρpos.ne'
  have hA₁pos : 0 < ρ A₁ := by
    refine lt_of_lt_of_le ?_ hA₁mass
    exact ENNReal.mul_pos (by simp; positivity) hρpos.ne'
  obtain ⟨ω₀, hω₀⟩ := nonempty_of_measure_ne_zero hA₁pos.ne'
  set v₁ := (b 0 : ℝ) * δv with hv₁def
  set v₂ := (b 1 : ℝ) * δv with hv₂def
  have hvbound : ∀ i : Fin 2, |(b i : ℝ) * δv| ≤ Λ + 1 := by
    intro i
    obtain ⟨hwS, _, hwb, _⟩ := hwit ω₀ hω₀ i
    have hV := hcoefA _ (hS₀A hwS).1 1
    have := bin_velocity_bound hδv hδv1 (wit i (physCube N B ω₀)) hV
    rwa [hwb] at this
  have hv₁ : |v₁| ≤ Λ + 1 := hvbound 0
  have hv₂ : |v₂| ≤ Λ + 1 := hvbound 1
  have hsep : 1 / Λ ≤ |v₂ - v₁| := bin_separation hδv hδs hΛ0 hδs1 (b 0) (b 1) hbsep
  have hsep' : 1 / Λ ≤ |v₁ - v₂| := by rwa [abs_sub_comm]
  have hsepne : v₂ ≠ v₁ := by
    intro he; rw [he, sub_self, abs_zero] at hsep; exact absurd hsep (not_le.mpr (by positivity))
  -- Step 2: witness polynomials
  set Pfun : Incidence → Fin 2 → Polynomial ℝ := fun p =>
    if hp : p ∈ S₀ then (hqual p hp).choose else 0 with hPfun_def
  have hPfun : ∀ p ∈ S₀, (∀ e, (Pfun p e).natDegree ≤ M ∧ ∀ i, |(Pfun p e).coeff i| ≤ Λ) ∧
      (∀ e, |G (physCube N B p) e - (Pfun p e).eval p.2| ≤ h ^ M) ∧
      ENNReal.ofReal (h / Λ) ≤ volume {t | (p.1, t) ∈ E ∧ t ∈ Icc a (a + h) ∧
        ∀ e, |G (physCube N B (p.1, t)) e - (Pfun p e).eval t| ≤ h ^ M} := by
    intro p hp
    simp only [hPfun_def, dif_pos hp]
    exact (hqual p hp).choose_spec
  set Pw : Fin 2 → (Fin 3 → ℤ) → Fin 2 → Polynomial ℝ := fun i q => Pfun (wit i q) with hPw_def
  set Hp := Cu * (((M : ℝ) + 1) * Λ) with hHp_def
  have hHp0 : 0 ≤ Hp := by positivity
  have hPwdata : ∀ ω ∈ A₁, ∀ i : Fin 2, (∀ e, (Pw i (physCube N B ω) e).natDegree ≤ M) ∧
      (∀ e k, |(normPoly a h (Pw i (physCube N B ω) e)).coeff k| ≤ Hp) ∧
      ENNReal.ofReal (h / Λ) ≤ volume {t | ((wit i (physCube N B ω)).1, t) ∈ E ∧
        t ∈ Icc a (a + h) ∧ ∀ e, |G (physCube N B ((wit i (physCube N B ω)).1, t)) e -
          (Pw i (physCube N B ω) e).eval t| ≤ h ^ M} := by
    intro ω hω i
    obtain ⟨hwS, _, _, _⟩ := hwit ω hω i
    obtain ⟨hdeg, _, hrow⟩ := hPfun _ hwS
    refine ⟨fun e => (hdeg e).1, fun e k => ?_, hrow⟩
    exact hnorm _ (hdeg e).1 Λ hΛ0.le (hdeg e).2 a h ha hh.le hah k
  -- Step 3: the frame box
  set Bf := coreBf Λ with hBf_def
  have hBf1 : 1 ≤ Bf := by
    simp only [hBf_def, coreBf]
    have h1 : 1 ≤ (Λ + 1) ^ 2 := one_le_pow₀ (by linarith)
    calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
      _ ≤ 2 * (Λ + 1) ^ 2 * Λ := by
          apply mul_le_mul (mul_le_mul (by norm_num) h1 (by norm_num) (by norm_num)) hΛ
            (by norm_num) (by positivity)
  have hbaseS₀ : ∀ p ∈ S₀, |coreBase h a y₀ p 0| ≤ Λ ∧ |coreBase h a y₀ p 1| ≤ Λ := by
    intro p hp
    obtain ⟨hpA, hpI⟩ := hS₀A hp
    constructor
    · rw [coreBase_zero, abs_div, abs_of_pos hh, div_le_iff₀ hh,
        abs_of_nonneg (by linarith [hpI.1])]
      have : h ≤ Λ * h := le_mul_of_one_le_left hh.le hΛ
      linarith [hpI.2]
    · rw [coreBase_one, abs_div, abs_of_pos hh, div_le_iff₀ hh]
      exact hconf p.1 hpA p.2 hpI
  have hsepf : 1 / (Λ + 1) ≤ |v₂ - v₁| :=
    le_trans (one_div_le_one_div_of_le hΛ0 (by linarith)) hsep
  have hboxS₀ : ∀ p ∈ S₀, ∀ i, |frameOf v₁ v₂ (coreBase h a y₀ p) i| ≤ Bf := by
    intro p hp i
    have h1 := frameOf_bound (K := Λ + 1) (R := Λ) (by linarith) hΛ0.le hv₁ hv₂ hsepf
      (coreBase h a y₀ p) (hbaseS₀ p hp).1 (hbaseS₀ p hp).2 i
    simpa [hBf_def, coreBf] using h1
  have hboxS₀' : ∀ p ∈ S₀, |frameOf v₂ v₁ (coreBase h a y₀ p) 1| ≤ Bf := by
    intro p hp
    rw [frameOf_swap]
    exact hboxS₀ p hp 0
  -- Step 4: the lists
  obtain ⟨Lco, hLco, hLcomem⟩ := exists_coarse_lists ρ E hEm G N rT B Λ (hεT ▸ hεpos)
    (fun p hp e => (hgraph p hp).1 e) hlists
  have hknown₀ : ∀ p ∈ A₁, rowBin N rT (G (physCube N B p)) ∈ Lco (physCube N rT p) := by
    intro p hp
    apply hLcomem
    have := hA₁null p hp
    simpa [nullCodeSet] using this
  have hA₁AI : ∀ p ∈ A₁, p.1 ∈ A ∧ p.2 ∈ Icc a (a + h) := fun p hp => hS₀A (hA₁S₀ hp)
  obtain ⟨L₀, hL₀card, hL₀mem⟩ := exists_cell_palettes A₁ G N B rT εT Λ h a y₀ v₁ v₂ Bf ξ A
    hN0 hεT hεpos hΛ hh hh1 hξ hsepne hv₁ hv₂ hlayer hcellsmall hA₁AI hlip
    (fun p hp => hboxS₀ p (hA₁S₀ hp)) Lco hLco hknown₀
  have hwitdata : ∀ i : Fin 2, ∀ p ∈ A₁, (wit i (physCube N B p)).1 ∈ A ∧
      (wit i (physCube N B p)).2 ∈ Icc a (a + h) ∧
      physCube N B (wit i (physCube N B p)) = physCube N B p ∧
      velBin δv (wit i (physCube N B p)) = b i ∧
      (wit i (physCube N B p)).1 ∉ badLines ρ E (coreCode N B rT) := by
    intro i p hp
    obtain ⟨hwS, hwq, hwb, hwbad⟩ := hwit p hp i
    exact ⟨(hS₀A hwS).1, (hS₀A hwS).2, hwq, hwb, hwbad⟩
  obtain ⟨Lr, hLrcard, hLrmem⟩ := hfiber ρ E A₁ hEm G N B rT εT Λ h a y₀ v₁ v₂ δv Bf ξ Hp A
    (b 0) (wit 0) (Pw 0) hN0 hεT hεpos hΛ hh hh1 hξ hδv hHp0 hsep hv₁ hv₂ rfl hlayer
    hcellsmall hδvξ hfine hfitp hA₁AI hlip (fun p hp => hboxS₀ p (hA₁S₀ hp) 1)
    (hwitdata 0) (fun p hp => hPwdata p hp 0) Lco hLco hLcomem
  obtain ⟨Lc, hLccard, hLcmem⟩ := hfiber ρ E A₁ hEm G N B rT εT Λ h a y₀ v₂ v₁ δv Bf ξ Hp A
    (b 1) (wit 1) (Pw 1) hN0 hεT hεpos hΛ hh hh1 hξ hδv hHp0 hsep' hv₂ hv₁ rfl hlayer
    hcellsmall hδvξ hfine hfitp hA₁AI hlip (fun p hp => hboxS₀' p (hA₁S₀ hp))
    (hwitdata 1) (fun p hp => hPwdata p hp 1) Lco hLco hLcomem
  -- Step 5: the timed Cartesian mesh field
  have hn0 : (0 : ℝ) < (gridSize Bf ξ : ℝ) := by exact_mod_cast Nat.pos_of_neZero (gridSize Bf ξ)
  have hnξ : (gridSize Bf ξ : ℝ) * ξ ≤ 2 * Bf + 2 := by
    have := gridSize_le hξ (by linarith : 0 ≤ Bf)
    have h1 : (gridSize Bf ξ : ℝ) * ξ ≤ (2 * Bf / ξ + 2) * ξ := mul_le_mul_of_nonneg_right this hξ.le
    rw [add_mul, div_mul_cancel₀ _ hξ.ne'] at h1
    linarith
  set m := ρ₀ / (4 * Λ ^ 2) with hm_def
  have hm0 : 0 < m := by positivity
  set Mcap := 5 * (4 * Λ + 9) * (Λ * ξ ^ 2) * ρ₀ with hMcap_def
  have hMcap0 : 0 < Mcap := by positivity
  set θl := m / (2 * K ^ 3 * ((gridSize Bf ξ : ℝ) * (gridSize Bf ξ : ℝ))) with hθl_def
  have hθl0 : 0 < θl := by positivity
  set δ₁ := N ^ (-B) / h with hδ₁_def
  have hδ₁ : δ₁ ≤ ξ := by
    have h1 : N ^ (-B) ≤ ξ * h := le_trans (le_mul_of_one_le_left
      (Real.rpow_nonneg hN0.le _) (one_le_pow₀ hΛ)) hfine
    rw [hδ₁_def, div_le_iff₀ hh]; exact h1
  set ρfit := h ^ M + ((M : ℝ) + 1) * M * Hp * 1 ^ M * δ₁ with hρfit_def
  have hρfit0 : 0 ≤ ρfit := by positivity
  have hinj : Function.Injective (gridPos Bf ξ) := by
    intro i j hij
    simp only [gridPos] at hij
    have : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by
      have := mul_left_cancel₀ hξ.ne' (by linarith : ξ * ((i : ℕ) : ℝ) = ξ * ((j : ℕ) : ℝ))
      exact this
    exact Fin.ext (by exact_mod_cast this)
  have hgridB : ∀ i, |gridPos Bf ξ i| ≤ Bf + 2 := by
    intro i
    have := gridPos_abs_le hξ (by linarith : 0 ≤ Bf) i
    linarith
  have hcellspec : ∀ ω ∈ A₁,
      (gridPos Bf ξ (coreCell h a y₀ v₁ v₂ Bf ξ ω).1 ≤ frameOf v₁ v₂ (coreBase h a y₀ ω) 0 ∧
        frameOf v₁ v₂ (coreBase h a y₀ ω) 0 < gridPos Bf ξ (coreCell h a y₀ v₁ v₂ Bf ξ ω).1 + ξ) ∧
      (gridPos Bf ξ (coreCell h a y₀ v₁ v₂ Bf ξ ω).2 ≤ frameOf v₁ v₂ (coreBase h a y₀ ω) 1 ∧
        frameOf v₁ v₂ (coreBase h a y₀ ω) 1 < gridPos Bf ξ (coreCell h a y₀ v₁ v₂ Bf ξ ω).2 + ξ) :=
    fun ω hω => coreCell_spec hξ ω (hboxS₀ ω (hA₁S₀ hω))
  have htimeω : ∀ ω ∈ A₁, coreBase h a y₀ ω 0 ∈ Icc (0 : ℝ) 1 := by
    intro ω hω
    have hI := (hA₁AI ω hω).2
    rw [coreBase_zero]
    constructor
    · exact div_nonneg (by linarith [hI.1]) hh.le
    · rw [div_le_one hh]; linarith [hI.2]
  have hcelltime : ∀ ω ∈ A₁, |coreBase h a y₀ ω 0 -
      (0 + gridPos Bf ξ (coreCell h a y₀ v₁ v₂ Bf ξ ω).1 + gridPos Bf ξ (coreCell h a y₀ v₁ v₂ Bf ξ ω).2)| ≤ 2 * ξ := by
    intro ω hω
    have hs := hcellspec ω hω
    have ht := frameOf_time hsepne (coreBase h a y₀ ω)
    rw [abs_le]; constructor <;> linarith [hs.1.1, hs.1.2, hs.2.1, hs.2.2]
  -- the qualification fit transported to the incidence's own time
  have hfitω : ∀ i : Fin 2, ∀ ω ∈ A₁, ∀ e : Fin 2,
      |G (physCube N B ω) e - (normPoly a h (Pw i (physCube N B ω) e)).eval
        (coreBase h a y₀ ω 0)| ≤ ρfit := by
    intro i ω hω e
    obtain ⟨hwS, hwq, _, _⟩ := hwit ω hω i
    set w := wit i (physCube N B ω)
    obtain ⟨hdeg, hfit, _⟩ := hPfun w hwS
    obtain ⟨_, hcoefn, _⟩ := hPwdata ω hω i
    have hfitw : |G (physCube N B ω) e -
        (normPoly a h (Pw i (physCube N B ω) e)).eval (coreBase h a y₀ w 0)| ≤ h ^ M := by
      rw [eval_normPoly, coreBase_zero]
      have : a + h * ((w.2 - a) / h) = w.2 := by field_simp; ring
      rw [this]
      have h1 := hfit e
      rw [hwq] at h1
      exact h1
    have hτw : coreBase h a y₀ w 0 ∈ Icc (0 : ℝ) 1 := by
      have hI := (hS₀A hwS).2
      rw [coreBase_zero]
      constructor
      · exact div_nonneg (by linarith [hI.1]) hh.le
      · rw [div_le_one hh]; linarith [hI.2]
    have hτω := htimeω ω hω
    have hclose := (coreBase_close (a := a) (y₀ := y₀)
      (Real.rpow_pos_of_pos hN0 (-B)) hh hwq).1
    exact Cart.polynomial_fit_at_nearby_time M _ (natDegree_normPoly_le a h _ M (hdeg e).1)
      Hp 1 hHp0 le_rfl (fun k _ => hcoefn e k) _ _ _ (h ^ M) δ₁
      (by rw [abs_of_nonneg hτw.1]; exact hτw.2) (by rw [abs_of_nonneg hτω.1]; exact hτω.2)
      hfitw hclose
  have hmeasstate : ∀ (β : Type) (f : (Fin 3 → ℤ) → β) (c : β),
      MeasurableSet {ω : Incidence | f (physCube N B ω) = c} := by
    intro β f c
    exact (measurable_physCube N B) (Set.to_countable {q | f q = c}).measurableSet
  obtain ⟨P, S, hPdeg, hPnorm, hSm, hSA₁, hSmass, hSfit⟩ := hmesh (ι := Fin 2) ρ A₁ hA₁m (coreCell h a y₀ v₁ v₂ Bf ξ)
    (fun c => measurable_coreCell h a y₀ v₁ v₂ Bf ξ (measurableSet_singleton c))
    (gridPos Bf ξ) (gridPos Bf ξ) hinj hinj
    (Bf + 2) 2 0 gap (7 * gap) (7 * gap) η εT ρfit Λ Hp K θl m Mcap (2 * ξ) (2 * ξ)
    (by linarith) (by norm_num) hgap (by positivity) (by positivity) hη hεpos hρfit0 hΛ0.le
    hHp0 hK1 hθl0 hm0 hMcap0 (by positivity) hgridB hgridB
    (by
      rw [hm_def]
      calc ENNReal.ofReal (ρ₀ / (4 * Λ ^ 2)) = ENNReal.ofReal (1 / (4 * Λ ^ 2)) * ρ S₀ := by
            rw [hρS₀eq, ← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
        _ ≤ ρ A₁ := hA₁mass)
    (fun c => cell_cap ρ S₀ A₁ hS₀m hA₁S₀ h a y₀ v₁ v₂ Λ ξ Bf hξ hΛ hsepne hv₁ hv₂
      (fun p hp => hboxS₀ p (hA₁S₀ hp)) hbase hρS₀fin c)
    (by
      simp only [Fintype.card_fin]
      rw [hθl_def]
      apply le_of_eq
      field_simp)
    (by
      simp only [Fintype.card_fin]
      have hsq : ((gridSize Bf ξ : ℝ) * ξ) ^ 2 ≤ (2 * Bf + 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hnξ 2
      calc 2 * Mcap * ((gridSize Bf ξ : ℝ) * (gridSize Bf ξ : ℝ)) * η
          = 10 * (4 * Λ + 9) * Λ * ρ₀ * ((gridSize Bf ξ : ℝ) * ξ) ^ 2 * η := by
            rw [hMcap_def]; ring
        _ ≤ 10 * (4 * Λ + 9) * Λ * ρ₀ * (2 * Bf + 2) ^ 2 * η := by gcongr
        _ = ρ₀ / (4 * Λ ^ 2 * K ^ 3) *
            (η * (40 * (4 * Λ + 9) * Λ ^ 3 * K ^ 3 * (2 * Bf + 2) ^ 2)) := by
            field_simp; ring
        _ ≤ ρ₀ / (4 * Λ ^ 2 * K ^ 3) * 1 := by gcongr
        _ = m / K ^ 3 := by rw [hm_def]; field_simp)
    (fun z => by
      have := Cart.regular_grid_pencil_small (gridSize Bf ξ) (-Bf) ξ gap z hξ hgap.le
        (gridSize_span hξ hBf1) hξgap
      convert this using 3 with x
      simp only [gridPos]
      by_cases hP : |-Bf + ξ * ((x : ℕ) : ℝ) - z| < gap <;> simp [hP])
    (fun z => by
      have := Cart.regular_grid_pencil_small (gridSize Bf ξ) (-Bf) ξ gap z hξ hgap.le
        (gridSize_span hξ hBf1) hξgap
      convert this using 3 with x
      simp only [gridPos]
      by_cases hP : |-Bf + ξ * ((x : ℕ) : ℝ) - z| < gap <;> simp [hP])
    (by linarith)
    (fun i ω => G (physCube N B ω) i)
    (fun i ω => normPoly a h (Pw 0 (physCube N B ω) i))
    (fun i ω => normPoly a h (Pw 1 (physCube N B ω) i))
    (fun ω => coreBase h a y₀ ω 0)
    (fun ω => frameOf v₁ v₂ (coreBase h a y₀ ω))
    (fun ω hω => by
      have h1 := hcelltime ω hω
      have h2 := htimeω ω hω
      rw [abs_le] at h1 ⊢
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2])
    (fun ω hω => by
      have h2 := htimeω ω hω
      rw [abs_le]; constructor <;> linarith [h2.1, h2.2])
    hcelltime
    (fun ω hω => by
      constructor <;> intro j <;> fin_cases j <;>
        · have := hboxS₀ ω (hA₁S₀ hω)
          first
          | exact (by have h0 := abs_le.mp (this 0); simp only [Fin.zero_eta, Fin.isValue]; linarith)
          | exact (by have h1 := abs_le.mp (this 1); simp only [Fin.mk_one, Fin.isValue]; linarith))
    (fun ω hω => by
      have hs := hcellspec ω hω
      have h0 : |frameOf v₁ v₂ (coreBase h a y₀ ω) 0 - gridPos Bf ξ (coreCell h a y₀ v₁ v₂ Bf ξ ω).1| ≤ ξ := by
        rw [abs_le]; constructor <;> linarith [hs.1.1, hs.1.2]
      have h1 : |frameOf v₁ v₂ (coreBase h a y₀ ω) 1 - gridPos Bf ξ (coreCell h a y₀ v₁ v₂ Bf ξ ω).2| ≤ ξ := by
        rw [abs_le]; constructor <;> linarith [hs.2.1, hs.2.2]
      linarith)
    (fun i ω hω => (hgraph ω (hS₀E (hA₁S₀ hω))).1 i)
    (fun i ω hω => natDegree_normPoly_le a h _ M ((hPwdata ω hω 0).1 i))
    (fun i ω hω => natDegree_normPoly_le a h _ M ((hPwdata ω hω 1).1 i))
    (fun i ω hω k _ => (hPwdata ω hω 0).2.1 i k)
    (fun i ω hω k _ => (hPwdata ω hω 1).2.1 i k)
    (fun i ω hω => hfitω 0 ω hω i)
    (fun i ω hω => hfitω 1 ω hω i)
    (fun j => hmeasstate _ (fun q i => ⌊G q i / εT⌋) j)
    (fun c => hmeasstate _ (fun q i (k : Fin (M + 1)) =>
      ⌊(normPoly a h (Pw 0 q i)).coeff k / εT⌋) c)
    (fun c => hmeasstate _ (fun q i (k : Fin (M + 1)) =>
      ⌊(normPoly a h (Pw 1 q i)).coeff k / εT⌋) c)
    L₀ Lr (fun x => Lc x)
    (fun c => (hL₀card c).trans hKcell)
    (fun y => (hLrcard y).trans hKrow)
    (fun x => (hLccard x).trans hKrow)
    (fun ω hω => by
      have := hL₀mem ω hω
      rw [hεT]
      exact this)
    (fun ω hω => hLrmem ω hω)
    (fun ω hω => by
      have := hLcmem ω hω
      rw [frameOf_swap] at this
      exact this)
  -- Step 6: the field in normalized base coordinates
  set W := ((M : ℝ) + 1) * (2 * (Bf + 2) / gap) ^ M with hW_def
  have hW0 : 0 ≤ W := by positivity
  set 𝒯 : Fin 2 → MvPolynomial (Fin 2) ℝ := fun e =>
    Cart.cartesianFramePolynomial 0 0 v₁ v₂ (P e) with h𝒯_def
  have h𝒯eval : ∀ (z : Fin 2 → ℝ) (e : Fin 2),
      MvPolynomial.eval z (𝒯 e) = MvPolynomial.eval (frameOf v₁ v₂ z) (P e) := by
    intro z e
    have hz : z = ![z 0, z 1] := by funext j; fin_cases j <;> rfl
    rw [hz, h𝒯_def]
    simp only
    rw [Cart.eval_cartesianFramePolynomial]
    rfl
  have h𝒯deg : ∀ e, (𝒯 e).totalDegree ≤ 2 * M := fun e =>
    (Cart.cartesianFramePolynomial_degree 0 0 v₁ v₂ (P e)).trans (hPdeg e)
  have hPnorm' : ∀ e (z : Fin 2 → ℝ), |z 0| ≤ Bf + 2 → |z 1| ≤ Bf + 2 →
      |MvPolynomial.eval z (P e)| ≤ (εT + Λ) * W ^ 2 := by
    intro e z hz0 hz1
    have hz : z = ![z 0, z 1] := by funext j; fin_cases j <;> rfl
    rw [hz]
    exact hPnorm e (z 0) (z 1) hz0 hz1
  have h𝒯coef : ∀ e b, |(𝒯 e).coeff b| ≤ Cc ^ 2 * ((εT + Λ) * W ^ 2) := by
    intro e b
    apply hcoef 2 (𝒯 e) (h𝒯deg e) _ (by positivity)
    intro z hz
    rw [h𝒯eval]
    have hzi : ∀ i, |z i| ≤ 1 := fun i => by
      have h0 : (0 : ℝ) ≤ z i := hz.1 i
      have h1 : z i ≤ 1 := hz.2 i
      rw [abs_le]; constructor <;> linarith
    have hfb : ∀ i, |frameOf v₁ v₂ z i| ≤ Bf + 2 := by
      intro i
      have h1 := frameOf_bound (K := Λ + 1) (R := 1) (by linarith) zero_le_one hv₁ hv₂ hsepf z
        (hzi 0) (hzi 1) i
      have h2 : 2 * (Λ + 1) ^ 2 * 1 ≤ Bf := by
        simp only [hBf_def, coreBf]
        exact mul_le_mul_of_nonneg_left hΛ (by positivity)
      linarith
    exact hPnorm' e _ (hfb 0) (hfb 1)
  -- the mesh error is a multiple of `εT`
  set Ec := 2 + ((M : ℝ) + 1) * M * Hp * (1 + 2 ^ (M + 1)) + 2 * ((M : ℝ) + 1) * 2 ^ M
    with hEc_def
  set E1c := 1 + Ec * (1 + 2 * W + W ^ 2) + 2 * Cm * (1 + Λ) * W ^ 2 with hE1c_def
  have hhM : h ^ M ≤ εT := hfitp
  have hρfitε : ρfit ≤ εT + ((M : ℝ) + 1) * M * Hp * εT := by
    rw [hρfit_def, one_pow, mul_one]
    have : ((M : ℝ) + 1) * M * Hp * δ₁ ≤ ((M : ℝ) + 1) * M * Hp * εT :=
      mul_le_mul_of_nonneg_left (hδ₁.trans hξε) (by positivity)
    linarith
  have hfitS : ∀ p ∈ S, ∀ e, |G (physCube N B p) e -
      MvPolynomial.eval (coreBase h a y₀ p) (𝒯 e)| ≤ E1c * εT := by
    intro p hp e
    rw [h𝒯eval]
    refine (hSfit p hp e).trans ?_
    have hξ2 : 2 * ξ ≤ 2 * εT := by linarith
    have hRho : ρfit + ((M : ℝ) + 1) * (M : ℝ) * Hp * 2 ^ M * (2 * ξ) ≤
        εT + ((M : ℝ) + 1) * M * Hp * εT + ((M : ℝ) + 1) * M * Hp * 2 ^ (M + 1) * εT := by
      have : ((M : ℝ) + 1) * (M : ℝ) * Hp * 2 ^ M * (2 * ξ) ≤
          ((M : ℝ) + 1) * M * Hp * 2 ^ (M + 1) * εT := by
        rw [pow_succ]
        have h1 : 0 ≤ ((M : ℝ) + 1) * (M : ℝ) * Hp * 2 ^ M := by positivity
        have h2 := mul_le_mul_of_nonneg_left hξ2 h1
        have e1 : ((M : ℝ) + 1) * (M : ℝ) * Hp * 2 ^ M * (2 * εT) =
            ((M : ℝ) + 1) * M * Hp * (2 ^ M * 2) * εT := by ring
        linarith
      linarith
    have hErr : εT + (ρfit + ((M : ℝ) + 1) * (M : ℝ) * Hp * 2 ^ M * (2 * ξ)) +
        2 * ((M : ℝ) + 1) * εT * 2 ^ M ≤ Ec * εT := by
      have e1 : Ec * εT = εT + εT + ((M : ℝ) + 1) * M * Hp * εT +
          ((M : ℝ) + 1) * M * Hp * 2 ^ (M + 1) * εT + 2 * ((M : ℝ) + 1) * εT * 2 ^ M := by
        rw [hEc_def]; ring
      rw [e1]
      linarith
    have hW1 : 0 ≤ 1 + 2 * W + W ^ 2 := by positivity
    have hlast : Cm * ((εT + Λ) * W ^ 2) * (2 * ξ) ≤ 2 * Cm * (1 + Λ) * W ^ 2 * εT := by
      have h1 : εT + Λ ≤ 1 + Λ := by linarith
      have h2 : (εT + Λ) * W ^ 2 ≤ (1 + Λ) * W ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have h3 : Cm * ((εT + Λ) * W ^ 2) ≤ Cm * ((1 + Λ) * W ^ 2) :=
        mul_le_mul_of_nonneg_left h2 hCm.le
      have h4 : Cm * ((εT + Λ) * W ^ 2) * (2 * ξ) ≤ Cm * ((1 + Λ) * W ^ 2) * (2 * εT) :=
        mul_le_mul h3 hξ2 (by positivity) (by positivity)
      linarith
    have hmid := mul_le_mul_of_nonneg_right hErr hW1
    rw [hE1c_def]
    have e1 : (1 + Ec * (1 + 2 * W + W ^ 2) + 2 * Cm * (1 + Λ) * W ^ 2) * εT =
        εT + Ec * εT * (1 + 2 * W + W ^ 2) + 2 * Cm * (1 + Λ) * W ^ 2 * εT := by ring
    rw [e1]
    linarith
  -- Step 7: whole-block rows
  have hνA : ν A ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top (by simpa using hh)] at hmassA
    exact absurd hmassA (not_le.mpr (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_top_iff_ne_top.mpr hρS₀fin)))
  haveI : IsFiniteMeasure (ν.restrict A) := isFiniteMeasure_restrict.mpr hνA
  set νA := (ν A).toReal with hνA_def
  have hνAeq : ν A = ENNReal.ofReal νA := (ENNReal.ofReal_toReal hνA).symm
  have hνA0 : 0 ≤ νA := ENNReal.toReal_nonneg
  -- real form of the packet mass comparisons
  have hmassR : h * νA ≤ Λ * ρ₀ := by
    have h1 := hmassA
    rw [hνAeq, hρS₀eq, ← ENNReal.ofReal_mul hh.le, ← ENNReal.ofReal_mul hΛ0.le,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    exact h1
  have hS₀AI : S₀ ⊆ A ×ˢ Icc a (a + h) := fun p hp => ⟨(hS₀A hp).1, (hS₀A hp).2⟩
  have hρ₀le : ρ₀ ≤ Λ * (νA * h) := by
    have h1 : ρ S₀ ≤ ENNReal.ofReal Λ * (ν.prod volume) (A ×ˢ Icc a (a + h)) := by
      have := hdens (A ×ˢ Icc a (a + h))
      rw [Measure.restrict_apply (hAm.prod measurableSet_Icc),
        Set.inter_eq_right.mpr hS₀AI, Measure.smul_apply, smul_eq_mul] at this
      exact this
    rw [Measure.prod_prod, Real.volume_Icc, show a + h - a = h by ring, hνAeq, hρS₀eq,
      ← ENNReal.ofReal_mul hνA0, ← ENNReal.ofReal_mul hΛ0.le,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    exact h1
  have hdom : ρ.restrict S₀ ≤ ENNReal.ofReal Λ • (ν.restrict A).prod volume := by
    have hS₀sub : S₀ ⊆ A ×ˢ (univ : Set ℝ) := fun p hp => ⟨(hS₀A hp).1, trivial⟩
    calc ρ.restrict S₀ = (ρ.restrict S₀).restrict (A ×ˢ (univ : Set ℝ)) := by
          rw [Measure.restrict_restrict (hAm.prod MeasurableSet.univ),
            Set.inter_eq_right.mpr hS₀sub]
      _ ≤ (ENNReal.ofReal Λ • ν.prod volume).restrict (A ×ˢ (univ : Set ℝ)) :=
          Measure.restrict_mono le_rfl hdens
      _ = ENNReal.ofReal Λ • (ν.prod volume).restrict (A ×ˢ (univ : Set ℝ)) :=
          Measure.restrict_smul _ _ _
      _ = ENNReal.ofReal Λ • (ν.restrict A).prod volume := by
          rw [← Measure.prod_restrict, Measure.restrict_univ]
  set ηr := η ^ ((M + 2) ^ 2) / (32 * Λ ^ 4 * K ^ 3) with hηr_def
  set m₂ := h * η ^ ((M + 2) ^ 2) / (16 * Λ ^ 3 * K ^ 3) with hm₂_def
  have hηr0 : 0 < ηr := by positivity
  have hηr1 : ηr ≤ 1 := by
    rw [hηr_def, div_le_one (by positivity)]
    have h1 : η ^ ((M + 2) ^ 2) ≤ 1 := pow_le_one₀ hη.le hη1
    have h2 : 1 ≤ 32 * Λ ^ 4 * K ^ 3 := by
      have h4 : 1 ≤ Λ ^ 4 := one_le_pow₀ hΛ
      have h5 : 1 ≤ K ^ 3 := one_le_pow₀ hK1
      calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
        _ ≤ 32 * Λ ^ 4 * K ^ 3 := by
            apply mul_le_mul (mul_le_mul (by norm_num) h4 (by norm_num) (by norm_num)) h5
              (by norm_num) (by positivity)
    linarith
  have hm₂0 : 0 < m₂ := by positivity
  set curve : Trajectory → Fin 2 → Polynomial ℝ := fun l =>
    ![Polynomial.C (1 / h) * (Polynomial.X - Polynomial.C a),
      Polynomial.C (1 / h) * (Polynomial.C (l.2 0) + Polynomial.X * Polynomial.C (l.2 1) -
        Polynomial.C y₀)] with hcurve_def
  have hcurve : ∀ l e, (curve l e).natDegree ≤ 1 := by
    intro l e
    fin_cases e
    · show (Polynomial.C (1 / h) * (Polynomial.X - Polynomial.C a)).natDegree ≤ 1
      apply (Polynomial.natDegree_C_mul_le _ _).trans
      exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
    · show (Polynomial.C (1 / h) * (Polynomial.C (l.2 0) + Polynomial.X * Polynomial.C (l.2 1) -
        Polynomial.C y₀)).natDegree ≤ 1
      apply (Polynomial.natDegree_C_mul_le _ _).trans
      apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le _ (by simp)
      apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le (by simp)
      exact (Polynomial.natDegree_mul_le).trans (by simp)
  have hcurveval : ∀ (l : Trajectory) (t : ℝ),
      (fun j => (curve l j).eval t) = coreBase h a y₀ (l, t) := by
    intro l t
    funext j
    fin_cases j
    · show (Polynomial.C (1 / h) * (Polynomial.X - Polynomial.C a)).eval t = coreBase h a y₀ (l, t) 0
      rw [coreBase_zero]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
      ring
    · show (Polynomial.C (1 / h) * (Polynomial.C (l.2 0) + Polynomial.X * Polynomial.C (l.2 1) -
        Polynomial.C y₀)).eval t = coreBase h a y₀ (l, t) 1
      rw [coreBase_one]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_add, scalarY]
      ring
  set Tpoly : Trajectory → Polynomial ℝ := fun l =>
    Polynomial.C (l.2 3) + Polynomial.C (2 * l.2 4) * Polynomial.X with hTpoly_def
  have hT : ∀ l, (Tpoly l).natDegree ≤ 2 := by
    intro l
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le (by simp)
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  have hTeval : ∀ (l : Trajectory) (t : ℝ), (Tpoly l).eval t = l.2 3 + 2 * t * l.2 4 := by
    intro l t
    simp only [hTpoly_def, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X]
    ring
  have hSS₀ : S ⊆ S₀ := hSA₁.trans hA₁S₀
  obtain ⟨U, hUm, hUS, hUmass, hUrow⟩ := Cart.exists_original_whole_block_field_rows
    (ν.restrict A) (ρ.restrict S₀) Λ m₂ a h ηr Λ (Λ * N ^ (-L)) (E1c * εT) hΛ0 hm₂0 hh hηr0
    hηr1 hΛ0.le (by positivity) (by positivity)
    (by rw [hηr_def, hm₂_def]; apply le_of_eq; field_simp; ring)
    hdom (2 * M) 𝒯 h𝒯deg curve hcurve Tpoly hT (fun l => l.2 1)
    (fun e p => G (physCube N B p) e) S hSm
    (fun p hp => (hS₀A (hSS₀ hp)).2)
    (by
      rw [Measure.restrict_apply_univ, Measure.restrict_apply hSm,
        Set.inter_eq_left.mpr hSS₀, hνAeq]
      refine le_trans ?_ hSmass
      simp only [Fintype.card_fin]
      rw [← ENNReal.ofReal_mul hm₂0.le]
      apply ENNReal.ofReal_le_ofReal
      have hn2 : (gridSize Bf ξ : ℝ) * (gridSize Bf ξ : ℝ) ≠ 0 := by positivity
      have hθn : θl * ((gridSize Bf ξ : ℝ) * (gridSize Bf ξ : ℝ)) = m / (2 * K ^ 3) := by
        rw [hθl_def]; field_simp
      rw [hθn, hm_def, hm₂_def]
      have hνle : νA ≤ Λ * ρ₀ / h := by rw [le_div_iff₀ hh]; linarith
      calc h * η ^ ((M + 2) ^ 2) / (16 * Λ ^ 3 * K ^ 3) * νA
          ≤ h * η ^ ((M + 2) ^ 2) / (16 * Λ ^ 3 * K ^ 3) * (Λ * ρ₀ / h) :=
            mul_le_mul_of_nonneg_left hνle (by positivity)
        _ = ρ₀ / (4 * Λ ^ 2) / (2 * K ^ 3) * (η ^ ((M + 2) ^ 2) / 2) := by
            field_simp; ring)
    (fun p hp => hcoefA p.1 (hS₀A (hSS₀ hp)).1 1)
    (fun p hp => by
      rw [hTeval]
      have := (hgraph p (hS₀E (hSS₀ hp))).2
      have e : p.1.2 3 + 2 * p.2 * p.1.2 4 - G (physCube N B p) 0 - p.1.2 1 * G (physCube N B p) 1 =
          p.1.2 3 + 2 * p.2 * p.1.2 4 - G (physCube N B p) 0 - G (physCube N B p) 1 * p.1.2 1 := by
        ring
      simpa only [e] using this)
    (fun p hp e => by
      rw [hcurveval]
      exact hfitS p hp e)
  -- Step 8: the conclusion
  refine ⟨𝒯, U, hUm, hUS.trans hSS₀, h𝒯deg, h𝒯coef, ?_, ?_⟩
  · have h1 : (ρ.restrict S₀) U = ρ U := by
      rw [Measure.restrict_apply hUm, Set.inter_eq_left.mpr (hUS.trans hSS₀)]
    rw [← h1]
    refine le_trans ?_ hUmass
    rw [Measure.restrict_apply_univ, hνAeq, hρS₀eq, ← ENNReal.ofReal_mul hηr0.le,
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [hηr_def, hm₂_def]
    have hρ₀' : ρ₀ ≤ Λ * (νA * h) := hρ₀le
    calc η ^ ((M + 2) ^ 2) / (32 * Λ ^ 4 * K ^ 3) * ρ₀
        ≤ η ^ ((M + 2) ^ 2) / (32 * Λ ^ 4 * K ^ 3) * (Λ * (νA * h)) :=
          mul_le_mul_of_nonneg_left hρ₀' (by positivity)
      _ = h * η ^ ((M + 2) ^ 2) / (16 * Λ ^ 3 * K ^ 3) / 2 * νA := by
          field_simp; ring
  · intro p hp t ht
    have h1 := hUrow p hp t ht
    rw [hcurveval, hTeval] at h1
    have hres : coreResidual 𝒯 h ![a, y₀] p.1 t =
        p.1.2 3 + 2 * t * p.1.2 4 - MvPolynomial.eval (coreBase h a y₀ (p.1, t)) (𝒯 0) -
          p.1.2 1 * MvPolynomial.eval (coreBase h a y₀ (p.1, t)) (𝒯 1) := by
      have hb : (fun e : Fin 2 => ((![t, scalarY p.1 t] : Fin 2 → ℝ) e - (![a, y₀] : Fin 2 → ℝ) e) / h) =
          coreBase h a y₀ (p.1, t) := by
        funext j
        fin_cases j
        · show (t - a) / h = coreBase h a y₀ (p.1, t) 0
          rw [coreBase_zero]
        · show (scalarY p.1 t - y₀) / h = coreBase h a y₀ (p.1, t) 1
          rw [coreBase_one]
      simp only [coreResidual, hb, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, mul_one]
      ring
    rw [hres]
    refine h1.trans ?_
    have hE0 : Λ * N ^ (-L) ≤ εT := hgraphp
    have hfac : 0 ≤ (8 * (((2 * M : ℕ) : ℝ) + 3) / ηr) ^ (2 * M + 2) := by positivity
    have : Λ * N ^ (-L) + (1 + Λ) * (E1c * εT) ≤ (1 + (1 + Λ) * E1c) * εT := by
      have e1 : (1 + (1 + Λ) * E1c) * εT = εT + (1 + Λ) * (E1c * εT) := by ring
      rw [e1]; linarith
    calc _ ≤ (8 * (((2 * M : ℕ) : ℝ) + 3) / ηr) ^ (2 * M + 2) * ((1 + (1 + Λ) * E1c) * εT) :=
          mul_le_mul_of_nonneg_left this hfac
      _ = _ := by rfl

end Submission.Obl.k4_scalar_grid_cartesian_field
