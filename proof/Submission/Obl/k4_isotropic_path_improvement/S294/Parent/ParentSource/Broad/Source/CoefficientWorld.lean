-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.CoefficientWorld, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/CoefficientWorld.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit 18a3db56eab47c441a364ba278c399c30491bda9,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/CoefficientWorld.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2.ParameterCompatibility
import Submission.Lib.K4CommonLocalChoice
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2.Interface

/-!
# Full original coefficient-bin worlds

This dimension-independent adapter follows the normalization calculation in
accepted o278, CoefficientZoom.lean and WorldDensity.lean (originally o229,
x0797, commit21d8c848). The original trajectory type and coefficient map remain
arbitrary; the seven-coordinate identities specialize it to this obligation.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CoefficientWorld
open MeasureTheory Set
open Submission.Lib.K4CommonLocalChoice
open scoped ENNReal
noncomputable section

variable {Λ : Type*} {n : ℕ}

def center (ρ : ℝ) (q : Fin n → ℤ) : Fin n → ℝ := fun j => (q j : ℝ)*ρ

def block (c : Λ → Fin n → ℝ) (ρ : ℝ) (q : Fin n → ℤ) : Set Λ :=
  {l | cell ρ (c l)=q}

def coeff (c : Λ → Fin n → ℝ) (ρ : ℝ) (q : Fin n → ℤ) (l : Λ) : Fin n → ℝ :=
  fun j => (c l j-center ρ q j)/ρ

theorem coeff_mem_unit {c : Λ → Fin n → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    {q : Fin n → ℤ} {l : Λ} (hl : l∈block c ρ q) (j : Fin n) :
    coeff c ρ q l j∈Ico (0:ℝ) 1 := by
  have he := congr_fun hl j
  change ⌊c l j/ρ⌋=q j at he
  have hlo := Int.floor_le (c l j/ρ)
  have hhi := Int.lt_floor_add_one (c l j/ρ)
  rw [he] at hlo hhi
  dsimp only [coeff,center]
  rw [sub_div,mul_div_cancel_right₀ _ hρ.ne']
  constructor <;> linarith

theorem coeff_abs_le_one {c : Λ → Fin n → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    {q : Fin n → ℤ} {l : Λ} (hl : l∈block c ρ q) (j : Fin n) :
    |coeff c ρ q l j|≤1 := by
  have hh := coeff_mem_unit hρ hl j
  rw [abs_of_nonneg hh.1]
  exact hh.2.le

/-- The finer pieces are defined before the incidence restriction and have
coefficient diameter at most the requested zoomed scale. -/
theorem coeff_piece_diameter (c : Λ → Fin n → ℝ) {ρ β r : ℝ}
    (hρ : 0 < ρ) (hβ : 0 < β) (hscale : β≤ρ*r) (q : Fin n → ℤ)
    {l l' : Λ} (hbin : cell β (c l)=cell β (c l')) :
    ‖coeff c ρ q l-coeff c ρ q l'‖≤r := by
  have hr : 0≤r := by nlinarith
  apply (pi_norm_le_iff_of_nonneg hr).mpr
  intro j
  have hd := norm_sub_lt_of_cell_eq hβ hbin
  have he := norm_le_pi_norm (c l-c l') j
  have hid : coeff c ρ q l j-coeff c ρ q l' j=(c l j-c l' j)/ρ := by
    dsimp [coeff]; ring
  change |coeff c ρ q l j-coeff c ρ q l' j|≤r
  rw [hid,abs_div,abs_of_pos hρ]
  apply (div_le_iff₀ hρ).mpr
  have hraw : |c l j-c l' j|≤β := he.trans hd.le
  nlinarith only [hraw,hscale]

section Measure
variable [MeasurableSpace Λ]

theorem measurable_coeff {c : Λ → Fin n → ℝ} (hc : Measurable c)
    (ρ : ℝ) (q : Fin n → ℤ) : Measurable (coeff c ρ q) := by
  apply measurable_pi_iff.mpr
  intro j
  exact ((((measurable_pi_apply j).comp hc).sub_const _).div_const ρ)

theorem measurableSet_block {c : Λ → Fin n → ℝ} (hc : Measurable c)
    (ρ : ℝ) (q : Fin n → ℤ) : MeasurableSet (block c ρ q) :=
  (measurable_cell ρ hc) (measurableSet_singleton q)

/-- The full original bin, with its original mass as denominator. -/
def prior (θ : Measure Λ) (c : Λ → Fin n → ℝ) (ρ : ℝ) (q : Fin n → ℤ) : Measure Λ :=
  (θ (block c ρ q))⁻¹ • θ.restrict (block c ρ q)

theorem prior_probability (θ : Measure Λ) [IsFiniteMeasure θ]
    (c : Λ → Fin n → ℝ) (ρ : ℝ) (q : Fin n → ℤ)
    (hpos : θ (block c ρ q)≠0) : IsProbabilityMeasure (prior θ c ρ q) := by
  constructor
  simp only [prior,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hpos (measure_ne_top θ _)

theorem prior_apply (θ : Measure Λ) {c : Λ → Fin n → ℝ} (hc : Measurable c)
    (ρ : ℝ) (q : Fin n → ℤ) (A : Set Λ) :
    prior θ c ρ q A=(θ (block c ρ q))⁻¹*θ (A∩block c ρ q) := by
  rw [prior,Measure.smul_apply,smul_eq_mul,
    Measure.restrict_apply' (measurableSet_block hc ρ q)]

/-- A cap and full-bin reference floor cancel before any current
incidence mass is used as a denominator. -/
theorem prior_cap_of_original_cap (θ : Measure Λ) {c : Λ → Fin n → ℝ}
    (hc : Measurable c) (ρ : ℝ) (q : Fin n → ℤ) (A : Set Λ) (C : ENNReal)
    (hcap : θ (A∩block c ρ q)≤C*θ (block c ρ q)) : prior θ c ρ q A≤C := by
  rw [prior_apply θ hc]
  by_cases hpos : θ (block c ρ q)=0
  · have hnum : θ (A∩block c ρ q)=0 := measure_mono_null inter_subset_right hpos
    simp only [hnum,mul_zero,zero_le]
  by_cases htop : θ (block c ρ q)=∞
  · simp [htop]
  calc
    _ ≤ (θ (block c ρ q))⁻¹*(C*θ (block c ρ q)) := mul_le_mul' le_rfl hcap
    _ = C := by rw [mul_left_comm,ENNReal.inv_mul_cancel hpos htop,mul_one]

theorem prior_prod_apply (θ : Measure Λ) [SFinite θ]
    (c : Λ → Fin n → ℝ) (ρ : ℝ) (q : Fin n → ℤ)
    {E : Set (Λ×ℝ)} (hE : MeasurableSet E) (hblock : ∀ p∈E, p.1∈block c ρ q) :
    ((prior θ c ρ q).prod volume) E=(θ (block c ρ q))⁻¹*(θ.prod volume) E := by
  rw [prior,Measure.prod_smul_left,Measure.smul_apply,
    Measure.restrict_prod_eq_prod_univ,Measure.restrict_apply hE]
  have hsub : E⊆block c ρ q×ˢ(univ:Set ℝ) := fun p hp => ⟨hblock p hp,mem_univ _⟩
  rw [inter_eq_left.mpr hsub]
  rfl

/-- Dense labels in a world are assessed against the full original bin
prior, using only the entering original density ceiling. -/
theorem prior_product_dense (θ : Measure Λ) [IsFiniteMeasure θ]
    (μ : Measure (Λ×ℝ)) {H δ ρ : ℝ} (hH : 0 < H)
    (hμ : μ≤ENNReal.ofReal H • θ.prod volume)
    (c : Λ → Fin n → ℝ) (q : Fin n → ℤ)
    (hpositive : θ (block c ρ q)≠0) {E : Set (Λ×ℝ)} (hE : MeasurableSet E)
    (hblock : ∀ p∈E, p.1∈block c ρ q)
    (hmass : ENNReal.ofReal δ*θ (block c ρ q)≤μ E) :
    ENNReal.ofReal (δ/H)≤((prior θ c ρ q).prod volume) E := by
  let P := θ (block c ρ q)
  have hPt : P≠∞ := measure_ne_top θ _
  have hμE : μ E≤ENNReal.ofReal H*(θ.prod volume) E := by
    simpa only [Measure.smul_apply,smul_eq_mul] using hμ E
  have hnorm : ENNReal.ofReal δ≤ENNReal.ofReal H*(P⁻¹*(θ.prod volume) E) := by
    calc
      _ = ENNReal.ofReal δ*(P⁻¹*P) := by rw [ENNReal.inv_mul_cancel hpositive hPt,mul_one]
      _ = P⁻¹*(ENNReal.ofReal δ*P) := by ring
      _ ≤ P⁻¹*(ENNReal.ofReal H*(θ.prod volume) E) := mul_le_mul' le_rfl (hmass.trans hμE)
      _ = _ := by ring
  rw [prior_prod_apply θ c ρ q hE hblock,ENNReal.ofReal_div_of_pos hH]
  exact (ENNReal.div_le_iff' (by positivity) ENNReal.ofReal_ne_top).mpr hnorm

end Measure

section Seven
variable (c : Λ → Fin 7 → ℝ) (ρ : ℝ) (q : Fin 7 → ℤ) (l : Λ) (t : ℝ)

/-- The quadratic central signal is removed exactly. -/
theorem zx_coeff : Jets2.zx (coeff c ρ q l) t=
    (Jets2.zx (c l) t-Jets2.zx (center ρ q) t)/ρ := by
  dsimp [Jets2.zx,coeff]; ring

theorem zy_coeff : Jets2.zy (coeff c ρ q l) t=
    fun i => (Jets2.zy (c l) t i-Jets2.zy (center ρ q) t i)/ρ := by
  funext i
  fin_cases i <;> dsimp [Jets2.zy,coeff] <;> ring

theorem zv_coeff : Jets2.zv (coeff c ρ q l)=
    fun i => (Jets2.zv (c l) i-Jets2.zv (center ρ q) i)/ρ := by
  funext i
  fin_cases i <;> rfl

theorem zS_coeff (F : ℝ → Fin 2 → ℝ) : Jets2.zS F (coeff c ρ q l) t=
    (Jets2.zS F (c l) t-Jets2.zS F (center ρ q) t)/ρ := by
  simp only [Jets2.zS,zx_coeff,zy_coeff,dotProduct,Fin.sum_univ_two]
  ring

theorem zR_coeff (F : ℝ → Fin 2 → ℝ) : Jets2.zR F (coeff c ρ q l) t=
    (Jets2.zR F (c l) t-Jets2.zR F (center ρ q) t)/ρ := by
  simp only [Jets2.zR,zv_coeff,dotProduct,Fin.sum_univ_two,coeff]
  ring

/-- Zoomed spatial cubes are literal original cubes after translating by
the central quadratic and affine curves. Time stays unchanged. -/
theorem inCube_coeff_iff (hρ : 0 < ρ) (a : ℝ) (b : Fin 2 → ℝ) (r : ℝ) :
    Jets2.InCube (coeff c ρ q l) t a b r ↔
      Jets2.InCube (c l) t (Jets2.zx (center ρ q) t+ρ*a)
        (fun i => Jets2.zy (center ρ q) t i+ρ*b i) (ρ*r) := by
  have hi (z c0 a0 : ℝ) : (z-c0)/ρ∈Ico a0 (a0+r) ↔
      z∈Ico (c0+ρ*a0) (c0+ρ*a0+ρ*r) := by
    constructor
    · intro hz
      have hlo := (le_div_iff₀ hρ).mp hz.1
      have hhi := (div_lt_iff₀ hρ).mp hz.2
      constructor <;> nlinarith
    · intro hz
      constructor
      · apply (le_div_iff₀ hρ).mpr; nlinarith [hz.1]
      · apply (div_lt_iff₀ hρ).mpr; nlinarith [hz.2]
  simp only [Jets2.InCube,zx_coeff,zy_coeff,hi]

end Seven
end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CoefficientWorld
