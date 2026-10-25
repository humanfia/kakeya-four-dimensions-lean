/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/PreparedDomainMeshes.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.PreparedSourceDomains
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonMeshResolution
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.PreparedCommonNativeCaps
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.FiniteNativeMesh
import Submission.Obl.k4_subcritical_endpoint_native_pairing.PositivePalette

/-! Actual prepared-domain source laws, frames and primitive native mesh caps. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open MeasureTheory Set
open Submission.Obl.k4_general_parent_projected_layers
open CommonDomain
open scoped ENNReal

noncomputable section

namespace PreparedDomainData

variable {α : Type} [MeasurableSpace α] {p : Parameters} {a : PreparedModel α}
  {k : ℕ} {s H q χ m : ℝ} {L : ProjLayer α} {ζ : Measure (α × ℝ)} {Extra : α × ℝ → Prop}
  (D : PreparedDomainData p a k s H q χ m L ζ Extra)

def law (i : Fin D.n) : Measure (α × ℝ) := codePieces ζ D.code i

def core (i : Fin D.n) : Set (α × ℝ) := D.G ∩ {z | D.code z = i}

def base (i : Fin D.n) (z : α × ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (coords q χ (PreparedModel.narrow p k s) m (D.decode i) (point (a.b k z.1) z.2))

theorem measurable_core (i : Fin D.n) : MeasurableSet (D.core i) :=
  D.measurable_G.inter (D.measurable_code (measurableSet_singleton i))

theorem core_ae (i : Fin D.n) : ∀ᵐ z ∂D.law i, z ∈ D.core i := by
  have hG : ∀ᵐ z ∂ζ, z ∈ D.G := ae_iff.mpr D.full_G
  change ∀ᵐ z ∂ζ.restrict {z | D.code z = i}, z ∈ D.G ∩ {z | D.code z = i}
  filter_upwards [ae_restrict_of_ae hG, ae_restrict_mem (D.measurable_code (measurableSet_singleton i))]
    with z hz hzi
  exact ⟨hz, hzi⟩

theorem ae_of_domains (P : Fin D.n → α × ℝ → Prop)
    (hP : ∀ u, ∀ᵐ z ∂D.law u, P u z) : ∀ᵐ z ∂ζ, P (D.code z) z := by
  have hconditional (u : Fin D.n) : ∀ᵐ z ∂ζ, D.code z = u → P u z := by
    have hmeas : MeasurableSet {z | D.code z = u} := D.measurable_code (measurableSet_singleton u)
    apply (ae_restrict_iff' hmeas).mp
    exact hP u
  filter_upwards [ae_all_iff.mpr hconditional] with z hz
  exact hz (D.code z) rfl

theorem core_point {i : Fin D.n} {z : α × ℝ} (hz : z ∈ D.core i) :
    PreparedSourcePoint p a k s L Extra z ∧
      CommonDomain.code q χ (PreparedModel.narrow p k s) m (a.b k z.1) z.2 = D.decode i := by
  have hp := D.pointwise z hz.1
  exact ⟨hp.1, hp.2.symm.trans (congrArg D.decode hz.2)⟩

theorem measurable_base (hb : Measurable (a.b k)) (i : Fin D.n) : Measurable (D.base i) := by
  apply (WithLp.measurable_toLp 2 (Fin 3 → ℝ)).comp
  apply measurable_pi_iff.mpr
  intro j
  fin_cases j <;> dsimp [coords, point, majorCenter, minorCenter] <;> fun_prop

theorem base_norm {i : Fin D.n} {z : α × ℝ} (hz : z ∈ D.core i)
    (hq : 0 < q) (hχ : 0 < χ) (hg : 0 < PreparedModel.narrow p k s) (hm : 0 < m)
    (hqg : q * PreparedModel.narrow p k s ≤ m) : ‖D.base i z‖ ≤ 1 / 8 := by
  obtain ⟨hp, hc⟩ := D.core_point hz
  dsimp only [base]
  rw [← hc]
  exact coords_norm_le hq hχ hg hm hqg (a.b k z.1) hp.time

theorem velocity_ae (i : Fin D.n) :
    ∀ᵐ z ∂D.law i, ⌊a.b k z.1 3 / χ⌋ = (D.decode i) 1 := by
  filter_upwards [D.core_ae i] with z hz
  have h := congrArg (fun c : Code => c 1) (D.core_point hz).2
  simpa only [CommonDomain.code, Matrix.cons_val_one, Matrix.cons_val_zero] using h

theorem palette_ne_zero (hpalette : ∀ᵐ z ∂ζ,
    0 < a.pi k {w : ℝ | ⌊w / χ⌋ = ⌊a.b k z.1 3 / χ⌋}) (i : Fin D.n) :
    a.pi k {w : ℝ | ⌊w / χ⌋ = (D.decode i) 1} ≠ 0 := by
  have hpal : ∀ᵐ z ∂D.law i, 0 < a.pi k {w : ℝ | ⌊w / χ⌋ = ⌊a.b k z.1 3 / χ⌋} :=
    ae_restrict_of_ae hpalette
  have hpositive : ∀ᵐ _z ∂D.law i, 0 < a.pi k {w : ℝ | ⌊w / χ⌋ = (D.decode i) 1} := by
    filter_upwards [hpal, D.velocity_ae i] with z hz hv
    rwa [hv] at hz
  obtain ⟨z, -, hz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (D.positive_domain i)
    (ae_restrict_of_ae hpositive : ∀ᵐ _z ∂(D.law i).restrict univ,
      0 < a.pi k {w : ℝ | ⌊w / χ⌋ = (D.decode i) 1})
  exact hz.ne'

theorem palette_ne_zero_of_caps (hζ : ζ ≤ a.mu k) {r v S : ℝ}
    (hχeq : χ = p.N k ^ (-v)) (hS : 0 ≤ S)
    (hcap : ∀ t : ℝ, 0 ≤ t → t ≤ S → ∀ (z : Fin 3 → ℤ) (j v₀ : ℤ),
      a.mu k {w | a.cell (p.N k) r k w = z ∧
        ⌊MvPolynomial.eval (a.x k w.1 w.2) (a.P k) / p.N k ^ (-t)⌋ = j ∧
        ⌊a.b k w.1 3 / p.N k ^ (-v)⌋ = v₀} ≤
      ENNReal.ofReal (p.K k * p.N k ^ (-3 * r - p.d * t)) *
        a.pi k {w : ℝ | ⌊w / p.N k ^ (-v)⌋ = v₀}) (i : Fin D.n) :
    a.pi k {w : ℝ | ⌊w / χ⌋ = (D.decode i) 1} ≠ 0 := by
  have hpositive := Submission.Obl.k4_subcritical_endpoint_native_pairing.ae_positive_palette_of_cell_caps
    (a.mu k)
    (fun z => (a.cell (p.N k) r k z, ⌊MvPolynomial.eval (a.x k z.1 z.2) (a.P k)⌋))
    (fun z => ⌊a.b k z.1 3 / χ⌋) (fun v₀ => a.pi k {w : ℝ | ⌊w / χ⌋ = v₀})
    (ENNReal.ofReal (p.K k * p.N k ^ (-3 * r))) (fun z v₀ => by
      rcases z with ⟨z, j⟩
      have h := hcap 0 (by norm_num) hS z j v₀
      simpa only [hχeq, Prod.mk.injEq, and_assoc, neg_zero, Real.rpow_zero, div_one,
        mul_zero, sub_zero] using h)
  exact D.palette_ne_zero (ae_mono hζ hpositive) i

theorem resolved (hp : p.Valid) (hq : 0 < q) (hχ : 0 < χ) (hχ1 : χ ≤ 1)
    (hg : 0 < PreparedModel.narrow p k s) (hg1 : PreparedModel.narrow p k s ≤ 1)
    (hm : 0 < m) {δ σ : ℝ} (hδ : 0 ≤ δ)
    (hδq : (2 * p.K k + 1) * δ ≤ 100 * q * σ)
    (hδχ : (2 * p.K k + 1) * δ ≤ 100 * χ * σ)
    (hδm : (2 * p.K k + 1) * δ ≤ 100 * m * σ) (i : Fin D.n) :
    ∀ e, (∑ j, |coordMatrix q χ (PreparedModel.narrow p k s) m (D.decode i) e j| * δ) ≤ σ := by
  obtain ⟨z, hz, hzi⟩ := D.source_point i
  have hz' : z ∈ D.core i := ⟨hz, hzi⟩
  have hcoef := (D.core_point hz').1.coefficients
  have hb₃ : |a.b k z.1 3| ≤ p.K k := by
    linarith only [hcoef, abs_nonneg (a.b k z.1 0), abs_nonneg (a.b k z.1 1), abs_nonneg (a.b k z.1 4)]
  have hb₄ : |a.b k z.1 4| ≤ p.K k := by
    linarith only [hcoef, abs_nonneg (a.b k z.1 0), abs_nonneg (a.b k z.1 1), abs_nonneg (a.b k z.1 3)]
  have h := actual_common_mesh_resolution (t := z.2) (hp.2.2.1.1 k) hq hχ hχ1 hg hg1 hm hδ
    (a.b k z.1) hb₃ hb₄ hδq hδχ hδm
  rw [(D.core_point hz').2] at h
  exact h

theorem exists_native_mesh (hp : p.Valid) (hcommon : a.Common p) (hζ : ζ ≤ a.mu k)
    (hq : 0 < q) (hχ : 0 < χ) (hm : 0 < m)
    (hqg : q * PreparedModel.narrow p k s ≤ m)
    {r v S σ aTable : ℝ} (hχeq : χ = p.N k ^ (-v)) (hS : 0 ≤ S)
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 24) (haTable : 0 < aTable)
    (haMin : p.N k ^ (-S) ≤ aTable)
    (hresolve : ∀ i e, (∑ j, |coordMatrix q χ (PreparedModel.narrow p k s) m (D.decode i) e j| *
      p.N k ^ (-r)) ≤ σ)
    (hcap : ∀ t : ℝ, 0 ≤ t → t ≤ S → ∀ (z : Fin 3 → ℤ) (j v₀ : ℤ),
      a.mu k {w | a.cell (p.N k) r k w = z ∧
        ⌊MvPolynomial.eval (a.x k w.1 w.2) (a.P k) / p.N k ^ (-t)⌋ = j ∧
        ⌊a.b k w.1 3 / p.N k ^ (-v)⌋ = v₀} ≤
      ENNReal.ofReal (p.K k * p.N k ^ (-3 * r - p.d * t)) *
        a.pi k {w : ℝ | ⌊w / p.N k ^ (-v)⌋ = v₀}) (i : Fin D.n) :
    ∃ M : ComparisonMesh (D.law i), M.base = D.base i ∧ M.diameter = 3 * σ ∧
      (∑ _j : Fin M.n, M.vol) ≤ 1 ∧ ∀ R : ℝ, aTable ≤ R → ∀ j x,
        D.law i {z | M.code z = j ∧ ⌊MvPolynomial.eval (a.x k z.1 z.2) (a.P k) / R⌋ = x} ≤
          (ENNReal.ofReal ((27000000 * p.K k * (2 * p.K k + 5)) *
            ((q * χ * m) * aTable ^ p.d) * (R / aTable) ^ p.d) *
              a.pi k {w : ℝ | ⌊w / χ⌋ = (D.decode i) 1}) * M.vol := by
  have hN : 0 < p.N k := lt_of_lt_of_le (by norm_num) (hp.1 k)
  have hg : 0 < PreparedModel.narrow p k s := Real.rpow_pos_of_pos hN _
  have hK : 0 ≤ p.K k := zero_le_one.trans (hp.2.2.1.1 k)
  apply exists_finite_native_mesh (a.mu k) (D.law i)
    (Measure.restrict_le_self.trans hζ) (D.base i) (D.measurable_base (hcommon k).1 i)
    ((D.core_ae i).mono fun z hz => D.base_norm hz hq hχ hg hm hqg)
    (fun z => MvPolynomial.eval (a.x k z.1 z.2) (a.P k))
    (fun z => ⌊a.b k z.1 3 / χ⌋ = (D.decode i) 1) (D.velocity_ae i)
    haTable (by positivity) (by positivity) hσ hσsmall
    (a.pi k {w : ℝ | ⌊w / χ⌋ = (D.decode i) 1})
  intro R hRa z j
  have hc := prepared_common_native_caps p hp a hcommon hS hq hm hσ (D.decode i)
    (by simpa only [← hχeq] using hresolve i) hcap (haMin.trans hRa) z j
  rw [← hχeq] at hc
  convert hc using 1 <;> first | rfl | (congr 2 <;> ring)

end PreparedDomainData

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
