-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.ScaledQualWitness, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.QualWitness

/-! Return a normalized qualification row to its original signal units.
The block clock and all witness events are unchanged. -/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory Polynomial
open Submission.Obl.k4_physical_row_packet_potential.Cartesian

noncomputable section

/-- A positive change of signal units scales the polynomial and error
and leaves its degree, reference events and witness duration intact. -/
theorem scaled_qualWitness {Λ σ : Type*}
    {Eref : Set (Λ × ℝ)} {st : Λ × ℝ → σ} {Gs : σ → Fin 3 → ℝ}
    {t0 h Kq err dur scale : ℝ} {M : ℕ} {w : Λ × ℝ}
    (hscale : 0 ≤ scale) (hq : QualWitness Eref st Gs t0 h M Kq err dur w) :
    QualWitness Eref st (fun k i => scale*Gs k i) t0 h M (scale*Kq) (scale*err) dur w := by
  obtain ⟨P,hdeg,hcoeff,hpoint,Et,hEt,hEtI,hEtmass,hfit⟩ := hq
  have herror (k : σ) (i : Fin 3) (t : ℝ) :
      |scale*Gs k i-(C scale*P i).eval t|=scale*|Gs k i-(P i).eval t| := by
    rw [eval_mul,eval_C,←mul_sub,abs_mul,abs_of_nonneg hscale]
  refine ⟨fun i => C scale*P i,
    fun i => (natDegree_C_mul_le _ _).trans (hdeg i),?_,?_,Et,hEt,hEtI,hEtmass,?_⟩
  · intro i n
    rw [coeff_C_mul,abs_mul,abs_of_nonneg hscale]
    exact mul_le_mul_of_nonneg_left (hcoeff i n) hscale
  · intro i
    rw [herror]
    exact mul_le_mul_of_nonneg_left (hpoint i) hscale
  · intro t ht
    refine ⟨(hfit t ht).1,?_⟩
    intro i
    rw [herror]
    exact mul_le_mul_of_nonneg_left ((hfit t ht).2 i) hscale

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
