-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.ReindexedQualWitness, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.QualWitness

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Submission.Obl.k4_physical_row_packet_potential.Cartesian

/-- A global row readout identity transports the same polynomial and
ALL original witness times through a later state coding. -/
theorem qualWitness_readout_congr {Λ I J : Type*}
    {Eref : Set (Λ × ℝ)} {st : Λ × ℝ → I} {st' : Λ × ℝ → J}
    {row : I → Fin 3 → ℝ} {row' : J → Fin 3 → ℝ}
    (hreadout : ∀ z, row' (st' z)=row (st z))
    {t0 h K err duration : ℝ} {M : ℕ} {w : Λ × ℝ} :
    QualWitness Eref st' row' t0 h M K err duration w ↔
      QualWitness Eref st row t0 h M K err duration w := by
  simp only [QualWitness,hreadout]

/-- It suffices that the readout agrees on the fixed witness reference,
including the current point. This also covers a coefficient-table
cutoff whose equality with the original table is only known there. -/
theorem qualWitness_of_readout_eq_on_reference {Λ I J : Type*}
    {Eref : Set (Λ × ℝ)} {st : Λ × ℝ → I} {st' : Λ × ℝ → J}
    {row : I → Fin 3 → ℝ} {row' : J → Fin 3 → ℝ}
    (hreadout : ∀ z∈Eref, row' (st' z)=row (st z))
    {t0 h K err duration : ℝ} {M : ℕ} {w : Λ × ℝ} (hw : w∈Eref)
    (hq : QualWitness Eref st row t0 h M K err duration w) :
    QualWitness Eref st' row' t0 h M K err duration w := by
  obtain ⟨P,hdegree,hcoeff,hpoint,Et,hEt,hEtI,hEtmass,hfit⟩ := hq
  refine ⟨P,hdegree,hcoeff,?_,Et,hEt,hEtI,hEtmass,?_⟩
  · simpa only [hreadout w hw] using hpoint
  · intro s hs
    obtain ⟨href,hfit'⟩ := hfit s hs
    refine ⟨href,?_⟩
    simpa only [hreadout _ href] using hfit'

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
