import Submission.Obl.k4_unbounded_geometric_packet_reduction.SupportLaw
import Submission.Obl.k4_unbounded_geometric_packet_reduction.SupportPruning
import Submission.Obl.k4_fixed_budget_quadratic_recovery.Grouping
import Submission.Lib.K4XInterface.Charts

namespace Submission.Obl.k4_unbounded_geometric_packet_reduction

open MeasureTheory
open Submission.Lib.K4XInterface

noncomputable section

/-- Complete occupied support at one sample.  All analytical masks remain in
the laws; surviving parents keep their original assignments, formatted events,
frames and full-assignment conditional priors. -/
theorem PacketSample.complete_support
    {N K h χ η d s m S U loss₀ loss : ℝ} {W M D Cpart : ℕ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Traj} {E : Fin W → Set Inc}
    {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    (hsample : PacketSample true N K W ω ν E P B M D loss₀ h χ d s m S U)
    (hpieces : ∀ (C : ℕ) (R : Fin C → ENNReal) (μ : Fin C → Measure Inc)
      (b : Fin C → Traj → Fin 5 → ℝ), SupportCertificate N χ d s m C R μ b →
        Nonempty (OscillationPieces N χ d s m C Cpart R μ b))
    (hN : 2 ≤ N) (hB : ∀ w, 0 ≤ B w) (hm : 0 ≤ m) (hχη : χ ≤ η)
    (hχ : χ * ((2 * Cpart + 12 : ℕ) : ℝ) ≤ η) (hloss : loss₀ ≤ loss)
    (hgap : 2 * N ^ (-loss) + N ^ (-η) + N ^ (-χ) ≤ N ^ (-loss₀)) :
    PacketSample false N K W ω ν E P B M D loss h η d s m S U := by
  classical
  obtain ⟨T, C, γ, j, center, velocity, Q, A, F, lst, offset, tangent,
    law, base, signal, hK, hT, hC, hdisj, hlst, hlstm, hcharts, hcoords,
    hbudget, hdata, hmass, hcert⟩ := hsample
  let q : ℝ := 1 / (2 : ℝ) ^ T
  let t₀ (a : Fin C) : ℝ := ((j a : ℕ) : ℝ) / (2 : ℝ) ^ T
  let expand (a : Fin C) (z : Inc) : Inc := (z.1, t₀ a + q * z.2)
  let coeff (a : Fin C) := nativeCoeff (P (γ a)) (t₀ a) q (offset a) (tangent a) (A a)
  let budget (a : Fin C) : ENNReal := ENNReal.ofReal q * ν (γ a) (A a)
  let R (a : Fin C) : ENNReal := ENNReal.ofReal (ω (γ a)) * budget a
  have hc : SupportCertificate N χ d s m C R law coeff := by
    simpa [R, budget, coeff, t₀, q] using hcert
  have hKscalar : 2 ≤ N ^ χ := by
    obtain ⟨J, w, Λ, P', S', tag, A', z, hw, hKs, hrest⟩ := hc
    exact hKs
  let o := Classical.choice (hpieces C R law coeff hc)
  let good (a : Fin C) : Set Inc := ⋃ e, ⋃ i, o.piece a e i
  let law' (a : Fin C) : Measure Inc := (law a).restrict (good a)
  have hsub a : law' a ≤ law a := Measure.restrict_le_self
  have hcaps a : ScalarCaps N χ d s m S U
      ((ν (γ a) (A a))⁻¹ • (ν (γ a)).restrict (A a)) (law a) (coeff a) := by
    simpa [coeff, t₀, q] using (hdata a).1
  have hprojected := o.projected_law hcaps hN hKscalar hm hχη hχ
  let Good := {a : Fin C | ENNReal.ofReal (N ^ (-η)) ≤ law' a Set.univ}
  let C' : ℕ := Fintype.card Good
  let e : Good ≃ Fin C' := Fintype.equivFin Good
  let index (a : Fin C') : Fin C := (e.symm a).val
  have hindex : Function.Injective index := Subtype.val_injective.comp e.symm.injective
  have hNp : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hpow : N ^ loss₀ ≤ N ^ loss := Real.rpow_le_rpow_of_exponent_le hN1 hloss
  have hlistNat w v : (lst w v).card ≤ ⌊N ^ loss₀⌋₊ := Nat.le_floor (hlst w v)
  have hlistData w := Submission.Obl.k4_fixed_budget_quadratic_recovery.reindex_lists
    index hindex (lst w) (hlistNat w) (hlstm w)
  choose lst' hmem' hcard' hmeas' using hlistData
  have hnewlist w v : ((lst' w v).card : ℝ) ≤ N ^ loss := by
    have hh : ((lst' w v).card : ℝ) ≤ (⌊N ^ loss₀⌋₊ : ℝ) := by exact_mod_cast hcard' w v
    exact hh.trans ((Nat.floor_le (Real.rpow_nonneg hNp.le _)).trans hpow)
  have hcount : (C' : ℝ) ≤ N ^ M := by
    have hh : C' ≤ C := by simpa using Fintype.card_le_of_injective index hindex
    exact (show (C' : ℝ) ≤ C by exact_mod_cast hh).trans hC
  have hbudget' : (∑ a : Fin C', R (index a)) ≤ 1 := by
    calc
      _ = ∑ a : Good, R a.val := e.symm.sum_comp (fun a : Good => R a.val)
      _ = ∑ a ∈ Finset.univ.filter (fun a => ENNReal.ofReal (N ^ (-η)) ≤ law' a Set.univ), R a :=
        (Finset.sum_subtype _ (by simp [Good]) _).symm
      _ ≤ ∑ a, R a := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ => zero_le)
      _ ≤ 1 := hbudget
  have hretained : ENNReal.ofReal (N ^ (-loss₀)) ≤
      (∑ a, R a * law' a Set.univ) + ENNReal.ofReal (N ^ (-χ)) := by
    have hh := hmass.trans o.retained
    simpa only [law', good, Measure.restrict_apply_univ] using hh
  have hheavy := retained_heavy_mass R (fun a => law' a Set.univ) hbudget
    (Real.rpow_nonneg hNp.le (-loss)) (Real.rpow_nonneg hNp.le (-η))
    (Real.rpow_nonneg hNp.le (-χ)) hgap hretained
  have hmass' : ENNReal.ofReal (N ^ (-loss)) ≤ ∑ a : Fin C', R (index a) * law' (index a) Set.univ := by
    rw [e.symm.sum_comp (fun a : Good => R a.val * law' a.val Set.univ)]
    exact hheavy
  have hexpand a : Measurable (expand a) :=
    measurable_fst.prodMk (measurable_const.add (measurable_const.mul measurable_snd))
  refine ⟨T, C', (fun a => γ (index a)), (fun a => j (index a)),
    (fun a => center (index a)), (fun a => velocity (index a)), (fun a => Q (index a)),
    (fun a => A (index a)), (fun a => F (index a)), lst',
    (fun a => offset (index a)), (fun a => tangent (index a)),
    (fun a => law' (index a)), (fun a => base (index a)), (fun a => signal (index a)),
    hK.trans hpow, hT.trans ?_, hcount, ?_, hnewlist, hmeas', ?_,
    (fun a => hcoords (index a)), hbudget', ?_, hmass', ?_⟩
  · exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  · intro a a' haa hγ hj
    exact hdisj _ _ (fun hh => haa (hindex hh)) hγ hj
  · intro a
    have hh := hcharts (index a)
    change gchart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ at hh
    exact gchart_mono hh hN1 le_rfl le_rfl (Real.rpow_pos_of_pos hNp loss₀) hpow
      (hB _) (fun hknown p hp => (hmem' _ _ a).mpr (hknown p hp))
  · intro a
    refine ⟨?_, (e.symm a).property, (hdata (index a)).2.2.1,
      (hdata (index a)).2.2.2.1, ?_, ?_, ?_⟩
    · simpa [law', good, coeff, t₀, q] using hprojected (index a)
    · have hh := ((hdata (index a)).2.2.2.2.1).filter_mono (ae_mono (hsub (index a)))
      filter_upwards [hh] with p hp
      exact ⟨hp.1, hp.2.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))⟩
    · exact ((hdata (index a)).2.2.2.2.2.1).filter_mono (ae_mono (hsub (index a)))
    · have hmap := Measure.map_mono (hsub (index a)) (hexpand (index a))
      apply (le_trans ?_ (hdata (index a)).2.2.2.2.2.2)
      intro S'
      simp only [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (hmap S') zero_le
  · simp

end
end Submission.Obl.k4_unbounded_geometric_packet_reduction
