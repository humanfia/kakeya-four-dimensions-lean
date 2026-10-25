-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.CoverSize.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoverMass

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open Finset MeasureTheory

/-- If a nonempty finite family has balanced fibers, every fiber is nonempty. -/
theorem balanced_fibers_nonempty {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (hS : S.Nonempty) (f : ι → κ) {L : ℝ}
    (hbal : ∀ k k', ((S.filter (fun i => f i = k)).card : ℝ) ≤
      L * (S.filter (fun i => f i = k')).card) (k : κ) :
    ∃ i ∈ S, f i = k := by
  obtain ⟨i₀, hi₀⟩ := hS
  have hsource : 0 < (S.filter (fun i => f i = f i₀)).card :=
    card_pos.mpr ⟨i₀, mem_filter.mpr ⟨hi₀, rfl⟩⟩
  have ht := hbal (f i₀) k
  have htarget : (S.filter (fun i => f i = k)).Nonempty := by
    by_contra hh
    rw [not_nonempty_iff_eq_empty.mp hh, card_empty, Nat.cast_zero, mul_zero] at ht
    have hsource' : (0 : ℝ) < (S.filter (fun i => f i = f i₀)).card := Nat.cast_pos.mpr hsource
    linarith
  obtain ⟨i, hi⟩ := htarget
  exact ⟨i, (mem_filter.mp hi).1, (mem_filter.mp hi).2⟩

namespace Interfaces

/-- The mass retained by `C` forces a nonempty selected fine family. -/
theorem c_fine_nonempty {δ η m l h ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hA : A δ η m l n x v Y) (hC : C δ h n x v Y S Z ρ N y w f) :
    S.Nonempty := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr hA.1
  have hmass : 0 < ∑ i, μ (Y i) :=
    (ENNReal.ofReal_pos.mpr (by positivity : 0 < δ ^ η * n * δ ^ 2)).trans_le hA.2.2.2.1
  have hmul : 0 < o (δ ^ h) * ∑ i, μ (Y i) := by
    unfold o
    positivity
  have hmass' : 0 < ∑ i ∈ S, μ (Z i) := hmul.trans_le hC.2.1
  by_contra hh
  rw [not_nonempty_iff_eq_empty.mp hh, sum_empty] at hmass'
  exact lt_irrefl _ hmass'

/-- Every coarse tube of a balanced retained cover carries a nonempty fine fiber. -/
theorem c_fibers_nonempty {δ η m l h ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hA : A δ η m l n x v Y) (hC : C δ h n x v Y S Z ρ N y w f)
    (k : Fin N) : ∃ i ∈ S, f i = k := by
  classical
  apply balanced_fibers_nonempty S (c_fine_nonempty hδ hA hC) f (L := δ ^ (-h))
  intro k k'
  have hh := hC.2.2.2.2.2.2.1 k k'
  simpa only [q, ← Finset.coe_filter, Set.ncard_coe_finset] using hh

/-- In particular the coarse family has no more members than the original fine family. -/
theorem c_coarse_count_le {δ η m l h ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hA : A δ η m l n x v Y) (hC : C δ h n x v Y S Z ρ N y w f) :
    N ≤ n := by
  have hsurj : Function.Surjective f := by
    intro k
    obtain ⟨i, -, hi⟩ := c_fibers_nonempty hδ hA hC k
    exact ⟨i, hi⟩
  simpa using Fintype.card_le_of_surjective f hsurj

/-- An a priori polynomial bound for the coarse convex-count coefficient, in the
normalization used by the variational selection. -/
theorem coarse_size_power_bound {δ η h ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hA : A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f) :
    (N : ℝ) / ρ ≤ wz_endpoint_bootstrap.ballConstant * δ ^ (-(η + 3)) := by
  have hn : (n : ℝ) * δ ^ 2 ≤ δ ^ (-η) * wz_endpoint_bootstrap.ballConstant :=
    Hypotheses.count_bound (hypotheses_iff.mpr hA) hδ
  have hN : (N : ℝ) ≤ n := Nat.cast_le.mpr (c_coarse_count_le hδ hA hC)
  have hρ : 0 < ρ := hδ.trans_le hδρ
  calc
    (N : ℝ) / ρ ≤ n / δ := div_le_div₀ (Nat.cast_nonneg _) hN hδ hδρ
    _ = ((n : ℝ) * δ ^ 2) / δ ^ 3 := by field_simp
    _ ≤ (δ ^ (-η) * wz_endpoint_bootstrap.ballConstant) / δ ^ 3 :=
      div_le_div_of_nonneg_right hn (pow_nonneg hδ.le _)
    _ = wz_endpoint_bootstrap.ballConstant * δ ^ (-(η + 3)) := by
      rw [show -(η + 3) = -η + -(3 : ℝ) by ring, Real.rpow_add hδ,
        Real.rpow_neg hδ.le (3 : ℝ), Real.rpow_ofNat, div_eq_mul_inv]
      ring

end Interfaces

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
