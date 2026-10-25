-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Forward.PreparedDenseChoice, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Adapted from this LOT tree, obligation o294, session x1082, commit842fd2d7,
-- Forward/DenseChoice.lean. The actual prepared family and its density replace
-- the original residual as the input to the same dense-packet selection.
import Submission.Obl.k4_isotropic_path_improvement.S294.Forward.DenseChoice

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Forward

open MeasureTheory Set
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
open scoped ENNReal

noncomputable section

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a₁ A : ℝ} {θ : ENNReal}

/-- Select the actual dense child AFTER all global preparation and
qualification exceptions. Original residual membership supplies the same
active ancestor and good original history as before the cuts. -/
theorem exists_dense_good_descendant_after_preparation
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ} (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (F : PaletteFamily Q i stop a₁ A θ) {r fraction : ℝ} (R : BroadResidual F r fraction)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (current : Fin (d.W k) → Set Ev)
    (hcurrent : ∀ w, current w⊆R.residual w)
    (density : ℝ) (hdensity : 0 < density)
    (hmass : ENNReal.ofReal density+ENNReal.ofReal density ≤
      ∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (current w))
    (ib : ℕ) (hiib : i ≤ ib) (hib : ib ≤ m - 1) :
    ∃ b : Fin p.C, p.lev b = ib ∧ 0 < d.ω k (p.γ b) ∧ d.ν k (p.γ b) (p.A b) ≠ 0 ∧
      ENNReal.ofReal density *
          (d.ν k (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T ib)⁻¹)) ≤
        ((d.ν k (p.γ b)).prod volume) (current (p.γ b) ∩ p.F b) ∧
      p.lev (p.par^[ib - i] b) = i ∧ p.γ (p.par^[ib - i] b) = p.γ b ∧
      p.F b ⊆ p.F (p.par^[ib - i] b) ∧ p.A b ⊆ p.A (p.par^[ib - i] b) ∧
      F.active (p.par^[ib - i] b) ∧
      ∀ x ∈ current (p.γ b) ∩ p.F b,
        (p.γ b, x) ∈ F.U (p.par^[ib - i] b) ∧ ∃ f, p.lev f = stop ∧ p.γ f = p.γ b ∧
          x ∈ p.packetWitness m stop (p.γ b) f ∧
          F.coding.code f ∉
            Q.intrinsicNarrowStates F.code stop F.U r fraction (p.par^[ib - i] b) ∧
          F.coding.code f ∉ fineRetentionFailures
            (Q.coarseLaw (p.lev (p.par^[ib - i] b)) (F.code (p.par^[ib - i] b)))
            (finitePacketHistory p.lev p.γ p.F stop) (F.U (p.par^[ib - i] b))
            (ENNReal.ofReal (1 / 8 : ℝ)) := by
  have hterm : ∀ w, current w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b} :=
    fun w => (hcurrent w).trans ((R.subset_H w).trans (hH w))
  obtain ⟨b, hblev, hω, hA0, hfloor⟩ := Parent.DensePacket.exists_dense_packet_at_level hd hp ib hib
    current hterm hdensity hmass
  -- the ancestor at level `i`
  have hn : ib - i ≤ p.lev b := by omega
  obtain ⟨hal, hag, haF⟩ := Broad.iterate_par_spec hp.toOriginal (ib - i) b hn
  change p.lev (p.par^[ib - i] b) = p.lev b - (ib - i) at hal
  change p.γ (p.par^[ib - i] b) = p.γ b at hag
  change p.F b ⊆ p.F (p.par^[ib - i] b) at haF
  have hal' : p.lev (p.par^[ib - i] b) = i := by omega
  have haA : p.A b ⊆ p.A (p.par^[ib - i] b) := hp.iterate_par_assignment (ib - i) b hn
  set a := p.par^[ib - i] b with ha_def
  -- every residual event of `b` identifies `a` as its active level-`i` packet
  have hwit : ∀ x ∈ current (p.γ b) ∩ p.F b,
      F.active a ∧ (p.γ b, x) ∈ F.U a ∧ ∃ f, p.lev f = stop ∧ p.γ f = p.γ b ∧
        x ∈ p.packetWitness m stop (p.γ b) f ∧
        F.coding.code f ∉ Q.intrinsicNarrowStates F.code stop F.U r fraction a ∧
        F.coding.code f ∉ fineRetentionFailures (Q.coarseLaw (p.lev a) (F.code a))
          (finitePacketHistory p.lev p.γ p.F stop) (F.U a) (ENNReal.ofReal (1 / 8 : ℝ)) := by
    intro x hx
    obtain ⟨b', hb'lev, hb'γ, hxb', hact, hU, f, hflev, hfγ, hxf, hnar, hret⟩ :=
      R.witness (p.γ b) x (hcurrent (p.γ b) hx.1)
    -- uniqueness of the level-`i` packet of `x`
    have huniq : packetUnique p.lev p.γ p.F (p.γ b) x := by
      have htag : p.lev f = stop ∧ p.γ f = p.γ b := ⟨hflev, hfγ⟩
      simp only [PathData.packetWitness, ite_eq_left htag, mem_inter_iff, mem_ofPred_eq] at hxf
      exact hxf.1.2
    have hab' : a = b' := huniq a b' (hal'.trans hb'lev.symm) hag hb'γ (haF hx.2) hxb'
    subst hab'
    rw [hb'γ] at hU
    exact ⟨hact, hU, f, hflev, hfγ, hxf, hnar, hret⟩
  -- the residual events of `b` are nonempty, so `a` is active
  have hpos : 0 < ((d.ν k (p.γ b)).prod volume) (current (p.γ b) ∩ p.F b) := by
    refine lt_of_lt_of_le ?_ hfloor
    apply ENNReal.mul_pos (by simpa using hdensity)
    refine mul_ne_zero hA0 ?_
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, inv_pos]
    positivity
  obtain ⟨x₀, hx₀⟩ := nonempty_of_measure_ne_zero hpos.ne'
  refine ⟨b, hblev, hω, hA0, hfloor, hal', hag, haF, haA,
    (hwit x₀ hx₀).1, fun x hx => (hwit x hx).2⟩


end

end Submission.Obl.k4_isotropic_path_improvement.S294.Forward
