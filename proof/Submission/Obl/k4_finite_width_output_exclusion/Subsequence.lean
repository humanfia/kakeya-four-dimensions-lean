import Submission.Obl.k4_finite_width_output_exclusion.Interfaces

namespace Submission.Obl.k4_finite_width_output_exclusion

open MeasureTheory Filter

noncomputable section

def Data.reindex (p : Data) (φ : ℕ → ℕ) : Data where
  N := p.N ∘ φ
  K := p.K ∘ φ
  L := p.L
  d := p.d
  S := p.S
  η := p.η
  W := p.W ∘ φ
  ω := fun k => p.ω (φ k)
  ν := fun k => p.ν (φ k)
  E := fun k => p.E (φ k)
  P := fun k => p.P (φ k)
  B := fun k => p.B (φ k)
  f := p.f
  g := fun k => p.g (φ k)
  G := fun k => p.G (φ k)

lemma valid_reindex {p : Data} (hp : Valid p) {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) : Valid (p.reindex φ) := by
  rcases hp with ⟨hN, ht, hK, hL, hd, hd1, hS, hη,
    ⟨M, D, hfmt⟩, hg, hG, hLip, htyp, hcap, hang⟩
  refine ⟨fun k => hN (φ k), ht.comp hφ,
    ⟨fun k => hK.1 (φ k), fun ε hε => hφ.eventually (hK.2 ε hε)⟩,
    hL, hd, hd1, hS, hη, ⟨M, D, fun k => hfmt (φ k)⟩,
    fun k => hg (φ k), fun k => hG (φ k), hLip, ?_, hcap, ?_⟩
  · intro r τ hr hrL hτ
    obtain ⟨c, hc, h⟩ := htyp r τ hr hrL hτ
    exact ⟨c, hc, hφ.eventually h⟩
  · intro u τ hu huη hτ
    obtain ⟨c, hc, h⟩ := hang u τ hu huη hτ
    exact ⟨c, hc, hφ.eventually h⟩

def Atlas.reindex {p : Data} {φ : ℕ → ℕ} {k : ℕ} (a : Atlas p (φ k)) :
    Atlas (p.reindex φ) k where
  T := a.T
  C := a.C
  γ := a.γ
  j := a.j
  c := a.c
  u := a.u
  Q := a.Q
  R := a.R
  A := a.A
  F := a.F
  lst := a.lst

def Atlas.unreindex {p : Data} {φ : ℕ → ℕ} {k : ℕ} (a : Atlas (p.reindex φ) k) :
    Atlas p (φ k) where
  T := a.T
  C := a.C
  γ := a.γ
  j := a.j
  c := a.c
  u := a.u
  Q := a.Q
  R := a.R
  A := a.A
  F := a.F
  lst := a.lst

lemma cost_of_reindex {p : Data} {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    {h : ℝ} (hc : Cost (p.reindex φ) h) : Cost p h := by
  rw [cost_iff] at hc ⊢
  obtain ⟨M, D, hc⟩ := hc
  refine ⟨M, D, fun ε hε => hφ.frequently ?_⟩
  apply (hc ε hε).mono
  rintro k ⟨κ, hκ, hKκ, hκε, a, hT, ha⟩
  exact ⟨κ, hκ, hKκ, hκε, a.unreindex, hT, ha⟩

lemma narrow_of_reindex {p : Data} {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    {h w : ℝ} (hc : Narrow (p.reindex φ) h w) : Narrow p h w := by
  rw [narrow_iff] at hc ⊢
  obtain ⟨M, D, hc⟩ := hc
  refine ⟨M, D, fun ε hε => hφ.frequently ?_⟩
  apply (hc ε hε).mono
  rintro k ⟨κ, hκ, hKκ, hκε, a, hT, hw, ha⟩
  exact ⟨κ, hκ, hKκ, hκε, a.unreindex, hT, hw, ha⟩

end
end Submission.Obl.k4_finite_width_output_exclusion
