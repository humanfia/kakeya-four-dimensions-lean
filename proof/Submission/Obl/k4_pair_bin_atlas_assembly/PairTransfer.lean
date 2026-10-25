import Submission.Obl.k4_pair_bin_atlas_assembly.PairRepresentatives
import Submission.Obl.k4_pair_bin_atlas_assembly.AnchorParameters
import Submission.Obl.k4_pair_bin_atlas_assembly.BinKernel
import Submission.Obl.k4_pair_bin_atlas_assembly.AnchorEndpoints

namespace Submission.Obl.k4_pair_bin_atlas_assembly

open Set MeasureTheory
open Submission.Obl.k4_quadratic_atlas_normalization (δ)

namespace PairData

variable {Nk : ℝ} {Wk : ℕ}
    {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure Trajectory}
    {Ek : Fin Wk → Set Incidence} {Bk : Fin Wk → ℝ}
    {L a h : ℝ} {M D : ℕ} {ε : ℝ}
    (p : PairData Nk Wk ωk νk Ek Bk L a h M D ε)
    {Cs : ℕ} (k : BinKernel Cs)

noncomputable def bins (α : EuclideanSpace ℝ (Fin 3)) (s : Fin p.m) : Finset (Fin k.d → ℤ) :=
  k.Bins Nk a (δ Nk L) (p.P s) α

/-- The local trajectory estimates supplied by the analytic kernel. -/
def shortBounds (s : Fin p.m) (v : PairPoint) (R : MvPolynomial (Fin 4) ℝ) : Prop :=
  ∀ t ∈ p.block s, |t - v.2.1| ≤ Nk ^ (-(k.CR * a)) / (2 : ℝ) ^ p.T →
    |MvPolynomial.eval (Fin.snoc (fun i => p.baseLine s v.1 t i) (p.hiddenLine s v.1 t)) R| ≤
        δ Nk L * Nk ^ (k.CK * a) ∧
      |MvPolynomial.eval (Fin.snoc (fun i => p.baseLine s v.1 t i) (p.hiddenLine s v.1 t))
        (MvPolynomial.pderiv (3 : Fin 4) R)| ≤ Nk ^ (k.CK * a)

/-- A safe successful pair supplies a valid source bin, an observable neighbour
bin and a representative equation with the kernel's short-interval bounds. -/
theorem exists_short_representative
    (hNk : 0 < Nk) (hAt : k.At Nk a (δ Nk L) ((2 : ℝ) ^ p.T) M)
    (θ : AnchorParameter) (hθ : θ ∈ anchorDomain)
    (s : Fin p.m) (v : PairPoint) (hv : v ∈ p.H s)
    (hsafe : ∀ s' ∈ p.sourceList s v,
      Nk ^ (-a) ≤ |MvPolynomial.eval (fun n => p.sourceBase s v n) (disc (p.P s'))| →
      SafeFor ((Nk ^ a) ^ (-(Cs : ℝ))) (disc (p.P s)) (disc (p.P s'))
        (p.sourceBase s v) θ.1 θ.2) :
    ∃ β ∈ p.bins k θ.1 s, ∃ r : Fin p.m,
      p.representative (p.bins k θ.1) θ.1 ((Nk ^ a) ^ (-(Cs : ℝ))) (p.frame s) β = some r ∧
      (∃ s' ∈ p.sourceList s v, p.frame s' = p.frame s ∧
        ∃ β' ∈ p.bins k θ.1 s', ∀ i, |β i - β' i| ≤ 1) ∧
      p.shortBounds k s v (p.P r) := by
  obtain ⟨s', hs', hframe, hlocal⟩ := p.localPair_witness s hv
  have hpath := hsafe s' hs' hlocal.2.1
  obtain ⟨β, hβ, β', hβ', hnear, htransfer⟩ :=
    hAt (p.P s) (p.P s') (p.sourceBase s v) θ.1 θ.2 (p.baseLine s v.1)
      (p.hiddenLine s v.1) v.2.1 (p.block s) (p.tests s) (p.tests s')
      (p.sourceBase_norm s hv) (p.source_time s hv) rfl (p.baseLine_lipschitz s hv)
      hlocal hθ.1 hθ.2 hpath
  have hρ : 0 < (Nk ^ a) ^ (-(Cs : ℝ)) :=
    Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hNk a) _
  have hgood : p.anchorGood θ.1 ((Nk ^ a) ^ (-(Cs : ℝ))) s :=
    (hpath.anchor_bounds hρ).1
  obtain ⟨r, hr, _, hβr, hgoodr⟩ :=
    p.representative_exists (p.bins k θ.1) θ.1 ((Nk ^ a) ^ (-(Cs : ℝ))) s β hβ hgood
  refine ⟨β, hβ, r, hr, ⟨s', hs', hframe, β', hβ', hnear⟩, ?_⟩
  exact htransfer (p.P r) (p.tests r) hgoodr hβr

end PairData
end Submission.Obl.k4_pair_bin_atlas_assembly
