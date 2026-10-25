import Submission.Obl.k4_narrow_projected_row_parents.ModelLoss
import Submission.Obl.k4_general_parent_projected_layers.Support.ParentMass

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Filter
open Submission.Obl.k4_general_parent_projected_layers

noncomputable section

/-- Reassemble the frozen data record from the accepted numerical and
prepared-model records. Both projections are exact. -/
def modelOfPrepared {α : Type} [MeasurableSpace α] (p : Parameters)
    (a : PreparedModel α) : Model α :=
  ⟨p.N, p.K, p.d, p.kappa, p.ell, p.S, p.U, p.e₀,
    a.nu, a.mu, a.rho, a.pi, a.b, a.P, a.T, a.n, a.j, a.A, a.B, a.c, a.F⟩

theorem parameters_modelOfPrepared {α : Type} [MeasurableSpace α]
    (p : Parameters) (a : PreparedModel α) : Model.parameters (modelOfPrepared p a) = p := rfl

theorem prepared_modelOfPrepared {α : Type} [MeasurableSpace α]
    (p : Parameters) (a : PreparedModel α) : Model.prepared (modelOfPrepared p a) = a := rfl

namespace Parameters

/-- Increase only the permitted loss of the accepted numerical record. -/
def withLoss (p : Submission.Obl.k4_general_parent_projected_layers.Parameters)
    (M : ℕ → ℝ) : Submission.Obl.k4_general_parent_projected_layers.Parameters :=
  { p with K := M }

theorem Valid.withLoss {p : Submission.Obl.k4_general_parent_projected_layers.Parameters}
    (hp : p.Valid) {M : ℕ → ℝ} (hKM : ∀ k, p.K k ≤ M k)
    (hM : Model.Subpow p.N M) : (withLoss p M).Valid := by
  rcases hp with ⟨hN, hlim, hsub, hd, hd1, hκ, hκ1, hℓ, hS, hS1, hU, he₀⟩
  exact ⟨hN, hlim, ⟨fun k => (hsub.1 k).trans (hKM k), hM⟩,
    hd, hd1, hκ, hκ1, hℓ, hS, hS1, hU, he₀⟩

end Parameters

namespace PreparedModel

variable {α : Type} [MeasurableSpace α]
  {p : Submission.Obl.k4_general_parent_projected_layers.Parameters} {a : PreparedModel α}

theorem Common.withLoss (h : a.Common p) {M : ℕ → ℝ}
    (hK : ∀ k, 0 < p.K k) (hKM : ∀ k, p.K k ≤ M k) :
    a.Common (Parameters.withLoss p M) :=
  Model.basic_withLoss (modelOfPrepared p a) h hK hKM

theorem Caps.withLoss (h : a.Caps p) {M : ℕ → ℝ}
    (hN : ∀ k, 0 < p.N k) (hKM : ∀ k, p.K k ≤ M k) :
    a.Caps (Parameters.withLoss p M) :=
  Model.caps_withLoss (modelOfPrepared p a) h hN hKM

theorem AtlasAt.withLoss {R : ℝ} {k : ℕ} {s : ℝ}
    (h : a.AtlasAt p R k s) {M : ℕ → ℝ}
    (hN : 0 < p.N k) (hK : 0 < p.K k) (hKM : p.K k ≤ M k) :
    a.AtlasAt (Parameters.withLoss p M) R k s :=
  Model.atlasAt_withLoss (modelOfPrepared p a) h hN hK hKM

theorem Valid.withLoss (h : a.Valid p) {M : ℕ → ℝ}
    (hN : ∀ k, 0 < p.N k) (hK : ∀ k, 0 < p.K k) (hKM : ∀ k, p.K k ≤ M k) :
    a.Valid (Parameters.withLoss p M) := by
  rcases h with ⟨hcommon, hcaps, hatlas, hnested⟩
  refine ⟨Common.withLoss hcommon hK hKM, Caps.withLoss hcaps hN hKM, ?_, hnested⟩
  intro R hR
  filter_upwards [hatlas R hR] with k hk
  intro s hs hsU
  exact AtlasAt.withLoss (hk s hs hsU) (hN k) (hK k) (hKM k)

end PreparedModel

/-- The accepted fixed-power filling bound is monotone in the permitted loss. -/
theorem parentFilling_mono {K M a : ℝ} (hK : 0 ≤ K) (hKM : K ≤ M) (ha : 0 < a) :
    parentFilling K a ≤ parentFilling M a := by
  unfold parentFilling
  gcongr

end

end Submission.Obl.k4_narrow_projected_row_parents
