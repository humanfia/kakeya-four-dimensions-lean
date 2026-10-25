-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Gain
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Counts
import Submission.WZ.Obl.wz_nonflat_factored_improvement.SmallCount
import Submission.WZ.Obl.wz_nonflat_factored_improvement.CellProduct
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Prisms
import Submission.WZ.Obl.wz_nonflat_factored_improvement.CoarseGeometry
import Submission.WZ.Obl.wz_nonflat_factored_improvement.CoarseCount
import Submission.WZ.Obl.wz_nonflat_factored_improvement.CoarseNet
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Incidences
import Submission.WZ.Obl.wz_nonflat_factored_improvement.CoarseSlabs
import Submission.WZ.Obl.wz_nonflat_factored_improvement.AffineNet
import Submission.WZ.Obl.wz_nonflat_factored_improvement.FineGeometry
import Submission.WZ.Obl.wz_nonflat_factored_improvement.FineMap
import Submission.WZ.Obl.wz_nonflat_factored_improvement.AffineCounts
import Submission.WZ.Obl.wz_nonflat_factored_improvement.FineEstimate
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Grid
import Submission.WZ.Obl.wz_nonflat_factored_improvement.GridGeometry
import Submission.WZ.Obl.wz_nonflat_factored_improvement.GridUnion
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Selection
import Submission.WZ.Obl.wz_nonflat_factored_improvement.CellRegularization
import Submission.WZ.Obl.wz_nonflat_factored_improvement.PrismRegularization
import Submission.WZ.Obl.wz_nonflat_factored_improvement.FineNormalized
import Submission.WZ.Obl.wz_nonflat_factored_improvement.FineCells
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Packets
import Submission.WZ.Obl.wz_nonflat_factored_improvement.CoarseEstimate
import Submission.WZ.Obl.wz_nonflat_factored_improvement.CoarseFamily
import Submission.WZ.Obl.wz_nonflat_factored_improvement.RealWeight
import Submission.WZ.Obl.wz_nonflat_factored_improvement.FiniteProduct
import Submission.WZ.Obl.wz_nonflat_factored_improvement.SaturationPacking
import Submission.WZ.Obl.wz_nonflat_factored_improvement.DirectEstimate
import Submission.WZ.Obl.wz_nonflat_factored_improvement.ScaleAlgebra
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Admissibility
import Submission.WZ.Obl.wz_nonflat_factored_improvement.ProductLoss
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Product
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_nonflat_factored_improvement`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_nonflat_factored_improvement`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_nonflat_factored_improvement/`
belong to this obligation.
-/

theorem WangZahlLot.wz_nonflat_factored_improvement : ∀ σ ω u:ℝ, (fun (B:Set (EuclideanSpace ℝ (Fin 3))) => (fun (μ:MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) => (fun (o:ℝ → ENNReal) => (fun (T:ℝ → (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))) => (fun (H:ℝ → ℝ → (n:ℕ) → (Fin n → (EuclideanSpace ℝ (Fin 3))) → (Fin n → (EuclideanSpace ℝ (Fin 3))) → (Fin n → Set (EuclideanSpace ℝ (Fin 3))) → Prop → Prop) => (fun (J:(ℝ → ℝ → ℝ → ℝ → Prop) → Prop) => (fun (K:ℝ → ℝ → ℝ → (n:ℕ) → (Fin n → (EuclideanSpace ℝ (Fin 3))) → (Fin n → (EuclideanSpace ℝ (Fin 3))) → Prop → Prop) => (fun (Q:ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → Prop) => (fun (D:ℝ → ℝ → Prop) => (fun (E:ℝ → ℝ → Prop) => (fun (F:ℝ → ℝ → ℝ → ℝ → ℝ → (n:ℕ) → (Fin n → (EuclideanSpace ℝ (Fin 3))) → (Fin n → (EuclideanSpace ℝ (Fin 3))) → Prop) => (fun (R:ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℕ → ENNReal) => 0 < σ → σ ≤ 1/2 → 0 < ω → ω < u → D σ ω → E σ u → ∀ ζ:ℝ, 0 < ζ → ∃ β:ℝ, 0 < β∧∃ α:ℝ, 0 < α∧∀ ε:ℝ, 0 < ε → ∃ A:ℝ, 0 < A∧∃ η:ℝ, 0 < η∧∃ d:ℝ, 0 < d∧∀ ν:ℝ, 0 < ν → ν ≤ η → ∀ δ:ℝ, 0 < δ → δ ≤ (1/100:ℝ) → δ ≤ d → ∀ m:ℝ, 1 ≤ m → ∀ (n:ℕ) (x v:Fin n → (EuclideanSpace ℝ (Fin 3))) (Y:Fin n → Set (EuclideanSpace ℝ (Fin 3))), H ν δ n x v Y (K δ m (δ^(-ν)) n x v ((∀ i, o (δ^ν*δ^2) ≤ μ (Y i)) → ∀ a b:ℝ, δ ≤ a → a ≤ b → b ≤ 2 → F ν δ a b m n x v → a*b ≤ δ^(ζ / 2) → δ^β*b < a → R σ (u - α) ε A δ m n ≤ μ (⋃ i, Y i)))) (fun σ w ε A δ m n => o (A*δ^(w+ε)*m⁻¹*(n*δ^2)*(m^(-(3/2:ℝ))*(n*δ))^(-σ)))) (fun ν δ a b m n x v => ∃ (k:ℕ) (g:Fin k → Fin n), Function.Injective g∧0 < k∧δ^ν*n ≤ k∧∃ c:ℝ, 1 ≤ c∧c ≤ m∧(∀ U:Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ U → o ((Set.ncard {i | T δ (x (g i)) (v (g i))⊆U}:ℝ)*δ^2) ≤ o c*μ U)∧∃ (q:ℕ), 0 < q∧∃ W:Fin q → Set (EuclideanSpace ℝ (Fin 3)), (∀ j, ∃ e:AffineIsometryEquiv ℝ (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)), W j=e '' {p:(EuclideanSpace ℝ (Fin 3)) | |p 0| ≤ a∧|p 1| ≤ b∧|p 2| ≤ 2})∧(∀ i, ∃ j, T δ (x (g i)) (v (g i))⊆W j)∧(∀ i, (Set.ncard {j | T δ (x (g i)) (v (g i))⊆W j}:ℝ) ≤ δ^(-ν))∧(∀ j j', (Set.ncard {i | T δ (x (g i)) (v (g i))⊆W j}:ℝ) ≤ δ^(-ν)*(Set.ncard {i | T δ (x (g i)) (v (g i))⊆W j'}:ℝ))∧(∀ j, δ^ν*c*a*b ≤ (Set.ncard {i | T δ (x (g i)) (v (g i))⊆W j}:ℝ)*δ^2)∧(∀ U:Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ U → o ((Set.ncard {j | W j⊆U}:ℝ)*a*b) ≤ o (δ^(-ν))*μ U)∧(∀ j, ∀ U:Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ U → o ((Set.ncard {i | T δ (x (g i)) (v (g i))⊆W j∧T δ (x (g i)) (v (g i))⊆U}:ℝ)*a*b) ≤ o (δ^(-ν)*(Set.ncard {i | T δ (x (g i)) (v (g i))⊆W j}:ℝ))*μ U))) (fun s w => J (fun ε a η δ => ∀ m l:ℝ, 1 ≤ m → 1 ≤ l → Q η δ m l (fun N => a*δ^(w+ε)*m⁻¹*(N*δ^2)*(m^(-(3/2:ℝ))*l*(N*δ))^(-s))))) (fun s w => J (fun ε a η δ => Q η δ (δ^(-η)) (δ^(-η)) (fun N => a*δ^(w+ε)*(N*δ^2)*(N*δ)^(-s))))) (fun η δ m l f => ∀ (n:ℕ) (x v:Fin n → (EuclideanSpace ℝ (Fin 3))) (Y:Fin n → Set (EuclideanSpace ℝ (Fin 3))), H η δ n x v Y (K δ m l n x v (o (f n) ≤ μ (⋃ i, Y i))))) (fun δ m l n x v P => (∀ W:Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ W → o ((Set.ncard {i | T δ (x i) (v i)⊆W}:ℝ)*δ^2) ≤ o m*μ W) → (∀ (u:(EuclideanSpace ℝ (Fin 3))) (t r:ℝ), ‖u‖=1 → 0 < r → o (Set.ncard {i | T δ (x i) (v i)⊆(B∩{p | |inner ℝ u p - t| ≤ r})}:ℝ) ≤ o (l*n)*μ (B∩{p | |inner ℝ u p - t| ≤ r})) → P)) (fun P => ∀ ε:ℝ, 0 < ε → ∃ a:ℝ, 0 < a∧∃ η:ℝ, 0 < η∧∀ δ:ℝ, 0 < δ → δ ≤ 1/100 → P ε a η δ)) (fun η δ n x v Y P => 0 < n → (∀ i, ‖v i‖=1) → (∀ i, T δ (x i) (v i)⊆B) → (∀ i j, i ≠ j → μ (T δ (x i) (v i)∩T δ (x j) (v j)) ≤ (1/2:ENNReal)*μ (T δ (x i) (v i))) → (∀ i, MeasurableSet (Y i)) → (∀ i, Y i⊆T δ (x i) (v i)) → o (δ^η*n*δ^2) ≤ Finset.sum Finset.univ (fun i => μ (Y i)) → P)) (fun δ x v => Metric.thickening δ (segment ℝ x (x+v)))) (ENNReal.ofReal)) (MeasureTheory.volume)) (Metric.ball (0:(EuclideanSpace ℝ (Fin 3))) 1) := by
  intro σ ω u hσ hσ1 _hω hgap hD hE ζ hζ
  change WangZahlLot.Obl.wz_nonflat_factored_improvement.EstimateD σ ω at hD
  change WangZahlLot.Obl.wz_nonflat_factored_improvement.EstimateE σ u at hE
  change WangZahlLot.Obl.wz_nonflat_factored_improvement.NonflatImprovement σ u ζ
  exact WangZahlLot.Obl.wz_nonflat_factored_improvement.improvement_of_product hgap
    (WangZahlLot.Obl.wz_nonflat_factored_improvement.has_two_scale_product
      hσ.le hσ1 hgap hD hE) ζ hζ
