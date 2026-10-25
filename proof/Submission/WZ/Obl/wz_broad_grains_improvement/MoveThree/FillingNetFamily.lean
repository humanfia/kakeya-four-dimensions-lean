-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.FillingNetFamily.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/FillingNetFamily.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641 commit 7652d3d, FillingNetFamily.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.SummedNet
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.FirstPacketFilling
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyTransport
import Submission.WZ.Obl.wz_transverse_cell_weighted_cover.Assembly

set_option autoImplicit false

noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open scoped ENNReal Classical
open WangZahlLot.Obl.wz_flat_factored_improvement (BodyConvexCount)
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover (prism cTube netConst asm_measurableSet_image)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent (uniformMap uniformMap_volume)

/-- All packet normalizations have the same volume factor after the common
contraction. The packet centre and frame do not enter the factor. -/
theorem contracted_flat_normalization_volume {a b k : ℝ} (hk : 0 < k) (f : V ≃ᵃ[ℝ] V)
    (hfvol : ∀ Q : Set V, μ (f '' Q) = O (1 / (4 * a * b)) * μ Q)
    (Q : Set V) :
    μ ((f.trans (uniformMap hk).toAffineEquiv) '' Q) =
      O (k ^ 3 / (4 * a * b)) * μ Q := by
  have he : (f.trans (uniformMap hk).toAffineEquiv) '' Q =
      uniformMap hk '' (f '' Q) := by rw [Set.image_image]; rfl
  rw [he]
  have hcvol : μ (uniformMap hk '' (f '' Q)) = O (k ^ 3) * μ (f '' Q) :=
    uniformMap_volume hk _
  rw [hcvol, hfvol, ← mul_assoc]
  dsimp only [O]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 2
  ring

/-- Compose the filled square prisms with the balanced net estimate. The body
count retains its original coefficient, and the low-fibre estimate is written
with one common Jacobian times the sum of the original packet volumes. -/
theorem filled_packet_balanced_nets {σ ω : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hω : 0 < ω) (hE : E σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ A η d₀ : ℝ, 0 < A ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (Kc : ℝ), 1 ≤ Kc →
      ∀ {ι : Type} (Lab : Finset ι) (n d : ℕ) (I : ι → Finset (Fin n))
        (U : Fin n → Set V) (x v : Fin n → V) (Y : ι → Fin n → Set V)
        (f : ι → V ≃ᵃ[ℝ] V) (u : ι → Fin n → Fin 3 → V)
        (r B Λ w M D J : ℝ),
      (n : ℝ) ≤ δ ^ (-100 : ℝ) → 0 < d → 1 < Λ → (n : ℝ) < Λ ^ d →
      4 * δ ≤ B → B ≤ 1 / 1000000 → 0 < w → 0 < M → 0 < J →
      6144 * δ ^ η ≤ D → BodyConvexCount U w M →
      (∀ i, U i ⊆ T r (x i) (v i)) →
      (∀ ℓ ∈ Lab, (I ℓ).Nonempty ∧ (∀ i, MeasurableSet (Y ℓ i)) ∧
        (∀ Q : Set V, μ (f ℓ '' Q) = O J * μ Q) ∧
        ∀ i ∈ I ℓ, Orthonormal ℝ (u ℓ i) ∧
          ‖f ℓ (x i + (1 / 2 : ℝ) • v i)‖ < 1 / 100 ∧
          f ℓ '' T r (x i) (v i) ⊆
            prism B B (f ℓ (x i + (1 / 2 : ℝ) • v i)) (u ℓ i) ∧
          O (D * B ^ 2) ≤ μ (prism B B (f ℓ (x i + (1 / 2 : ℝ) • v i))
            (u ℓ i) ∩ f ℓ '' (⋃ j, Y ℓ j))) →
      ∃ (N q : ι → ℕ) (k : ∀ ℓ, Fin (N ℓ) → Fin n)
        (Fib : ∀ ℓ, Fin (N ℓ) → Finset (Fin n)),
        (∀ ℓ ∈ Lab, 0 < N ℓ ∧ 0 < q ℓ ∧ (∀ j, k ℓ j ∈ I ℓ) ∧
          (∀ j, Fib ℓ j ⊆ I ℓ) ∧ (∀ j, (Fib ℓ j).card = q ℓ) ∧
          (∀ j j', j ≠ j' → Disjoint (Fib ℓ j) (Fib ℓ j')) ∧
          netConst * ((I ℓ).card : ℝ) ≤ (d : ℝ) * Λ * N ℓ * q ℓ ∧
          (∀ j, ∀ i ∈ Fib ℓ j, f ℓ '' U i ⊆
            cTube B (f ℓ (x (k ℓ j) + (1 / 2 : ℝ) • v (k ℓ j))) (u ℓ (k ℓ j))) ∧
          (∀ j j', j ≠ j' →
            μ (cTube B (f ℓ (x (k ℓ j) + (1 / 2 : ℝ) • v (k ℓ j))) (u ℓ (k ℓ j)) ∩
              cTube B (f ℓ (x (k ℓ j') + (1 / 2 : ℝ) • v (k ℓ j'))) (u ℓ (k ℓ j'))) ≤
            (1 / 2 : ℝ≥0∞) *
              μ (cTube B (f ℓ (x (k ℓ j) + (1 / 2 : ℝ) • v (k ℓ j))) (u ℓ (k ℓ j))))) ∧
        ∑ ℓ ∈ Lab.filter (fun ℓ => (q ℓ : ℝ) * (J * w) ≤ M * (4 * B) ^ 2 / Kc),
            O (lowQCoeff A δ ε B ω σ (J * w) M Λ d * Kc ^ (σ / 2) * (I ℓ).card) ≤
          O J * ∑ ℓ ∈ Lab.filter (fun ℓ => (q ℓ : ℝ) * (J * w) ≤ M * (4 * B) ^ 2 / Kc),
            μ (⋃ i, Y ℓ i) := by
  intro ε hε
  obtain ⟨A, η, d₀, hA, hη, hd₀, hd₀small, H⟩ :=
    summed_low_q_net_conc hσ hσhalf hω hE ε hε
  refine ⟨A, η, d₀, hA, hη, hd₀, hd₀small, ?_⟩
  intro δ hδ hδd Kc hKc ι Lab n d I U x v Y f u r B Λ w M D J hn hd hΛ hnΛ
    hδB hB hw hM hJ hD hK hUT hfilled
  let centers := fun ℓ i => f ℓ (x i + (1 / 2 : ℝ) • v i)
  let Γ := fun ℓ => f ℓ '' (⋃ i, Y ℓ i)
  let shades := fun ℓ i => prism B B (centers ℓ i) (u ℓ i) ∩ Γ ℓ
  have hB0 : 0 ≤ B := le_trans (by positivity : 0 ≤ 4 * δ) hδB
  have hinputs (ℓ : ι) (hℓ : ℓ ∈ Lab) :
      (I ℓ).Nonempty ∧ MeasurableSet (Γ ℓ) ∧
        (∀ i ∈ I ℓ, Orthonormal ℝ (u ℓ i)) ∧
        (∀ i ∈ I ℓ, ‖centers ℓ i‖ < 1 / 100) ∧
        (∀ i ∈ I ℓ, f ℓ '' U i ⊆ prism B B (centers ℓ i) (u ℓ i)) ∧
        (∀ i ∈ I ℓ, shades ℓ i ⊆ Γ ℓ ∩ prism B B (centers ℓ i) (u ℓ i)) ∧
        (∀ i ∈ I ℓ, O (D * B ^ 2) ≤ μ (shades ℓ i)) ∧
        BodyConvexCount (fun i => f ℓ '' U i) (J * w) M := by
    obtain ⟨hI, hYm, hvol, hf⟩ := hfilled ℓ hℓ
    refine ⟨hI, asm_measurableSet_image _ (MeasurableSet.iUnion hYm),
      fun i hi => (hf i hi).1, fun i hi => (hf i hi).2.1, ?_, ?_,
      fun i hi => (hf i hi).2.2.2, ?_⟩
    · exact fun i hi => (image_mono (hUT i)).trans (hf i hi).2.2.1
    · exact fun _ _ p hp => ⟨hp.2, hp.1⟩
    · exact hK.affine_image hw.le hJ (f ℓ) hvol
  obtain ⟨N, q, k, Fib, hnet, hsum⟩ := H δ hδ hδd Kc hKc Lab n d I
    (fun ℓ i => f ℓ '' U i) shades Γ centers u B B Λ (J * w) M D hn hd hΛ hnΛ
    hB0 le_rfl hδB hB (by positivity) hM hD hinputs
  refine ⟨N, q, k, Fib, hnet, hsum.trans_eq ?_⟩
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  exact (hfilled ℓ (Finset.mem_filter.mp hℓ).1).2.2.1 _

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
